#!/usr/bin/env python3
"""Pull the Prove2Me mission's Lean sources; never upload or modify the platform.

Run: python3 PoincareConjecture/sync.py
Review the saved snapshot without network access: add --review-only.
Credentials: PROVE2ME_API_KEY or the gitignored .credentials.json beside this file.
Theorems are platform statement stubs, including sorry. Solutions are verbatim
accepted submissions, including conditional sketches, not curated library code.
Additional published theorem names can be followed through sync_targets.json;
they are synchronized without implying membership in the mission's root graph.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import HTTPRedirectHandler, Request, build_opener

BASE = "https://prove2.me/api/v1"
MISSION_ID = "29133a9f-c412-4f19-968e-3deae9a335b5"
ROOT = Path(__file__).resolve().parent


class NoRedirects(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise RuntimeError("Refusing an API redirect; credentials stay on prove2.me.")


class Client:
    def __init__(self, key):
        self.opener = build_opener(NoRedirects())
        self.token = None
        refreshed = self.request("/agent/refresh", {"api_key": key})
        self.token = refreshed["access_token"]
        self.version = refreshed.get("version")

    def request(self, path, body=None):
        if not path.startswith("/") or path.startswith("//"):
            raise ValueError("Expected a relative API path")
        headers = {"Accept": "application/json", "Content-Type": "application/json"}
        if self.token:
            headers["Authorization"] = "Bearer " + self.token
        data = None if body is None else json.dumps(body).encode()
        with self.opener.open(Request(BASE + path, data=data, headers=headers), timeout=60) as response:
            return json.load(response)

    def pages(self, path, key, **params):
        items, offset = [], 0
        while True:
            page = self.request(path + "?" + urlencode(dict(params, limit=100, offset=offset)))
            batch = page[key]
            items.extend(batch)
            total = page.get("total", page.get("pagination", {}).get("total"))
            offset += len(batch)
            if total is None:
                raise RuntimeError("Missing pagination total at " + path)
            if offset >= total:
                return items
            if not batch:
                raise RuntimeError("Incomplete pagination at " + path)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()


def module_name(name):
    name = name.replace(".", "_")
    if not re.fullmatch(r"[A-Za-z0-9_]+", name):
        raise ValueError("Unsupported platform module name: " + name)
    return name


def resolve_additional_theorems(client, names, revision):
    """Resolve explicit names in the mission environment, rejecting stale targets."""
    resolved = {}
    for name in names:
        if not isinstance(name, str) or not re.fullmatch(
                r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*", name):
            raise ValueError("Invalid additional theorem name")
        if name in resolved:
            continue
        rows = client.pages("/theorems", "theorems", theorem_name=name, env=revision)
        matches = [row for row in rows if row["theorem_name"] == name
                   and row["mathlib_rev"] == revision and not row.get("deprecated_at")]
        if len(matches) != 1:
            raise RuntimeError("Expected one active theorem in the mission environment: " + name)
        resolved[name] = matches[0]["theorem_id"]
    return resolved


def collect(client, additional_theorems=()):
    mission = next(m for m in client.pages("/missions", "missions") if m["id"] == MISSION_ID)
    milestones = client.pages("/missions/" + MISSION_ID + "/milestones", "milestones")
    root_id = mission["main_theorem"]["theorem_id"]
    pending = [root_id] + [m["theorem"]["id"] for m in milestones if m.get("theorem")]
    nodes, submissions, decompositions, files = {}, {}, {}, {}
    graph = client.request("/theorems/" + root_id + "/graph")
    root_revision = next(node["mathlib_rev"] for node in graph["nodes"]
                         if node.get("theorem_id") == root_id)
    additional = resolve_additional_theorems(client, additional_theorems, root_revision)
    pending.extend(additional.values())

    def add_file(path, content):
        data = content.encode()
        if path in files and files[path] != data:
            raise RuntimeError("Conflicting platform module: " + path)
        files[path] = data

    def add_definition(child):
        definition_id = child["definition_id"]
        if definition_id in nodes:
            return
        matches = client.pages("/theorems", "theorems", status="Definition",
                               theorem_name=child["definition_name"], env=child["mathlib_rev"])
        definition = next(d for d in matches if d["theorem_id"] == definition_id)
        definition["local_path"] = "Definitions/Def_" + module_name(definition["theorem_name"]) + ".lean"
        nodes[definition_id] = definition
        add_file(definition["local_path"], definition["definition"])

    for child in graph["nodes"]:
        if child["node_type"] == "definition":
            add_definition(child)

    while pending:
        theorem_id = pending.pop()
        if theorem_id in nodes:
            continue
        node = client.request("/theorems/" + theorem_id)
        nodes[theorem_id] = node
        name = module_name(node["theorem_name"])
        if node["status"] == "Definition":
            node["local_path"] = "Definitions/Def_" + name + ".lean"
            add_file(node["local_path"], node["definition"])
            continue
        node["local_path"] = "Theorems/Thm_" + name + ".lean"
        add_file(node["local_path"], node["preamble"] + "\n\n" + node["formal_statement"] + "\n")
        decomps = client.request("/theorems/" + theorem_id + "/decompositions")["decompositions"]
        decompositions[theorem_id] = decomps
        for decomp in decomps:
            for child in decomp["children"]:
                if child.get("theorem_id"):
                    pending.append(child["theorem_id"])
                elif child.get("definition_id"):
                    add_definition(child)
        for sub in client.pages("/theorems/" + theorem_id + "/submissions", "submissions",
                                status="ACCEPTED,SKETCH_ACCEPTED"):
            source = client.request("/submissions/" + sub["id"] + "/solution")["content"]
            sub["local_path"] = "Solutions/Sol_" + name + "_" + module_name(sub["id"].replace("-", "")) + ".lean"
            add_file(sub["local_path"], source)
            submissions[sub["id"]] = sub

    revisions = {n["mathlib_rev"] for n in nodes.values()}
    if len(revisions) != 1:
        raise RuntimeError("Mission spans multiple Mathlib environments; refusing to mix modules.")
    revision = revisions.pop()
    environments = client.request("/environments")["environments"]
    environment = next(e for e in environments if e["mathlib_rev"] == revision)
    metadata = {"mission": mission, "milestones": milestones, "environment": environment,
                "nodes": nodes, "submissions": submissions, "decompositions": decompositions,
                "graph": graph, "api_base": BASE,
                "additional_theorems": additional,
                "submission_statuses": ["ACCEPTED", "SKETCH_ACCEPTED"]}
    return files, metadata


def build_files(parent, environment):
    """Reuse the repository's exact dependency lock and downloaded Mathlib cache."""
    lock = json.loads((parent / "lake-manifest.json").read_text())
    mathlib = next(p for p in lock["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != environment["mathlib_rev"]:
        raise RuntimeError("Platform and OpenGALib Mathlib revisions differ; update the parent dependency first.")
    if (parent / "lean-toolchain").read_text().strip() != environment["toolchain"]:
        raise RuntimeError("Platform and OpenGALib Lean toolchains differ.")
    lock["name"] = "PoincareConjecture"
    lock["packagesDir"] = "../.lake/packages"
    config = '''import Lake
open Lake DSL

package PoincareConjecture where
  packagesDir := "../.lake/packages"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "REVISION"

@[default_target]
lean_lib Theorems where
  globs := #[.submodules `Theorems]

@[default_target]
lean_lib Definitions where
  globs := #[.submodules `Definitions]

@[default_target]
lean_lib Solutions where
  globs := #[.submodules `Solutions]
'''.replace("REVISION", environment["mathlib_rev"])
    return {"lakefile.lean": config.encode(), "lake-manifest.json": json_bytes(lock),
            "lean-toolchain": (environment["toolchain"] + "\n").encode()}


def safe_path(root, relative):
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError("Unsafe output path")
    target = root
    for part in path.parts:
        target = target / part
        if target.is_symlink():
            raise RuntimeError("Refusing to write through a symlink: " + relative)
    return target


def write_atomic(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(data)
    try:
        temporary.chmod(0o644)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def install(root, files, metadata):
    manifest_path = safe_path(root, "sync.json")
    previous = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
    hashes = previous.get("file_hashes", {})
    # Check every destination before changing any file. Keep locally edited code intact.
    for relative, data in files.items():
        path = safe_path(root, relative)
        if path.exists() and digest(path.read_bytes()) not in (hashes.get(relative), digest(data)):
            raise RuntimeError("Local changes found; move or reconcile this file before syncing: " + relative)
    changed = 0
    for relative, data in sorted(files.items()):
        path = safe_path(root, relative)
        if not path.exists() or path.read_bytes() != data:
            write_atomic(path, data)
            changed += 1
        hashes[relative] = digest(data)
    metadata["file_hashes"] = hashes
    metadata["retained_files"] = sorted(set(hashes) - set(files))
    metadata["synced_at"] = datetime.now(timezone.utc).isoformat()
    write_atomic(manifest_path, json_bytes(metadata))
    return changed


def review_status(metadata, curation):
    """Compare reviewed source revisions; platform acceptance alone is not library admission."""
    if curation and curation["mission_id"] != metadata["mission"]["id"]:
        raise ValueError("Curation records belong to a different mission")
    reviews = curation.get("reviews", {})
    result = {key: [] for key in
              ("integrated", "partially_integrated", "deferred", "new_proofs", "new_sketches", "needs_review")}
    for submission_id in sorted(set(metadata["submissions"]) | set(reviews)):
        sub = metadata["submissions"].get(submission_id)
        review = reviews.get(submission_id)
        if review:
            node = metadata["nodes"].get(sub["theorem_id"]) if sub else None
            source_matches = (sub and node and not sub.get("deprecated_at")
                              and not node.get("deprecated_at")
                              and sub["theorem_id"] == review["source_theorem_id"]
                              and sub["status"] == review["source_status"]
                              and node["mathlib_rev"] == review["source_mathlib_rev"]
                              and metadata["file_hashes"].get(sub["local_path"]) == review["source_sha256"])
            result[review["status"] if source_matches else "needs_review"].append(submission_id)
        elif sub and not sub.get("deprecated_at"):
            node = metadata["nodes"][sub["theorem_id"]]
            if node.get("deprecated_at"):
                continue
            if sub["status"] == "ACCEPTED":
                result["new_proofs"].append(submission_id)
            elif sub["status"] == "SKETCH_ACCEPTED":
                result["new_sketches"].append(submission_id)
    return result


def print_review(root, metadata):
    path = root / "curation.json"
    curation = json.loads(path.read_text()) if path.exists() else {}
    result = review_status(metadata, curation)
    print("Curation: {} integrated, {} partially integrated, {} deferred.".format(
        len(result["integrated"]), len(result["partially_integrated"]), len(result["deferred"])))
    print("To review: {} new complete proofs, {} new sketches, {} changed or unavailable sources.".format(
        len(result["new_proofs"]), len(result["new_sketches"]), len(result["needs_review"])))
    for category in ("new_proofs", "new_sketches", "needs_review"):
        for submission_id in result[category]:
            print("  {}: {}".format(category, submission_id))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--credentials", type=Path, default=ROOT / ".credentials.json",
                        help="JSON file containing api_key (never written to sync.json)")
    parser.add_argument("--review-only", action="store_true",
                        help="show curation status from the saved snapshot; do not access the network")
    args = parser.parse_args()
    if args.review_only:
        print_review(ROOT, json.loads((ROOT / "sync.json").read_text()))
        return
    key = os.environ.get("PROVE2ME_API_KEY")
    if not key:
        if not args.credentials.is_file():
            parser.error("Set PROVE2ME_API_KEY or supply --credentials PATH.")
        key = json.loads(args.credentials.read_text())["api_key"]
    targets_path = ROOT / "sync_targets.json"
    names = []
    if targets_path.exists():
        targets = json.loads(targets_path.read_text())
        if targets["mission_id"] != MISSION_ID or not isinstance(targets["theorem_names"], list):
            raise ValueError("Invalid additional synchronization targets")
        names = targets["theorem_names"]
    client = Client(key)
    if client.version != "0.9.8":
        raise RuntimeError("Platform version changed; refresh https://prove2.me/skill.md before synchronizing")
    files, metadata = collect(client, names)
    source_count = len(files)
    files.update(build_files(ROOT.parent, metadata["environment"]))
    changed = install(ROOT, files, metadata)
    print("Synced {} Lean source files, {} nodes, {} accepted submissions; {} files changed.".format(
        source_count, len(metadata["nodes"]), len(metadata["submissions"]), changed))
    print("Environment: " + metadata["environment"]["display_name"])
    print_review(ROOT, metadata)


if __name__ == "__main__":
    try:
        main()
    except HTTPError as error:
        print("Prove2Me HTTP {}. Check credentials if 401; no files were installed.".format(error.code), file=sys.stderr)
        sys.exit(1)
    except (URLError, RuntimeError, ValueError, KeyError, StopIteration, OSError) as error:
        print("Sync failed: {}".format(error), file=sys.stderr)
        sys.exit(1)
