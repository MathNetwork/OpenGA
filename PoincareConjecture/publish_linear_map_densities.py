#!/usr/bin/env python3
"""Publish the audited linear-map density theorems and their bilinear helper.

Run from the repository: python3 PoincareConjecture/publish_linear_map_densities.py
Repeat while jobs are pending. The manifest fixes the exact reviewed payloads.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
from urllib.error import HTTPError, URLError
from urllib.request import Request
from uuid import uuid4

from sync import BASE, Client, MISSION_ID, ROOT, safe_path, write_atomic, json_bytes

DIRECTORY = ROOT / "Contributions/LinearMapDensities"
RECORD = DIRECTORY / "publication.json"


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(record):
    write_atomic(RECORD, json_bytes(record))


def verify_item(client, entry, definition=False):
    item = client.request("/theorems/" + entry["publication"]["theorem_id"])
    fields = ("definition",) if definition else ("theorem_name", "formal_statement", "preamble")
    for key in fields:
        if item.get(key, "").strip() != entry["payload"][key].strip():
            raise RuntimeError("Published content differs: " + key)
    if item["mathlib_rev"] != entry["payload"]["env"]:
        raise RuntimeError("Published environment differs")
    return item


def publish(client, record, entry, definition=False):
    name = entry["payload"]["definition_name" if definition else "theorem_name"]
    publication = entry.get("publication")
    if not publication:
        matches = client.pages("/theorems", "theorems", theorem_name=name, env=entry["payload"]["env"])
        matches = [m for m in matches if m["theorem_name"] == name]
        if matches:
            raise RuntimeError("Name already exists; reconcile its source before reusing: " + name)
        publication = entry["publication"] = {"status": "SUBMITTING", "started_at": now()}
        save(record)
        response = client.request("/submit-definition" if definition else "/submit-problem", entry["payload"])
        publication["response"] = response
        save(record)
        job_id = response.get("job_id")
        if not job_id and len(response.get("jobs", [])) == 1:
            job_id = response["jobs"][0]["job_id"]
        if not job_id:
            raise RuntimeError("No job id; inspect the saved response")
        publication.update(status="PENDING", job_id=job_id)
        save(record)
        print("Queued:", name, job_id, flush=True)
        return False
    if publication["status"] != "PUBLISHED":
        if not publication.get("job_id"):
            raise RuntimeError("Uncertain request outcome; reconcile before retrying: " + name)
        job = client.request("/publish-jobs/" + publication["job_id"])
        publication.update(status=job["status"], job=job, checked_at=now())
        if job["status"] == "PUBLISHED":
            publication["theorem_id"] = job["theorem_id"]
        save(record)
        print("Publication:", name, job["status"], flush=True)
        if job["status"] in ("FAILED", "ERROR"):
            raise RuntimeError(job.get("error_message") or "Publication failed")
        if job["status"] != "PUBLISHED":
            return False
    verify_item(client, entry, definition)
    publication["verified_at"] = now()
    save(record)
    return True


def prove(client, record, entry):
    theorem = verify_item(client, entry)
    submission = entry.get("submission")
    if not submission:
        code = safe_path(DIRECTORY, entry["proof_path"]).read_bytes()
        boundary = "openga-" + uuid4().hex
        fields = {"theorem_id": theorem["theorem_id"], "proof_type": "prove",
                  "explanation": entry["explanation"]}
        parts = []
        for key, value in fields.items():
            parts.append(("--" + boundary + '\r\nContent-Disposition: form-data; name="' + key + '"\r\n\r\n' + value + "\r\n").encode())
        parts.append(("--" + boundary + '\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode() + code + b"\r\n")
        parts.append(("--" + boundary + "--\r\n").encode())
        submission = entry["submission"] = {"status": "SUBMITTING", "started_at": now()}
        save(record)
        request = Request(BASE + "/verify", data=b"".join(parts), method="POST", headers={
            "Authorization": "Bearer " + client.token, "Accept": "application/json",
            "Content-Type": "multipart/form-data; boundary=" + boundary})
        with client.opener.open(request, timeout=60) as response:
            result = json.load(response)
        submission.update(response=result, status=result.get("status"), submission_id=result.get("submission_id"))
        save(record)
        if not submission.get("submission_id"):
            raise RuntimeError("No submission id; reconcile the saved response")
        print("Proof queued:", entry["id"], submission["submission_id"], flush=True)
        return False
    if not submission.get("submission_id"):
        raise RuntimeError("Uncertain proof request; reconcile before retrying")
    if submission["status"] != "ACCEPTED":
        result = client.request("/verify?submission_id=" + submission["submission_id"])
        submission.update(status=result["status"], verdict=result, checked_at=now())
        save(record)
        print("Proof:", entry["id"], result["status"], flush=True)
        if result["status"] in ("PENDING", "COMPILING"):
            return False
        if result["status"] != "ACCEPTED":
            raise RuntimeError(result.get("error_message") or "Unexpected proof verdict")
    content = client.request("/submissions/" + submission["submission_id"] + "/solution")["content"]
    if digest(content.encode()) != entry["proof_sha256"]:
        raise RuntimeError("Accepted source differs from the validated proof")
    theorem = verify_item(client, entry)
    if theorem["status"] != "Proved":
        raise RuntimeError("Accepted proof has not resolved the theorem")
    submission.update(verified_at=now(), accepted_source_sha256=digest(content.encode()))
    save(record)
    return True


def finish(client, record):
    graphs = {}
    for entry in record["theorems"]:
        theorem_id = entry["publication"]["theorem_id"]
        graph = client.request("/theorems/" + theorem_id + "/graph")
        graphs[entry["id"]] = graph
        expected = {next(t for t in record["theorems"] if t["id"] == name)["publication"]["theorem_id"]
                    for name in entry["imports"]}
        decompositions = client.request("/theorems/" + theorem_id + "/decompositions")["decompositions"]
        matching = [d for d in decompositions if d["submission_id"] == entry["submission"]["submission_id"]]
        if expected:
            if len(matching) != 1:
                raise RuntimeError("Accepted proof decomposition missing")
            children = {c.get("theorem_id") for c in matching[0]["children"]}
            if not expected <= children:
                raise RuntimeError("Expected proof dependency missing")
    root_graph = client.request("/theorems/7ea2da12-4d1b-4bbc-8257-df87d92f5a8e/graph")
    root_ids = {n.get("theorem_id") for n in root_graph["nodes"]}
    record["root_graph_membership"] = {entry["id"]: entry["publication"]["theorem_id"] in root_ids
                                       for entry in record["theorems"]}
    write_atomic(DIRECTORY / "graphs.json", json_bytes(graphs))
    record.update(status="COMPLETE", verified_at=now())
    save(record)
    print("All four theorems are public and Proved; both reusable proof dependencies verified.", flush=True)


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    record = json.loads(RECORD.read_text())
    if record["mission_id"] != MISSION_ID or record["source_reviewed"] is not True:
        raise RuntimeError("Mission or source review mismatch")
    if record.get("validation", {}).get("status") != "passed":
        raise RuntimeError("Exact payload validation is required")
    for source in record["sources"]:
        if digest(safe_path(ROOT.parent, source["path"]).read_bytes()) != source["sha256"]:
            raise RuntimeError("Original source changed after export")
    for entry in record["theorems"]:
        for field, hash_field in (("path", "sha256"), ("proof_path", "proof_sha256")):
            if digest(safe_path(DIRECTORY, entry[field]).read_bytes()) != entry[hash_field]:
                raise RuntimeError("Export changed after validation: " + entry[field])
        exact = entry["payload"]["preamble"] + "\n\n" + entry["payload"]["formal_statement"] + "\n"
        if digest(exact.encode()) != entry["sha256"]:
            raise RuntimeError("Upload text differs from the compiled file")
        if entry["payload"]["env"] != record["mathlib_rev"]:
            raise RuntimeError("Inconsistent environment")
    if args.check_only:
        print("Validated the four exact theorem/solution pairs; no network request made.")
        return
    client = Client(json.loads((ROOT / ".credentials.json").read_text())["api_key"])
    envs = client.request("/environments")["environments"]
    if not any(e["mathlib_rev"] == record["mathlib_rev"] and e["toolchain"] == record["toolchain"] for e in envs):
        raise RuntimeError("Platform environment no longer matches")
    definition = client.request("/theorems/" + record["existing_definition"]["id"])
    if definition["mathlib_rev"] != record["mathlib_rev"] or definition["status"] != "Definition":
        raise RuntimeError("Existing definition environment or status differs")
    if digest(definition["definition"].encode()) != record["existing_definition"]["sha256"]:
        raise RuntimeError("Existing definition source differs")
    problems_ready = True
    for entry in record["theorems"]:
        problems_ready = publish(client, record, entry) and problems_ready
    if not problems_ready:
        return
    by_id = {entry["id"]: entry for entry in record["theorems"]}
    proofs_ready = True
    for entry in record["theorems"]:
        if any(by_id[d].get("submission", {}).get("status") != "ACCEPTED" for d in entry["imports"]):
            proofs_ready = False
            continue
        proofs_ready = prove(client, record, entry) and proofs_ready
    if proofs_ready:
        finish(client, record)


if __name__ == "__main__":
    try:
        main()
    except HTTPError as error:
        print("Prove2Me HTTP", error.code, file=sys.stderr)
        raise SystemExit(1)
    except (URLError, OSError, RuntimeError, KeyError, ValueError) as error:
        print("Publication stopped:", str(error), file=sys.stderr)
        raise SystemExit(1)
