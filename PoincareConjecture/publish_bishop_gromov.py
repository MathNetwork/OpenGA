#!/usr/bin/env python3
"""Publish validated Bishop-Gromov prerequisites; default to a local check only."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import sys
from urllib.error import HTTPError, URLError
from urllib.request import Request
from uuid import uuid4

from sync import BASE, Client, MISSION_ID, ROOT, json_bytes, safe_path, write_atomic

DIRECTORY = ROOT / "Contributions/BishopGromov"
RECORD = DIRECTORY / "publication.json"


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(record):
    write_atomic(RECORD, json_bytes(record))


def validate(record):
    if record["mission_id"] != MISSION_ID or record.get("source_reviewed") is not True:
        raise RuntimeError("The mission or source review does not match")
    if record.get("validation", {}).get("status") != "passed":
        raise RuntimeError("Compile, type-equivalence, and axiom checks must pass first")
    for source in record["sources"]:
        if digest(safe_path(ROOT.parent, source["path"]).read_bytes()) != source["sha256"]:
            raise RuntimeError("Reviewed source changed: " + source["path"])
    for entry in record["definitions"] + record["theorems"]:
        payload = entry["payload"]
        if payload["env"] != record["mathlib_rev"]:
            raise RuntimeError("Inconsistent environment")
        if "definition" in payload:
            code = payload["definition"]
        else:
            code = payload["preamble"] + "\n\n" + payload["formal_statement"] + "\n"
        if digest(code.encode()) != entry["sha256"]:
            raise RuntimeError("The payload differs from the validated source")
        if safe_path(DIRECTORY, entry["path"]).read_bytes() != code.encode():
            raise RuntimeError("A staged source has changed")
        if "proof_path" in entry:
            if digest(safe_path(DIRECTORY, entry["proof_path"]).read_bytes()) != entry["proof_sha256"]:
                raise RuntimeError("A validated proof has changed")


def verify_item(client, entry):
    item = client.request("/theorems/" + entry["publication"]["theorem_id"])
    payload = entry["payload"]
    fields = ("definition",) if "definition" in payload else ("theorem_name", "preamble", "formal_statement")
    for field in fields:
        if item.get(field, "").strip() != payload[field].strip():
            raise RuntimeError("Platform readback differs: " + field)
    if item["mathlib_rev"] != payload["env"]:
        raise RuntimeError("Platform readback uses a different environment")
    return item


def publish(client, record, entry):
    definition = "definition" in entry["payload"]
    name = entry["payload"]["definition_name" if definition else "theorem_name"]
    publication = entry.get("publication")
    if publication is None:
        matches = client.pages("/theorems", "theorems", theorem_name=name, env=record["mathlib_rev"])
        if any(item["theorem_name"] == name for item in matches):
            raise RuntimeError("Existing name requires reconciliation before publication: " + name)
        publication = entry["publication"] = {"status": "SUBMITTING", "started_at": now()}
        save(record)
        response = client.request("/submit-definition" if definition else "/submit-problem", entry["payload"])
        publication["response"] = response
        job_id = response.get("job_id")
        if not job_id and len(response.get("jobs", [])) == 1:
            job_id = response["jobs"][0]["job_id"]
        if job_id:
            publication.update(status="PENDING", job_id=job_id)
        save(record)
        if not job_id:
            raise RuntimeError("No publish job id; inspect the saved response before retrying")
        print("Queued:", name, flush=True)
        return False
    if publication["status"] != "PUBLISHED":
        if not publication.get("job_id"):
            raise RuntimeError("Uncertain request outcome; reconcile instead of duplicating the upload")
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
    verify_item(client, entry)
    publication["verified_at"] = now()
    save(record)
    return True


def prove(client, record, entry):
    theorem = verify_item(client, entry)
    submission = entry.get("submission")
    if submission is None:
        code = safe_path(DIRECTORY, entry["proof_path"]).read_bytes()
        boundary = "openga-" + uuid4().hex
        fields = {"theorem_id": theorem["theorem_id"], "proof_type": "prove", "explanation": entry["explanation"]}
        parts = []
        for key, value in fields.items():
            parts.append(("--" + boundary + '\r\nContent-Disposition: form-data; name="' + key +
                          '"\r\n\r\n' + value + "\r\n").encode())
        parts.append(("--" + boundary + '\r\nContent-Disposition: form-data; name="file"; '
                      'filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode()
                     + code + b"\r\n")
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
            raise RuntimeError("No submission id; inspect the saved response before retrying")
        print("Proof queued:", entry["id"], flush=True)
        return False
    if not submission.get("submission_id"):
        raise RuntimeError("Uncertain proof request; reconcile instead of resubmitting")
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
        raise RuntimeError("Accepted proof source differs from the validated source")
    theorem = verify_item(client, entry)
    if theorem["status"] != "Proved":
        raise RuntimeError("The accepted proof has not resolved its theorem")
    submission.update(verified_at=now(), accepted_source_sha256=digest(content.encode()))
    save(record)
    return True


def annotate_milestone(client, record):
    """Add verified progress links while preserving the canonical geometric target."""
    plan_path = ROOT / "milestones.json"
    plan = json.loads(plan_path.read_text())
    local = next(m for m in plan["milestones"] if m.get("platform_milestone_id") == record["milestone_id"])
    live = next(m for m in client.pages("/missions/" + MISSION_ID + "/milestones", "milestones")
                if m["id"] == record["milestone_id"])
    update = record.get("milestone_annotation")
    if update is None:
        if live["milestone_description"] != local["payload"]["milestone_description"]:
            raise RuntimeError("Milestone text changed; review it before adding progress")
        links = ["[" + e["payload"]["theorem_title"] + "](https://prove2.me/theorems/" +
                 e["publication"]["theorem_id"] + ")" for e in record["theorems"]]
        paragraph = ("\n\n**Verified analytic prerequisites.** " + "; ".join(links) +
                     ". The first two results preserve the DifferentialGeometry proofs; the third "
                     "is an OpenGA corollary. These establish the integral comparison step. "
                     "The full geometric milestone remains open: geometric density comparison, "
                     "polar integration, the ball-local hypotheses and positive model curvature "
                     "still require a faithful platform development.")
        update = record["milestone_annotation"] = {
            "before": live["milestone_description"],
            "after": live["milestone_description"] + paragraph,
            "canonical_theorem": live.get("theorem"), "status": "PREPARED",
        }
        save(record)
    if live["milestone_description"] != update["after"]:
        if live["milestone_description"] != update["before"] or live.get("theorem") != update["canonical_theorem"]:
            raise RuntimeError("Milestone changed during annotation; no overwrite performed")
        request = Request(BASE + "/milestones/" + record["milestone_id"], method="PATCH",
                          data=json_bytes({"milestone_description": update["after"],
                                           "reason": "Record three verified analytic prerequisites; preserve the geometric statement and its unlinked Open status."}),
                          headers={"Authorization": "Bearer " + client.token,
                                   "Content-Type": "application/json", "Accept": "application/json"})
        with client.opener.open(request, timeout=60) as response:
            update["response"] = json.load(response)
        save(record)
        live = next(m for m in client.pages("/missions/" + MISSION_ID + "/milestones", "milestones")
                    if m["id"] == record["milestone_id"])
    if live["milestone_description"] != update["after"] or live.get("theorem") != update["canonical_theorem"]:
        raise RuntimeError("Milestone readback differs")
    update.update(status="VERIFIED", verified_at=now())
    local["payload"]["milestone_description"] = update["after"]
    local["platform_verified_at"] = now()
    local["local_progress"]["analytic_prerequisites"] = [
        {"declaration": e["payload"]["theorem_name"], "theorem_id": e["publication"]["theorem_id"],
         "submission_id": e["submission"]["submission_id"], "status": "Proved"}
        for e in record["theorems"]]
    local["local_progress"]["analytic_publication_record"] = str(RECORD.relative_to(ROOT.parent))
    write_atomic(plan_path, json_bytes(plan))
    receipt_path = ROOT / "milestones_published.json"
    receipt = json.loads(receipt_path.read_text())
    receipt["milestones"][local["id"]] = live
    receipt["verified_at"] = now()
    write_atomic(receipt_path, json_bytes(receipt))
    save(record)
    print("Verified progress links on the Bishop-Gromov milestone; canonical target remains unchanged.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true", help="Publish and poll validated entries")
    args = parser.parse_args()
    record = json.loads(RECORD.read_text())
    validate(record)
    if not args.apply:
        print("Validated all source hashes and exact payloads; no network request made.")
        return
    client = Client(json.loads((ROOT / ".credentials.json").read_text())["api_key"])
    envs = client.request("/environments")["environments"]
    if not any(e["mathlib_rev"] == record["mathlib_rev"] and e["toolchain"] == record["toolchain"] for e in envs):
        raise RuntimeError("Platform environment no longer matches")
    definitions_ready = {}
    for entry in record["definitions"]:
        definitions_ready[entry["id"]] = publish(client, record, entry)
    ready = True
    proofs_ready = {}
    for entry in record["theorems"]:
        proofs_ready[entry["id"]] = False
        if not all(definitions_ready[name] for name in entry["definitions"]):
            ready = False
            continue
        if not publish(client, record, entry):
            ready = False
            continue
        if not all(proofs_ready.get(name, False) for name in entry["imports"]):
            ready = False
            continue
        if not prove(client, record, entry):
            ready = False
        else:
            proofs_ready[entry["id"]] = True
    if ready:
        graphs = {entry["id"]: client.request("/theorems/" + entry["publication"]["theorem_id"] + "/graph")
                  for entry in record["theorems"]}
        write_atomic(DIRECTORY / "Metadata/platform_graphs.json", json_bytes(graphs))
        entries = {e["id"]: e for e in record["theorems"]}
        for entry in record["theorems"]:
            for dependency in entry["imports"]:
                reached = {entries[dependency]["publication"]["theorem_id"]}
                edges = graphs[entry["id"]]["edges"]
                while True:
                    expanded = reached | {edge["target"] for edge in edges if edge["source"] in reached}
                    if expanded == reached:
                        break
                    reached = expanded
                if entry["publication"]["theorem_id"] not in reached:
                    raise RuntimeError("Platform graph is missing a required proof dependency")
        record.update(status="ANALYTIC_PREREQUISITES_PUBLISHED", verified_at=now())
        save(record)
        annotate_milestone(client, record)
        print(f"All {len(record['theorems'])} analytic prerequisites are public and Proved. The geometric milestone remains Open.")


if __name__ == "__main__":
    try:
        main()
    except HTTPError as error:
        print("Prove2Me HTTP", error.code, file=sys.stderr)
        raise SystemExit(1)
    except (URLError, OSError, RuntimeError, KeyError, ValueError) as error:
        print("Publication stopped:", str(error), file=sys.stderr)
        raise SystemExit(1)
