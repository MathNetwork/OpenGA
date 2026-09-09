#!/usr/bin/env python3
"""Resume the validated width-comparison publication and verify root reachability."""

import argparse
from datetime import datetime, timezone
import json
import sys
from urllib.error import HTTPError, URLError
from urllib.request import Request
from uuid import uuid4

from sync import BASE, Client, MISSION_ID, ROOT, digest, json_bytes, safe_path, write_atomic

RECORD = ROOT / "Contributions/WidthComparison/publication.json"


def now():
    return datetime.now(timezone.utc).isoformat()


def save(record):
    write_atomic(RECORD, json_bytes(record))


def validate(record):
    if record["mission_id"] != MISSION_ID or record["source_reviewed"] is not True:
        raise RuntimeError("Mission or source review mismatch")
    if record.get("validation", {}).get("status") != "passed":
        raise RuntimeError("Exact payload validation is required")
    source = safe_path(ROOT.parent, record["local_source"]).read_bytes()
    if digest(source) != record["local_source_sha256"]:
        raise RuntimeError("Source changed after validation")
    seen = set()
    for item in record["items"]:
        if item["key"] in seen or not set(item["requires"]) <= seen:
            raise RuntimeError("Invalid publication dependency order")
        seen.add(item["key"])
        content = safe_path(ROOT.parent, item["path"]).read_bytes()
        if digest(content) != item["sha256"]:
            raise RuntimeError("Validated file changed: " + item["path"])
        if item["kind"] == "proof":
            if item["expected_status"] not in ("ACCEPTED", "SKETCH_ACCEPTED"):
                raise RuntimeError("Invalid expected proof status")
            continue
        payload = item["payload"]
        exact = payload.get("definition")
        if exact is None:
            exact = payload["preamble"] + "\n\n" + payload["formal_statement"] + "\n"
        if exact.encode() != content or payload["env"] != record["mathlib_rev"]:
            raise RuntimeError("Payload differs from validated file or environment")


def verify_theorem(client, item, theorem_id):
    theorem = client.request("/theorems/" + theorem_id)
    payload = item["payload"]
    fields = ("definition",) if item["kind"] == "definition" else (
        "theorem_name", "formal_statement", "preamble")
    for key in fields:
        if theorem.get(key, "").strip() != payload[key].strip():
            raise RuntimeError("Published source differs: " + key)
    if theorem["mathlib_rev"] != payload["env"]:
        raise RuntimeError("Published environment differs")
    return theorem


def publish(client, record, item):
    receipts = record["receipts"]
    receipt = receipts.get(item["key"])
    definition = item["kind"] == "definition"
    name = item["payload"]["definition_name" if definition else "theorem_name"]
    if receipt is None:
        matches = client.pages("/theorems", "theorems", theorem_name=name,
                               env=record["mathlib_rev"])
        if any(m["theorem_name"] == name for m in matches):
            raise RuntimeError("Name already exists; reconcile before publishing: " + name)
        receipt = receipts[item["key"]] = {"status": "SUBMITTING", "started_at": now()}
        save(record)
        response = client.request("/submit-definition" if definition else "/submit-problem",
                                  item["payload"])
        receipt["response"] = response
        save(record)
        job_id = response.get("job_id")
        if not job_id and len(response.get("jobs", [])) == 1:
            job_id = response["jobs"][0]["job_id"]
        if not job_id:
            raise RuntimeError("Missing publication job id; inspect saved response")
        receipt.update(status="PENDING", job_id=job_id)
        save(record)
        print("Queued:", item["key"], job_id, flush=True)
        return False
    if receipt["status"] != "PUBLISHED":
        if not receipt.get("job_id"):
            raise RuntimeError("Uncertain publication outcome; reconcile before retrying")
        job = client.request("/publish-jobs/" + receipt["job_id"])
        receipt.update(status=job["status"], job=job, checked_at=now())
        if job["status"] == "PUBLISHED":
            receipt["theorem_id"] = job["theorem_id"]
        save(record)
        print("Publication:", item["key"], job["status"], flush=True)
        if job["status"] in ("FAILED", "ERROR"):
            raise RuntimeError(job.get("error_message") or "Publication failed")
        if job["status"] != "PUBLISHED":
            return False
    verify_theorem(client, item, receipt["theorem_id"])
    receipt["verified_at"] = now()
    save(record)
    return True


def prove(client, record, item, by_key):
    receipts = record["receipts"]
    if item["target_key"]:
        target_id = receipts[item["target_key"]]["theorem_id"]
        verify_theorem(client, by_key[item["target_key"]], target_id)
    else:
        target_id = item["target_id"]
        current = client.request("/theorems/" + target_id)
        for field in ("theorem_id", "theorem_name", "formal_statement", "preamble", "mathlib_rev"):
            if current[field] != record["parent_theorem"][field]:
                raise RuntimeError("Existing reduction target changed: " + field)
    receipt = receipts.get(item["key"])
    if receipt is None:
        code = safe_path(ROOT.parent, item["path"]).read_bytes()
        boundary = "openga-" + uuid4().hex
        fields = {"theorem_id": target_id, "proof_type": "prove",
                  "explanation": item["explanation"]}
        parts = [("--" + boundary + '\r\nContent-Disposition: form-data; name="' + key +
                  '"\r\n\r\n' + value + "\r\n").encode() for key, value in fields.items()]
        parts.append(("--" + boundary + '\r\nContent-Disposition: form-data; name="file"; '
                      'filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode()
                     + code + b"\r\n")
        parts.append(("--" + boundary + "--\r\n").encode())
        receipt = receipts[item["key"]] = {"status": "SUBMITTING", "started_at": now(),
                                           "theorem_id": target_id}
        save(record)
        request = Request(BASE + "/verify", data=b"".join(parts), method="POST", headers={
            "Authorization": "Bearer " + client.token, "Accept": "application/json",
            "Content-Type": "multipart/form-data; boundary=" + boundary})
        with client.opener.open(request, timeout=60) as response:
            result = json.load(response)
        receipt.update(response=result, status=result.get("status"),
                       submission_id=result.get("submission_id"))
        save(record)
        if not receipt.get("submission_id"):
            raise RuntimeError("Missing proof id; reconcile saved response")
        print("Proof queued:", item["key"], receipt["submission_id"], flush=True)
        return False
    if not receipt.get("submission_id"):
        raise RuntimeError("Uncertain proof outcome; reconcile before retrying")
    if receipt["status"] != item["expected_status"]:
        result = client.request("/verify?submission_id=" + receipt["submission_id"])
        receipt.update(status=result["status"], verdict=result, checked_at=now())
        save(record)
        print("Proof:", item["key"], result["status"], flush=True)
        if result["status"] in ("PENDING", "COMPILING"):
            return False
        if result["status"] != item["expected_status"]:
            raise RuntimeError(result.get("error_message") or "Unexpected proof verdict")
    content = client.request("/submissions/" + receipt["submission_id"] + "/solution")["content"]
    if digest(content.encode()) != item["sha256"]:
        raise RuntimeError("Accepted proof source differs")
    theorem = client.request("/theorems/" + target_id)
    expected = "Proved" if item["expected_status"] == "ACCEPTED" else "Open"
    if theorem["status"] != expected:
        raise RuntimeError("Unexpected theorem status: " + theorem["status"])
    receipt.update(verified_at=now(), accepted_source_sha256=digest(content.encode()))
    save(record)
    return True


def verify_graph(client, record):
    root = record["root_theorem_id"]
    graph = client.request("/theorems/" + root + "/graph")
    write_atomic(RECORD.parent / "root_graph.json", json_bytes(graph))
    successors = {}
    for edge in graph["edges"]:
        successors.setdefault(edge["source"], []).append(edge["target"])

    def path(start):
        queue = [[start]]
        visited = {start}
        for route in queue:
            if route[-1] == root:
                return route
            for target in successors.get(route[-1], []):
                if target not in visited:
                    visited.add(target)
                    queue.append(route + [target])
        return None

    sources = ["2b8dd212-cbd1-4a9f-a5c0-bc4173eff02b",
               "d81e3640-8579-4396-babb-69edac82be33",
               "126d8aa9-2df0-4852-b3cd-4e4b6ffdd0c7",
               record["receipts"]["slope_problem"]["theorem_id"],
               record["receipts"]["geometry"]["theorem_id"]]
    paths = {source: path(source) for source in sources}
    root_status = client.request("/theorems/" + root)["status"]
    record["graph_verification"] = {"checked_at": now(), "node_count": len(graph["nodes"]),
        "edge_count": len(graph["edges"]), "paths_to_root": paths, "root_status": root_status,
        "status": "VERIFIED" if all(paths.values()) and root_status == "Open" else "INCOMPLETE"}
    save(record)
    if record["graph_verification"]["status"] != "VERIFIED":
        raise RuntimeError("Root graph reachability is not yet verified; inspect root_graph.json")
    record.update(status="COMPLETE", verified_at=now())
    save(record)
    print("Verified root graph:", len(graph["nodes"]), "nodes,", len(graph["edges"]), "edges", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    record = json.loads(RECORD.read_text())
    validate(record)
    if args.check_only:
        print("Validated all exact payloads and dependency order; no network request made.")
        return
    client = Client(json.loads((ROOT / ".credentials.json").read_text())["api_key"])
    by_key = {item["key"]: item for item in record["items"]}
    complete = set()
    for item in record["items"]:
        if not set(item["requires"]) <= complete:
            continue
        done = (prove(client, record, item, by_key) if item["kind"] == "proof"
                else publish(client, record, item))
        if done:
            complete.add(item["key"])
    if len(complete) == len(by_key):
        verify_graph(client, record)


if __name__ == "__main__":
    try:
        main()
    except HTTPError as error:
        print("Prove2Me HTTP", error.code, file=sys.stderr)
        raise SystemExit(1)
    except (URLError, OSError, RuntimeError, KeyError, ValueError) as error:
        print("Publication stopped:", str(error), file=sys.stderr)
        raise SystemExit(1)
