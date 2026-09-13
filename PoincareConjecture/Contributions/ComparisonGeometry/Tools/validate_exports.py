#!/usr/bin/env python3
"""Compile the exact payloads and compare all exported types and definition bodies."""

from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
import subprocess

from export_metric_balls import DIRECTORY, REPOSITORY, digest


def run(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=True)
    return result.stdout


def parse_types(output):
    return json.loads(next(line for line in output.splitlines() if line.startswith("[")))


def main():
    record_path = DIRECTORY / "publication.json"
    record = json.loads(record_path.read_text())
    if any(e.get("publication") or e.get("submission")
           for e in record["definitions"] + record["theorems"]):
        raise RuntimeError("Published receipt is immutable; do not replace its validation")
    build = run(["lake", "build"], DIRECTORY)
    jobs = [
        (["lake", "env", "lean", str(DIRECTORY / "Library.lean")], REPOSITORY),
        (["lake", "env", "lean", str(DIRECTORY / "Tools/OriginalTypes.lean")], REPOSITORY),
        (["lake", "env", "lean", "Tools/ExportedTypes.lean"], DIRECTORY),
        (["lake", "env", "lean", "Tools/Audit.lean"], DIRECTORY)]
    with ThreadPoolExecutor(max_workers=4) as executor:
        outputs = list(executor.map(lambda job: run(*job), jobs))
    original, exported = parse_types(outputs[1]), parse_types(outputs[2])
    if len(original) != 11 or original != exported:
        raise RuntimeError("Export changed an elaborated type or definition body")
    if "Exact target type and all 11 definition/proof axiom dependencies passed." not in outputs[3]:
        raise RuntimeError("Missing proof audit result")
    for name, data in [("original_types.json", original), ("exported_types.json", exported)]:
        (DIRECTORY / "Metadata" / name).write_text(json.dumps(data, indent=2) + "\n")
    for name, output in [("build.log", build), ("library_entry.log", outputs[0]), ("audit.log", outputs[3])]:
        (DIRECTORY / "Metadata" / name).write_text(output)
    metadata = [DIRECTORY / "Metadata" / n for n in
                ("original_types.json", "exported_types.json", "selected_declaration_graph.json")]
    scripts = list((DIRECTORY / "Tools").glob("*.lean")) + list((DIRECTORY / "Tools").glob("*.py"))
    receipts = {r["path"]: r for r in record["sources"]}
    for path in metadata + scripts + [DIRECTORY / "Library.lean"]:
        relative = str(path.relative_to(REPOSITORY))
        receipts[relative] = {"path": relative, "sha256": digest(path.read_bytes())}
    record["sources"] = list(receipts.values())
    record["validation"] = {
        "status": "passed", "checked_at": datetime.now(timezone.utc).isoformat(),
        "exact_types_and_definition_bodies": 11, "solution_type": "exact match",
        "axiom_audit": "passed: 11 definitions/proofs; only propext, Classical.choice and Quot.sound",
        "staged_build": "passed", "library_entry": "passed",
        "scope": "A metric-ball interface export; not the full geometric comparison."}
    record["status"] = "VALIDATED"
    record_path.write_text(json.dumps(record, indent=2, ensure_ascii=False, sort_keys=True) + "\n")
    print("Validated all 11 declaration types, definition bodies and proof axioms.")


if __name__ == "__main__":
    main()
