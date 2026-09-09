#!/usr/bin/env python3
"""Preview, or publish with --publish, the reviewed local milestone batch.

This command only creates missing milestones. It never edits or deletes an
existing milestone, links a theorem, or submits a proof. Receipts are saved
after each successful creation so an interrupted batch can be resumed.
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from urllib.error import HTTPError, URLError

from sync import Client, MISSION_ID, ROOT

PLAN = ROOT / "milestones.json"
RECEIPT = ROOT / "milestones_published.json"


def save_receipt(value):
    with tempfile.NamedTemporaryFile(mode="w", dir=ROOT, delete=False) as stream:
        json.dump(value, stream, indent=2, ensure_ascii=True)
        stream.write("\n")
        temporary = Path(stream.name)
    temporary.replace(RECEIPT)


def load_plan():
    plan = json.loads(PLAN.read_text())
    if plan["mission_id"] != MISSION_ID:
        raise ValueError("Milestone plan belongs to a different mission")
    entries = plan["milestones"]
    for field in ("id",):
        if len({entry[field] for entry in entries}) != len(entries):
            raise ValueError("Duplicate local milestone identifier")
    for field in ("title", "sort_order"):
        if len({entry["payload"][field] for entry in entries}) != len(entries):
            raise ValueError("Duplicate milestone " + field)
    platform_ids = [entry["platform_milestone_id"] for entry in entries if entry.get("platform_milestone_id")]
    if len(set(platform_ids)) != len(platform_ids):
        raise ValueError("Duplicate platform milestone identifier")
    for entry in entries:
        payload = entry["payload"]
        if entry.get("source_reviewed") is not True:
            raise ValueError("Source review required: " + entry["id"])
        if set(payload) != {"title", "milestone_description", "sort_order"}:
            raise ValueError("Only unlinked milestone creation is supported")
        if not payload["title"].strip() or len(payload["title"]) > 200:
            raise ValueError("Milestone title must contain 1 to 200 characters")
        if not re.fullmatch(r"(?:(Claim|Lemma|Proposition|Theorem|Corollary|Equation) (?:\d+|[A-Z])\.\d+(?:\(\d+\))?|Section \d+)", entry.get("source_index", "")):
            raise ValueError("A verified source index is required in the reference metadata")
        if not payload["milestone_description"].strip():
            raise ValueError("Empty milestone description")
        if not isinstance(payload["sort_order"], int) or payload["sort_order"] < 0:
            raise ValueError("Invalid milestone order")
    return plan


def match_existing(entry, milestones):
    milestone_id = entry.get("platform_milestone_id")
    if milestone_id:
        matches = [m for m in milestones if m["id"] == milestone_id]
        if not matches:
            raise RuntimeError("Published milestone is unavailable; refusing to recreate: " + entry["id"])
    else:
        matches = [m for m in milestones if m["title"] == entry["payload"]["title"]]
    if len(matches) > 1:
        raise RuntimeError("Duplicate platform titles require review: " + entry["id"])
    if not matches:
        return None
    milestone = matches[0]
    if any(milestone[field] != entry["payload"][field] for field in ("title", "milestone_description")):
        raise RuntimeError("Existing milestone text differs; refusing to overwrite: " + entry["id"])
    expected_theorem = entry.get("linked_theorem_id")
    if expected_theorem and (milestone.get("theorem") or {}).get("id") != expected_theorem:
        raise RuntimeError("Existing milestone theorem link differs: " + entry["id"])
    return milestone


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--publish", action="store_true", help="create missing reviewed milestones")
    args = parser.parse_args()
    plan = load_plan()
    key = os.environ.get("PROVE2ME_API_KEY")
    if not key:
        key = json.loads((ROOT / ".credentials.json").read_text())["api_key"]
    client = Client(key)
    path = "/missions/" + MISSION_ID + "/milestones"
    mission = next(m for m in client.pages("/missions", "missions") if m["id"] == MISSION_ID)
    if mission["creator"]["id"] != "cd9090e5-05ea-4bf2-9a9c-dd2100e2c82b":
        raise RuntimeError("Unexpected mission creator")
    milestones = client.pages(path, "milestones")
    # Check the entire batch before making any changes.
    for entry in plan["milestones"]:
        existing = match_existing(entry, milestones)
        if existing is None and any(m["sort_order"] == entry["payload"]["sort_order"] for m in milestones):
            raise RuntimeError("Planned position is occupied; review ordering before publication")
        print(("EXISTS " if existing else "CREATE ") + entry["payload"]["title"], flush=True)
    if not args.publish:
        print("Preview complete; no milestones were created.")
        return
    receipt = {"mission_id": MISSION_ID, "milestones": {}, "source": plan["source"]}
    if RECEIPT.exists():
        saved = json.loads(RECEIPT.read_text())
        if saved["mission_id"] != MISSION_ID:
            raise RuntimeError("Receipt belongs to a different mission")
        receipt["milestones"].update(saved["milestones"])
    for entry in plan["milestones"]:
        # Re-read after each write, and also before a resumed batch, to avoid duplicates.
        milestones = client.pages(path, "milestones")
        existing = match_existing(entry, milestones)
        if existing is None:
            if any(m["sort_order"] == entry["payload"]["sort_order"] for m in milestones):
                raise RuntimeError("Milestone order changed during publication")
            client.request(path, entry["payload"])
            milestones = client.pages(path, "milestones")
            existing = match_existing(entry, milestones)
            if existing is None:
                raise RuntimeError("Creation could not be verified; check the platform before retrying")
        receipt["milestones"][entry["id"]] = existing
        receipt["verified_at"] = datetime.now(timezone.utc).isoformat()
        save_receipt(receipt)
        print("Verified " + entry["id"] + ": " + existing["id"], flush=True)
    print("Verified {} milestones; receipts saved to {}.".format(len(plan["milestones"]), RECEIPT.name))


if __name__ == "__main__":
    try:
        main()
    except HTTPError as error:
        print("Prove2Me HTTP {}; inspect the platform before resuming.".format(error.code), file=sys.stderr)
        sys.exit(1)
    except (URLError, OSError, ValueError, KeyError, RuntimeError, StopIteration) as error:
        print("Milestone operation stopped: " + str(error), file=sys.stderr)
        sys.exit(1)
