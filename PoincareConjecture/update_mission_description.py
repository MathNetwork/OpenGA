#!/usr/bin/env python3
"""Apply the recorded mission introduction and verify the remote read-back.

Run without arguments to preview; pass --apply to update the live mission.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import sys
from urllib.error import HTTPError, URLError
from urllib.request import Request

from sync import BASE, Client, MISSION_ID, ROOT, json_bytes, write_atomic

RECORD = ROOT / "mission_description.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    record = json.loads(RECORD.read_text())
    payload = record["payload"]
    if record["mission_id"] != MISSION_ID or set(payload) != {"description"}:
        raise RuntimeError("Unexpected mission or metadata fields")
    if hashlib.sha256(payload["description"].encode()).hexdigest() != record["description_sha256"]:
        raise RuntimeError("Description changed after preparation")
    if not args.apply:
        print(payload["description"])
        return

    client = Client(json.loads((ROOT / ".credentials.json").read_text())["api_key"])

    def read_mission():
        return next(m for m in client.pages("/missions", "missions") if m["id"] == MISSION_ID)

    before = read_mission()
    if before["creator"]["id"] != record["expected_creator_id"]:
        raise RuntimeError("Mission creator changed")
    if before["description"] not in (record["previous_description"], payload["description"]):
        raise RuntimeError("Mission description changed remotely; reconcile before updating")
    if before["description"] != payload["description"]:
        record.update(status="SUBMITTING", started_at=datetime.now(timezone.utc).isoformat())
        write_atomic(RECORD, json_bytes(record))
        request = Request(BASE + "/missions/" + MISSION_ID,
                          data=json.dumps(payload).encode(), method="PATCH", headers={
                              "Authorization": "Bearer " + client.token,
                              "Accept": "application/json", "Content-Type": "application/json"})
        with client.opener.open(request, timeout=60) as response:
            record["response"] = json.load(response)
        write_atomic(RECORD, json_bytes(record))

    after = read_mission()
    if after["description"] != payload["description"]:
        raise RuntimeError("Mission description read-back differs from the prepared text")
    for key in ("name", "mission_type", "visibility", "fields", "creator"):
        if after[key] != before[key]:
            raise RuntimeError("Unexpected concurrent mission change: " + key)
    if after["main_theorem"]["theorem_id"] != before["main_theorem"]["theorem_id"]:
        raise RuntimeError("Mission goal changed concurrently")
    record.update(status="VERIFIED", verified_at=datetime.now(timezone.utc).isoformat(),
                  verified_mission=after)
    write_atomic(RECORD, json_bytes(record))
    print("Verified mission introduction:", ", ".join(item["name"] for item in record["libraries"]))


if __name__ == "__main__":
    try:
        main()
    except HTTPError as error:
        print("Prove2Me HTTP", error.code, file=sys.stderr)
        raise SystemExit(1)
    except (OSError, URLError, RuntimeError, KeyError, ValueError, StopIteration) as error:
        print("Mission update stopped:", str(error), file=sys.stderr)
        raise SystemExit(1)
