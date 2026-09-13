#!/usr/bin/env python3
"""Publish the validated metric-ball batch; resume queued jobs on subsequent runs."""

import argparse
import json
from urllib.request import Request

import publish_bishop_gromov as publisher
from sync import BASE, Client, MISSION_ID, ROOT, expand_dependency_graph, json_bytes, write_atomic

DIRECTORY = ROOT / "Contributions/ComparisonGeometry"


def annotate_milestone(client, record):
    milestones = client.pages("/missions/" + MISSION_ID + "/milestones", "milestones")
    live = next(m for m in milestones if m["id"] == record["milestone_id"])
    update = record.get("milestone_update")
    if update is None:
        links = ["[" + e["payload"].get("definition_title", e["payload"].get("theorem_title")) +
                 "](https://prove2.me/theorems/" + e["publication"]["theorem_id"] + ")"
                 for e in record["definitions"] + record["theorems"]]
        paragraph = ("\n\n**Reviewed geometric foundations.** " + "; ".join(links) +
                     ". These reuse the original Mathlib/DifferentialGeometry metric and distance "
                     "constructions, with OpenGA's ball interface and openness corollary. "
                     "They provide the basic geometric objects for subsequent comparison proofs; "
                     "the full Bishop-Gromov milestone remains Open.")
        update = record["milestone_update"] = {
            "before": live["milestone_description"],
            "after": live["milestone_description"] + paragraph,
            "canonical_theorem": live.get("theorem"), "status": "PREPARED"}
        publisher.save(record)
    if live["milestone_description"] != update["after"]:
        if live["milestone_description"] != update["before"] or live.get("theorem") != update["canonical_theorem"]:
            raise RuntimeError("Milestone changed concurrently; reconcile before editing")
        req = Request(BASE + "/milestones/" + record["milestone_id"], method="PATCH",
                      data=json_bytes({"milestone_description": update["after"],
                                       "reason": "Link reviewed metric and distance definitions with their original attribution."}),
                      headers={"Authorization": "Bearer " + client.token,
                               "Content-Type": "application/json", "Accept": "application/json"})
        with client.opener.open(req, timeout=60) as response:
            update["response"] = json.load(response)
        publisher.save(record)
        live = next(m for m in client.pages("/missions/" + MISSION_ID + "/milestones", "milestones")
                    if m["id"] == record["milestone_id"])
    if live["milestone_description"] != update["after"] or live.get("theorem") != update["canonical_theorem"]:
        raise RuntimeError("Milestone readback differs")
    update.update(status="VERIFIED", verified_at=publisher.now())
    publisher.save(record)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    publisher.DIRECTORY = DIRECTORY
    publisher.RECORD = DIRECTORY / "publication.json"
    record = json.loads(publisher.RECORD.read_text())
    publisher.validate(record)
    if not args.apply:
        print("Validated metric-ball sources and exact payloads; no network request made.")
        return
    client = Client(json.loads((ROOT / ".credentials.json").read_text())["api_key"])
    if client.version != "0.9.9":
        raise RuntimeError("Platform version changed; refresh the Prove2Me skill")
    envs = client.request("/environments")["environments"]
    if not any(e["mathlib_rev"] == record["mathlib_rev"] and e["toolchain"] == record["toolchain"] for e in envs):
        raise RuntimeError("Platform environment no longer matches")
    ready = {}
    for entry in record["definitions"]:
        ready[entry["id"]] = (all(ready.get(n, False) for n in entry["definitions"])
                              and publisher.publish(client, record, entry))
    for entry in record["theorems"]:
        ready[entry["id"]] = (all(ready.get(n, False) for n in entry["definitions"])
                              and publisher.publish(client, record, entry)
                              and publisher.prove(client, record, entry))
    if not all(ready.values()):
        print("Pending platform jobs; run again to resume.")
        return
    graphs = {e["id"]: expand_dependency_graph(client,
              client.request("/theorems/" + e["publication"]["theorem_id"] + "/graph"))
              for e in record["theorems"]}
    write_atomic(DIRECTORY / "Metadata/platform_graphs.json", json_bytes(graphs))
    entries = {e["id"]: e for e in record["definitions"] + record["theorems"]}
    for entry in record["theorems"]:
        for dependency in entry["definitions"]:
            reached = {entries[dependency]["publication"]["theorem_id"]}
            while True:
                more = reached | {e["target"] for e in graphs[entry["id"]]["edges"] if e["source"] in reached}
                if more == reached:
                    break
                reached = more
            if entry["publication"]["theorem_id"] not in reached:
                raise RuntimeError("Missing definition dependency in platform graph: " + dependency)
    record.update(status="PUBLISHED", verified_at=publisher.now())
    publisher.save(record)
    annotate_milestone(client, record)
    print("Published 3 definition bundles and 1 proved interface theorem; Bishop-Gromov remains Open.")


if __name__ == "__main__":
    main()
