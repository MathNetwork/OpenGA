#!/usr/bin/env python3
"""Publish the checked finite-extinction reduction and verify paths to the existing goal."""
import argparse
import json
import time
from urllib.request import Request

import publish_bishop_gromov as publisher
from sync import BASE, Client, MISSION_ID, ROOT, expand_dependency_graph, json_bytes, write_atomic

DIRECTORY = ROOT / "Contributions/ExtinctionEndgame/Upload"
ROOT_THEOREM = "7ea2da12-4d1b-4bbc-8257-df87d92f5a8e"
MILESTONES = ["33045187-e820-4325-a253-c8ba2c778897", "29f0d323-76f4-4288-b819-626a482e9d5f"]

def reachable(graph, source, target):
    reached = {source}
    while True:
        more = reached | {e["target"] for e in graph["edges"] if e["source"] in reached}
        if more == reached:
            return target in reached
        reached = more

def finish(client, record):
    entries = {e["id"]: e for e in record["definitions"] + record["theorems"]}
    for e in entries.values():
        item = publisher.verify_item(client, e)
        expected = "Definition" if "definition" in e["payload"] else (
            "Proved" if e.get("expected_verdict") == "ACCEPTED" else "Open")
        if item["status"] != expected:
            raise RuntimeError("Unexpected final status for " + e["id"])
    graph = expand_dependency_graph(client, client.request("/theorems/" + ROOT_THEOREM + "/graph"))
    for e in entries.values():
        if not reachable(graph, e["publication"]["theorem_id"], ROOT_THEOREM):
            raise RuntimeError("New node is not connected to the existing root: " + e["id"])
    old = json.loads((DIRECTORY / "Metadata/before.json").read_text())["graph"]
    old_edges = {(e["source"], e["target"]) for e in old["edges"]}
    new_edges = {(e["source"], e["target"]) for e in graph["edges"]}
    if not old_edges <= new_edges:
        raise RuntimeError("Previously observed dependency edges disappeared; inspect graph before claiming completion")
    record["graph_verification"] = {
        "status": "VERIFIED", "checked_at": publisher.now(), "root_status": "Open",
        "before": {"nodes": len(old["nodes"]), "edges": len(old["edges"])},
        "after": {"nodes": len(graph["nodes"]), "edges": len(graph["edges"])},
        "connected_new_nodes": [e["id"] for e in entries.values() if not e.get("existing_target")],
        "preserved_prior_edges": True,
        "path": "Uniform width-controlled surgery topology -> finite extinction -> standard connected-sum decomposition -> simply connected endgame -> existing Poincare goal",
        "open_inputs": [e["id"] for e in record["theorems"] if "proof_path" not in e]}
    write_atomic(DIRECTORY / "Metadata/goal_graph.json", json_bytes(graph))
    publisher.save(record)

    def link(name):
        e = entries[name]
        return "[" + e["payload"]["theorem_title"] + "](https://prove2.me/theorems/" + e["publication"]["theorem_id"] + ")"
    paragraph = ("\n\n**Finite-extinction endgame in the mission graph.** " +
        link("OpenGA.SurgeryTopologyEvolution.finiteExtinction_of_width_control") + "; " +
        link("OpenGA.SurgeryTopologyEvolution.topology_from_extinction") + "; " +
        link("PoincareFormalization.ExtinctionEndgame.nonempty_homeomorph_sphere_of_standard_decomposition") +
        ". These nodes now enter a checked [reduction of the existing Poincare goal](https://prove2.me/theorems/" + ROOT_THEOREM +
        "). The width deadline and finite reconstruction are proved implications for explicitly supplied data. " +
        "The construction of uniform width-controlled surgery topology and three connected-sum topology inputs remain Open. " +
        "The extracted evolution has a nonempty initial positive time interval and finite reconstruction histories; it is not a definition of metric Ricci flow. " +
        "The full geometric finite-extinction and classification milestones remain open.")
    annotations = record.setdefault("milestone_annotations", {})
    for id in MILESTONES:
        live = next(m for m in client.pages("/missions/" + MISSION_ID + "/milestones", "milestones") if m["id"] == id)
        update = annotations.get(id)
        if update is None:
            update = annotations[id] = {"status": "PREPARED", "before": live["milestone_description"],
                "after": live["milestone_description"] + paragraph, "canonical_theorem": live.get("theorem")}
            publisher.save(record)
        if live["milestone_description"] != update["after"]:
            if live["milestone_description"] != update["before"] or live.get("theorem") != update["canonical_theorem"]:
                raise RuntimeError("Milestone changed concurrently; reconcile before updating")
            request = Request(BASE + "/milestones/" + id, method="PATCH",
                data=json_bytes({"milestone_description": update["after"],
                    "reason": "Link the verified conditional finite-extinction endgame to the existing goal, retaining the open geometric target."}),
                headers={"Authorization": "Bearer " + client.token, "Content-Type": "application/json", "Accept": "application/json"})
            with client.opener.open(request, timeout=60) as response:
                update["response"] = json.load(response)
            publisher.save(record)
        live = next(m for m in client.pages("/missions/" + MISSION_ID + "/milestones", "milestones") if m["id"] == id)
        if live["milestone_description"] != update["after"] or live.get("theorem") != update["canonical_theorem"]:
            raise RuntimeError("Milestone readback differs")
        update.update(status="VERIFIED", verified_at=publisher.now())
    record.update(status="COMPLETE", verified_at=publisher.now())
    publisher.save(record)
    print("Verified root graph:", record["graph_verification"], flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--watch", action="store_true")
    args = parser.parse_args()
    if args.watch and not args.apply:
        parser.error("--watch requires --apply")
    publisher.DIRECTORY = DIRECTORY
    publisher.RECORD = DIRECTORY / "publication.json"
    record = json.loads(publisher.RECORD.read_text())
    publisher.validate(record)
    if not args.apply:
        print("Validated exact source and proof hashes. No network requests made.")
        return
    client = Client(json.loads((ROOT / ".credentials.json").read_text())["api_key"])
    if client.version != "0.9.8":
        raise RuntimeError("Review updated platform instructions before uploading")
    envs = client.request("/environments")["environments"]
    if not any(e["mathlib_rev"] == record["mathlib_rev"] and e["toolchain"] == record["toolchain"] for e in envs):
        raise RuntimeError("Platform environment changed")
    ready = {}
    for e in record["existing"]:
        item = client.request("/theorems/" + e["id"])
        expected = "Definition" if e["path"].startswith("Definitions/") else "Proved"
        if item["mathlib_rev"] != record["mathlib_rev"] or item["status"] != expected:
            raise RuntimeError("Existing prerequisite differs: " + e["name"])
        code = item["definition"] if expected == "Definition" else item["preamble"] + "\n\n" + item["formal_statement"] + "\n"
        if code.strip() != (DIRECTORY / e["path"]).read_text().strip():
            raise RuntimeError("Existing prerequisite source differs: " + e["name"])
        ready[e["name"]] = True
    while True:
        for e in record["definitions"]:
            if ready.get(e["id"]):
                continue
            ready[e["id"]] = all(ready.get(n, False) for n in e["definitions"]) and publisher.publish(client, record, e)
        for e in record["theorems"]:
            if ready.get(e["id"]):
                continue
            published = all(ready.get(n, False) for n in e["definitions"]) and publisher.publish(client, record, e)
            ready[e["id"]] = published and all(ready.get(n, False) for n in e["imports"]) and (
                "proof_path" not in e or publisher.prove(client, record, e))
        if all(ready.values()):
            finish(client, record)
            return
        print("Waiting for platform jobs; receipts saved.", flush=True)
        if not args.watch:
            return
        time.sleep(10)

if __name__ == "__main__":
    main()
