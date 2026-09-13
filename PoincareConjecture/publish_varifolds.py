#!/usr/bin/env python3
"""Publish reviewed varifold foundations, verify graph dependencies, and curate a milestone."""

import argparse
import json
import time
from urllib.request import Request

import publish_bishop_gromov as publisher
from sync import BASE, Client, MISSION_ID, ROOT, expand_dependency_graph, json_bytes, write_atomic

DIRECTORY = ROOT / "Contributions/Varifold"
ROOT_THEOREM = "7ea2da12-4d1b-4bbc-8257-df87d92f5a8e"
ENERGY_THEOREM = "d81e3640-8579-4396-babb-69edac82be33"
EXTINCTION_MILESTONE = "33045187-e820-4325-a253-c8ba2c778897"
TITLE = "Area-energy control of parametrized varifolds"


def link(entry):
    payload = entry["payload"]
    title = payload.get("definition_title", payload.get("theorem_title"))
    return "[" + title + "](https://prove2.me/theorems/" + entry["publication"]["theorem_id"] + ")"


def reachable(graph, source, target):
    reached = {source}
    while True:
        more = reached | {e["target"] for e in graph["edges"] if e["source"] in reached}
        if more == reached:
            return target in reached
        reached = more


def finish(client, record):
    entries = {e["id"]: e for e in record["definitions"] + record["theorems"]}
    external = {e["name"]: e["id"] for e in record["existing"]}
    graphs = {}
    for e in record["theorems"]:
        tid = e["publication"]["theorem_id"]
        graph = expand_dependency_graph(client, client.request("/theorems/" + tid + "/graph"))
        for name in e["definitions"] + e["imports"]:
            source = entries[name]["publication"]["theorem_id"] if name in entries else external[name]
            if not reachable(graph, source, tid):
                raise RuntimeError("Platform graph is missing a real dependency: " + name + " -> " + e["id"])
        graphs[e["id"]] = graph
    root = expand_dependency_graph(client, client.request("/theorems/" + ROOT_THEOREM + "/graph"))
    if not reachable(root, ENERGY_THEOREM, ROOT_THEOREM):
        raise RuntimeError("Existing width-route area-energy dependency is missing")
    target = entries["OpenGA.Varifold.mass_ofParametrization_le_energy"]
    record["graph_verification"] = {
        "status": "VERIFIED", "checked_at": publisher.now(),
        "shared_theorem": ENERGY_THEOREM,
        "existing_path": "Integral area-energy comparison -> width comparison -> mission goal",
        "new_path": "Integral area-energy comparison -> mass bound for parametrized varifolds",
        "new_theorems_in_goal_dependency_graph": [e["id"] for e in record["theorems"] if any(
            n.get("theorem_id") == e["publication"]["theorem_id"] for n in root["nodes"])],
        "scope": "The two branches share a proved prerequisite. A geometric CM reduction making the varifold results prerequisites of the goal remains open; no artificial edge is asserted."}
    write_atomic(DIRECTORY / "Metadata/platform_graphs.json", json_bytes(graphs))
    write_atomic(DIRECTORY / "Metadata/goal_graph.json", json_bytes(root))
    publisher.save(record)

    milestones = client.pages("/missions/" + MISSION_ID + "/milestones", "milestones")
    description = target["payload"]["natural_language_statement"]
    description += ("\n\n**Varifold foundations.** " + "; ".join(link(e) for e in record["definitions"]) +
        ". The published companion results verify the test-function formulas, independence of zero-Jacobian plane choices, and convergence of spatial weight integrals. " +
        "[Browse the dependency graph](https://prove2.me/theorems/" + target["publication"]["theorem_id"] + ").")
    description += ("\n\nThis is a proved Euclidean foundation for the Colding-Minicozzi route, using " +
        "[the existing area-energy comparison](https://prove2.me/theorems/" + ENERGY_THEOREM + ") shared with the width graph. " +
        "It does not close finite-time extinction. The manifold Grassmann bundle, Sobolev surface construction, " +
        "minimal-sphere approximation and quantitative variation transfer remain to be formalized. " +
        "Sources: [Colding-Minicozzi, equation (1.4) and Section 1.3](https://arxiv.org/pdf/0707.0108), " +
        "[Simon, Chapter 8, Section 1](https://math.stanford.edu/~lms/ntu-gmt-text.pdf).")
    payload = {"title": TITLE, "milestone_description": description,
               "theorem_id": target["publication"]["theorem_id"]}
    receipt = record.get("milestone")
    if receipt is None:
        if any(m["title"] == TITLE for m in milestones):
            raise RuntimeError("Matching milestone exists; reconcile before creating")
        receipt = record["milestone"] = {"status": "SUBMITTING", "payload": payload}
        publisher.save(record)
        receipt["response"] = client.request("/missions/" + MISSION_ID + "/milestones", payload)
        receipt["id"] = receipt["response"]["id"]
        publisher.save(record)
    if not receipt.get("id"):
        raise RuntimeError("Uncertain milestone creation; reconcile instead of duplicating")
    live = next(m for m in client.pages("/missions/" + MISSION_ID + "/milestones", "milestones") if m["id"] == receipt["id"])
    if live["title"] != TITLE or live["milestone_description"] != description or live["theorem"]["id"] != payload["theorem_id"]:
        raise RuntimeError("Milestone readback differs")
    receipt.update(status="VERIFIED", verified_at=publisher.now())
    publisher.save(record)

    extinction = next(m for m in milestones if m["id"] == EXTINCTION_MILESTONE)
    update = record.get("extinction_annotation")
    if update is None:
        paragraph = ("\n\n**Colding-Minicozzi foundations.** " + link(target) +
            " now connects the Euclidean varifold construction to the same integral area-energy theorem used by the width comparison branch. " +
            "See the **" + TITLE + "** milestone for the definitions and verified prerequisites. " +
            "The geometric CM min-max and variation steps remain open; this foundation does not establish finite-time extinction.")
        update = record["extinction_annotation"] = {"status": "PREPARED",
            "before": extinction["milestone_description"], "after": extinction["milestone_description"] + paragraph,
            "canonical_theorem": extinction.get("theorem")}
        publisher.save(record)
    if extinction["milestone_description"] != update["after"]:
        if extinction["milestone_description"] != update["before"] or extinction.get("theorem") != update["canonical_theorem"]:
            raise RuntimeError("Extinction milestone changed concurrently; reconcile first")
        request = Request(BASE + "/milestones/" + EXTINCTION_MILESTONE, method="PATCH",
            data=json_bytes({"milestone_description": update["after"],
                "reason": "Connect the reviewed CM varifold foundations through the shared area-energy theorem; retain the open geometric target."}),
            headers={"Authorization": "Bearer " + client.token, "Content-Type": "application/json", "Accept": "application/json"})
        with client.opener.open(request, timeout=60) as response:
            update["response"] = json.load(response)
        publisher.save(record)
    live = next(m for m in client.pages("/missions/" + MISSION_ID + "/milestones", "milestones") if m["id"] == EXTINCTION_MILESTONE)
    if live["milestone_description"] != update["after"] or live.get("theorem") != update["canonical_theorem"]:
        raise RuntimeError("Extinction annotation readback differs")
    update.update(status="VERIFIED", verified_at=publisher.now())
    record.update(status="COMPLETE", verified_at=publisher.now())
    publisher.save(record)
    print("Verified five definitions, six proved theorems, the shared graph dependency and the new milestone.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--watch", action="store_true", help="Resume queued work every ten seconds")
    args = parser.parse_args()
    if args.watch and not args.apply:
        parser.error("--watch requires --apply")
    while True:
        run_once(args.apply)
        record = json.loads((DIRECTORY / "publication.json").read_text())
        if not args.watch or record["status"] == "COMPLETE":
            break
        time.sleep(10)


def run_once(apply):
    publisher.DIRECTORY = DIRECTORY
    publisher.RECORD = DIRECTORY / "publication.json"
    record = json.loads(publisher.RECORD.read_text())
    publisher.validate(record)
    if not apply:
        print("Validated all reviewed source hashes and exact upload files; no network request made.")
        return
    client = Client(json.loads((ROOT / ".credentials.json").read_text())["api_key"])
    if client.version != "0.9.8":
        raise RuntimeError("Refresh platform instructions for the new client version")
    envs = client.request("/environments")["environments"]
    if not any(e["mathlib_rev"] == record["mathlib_rev"] and e["toolchain"] == record["toolchain"] for e in envs):
        raise RuntimeError("Platform Lean environment differs")
    ready = {}
    for e in record["existing"]:
        item = client.request("/theorems/" + e["id"])
        expected = "Definition" if e["path"].startswith("Definitions/") else "Proved"
        if item["mathlib_rev"] != record["mathlib_rev"] or item["status"] != expected:
            raise RuntimeError("Existing prerequisite no longer matches: " + e["name"])
        code = item["definition"] if expected == "Definition" else item["preamble"] + "\n\n" + item["formal_statement"] + "\n"
        if code.strip() != (DIRECTORY / e["path"]).read_text().strip():
            raise RuntimeError("Existing prerequisite source differs: " + e["name"])
        ready[e["name"]] = True
    for e in record["definitions"]:
        ready[e["id"]] = all(ready.get(n, False) for n in e["definitions"]) and publisher.publish(client, record, e)
    for e in record["theorems"]:
        can_publish = all(ready.get(n, False) for n in e["definitions"])
        published = can_publish and publisher.publish(client, record, e)
        ready[e["id"]] = published and all(ready.get(n, False) for n in e["imports"]) and publisher.prove(client, record, e)
    if all(ready.values()):
        finish(client, record)
    else:
        print("Jobs pending; rerun to resume from saved receipts.", flush=True)


if __name__ == "__main__":
    main()
