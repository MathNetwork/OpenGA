#!/usr/bin/env python3
"""Record reviewed platform receipts after publication and synchronization."""
import json
from datetime import datetime, timezone
from export_endgame import DIRECTORY, SOURCE, REPOSITORY, digest

def save(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")

def main():
    record = json.loads((DIRECTORY / "publication.json").read_text())
    if record["status"] != "COMPLETE" or record["graph_verification"]["status"] != "VERIFIED":
        raise RuntimeError("Publication and graph verification must finish first")
    mirror = REPOSITORY / "PoincareConjecture"
    snapshot = json.loads((mirror / "sync.json").read_text())
    curation = json.loads((mirror / "curation.json").read_text())
    source_paths = {
        "OpenGA.WidthComparisonTrace.le_extinctionTime": "OpenGALib/Analysis/ComparisonExtinction.lean",
        "OpenGA.SurgeryTopologyEvolution.finiteExtinction_of_width_control": "OpenGALib/Topology/ExtinctionEndgame.lean",
        "OpenGA.SurgeryTopologyEvolution.topology_from_extinction": "OpenGALib/Topology/SurgeryReconstruction.lean"}
    open_ids = [e["publication"]["theorem_id"] for e in record["theorems"] if "proof_path" not in e]
    for e in record["theorems"]:
        if "submission" not in e:
            continue
        sid = e["submission"]["submission_id"]
        sub = snapshot["submissions"][sid]
        node = snapshot["nodes"][sub["theorem_id"]]
        hash = digest((mirror / sub["local_path"]).read_bytes())
        if hash != e["proof_sha256"] or sub["status"] != e["expected_verdict"]:
            raise RuntimeError("Mirror source differs from accepted submission: " + e["id"])
        review = {"source_theorem_id": sub["theorem_id"], "source_status": sub["status"],
            "source_mathlib_rev": node["mathlib_rev"], "source_sha256": hash,
            "source_author": "Xinze-Li-Moqian",
            "source_url": "https://prove2.me/api/v1/submissions/" + sid + "/solution"}
        if e["id"] in source_paths:
            review.update(status="integrated", declarations=[{"name": e["id"], "path": source_paths[e["id"]]}],
                scope="Proved implications for explicitly supplied scalar/width comparison traces and finite topological surgery reconstruction records. The export types and definition bodies match OpenGA, and the source proof closure uses only standard logical axioms. The geometric construction is an open mission input.")
        else:
            review.update(status="deferred", declarations=[], deferred_theorem_ids=open_ids,
                reason="Verified conditional endgame, kept in the mission workspace. The extracted geometric-data construction and three topology lemmas remain Open; this sketch is not admitted into the reusable library as an unconditional proof.")
        curation["reviews"][sid] = review
    curation["reviewed_at"] = datetime.now(timezone.utc).isoformat()
    save(mirror / "curation.json", curation)
    review_path = SOURCE / "review.json"
    review = json.loads(review_path.read_text())
    review["status"] = "PUBLISHED_CONDITIONAL_REDUCTION"
    review["platform_publication"] = {"attempted": True, "graph_updated": True,
        "status": "COMPLETE", "root_status": "Open", "record": str((DIRECTORY / "publication.json").relative_to(REPOSITORY)),
        "source_revision": record["source_revision"], "verified_at": record["verified_at"],
        "graph": record["graph_verification"]}
    save(review_path, review)
    plan_path = mirror / "milestones.json"
    plan = json.loads(plan_path.read_text())
    for m in plan["milestones"]:
        update = record["milestone_annotations"].get(m.get("platform_milestone_id"))
        if update is None:
            continue
        if m["payload"]["milestone_description"] not in (update["before"], update["after"]):
            raise RuntimeError("Local milestone has changed; reconcile without overwriting")
        m["payload"]["milestone_description"] = update["after"]
        m["platform_verified_at"] = update["verified_at"]
        m.setdefault("local_progress", {})["extinction_endgame_publication"] = str((DIRECTORY / "publication.json").relative_to(REPOSITORY))
    save(plan_path, plan)
    print("Recorded three integrated proofs and two conditional sketches; synchronized milestone references.")

if __name__ == "__main__":
    main()
