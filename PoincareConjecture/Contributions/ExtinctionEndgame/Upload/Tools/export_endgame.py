#!/usr/bin/env python3
"""Export the reviewed endgame using Lean declaration and binding spans."""
import hashlib
import json
from pathlib import Path
import subprocess

DIRECTORY = Path(__file__).resolve().parents[1]
SOURCE = DIRECTORY.parent
REPOSITORY = SOURCE.parents[2]
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
MISSION = "29133a9f-c412-4f19-968e-3deae9a335b5"
ROOT_ID = "7ea2da12-4d1b-4bbc-8257-df87d92f5a8e"
NS = "PoincareFormalization.ExtinctionEndgame."
D1 = "OpenGA_CoordinateBallConnectedSum"
D2 = "OpenGA_SurgeryTopologyEvolution"
D3 = "OpenGA_ExtinctionWidthControl"
D4 = "OpenGA_WidthExtinctionTime"
T1 = "OpenGA.WidthComparisonTrace.le_extinctionTime"
T2 = "OpenGA.SurgeryTopologyEvolution.finiteExtinction_of_width_control"
T3 = "OpenGA.SurgeryTopologyEvolution.topology_from_extinction"
T4 = NS + "nonempty_homeomorph_sphere_of_standard_decomposition"
OPENS = [NS + n for n in ["exists_width_controlled_surgery_topology",
    "simply_connected_factors_of_connected_sum", "not_simply_connected_sphere_handle",
    "nonempty_homeomorph_sphere_of_connected_sum_spheres"]]

def digest(b):
    return hashlib.sha256(b).hexdigest()

def edited(source, edits):
    right = len(source)
    for start, end, value in sorted(set(edits), reverse=True):
        if not 0 <= start <= end <= right:
            raise RuntimeError("Overlapping Lean spans")
        source = source[:start] + value + source[end:]
        right = start
    return source.decode()

def main():
    record_path = DIRECTORY / "publication.json"
    if record_path.exists():
        old = json.loads(record_path.read_text())
        if any(e.get("submission") or (e.get("publication") and not e.get("existing_target"))
               for e in old["definitions"] + old["theorems"]):
            raise RuntimeError("Preserve publication receipts")
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPOSITORY, text=True).strip()
    keys = {k: REPOSITORY / ("OpenGALib/" + area + "/" + k + ".lean") for k, area in [
        ("ConnectedSum", "Topology"), ("SurgeryReconstruction", "Topology"),
        ("ExtinctionEndgame", "Topology"), ("ComparisonExtinction", "Analysis"),
        ("WidthExtinction", "Analysis"), ("SphereCovering", "Topology"), ("CoveringSpace", "Topology")]}
    keys.update({k: SOURCE / (k + ".lean") for k in ["OpenProblems", "Reduction"]})
    sources = {k: p.read_bytes() for k, p in keys.items()}
    facts = {k: [json.loads(l) for l in (DIRECTORY / "Metadata" / (k + "_facts.jsonl"))
        .read_text().splitlines() if l.startswith("{")] for k in keys}
    selected = []

    def module(key, keep, imports, *, target=None, stub=False, solution=False, bodies=None, select=False):
        edits = []
        for f in facts[key]:
            if f["kind"] != "decl":
                continue
            a, b = f["declStart"]["offset"], f["declEnd"]["offset"]
            if not keep(f):
                edits.append((a, b, b""))
                continue
            if select:
                selected.append({"key": key, "startLine": f["declStart"]["line"],
                                 "endLine": f["declEnd"]["line"]})
            if solution:
                binding, = [r for r in facts[key] if r["kind"] == "ref" and r["const"] == target
                    and a <= r["start"]["offset"] < r["end"]["offset"] <= f["valStart"]["offset"]]
                edits.append((binding["start"]["offset"], binding["end"]["offset"], b"_root_.solution"))
            body = (bodies or {}).get(f.get("nameText"))
            if stub or body is not None:
                edits.append((f["valStart"]["offset"], b, (":= by sorry" if stub else body).encode()))
            if stub and f.get("docstring"):
                edits.append((f["docstring"]["start"]["offset"], f["docstring"]["end"]["offset"], b""))
        code = edited(sources[key], edits)
        # Import commands are replaced; all scopes and declaration bodies retain Lean spans.
        code = "\n".join(l for l in code.splitlines() if not l.startswith("import ")) + "\n"
        return "".join("import " + n + "\n" for n in imports) + code

    def write(path, code):
        (DIRECTORY / path).write_text(code)
        return {"path": path, "sha256": digest(code.encode())}

    def source(key):
        return "https://github.com/MathNetwork/OpenGA/blob/" + revision + "/" + str(keys[key].relative_to(REPOSITORY)) + "#L1-L" + str(len(sources[key].splitlines()))

    def dm(n):
        return "Definitions.Def_" + n

    def tm(n):
        return "Theorems.Thm_" + n.replace(".", "_")

    common = {"env": ENV, "tags": ["poincare-conjecture", "finite-extinction", "connected-sum", "openga-endgame"]}
    refs = "; Kleiner-Lott, https://arxiv.org/pdf/math/0605667v5, Section 3.2 and Lemmas 73.4, 81.2; Colding-Minicozzi, https://arxiv.org/pdf/0707.0108, Theorem 1.7 and Corollary 1.11."
    surgery_helpers = {"nonempty_homeomorph_sphere_of_isSphereCovered", "bind", "reconstruct", "topology_from_empty", "topology_from_extinction"}
    def_specs = [
        (D1, "ConnectedSum", lambda f: True,
         ["Mathlib.Geometry.Manifold.ChartedSpace", "Mathlib.Analysis.InnerProductSpace.PiL2", "Mathlib.Topology.Constructions"],
         "Coordinate-ball connected sums of three-manifolds",
         "Remove open unit balls embedded by coordinate charts defined on their closed balls, then identify their boundary two-spheres through a homeomorphism. The construction carries the quotient topology. IsConnectedSum asks for a homeomorphism with this quotient; orientation is not imposed. The coordinate-ball condition gives collared boundaries. This is a topological construction, with no classification theorem built in."),
        (D2, "SurgeryReconstruction", lambda f: f.get("nameText") not in surgery_helpers,
         [dm(D1), "Mathlib.Topology.Homotopy.Lifting", "Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected"],
         "Finite topological reconstruction data for surgery",
         "Bundle connected nonempty compact Hausdorff three-manifolds. Standard factors are manifolds covered surjectively by the unit three-sphere, or homeomorphic to S1 times S2. The first condition is weaker than being a round spherical space form. ConnectedSumClosure is a finite nonempty expression using actual coordinate-ball connected sums and homeomorphisms. A reconstruction record expresses each earlier component using later components and standard factors; it need not use each later component once. SurgeryTopologyEvolution supplies component lists, an initial positive interval on which the list is [M], and a finite reconstruction history from time zero to every nonnegative horizon. FiniteExtinction means that every slice is empty after some positive time. This is extracted topological data, not a metric Ricci flow or a claim of geometric existence."),
        (D3, "ExtinctionEndgame", lambda f: f.get("nameText") == "HasWidthControl",
         [dm(D2), dm("OpenGA_WidthComparisonTrace")],
         "Uniform width control of nonempty component slices",
         "For an extracted SurgeryTopologyEvolution E and one real bound W, every positive time T with nonempty components must admit a WidthComparisonTrace W T. The same W is used for all horizons. The initial positive interval ensures this requirement is nonvacuous. The trace contains abstract analytic comparison data; realizing its fields by geometric sweepouts and a Ricci flow with surgery remains a separate open problem."),
        (D4, "WidthExtinction", lambda f: f.get("nameText") == "widthExtinctionTime",
         ["Mathlib.Analysis.Calculus.MeanValue", "Mathlib.Analysis.SpecialFunctions.Pow.Deriv"],
         "The explicit width extinction deadline",
         "Define T*(C,W) = (C^(1/4) + W/(16 pi C^(3/4)))^4 - C for real C and W. Its use as an extinction deadline requires C positive and the scalar/width comparison hypotheses; those conclusions are theorem nodes, not part of this definition.")]
    definitions = []
    for name, key, keep, imports, title, desc in def_specs:
        code = module(key, keep, imports, select=True)
        definitions.append({"id": name, "definitions": [i.removeprefix("Definitions.Def_") for i in imports if i.startswith("Definitions.")],
            **write("Definitions/Def_" + name + ".lean", code),
            "payload": dict(common, definition_name=name, definition_title=title, definition=code,
                            natural_language_statement=desc, source=source(key) + refs)})

    # Small adapters retain original signatures, with proofs supplied by existing platform nodes.
    deadline = module("WidthExtinction", lambda f: f.get("nameText") == "le_widthExtinctionTime_across_downward_jumps", [],
        bodies={"le_widthExtinctionTime_across_downward_jumps": ":= by\n  exact OpenGA.le_width_deadline_across_downward_jumps hC n hn times widths hzero htimes hcont hinitial hfinal hslope hjumps"})
    covering = module("CoveringSpace", lambda f: True, [], bodies={"IsCoveringMap.isHomeomorph_of_simplyConnectedSpace":
        ":= by\n  obtain ⟨e, he⟩ := PoincareFormalization.covering_is_homeomorph p hp\n  rw [← he]\n  exact e.isHomeomorph"})
    sphere = module("SphereCovering", lambda f: True, [])
    covered = module("SurgeryReconstruction", lambda f: f.get("nameText") == "nonempty_homeomorph_sphere_of_isSphereCovered", [])
    # Attribute commands name declarations already supplied by the definition module.
    core = module("ExtinctionEndgame", lambda f: f.get("nameText") == "nonempty_homeomorph_sphere_of_standard_connectedSum", [])
    topology_helpers = module("SurgeryReconstruction", lambda f: f.get("nameText") in {"bind", "reconstruct", "topology_from_empty"}, [])
    root_helpers = module("Reduction", lambda f: f.get("nameText") in {
        "exists_finitely_extinct_surgery_topology", "nonempty_homeomorph_sphere_of_finite_extinction"}, [])
    scalar = "OpenGA.scalar_lower_bound_across_upward_jumps"
    slope = "OpenGA.eventually_width_slope_lt_of_comparison"
    jump = "OpenGA.le_width_deadline_across_downward_jumps"
    cover = "PoincareFormalization.covering_is_homeomorph"
    titles = [
        ("Construct uniform width-controlled surgery topology", "For every closed simply connected topological three-manifold M, construct an extracted surgery topology E and one W >= 0 such that every nonempty positive-time slice supplies a WidthComparisonTrace W T. E must preserve [M] on an initial positive time interval and carry finite topological reconstruction records at every horizon. This statement requests extracted data, not a complete metric-flow object. The intended KL/CM construction must still provide smoothing, orientation, a normalized metric, controlled surgery, nontrivial sweepouts and the width estimates. These geometric obligations remain open."),
        ("Simply connected connected sums have simply connected factors", "For closed connected three-manifolds M, N, X with X a coordinate-ball connected sum of M and N, simple connectivity of X implies simple connectivity of both M and N. This is the van Kampen input; no such property is assumed in the connected-sum definition."),
        ("The sphere handle is not simply connected", "A closed three-manifold homeomorphic to S1 times S2 is not simply connected. This excludes the handle factors from a simply connected connected-sum decomposition."),
        ("A connected sum of three-spheres is a three-sphere", "If closed three-manifolds M and N are each homeomorphic to the unit three-sphere, then every coordinate-ball connected sum X of M and N is also homeomorphic to that sphere. The gluing may use any boundary homeomorphism.")]
    specs = [(name, "OpenProblems", name[len(NS):], [D3] if i == 0 else [D2], [], "", *titles[i], None)
             for i, name in enumerate(OPENS)]
    specs += [
        (T1, "ComparisonExtinction", "WidthComparisonTrace.le_extinctionTime", ["OpenGA_WidthComparisonTrace", D4], [scalar, slope, jump], deadline,
         "A width comparison trace has a finite deadline", "Every normalized finite scalar/width comparison trace with initial width bound W and final time T satisfies T <= T*(1/4,W). The proof combines the existing scalar lower bound, area-energy width comparison and finite downward-jump deadline. Existence of such traces is an explicit input.", "ACCEPTED"),
        (T2, "ExtinctionEndgame", "finiteExtinction_of_width_control", [D3, D4], [T1], "",
         "Uniform width control forces finite extinction", "If an extracted surgery topology E has width control with one bound W on every nonempty positive-time slice, all slices at and beyond max(T*(1/4,W),0)+1 are empty. This is a proved analytic implication; constructing the data from a geometric surgery flow remains open.", "ACCEPTED"),
        (T3, "SurgeryReconstruction", "topology_from_extinction", [D2], [], topology_helpers,
         "Finite extinction reconstructs a connected sum of standard factors", "If a SurgeryTopologyEvolution of M becomes empty after some positive time, M lies in the finite connected-sum closure of sphere-covered manifolds and S1 times S2 factors. The proof iterates its finite reconstruction history backwards from an empty slice. It formalizes the finite-induction step of KL Lemma 81.2 for explicitly supplied records; obtaining those records from metric surgery is still required.", "ACCEPTED"),
        (T4, "Reduction", "nonempty_homeomorph_sphere_of_standard_decomposition", [D2], OPENS[1:] + [cover], covering + sphere + covered + core,
         "The simply connected endgame for a standard connected-sum decomposition", "A closed simply connected three-manifold with a finite connected-sum decomposition into sphere-covered factors and S1 times S2 factors is homeomorphic to S3. This conditional proof sketch uses three open topology lemmas: simple connectivity descends to factors, sphere handles are not simply connected, and the sum of two three-spheres is a three-sphere. The sphere-covering base case reuses salim's proved covering theorem.", "SKETCH_ACCEPTED")]
    theorems = []
    for name, key, short, defs, deps, helpers, title, desc, verdict in specs:
        keep = lambda f, short=short: f.get("nameText") == short
        extra = ["Mathlib.Analysis.Normed.Module.Connected"] if name == T4 else []
        stub = module(key, keep, [], stub=True)
        preamble = "".join("import " + dm(d) + "\n" for d in defs)
        e = {"id": name, "definitions": defs, "imports": deps,
             **write("Theorems/Thm_" + name.replace(".", "_") + ".lean", preamble + "\n\n" + stub + "\n"),
             "payload": dict(common, theorem_name=name, theorem_title=title, preamble=preamble,
                 formal_statement=stub, natural_language_statement=desc, source=source(key) + refs)}
        if verdict:
            proof = preamble + "".join("import " + tm(n) + "\n" for n in deps) + "".join("import " + n + "\n" for n in extra)
            proof += helpers + module(key, keep, [], target=name, solution=True)
            p = write("Solutions/Sol_" + name.replace(".", "_") + ".lean", proof)
            e.update(proof_path=p["path"], proof_sha256=p["sha256"], expected_verdict=verdict,
                explanation=desc + " Reviewed source: " + source(key) + ". Small adapters reuse the existing platform theorem interfaces; no proof holes are added.")
        theorems.append(e)
    root = json.loads((DIRECTORY / "Metadata/before.json").read_text())["root"]
    root_name = root["theorem_name"]
    root_path = "Theorems/Thm_" + root_name.replace(".", "_") + ".lean"
    proof = "".join("import " + tm(n) + "\n" for n in [OPENS[0], T2, T3, T4]) + root_helpers
    proof += module("Reduction", lambda f: f.get("nameText") == "nonempty_homeomorph_sphere_three", [],
                    target=NS + "nonempty_homeomorph_sphere_three", solution=True)
    p = write("Solutions/Sol_ExtinctionEndgameRoot.lean", proof)
    theorems.append({"id": root_name, "existing_target": True, "definitions": [], "imports": [OPENS[0], T2, T3, T4],
        **write(root_path, root["preamble"] + "\n\n" + root["formal_statement"] + "\n"),
        "proof_path": p["path"], "proof_sha256": p["sha256"], "expected_verdict": "SKETCH_ACCEPTED",
        "publication": {"status": "PUBLISHED", "theorem_id": ROOT_ID},
        "payload": dict(common, theorem_name=root_name, preamble=root["preamble"], formal_statement=root["formal_statement"]),
        "explanation": "Finite-extinction endgame with the exact existing topological goal. The geometric extracted-data construction supplies uniform width control; the proved deadline forces extinction, and finite surgery histories reconstruct standard connected-sum factors. The standard decomposition sketch uses the three explicit open topology lemmas and the proved sphere-covering base case. Four open leaves remain; this submission is a conditional reduction. " + source("Reduction") + refs})

    existing = []
    mirror = REPOSITORY / "PoincareConjecture"
    nodes = json.loads((mirror / "sync.json").read_text())["nodes"]
    byname = {n["theorem_name"]: (i,n) for i,n in nodes.items()}
    needed = {"OpenGA_WidthComparisonTrace", scalar, slope, jump, cover}
    while needed:
        name = needed.pop()
        if any(e["name"] == name for e in existing):
            continue
        id, node = byname[name]
        path = node["local_path"]
        code = (mirror / path).read_text()
        existing.append({"name": name, "id": id, **write(path, code)})
        for line in code.splitlines():
            if line.startswith("import Definitions.Def_"):
                needed.add(line.removeprefix("import Definitions.Def_"))
            elif line.startswith("import Theorems.Thm_"):
                dep_path = line.removeprefix("import ").replace(".", "/") + ".lean"
                needed.add(next(n["theorem_name"] for n in nodes.values() if n.get("local_path") == dep_path))
    graph = [json.loads(l) for l in (DIRECTORY / "Metadata/declaration_graph.jsonl").read_text().splitlines()]
    names = {e["id"] for e in theorems if not e.get("existing_target")}
    for r in graph:
        key = r["module"].split(".")[-1]
        if any(s["key"] == key and s["startLine"] <= r["startLine"] <= s["endLine"] for s in selected):
            names.add(r["name"])
    (DIRECTORY / "Metadata/selected_declarations.json").write_text(json.dumps(sorted(names), indent=2) + "\n")
    record = {"schema_version": 1, "batch": "extinction_endgame", "mission_id": MISSION,
        "mathlib_rev": ENV, "toolchain": "leanprover/lean4:v4.33.1", "source_revision": revision,
        "source_reviewed": True, "sources": [{"path": str(p.relative_to(REPOSITORY)), "sha256": digest(p.read_bytes())} for p in keys.values()],
        "definitions": definitions, "theorems": theorems, "existing": existing,
        "status": "STAGED", "validation": {"status": "required"},
        "scope": "Extracted topology and width data, three proved implications, four open inputs, a conditional topology sketch and a reduction of the existing root. The full KL/CM geometric construction remains open."}
    record_path.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
    print("Staged four definitions, four open inputs, three proofs, one topology sketch and the existing root reduction.")

if __name__ == "__main__":
    main()
