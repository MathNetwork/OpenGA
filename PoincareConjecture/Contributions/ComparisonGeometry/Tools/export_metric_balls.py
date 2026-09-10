#!/usr/bin/env python3
"""Stage the metric-ball interface using Lean's declaration and reference spans."""

import hashlib
import json
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parents[1]
REPOSITORY = DIRECTORY.parents[2]
REVISION = "1b535dd102b94cc42b107cca27059687888f08b3"
LOCAL_REVISION = "16e60c2b09f5c1d3c2bf44ed81429b1a1fecc1b8"
ENVIRONMENT = "0df444a360eaa60ab8c11dca51a86af692955474"
PREFIX = "Riemannian.RiemannianMetric."
NOTICE = ("/-\nReuses qinz1yang/differential-geometry, Copyright 2026 The DifferentialGeometry\n"
          "contributors, Apache-2.0, commit " + REVISION + ".\n"
          "The metric and distance are upstream/Mathlib constructions. The ball interface\n"
          "is curated in OpenGA; source hypotheses and mathematical definitions are preserved.\n-/\n")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def edited(source, edits):
    right = len(source)
    for start, end, value in sorted(set(edits), reverse=True):
        if not 0 <= start <= end <= right:
            raise RuntimeError("Overlapping or invalid Lean source spans")
        source = source[:start] + value + source[end:]
        right = start
    return source


def main():
    record_path = DIRECTORY / "publication.json"
    if record_path.exists():
        old = json.loads(record_path.read_text())
        if any(e.get("publication") or e.get("submission")
               for e in old["definitions"] + old["theorems"]):
            raise RuntimeError("Refusing to overwrite publication receipts")
    upstream = REPOSITORY / ".lake/packages/DifferentialGeometry/DifferentialGeometry/Geometry/Metric"
    paths = {"upstream_metric": upstream / "Basic.lean",
             "upstream_distance": upstream / "DistanceScaling.lean",
             "local_metric": REPOSITORY / "OpenGALib/Riemannian/Metric/RiemannianMetric.lean",
             "local_ball": REPOSITORY / "OpenGALib/ComparisonGeometry/MetricBall.lean"}
    sources = {k: p.read_bytes() for k, p in paths.items()}
    facts = {k: [json.loads(line) for line in
                 (DIRECTORY / "Metadata" / (k + "_facts.jsonl")).read_text().splitlines()
                 if line.startswith("{")] for k in paths}
    selected = {k: [] for k in paths}

    def declaration(key, name, rename=None, stub=False):
        fact, = [f for f in facts[key] if f["kind"] == "decl" and f["nameText"] == name]
        selected[key].append(fact)
        # The oracle reports the core separately from an `attribute ... in` wrapper.
        # The removed wrappers only disable upstream tensor norm instances; those
        # instances are absent from this Mathlib-only staged environment.
        start = fact.get("coreDecl", {}).get("start", fact["declStart"])["offset"]
        end = fact["valStart"]["offset"] if stub else fact["declEnd"]["offset"]
        changes = []
        if rename:
            full = PREFIX + name
            binding, = [f for f in facts[key] if f["kind"] == "ref" and f["const"] == full
                        and start <= f["start"]["offset"] < f["end"]["offset"] <= fact["valStart"]["offset"]]
            changes.append((binding["start"]["offset"] - start,
                            binding["end"]["offset"] - start, rename.encode()))
        if stub and fact.get("docstring"):
            doc = fact["docstring"]
            changes.append((doc["start"]["offset"] - start, doc["end"]["offset"] - start, b""))
        return edited(sources[key][start:end], changes).decode().strip() + (" := by sorry" if stub else "")

    def commands(key, kinds):
        return "\n".join(sources[key][f["start"]["offset"]:f["end"]["offset"]].decode()
                         for f in facts[key] if f["kind"] == "command" and f["syntaxKind"] in kinds)

    variable_kind = {"Lean.Parser.Command.variable"}
    metric = (NOTICE + "import Mathlib.Geometry.Manifold.VectorBundle.Riemannian\n"
              "import Mathlib.Geometry.Manifold.VectorBundle.Tangent\n\n"
              "open Bundle\nopen scoped Manifold ContDiff\n\nnamespace DifferentialGeometry\n\n" +
              commands("upstream_metric", variable_kind) + "\n\n" +
              declaration("upstream_metric", "SmoothRiemannianMetric") +
              "\n\nend DifferentialGeometry\n\nnamespace Riemannian\n\n" +
              declaration("local_metric", "RiemannianMetric") + "\n\nend Riemannian\n")
    distance = (NOTICE + "import Definitions.Def_DifferentialGeometry_SmoothRiemannianMetric\n"
                "import Mathlib.Geometry.Manifold.Riemannian.Basic\n\n"
                "set_option autoImplicit false\nnoncomputable section\n"
                "open Bundle Manifold MeasureTheory Set\nopen scoped Manifold ContDiff ENNReal Topology\n\n"
                "namespace DifferentialGeometry\n\n" + commands("upstream_distance", variable_kind) +
                "\n\n" + declaration("upstream_distance", "riemannianEDistOf") + "\n\n" +
                declaration("upstream_distance", "riemannianEDistOf_self") + "\n\nend DifferentialGeometry\n")
    ball_names = ["geodesicBall", "mem_geodesicBall", "geodesicBall_eq_empty",
                  "geodesicBall_mono", "self_mem_geodesicBall", "geodesicBall_nonempty"]
    common = ("noncomputable section\nset_option autoImplicit false\n\n"
              "open Bundle Set DifferentialGeometry\nopen scoped Manifold ContDiff ENNReal\n\n")
    balls = (NOTICE + "import Definitions.Def_DifferentialGeometry_RiemannianDistance\n\n" + common +
             "namespace Riemannian.RiemannianMetric\n\n" + commands("local_ball", variable_kind) +
             "\n\n" + "\n\n".join(declaration("local_ball", n) for n in ball_names) +
             "\n\nend Riemannian.RiemannianMetric\n")
    preamble = ("import Definitions.Def_OpenGA_GeodesicBall\n"
                "import Mathlib.Geometry.Manifold.Metrizable\n\n" + common +
                "open Riemannian Riemannian.RiemannianMetric\n\n" + commands("local_ball", variable_kind))
    target = "isOpen_geodesicBall"
    statement = declaration("local_ball", target, PREFIX + target, stub=True)
    proof = NOTICE + preamble + "\n\n" + declaration("local_ball", target, "solution") + "\n"

    def save(path, code):
        (DIRECTORY / path).write_text(code)
        return {"path": path, "sha256": digest(code.encode())}

    upstream_url = "https://github.com/qinz1yang/differential-geometry/blob/" + REVISION + "/DifferentialGeometry/Geometry/Metric/"
    local_url = "https://github.com/MathNetwork/OpenGA/blob/" + LOCAL_REVISION + "/OpenGALib/"
    shared = {"env": ENVIRONMENT, "tags": ["comparison-geometry", "riemannian-geometry", "poincare-foundations"]}
    entries = []
    for name, title, code, deps, description, source in [
        ("DifferentialGeometry_SmoothRiemannianMetric", "Smooth Riemannian metric", metric, [],
         "Let $M$ be a smooth manifold. A smooth Riemannian metric assigns a positive-definite symmetric bilinear form $g_x$ to every tangent space $T_xM$, varying smoothly with $x$. This bundle reuses Mathlib's metric type through the original DifferentialGeometry and OpenGA aliases. It imposes no completeness, curvature or orientation assumption.",
         upstream_url + "Basic.lean#L12-L15; " + local_url + "Riemannian/Metric/RiemannianMetric.lean#L40-L49"),
        ("DifferentialGeometry_RiemannianDistance", "Distance induced by a specified Riemannian metric", distance,
         ["DifferentialGeometry_SmoothRiemannianMetric"],
         "For a smooth Riemannian metric $g$, define $d_g(x,y)$ as Mathlib's Riemannian extended distance computed using $g$: the infimum of lengths of the admissible differentiable paths from $x$ to $y$. The value lies in $[0,\\infty]$, allowing points in different components, and $d_g(x,x)=0$. This is the original DifferentialGeometry construction, based on Mathlib's path-length distance.",
         upstream_url + "DistanceScaling.lean#L22-L38"),
        ("OpenGA_GeodesicBall", "Open balls for a specified Riemannian metric", balls,
         ["DifferentialGeometry_RiemannianDistance"],
         "Let $g$ be a smooth Riemannian metric on $M$, $p\\in M$ and $r\\in\\mathbb R$. Define\n\n$$B_g(p,r)=\\{x\\in M:d_g(p,x)<\\max(r,0)\\}.$$\n\nFor $r>0$ this is the usual metric ball; for $r\\le0$ it is empty. The bundle includes its immediate membership, radius inclusion and center-membership properties. The distance is the imported DifferentialGeometry construction. No geodesic convexity, completeness or curvature bound is assumed.",
         local_url + "ComparisonGeometry/MetricBall.lean#L30-L61")]:
        entries.append({"id":name, "definitions":deps, **save("Definitions/Def_"+name+".lean",code),
                        "payload":dict(shared,definition_name=name,definition_title=title,definition=code,
                                       natural_language_statement=description,source=source)})
    theorem_name = PREFIX + target
    path = "Theorems/Thm_" + theorem_name.replace(".","_") + ".lean"
    proof_path = "Solutions/Sol_" + theorem_name.replace(".","_") + ".lean"
    proof_receipt = save(proof_path, proof)
    theorem = {"id":target, "definitions":[e["id"] for e in entries], "imports":[],
               **save(path,preamble+"\n\n"+statement+"\n"), "proof_path":proof_path,
               "proof_sha256":proof_receipt["sha256"],
               "payload":dict(shared,theorem_name=theorem_name,theorem_title="Riemannian metric balls are open in the manifold topology",
                   preamble=preamble,formal_statement=statement,
                   natural_language_statement="Let $M$ be a smooth Hausdorff, $\\sigma$-compact manifold with a finite-dimensional real inner-product model space, and let $g$ be a smooth Riemannian metric. For every $p\\in M$ and $r\\in\\mathbb R$, the metric ball $B_g(p,r)$ is open in the original manifold topology. Completeness, connectedness and curvature assumptions are not required. This identifies the ball interface with the topology needed for local volume estimates.",
                   source=local_url+"ComparisonGeometry/MetricBall.lean#L63-L78"),
               "explanation":"Reuse the specified metric to instantiate Mathlib's continuous Riemannian bundle and the induced extended metric with its compatible manifold topology. The set defining the ball is an extended-metric open ball, so Mathlib's openness theorem applies. The metric and distance definitions retain their original Mathlib/DifferentialGeometry provenance; this is OpenGA's interface corollary."}
    graph_path = DIRECTORY / "Metadata/declaration_graph.jsonl"
    graph = {r["name"]: r for r in map(json.loads, graph_path.read_text().splitlines())}
    pending = ["DifferentialGeometry.SmoothRiemannianMetric", "Riemannian.RiemannianMetric",
               "DifferentialGeometry.riemannianEDistOf", "DifferentialGeometry.riemannianEDistOf_self"]
    pending += [PREFIX + n for n in ball_names + [target]]
    closure = set()
    while pending:
        name = pending.pop()
        if name in closure:
            continue
        closure.add(name)
        pending.extend(graph[name]["typeDeps"] + graph[name]["valueDeps"])
    (DIRECTORY / "Metadata/selected_declaration_graph.json").write_text(
        json.dumps([graph[n] for n in sorted(closure)], indent=2) + "\n")
    source_records=[{"path":str(p.relative_to(REPOSITORY)),"sha256":digest(p.read_bytes())} for p in paths.values()]
    source_records += [{"path":str(p.relative_to(REPOSITORY)),"sha256":digest(p.read_bytes())}
                       for p in (DIRECTORY/"Metadata").glob("*_facts.jsonl")]
    record={"schema_version":1,"batch":"metric_balls","mission_id":"29133a9f-c412-4f19-968e-3deae9a335b5",
            "milestone_id":"cb96ab98-d517-4ecc-964b-b4b39a2d07a3", "mathlib_rev":ENVIRONMENT,
            "toolchain":"leanprover/lean4:v4.33.1","definitions":entries,"theorems":[theorem],
            "sources":source_records,"source_reviewed":True,"status":"STAGED",
            "source_graph_sha256":digest(graph_path.read_bytes()),
            "validation":{"status":"required"},
            "scope":"Three metric/distance/ball definition bundles and an openness interface corollary, reusing DifferentialGeometry and Mathlib. The full Bishop-Gromov milestone remains Open.",
            "transformations":["Lean source spans select original declarations and preserve variable contexts.",
                               "Remove scoped instance-disabling wrappers for upstream tensor instances absent from the staged environment.",
                               "Retain both metric aliases and all original definition names; verify their exact types and bodies.",
                               "Rename only the theorem binding to solution using the resolved reference span."]}
    record_path.write_text(json.dumps(record,indent=2,ensure_ascii=False,sort_keys=True)+"\n")
    print("Staged 3 definition bundles and the metric-ball openness theorem.")


if __name__ == "__main__":
    main()
