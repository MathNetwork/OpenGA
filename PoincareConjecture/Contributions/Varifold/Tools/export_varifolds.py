#!/usr/bin/env python3
"""Export reviewed varifold interfaces using Lean-reported declaration spans."""

import hashlib
import json
from pathlib import Path
import subprocess

DIRECTORY = Path(__file__).resolve().parents[1]
REPOSITORY = DIRECTORY.parents[2]
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
MISSION = "29133a9f-c412-4f19-968e-3deae9a335b5"
TARGETS = {
    "Convergence": ["tendsto_weightMeasure_integral"],
    "WeightedMap": ["testIntegral_ofWeightedMap", "ofWeightedMap_eq_of_plane_eq"],
    "Parametrization": ["testIntegral_ofParametrization", "ofParametrization_independent_of_lift"],
    "AreaEnergy": ["mass_ofParametrization_le_energy"],
}
DEFINITIONS = {
    "Grassmannian": "OpenGA_UnorientedGrassmannian",
    "Varifold": "OpenGA_EuclideanVarifold",
    "Convergence": "OpenGA_VarifoldConvergence",
    "WeightedMap": "OpenGA_WeightedMapVarifold",
    "Parametrization": "OpenGA_ParametrizedVarifold",
}


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
        if any(e.get("publication") or e.get("submission")
               for e in old["definitions"] + old["theorems"]):
            raise RuntimeError("Publication has started; preserve its receipts")
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPOSITORY, text=True).strip()
    paths = {key: REPOSITORY / "OpenGALib/GeometricMeasureTheory" /
             ((key + ".lean") if key in ("Grassmannian", "Varifold")
              else "Varifold/" + key + ".lean") for key in [*DEFINITIONS, "AreaEnergy"]}
    sources = {key: path.read_bytes() for key, path in paths.items()}
    facts = {key: [json.loads(line) for line in (DIRECTORY / "Metadata" /
                 (key + "_facts.jsonl")).read_text().splitlines() if line.startswith("{")]
             for key in paths}
    density_path = REPOSITORY / "OpenGALib/Analysis/AreaEnergy.lean"
    density_facts = [json.loads(line) for line in (DIRECTORY / "Metadata/Density_facts.jsonl")
                     .read_text().splitlines() if line.startswith("{")]
    fact, = [f for f in density_facts if f["kind"] == "decl" and f["nameText"] == "continuous_areaDensity"]
    density_helper = density_path.read_bytes()[fact["declStart"]["offset"]:fact["declEnd"]["offset"]].decode()
    helper = "\nnamespace OpenGA\nvariable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]\n" + density_helper + "\nend OpenGA\n"

    replacements = {"OpenGALib.GeometricMeasureTheory." + (k if k in ("Grassmannian", "Varifold") else "Varifold." + k):
                    "Definitions.Def_" + v for k, v in DEFINITIONS.items()}
    replacements["OpenGALib.Analysis.AreaEnergy.LinearMap"] = (
        "Mathlib.Analysis.InnerProductSpace.NormDet\nimport Mathlib.Analysis.InnerProductSpace.PiL2\n"
        "import Mathlib.Tactic\nimport Theorems.Thm_OpenGA_areaDensity_eq_normDet")

    def module(key, keep, rename=None, stub=False):
        edits = []
        for f in facts[key]:
            if f["kind"] != "decl":
                continue
            a, b = f["declStart"]["offset"], f["declEnd"]["offset"]
            if not keep(f):
                edits.append((a, b, b""))
                continue
            if rename:
                name = "OpenGA.Varifold." + f["nameText"]
                binding, = [r for r in facts[key] if r["kind"] == "ref" and r["const"] == name
                            and a <= r["start"]["offset"] < r["end"]["offset"] <= f["valStart"]["offset"]]
                edits.append((binding["start"]["offset"], binding["end"]["offset"], rename.encode()))
            if stub:
                edits.append((f["valStart"]["offset"], b, b":= by sorry"))
                if f["docstring"]:
                    edits.append((f["docstring"]["start"]["offset"], f["docstring"]["end"]["offset"], b""))
        result = edited(sources[key], edits)
        # Import commands only; theorem text and proof references come from Lean spans.
        for old, new in replacements.items():
            result = result.replace("import " + old + "\n", "import " + new + "\n")
        return result

    def write(path, code):
        (DIRECTORY / path).write_text(code)
        return {"path": path, "sha256": digest(code.encode())}

    def source(key):
        return ("https://github.com/MathNetwork/OpenGA/blob/" + revision + "/" +
                str(paths[key].relative_to(REPOSITORY)) + "#L1-L" + str(len(sources[key].splitlines())))

    common = {"env": ENV, "tags": ["geometric-measure-theory", "varifold", "poincare-foundations", "openga-varifold"]}
    descriptions = {
        "Grassmannian": ("Grassmannian of unoriented planes", "For a finite-dimensional real inner-product space $E$, $G_k(E)$ consists of its exactly $k$-dimensional linear subspaces, without orientation. Its distance is the operator norm of the difference of the orthogonal projections. This compact metric space has its Borel measurable structure. If $k>\\dim E$, it is empty. The compactness and projection lemmas here support the measure constructions. Simon uses the Euclidean matrix norm; this formalization uses the operator norm on the same finite-dimensional operator space."),
        "Varifold": ("Euclidean varifolds and their weight measures", "A $k$-varifold on a finite-dimensional real inner-product space $E$ is a nonnegative Radon measure on $E\\times G_k(E)$. Its weight is the spatial pushforward and its mass is the total measure, which may be infinite. Compactness of $G_k(E)$ makes the weight measure Radon. This interface includes compactly supported test integrals, support, addition and nonnegative scaling. It imposes neither rectifiability nor stationarity. A general manifold requires its tangent Grassmann bundle, not this product."),
        "Convergence": ("Weak convergence of varifolds", "Equip Euclidean varifolds with the topology of convergence of integrals against every continuous compactly supported function on $E\\times G_k(E)$. Such tests determine a Radon measure, so this topology is Hausdorff. Spatial tests lift through the proper projection with compact Grassmannian fiber. This is qualitative weak convergence; no estimate in a particular metric is asserted."),
        "WeightedMap": ("Varifolds induced by weighted maps", "Let $(X,\\mu)$ be a measure space, $f:X\\to E$ and $P:X\\to G_k(E)$ measurable, and $J:X\\to[0,\\infty)$ with $\\int J\\,d\\mu<\\infty$. Push the weighted measure $J\\mu$ forward by $x\\mapsto(f(x),P(x))$. The resulting finite Radon measure is a varifold and its mass is $\\int J\\,d\\mu$. Measurability of $J$ is explicit in the integral and zero-density extension theorems. Identifying $J$ and $P$ with geometric derivatives is done in the parametrization interface."),
        "Parametrization": ("Varifolds of Euclidean parametrized surfaces", "For a $C^1$ map $f:\\mathbb R^2\\to E$, set $J_f=\\sqrt{\\det(df^*df)}$. A measurable tangent lift $P$ must equal the image of $df$ wherever $J_f\\ne0$. On a parameter domain $\\Omega$ of finite parametrized area, define $V_f=(f,P)_*(J_f\\,\\mathcal L^2|_\\Omega)$. Its mass equals $\\int_\\Omega J_f$, including multiplicity. Compact parameter domains have finite area. The lift is supplied as input; automatic measurable-lift construction, manifold charts and Sobolev derivatives remain further work."),
    }
    definitions = []
    for key, name in DEFINITIONS.items():
        code = module(key, lambda f: f["nameText"] not in TARGETS.get(key, []))
        if key == "Parametrization":
            # Supporting continuity lemma is copied from its Lean-reported source span.
            pos = code.index("/-!")
            code = code[:pos] + helper + "\n" + code[pos:]
        title, description = descriptions[key]
        imports = [line.removeprefix("import ") for line in code.splitlines() if line.startswith("import ")]
        definitions.append({"id": name, "definitions": [i.removeprefix("Definitions.Def_") for i in imports if i.startswith("Definitions.Def_")],
            "existing_theorems": [i.removeprefix("Theorems.Thm_") for i in imports if i.startswith("Theorems.Thm_")],
            **write("Definitions/Def_" + name + ".lean", code),
            "payload": dict(common, definition_name=name, definition_title=title, definition=code,
                natural_language_statement=description, source=source(key) + "; Leon Simon, Introduction to Geometric Measure Theory (2018), Chapter 8, Section 1, pp. 235-236, https://math.stanford.edu/~lms/ntu-gmt-text.pdf; Colding-Minicozzi, https://arxiv.org/pdf/0707.0108#page=5, Section 1.3.")})

    titles = {
        "tendsto_weightMeasure_integral": ("Varifold convergence implies convergence of spatial test integrals", "If Euclidean varifolds $V_i$ converge weakly to $V$, then for every continuous compactly supported spatial function $\\phi$, $\\int\\phi\\,d\\|V_i\\|\\to\\int\\phi\\,d\\|V\\|$. The index may be any filter. Compactness of the Grassmannian makes the lifted spatial test compactly supported."),
        "testIntegral_ofWeightedMap": ("Integration against a varifold induced by a weighted map", "For measurable $f:X\\to E$, $P:X\\to G_k(E)$ and $J:X\\to[0,\\infty)$ of finite integral, and every compactly supported continuous $\\phi$ on positions and planes,\n\n$$\\int\\phi\\,d((f,P)_*(J\\mu))=\\int_X J(x)\\phi(f(x),P(x))\\,d\\mu(x).$$"),
        "ofWeightedMap_eq_of_plane_eq": ("Zero-density choices do not change a weighted-map varifold", "Let $f$, $P$, $Q$ and $J\\ge0$ be measurable, with finite integral of $J$. If $P(x)=Q(x)$ for almost every $x$ with $J(x)\\ne0$, then $(f,P)_*(J\\mu)=(f,Q)_*(J\\mu)$. Thus arbitrary tangent-plane choices on the zero-density set have no effect."),
        "testIntegral_ofParametrization": ("Test-function formula for a parametrized surface varifold", "Let $f:\\mathbb R^2\\to E$ be $C^1$, let $P$ be a measurable tangent lift agreeing with the derivative image where $J_f\\ne0$, and assume $\\int_\\Omega J_f<\\infty$. For every compactly supported continuous position-plane test $\\phi$,\n\n$$\\int\\phi\\,dV_f=\\int_\\Omega J_f(x)\\phi(f(x),P(x))\\,dx.$$\n\nThis is the Euclidean parameter-domain form of the construction in CM Section 1.3."),
        "ofParametrization_independent_of_lift": ("A parametrized surface varifold is independent of its tangent lift", "Let $f:\\mathbb R^2\\to E$ be $C^1$ and have finite parametrized area on $\\Omega$. If two measurable plane lifts both agree with $df(\\mathbb R^2)$ wherever $J_f\\ne0$, they induce the same varifold on $E\\times G_2(E)$. No injectivity or immersion assumption is imposed. This verifies that the zero-Jacobian choices in the CM construction do not affect the result, for this Euclidean setting."),
        "mass_ofParametrization_le_energy": ("The mass of a parametrized surface varifold is bounded by its energy", "Let $f:\\mathbb R^2\\to E$ be $C^1$, $b_0,b_1$ an orthonormal basis, $P$ a measurable tangent lift, and $\\Omega$ a parameter domain with finite area and finite Dirichlet energy. Then\n\n$$\\mathbf M(V_f)\\le\\frac12\\int_\\Omega\\bigl(|df(b_0)|^2+|df(b_1)|^2\\bigr)\\,dx.$$\n\nThe Jacobian and tangent planes are those of the actual derivative. The proof reuses OpenGA's published integral area-energy comparison, which also enters the existing width-decay graph. This is CM equation (1.4) in a Euclidean parameter domain; no global frame on a sphere is asserted."),
    }
    proof_imports = {
        "testIntegral_ofParametrization": ["OpenGA.Varifold.testIntegral_ofWeightedMap"],
        "ofParametrization_independent_of_lift": ["OpenGA.Varifold.ofWeightedMap_eq_of_plane_eq"],
        "mass_ofParametrization_le_energy": ["OpenGA.integral_areaDensity_le_energyDensity"],
    }
    theorems = []
    for key, names in TARGETS.items():
        for name in names:
            full = "OpenGA.Varifold." + name
            definition = DEFINITIONS.get(key, DEFINITIONS["Parametrization"])
            prefix = "import Definitions.Def_" + definition + "\n"
            stub = module(key, lambda f: f["nameText"] == name, stub=True)
            proof = module(key, lambda f: f["nameText"] == name, rename="_root_.solution")
            if key == "Parametrization":
                # The definition module already supplies all of this module's imports.
                stub = "\n".join(line for line in stub.splitlines() if not line.startswith("import ")) + "\n"
                proof = "\n".join(line for line in proof.splitlines() if not line.startswith("import ")) + "\n"
            deps = proof_imports.get(name, [])
            proof = prefix + "".join("import Theorems.Thm_" + n.replace(".", "_") + "\n" for n in deps) + proof
            # Preamble contains only imports; namespace and variable commands stay together.
            lines = stub.splitlines(keepends=True)
            preamble = prefix + "".join(line for line in lines if line.startswith("import "))
            statement = "".join(line for line in lines if not line.startswith("import "))
            title, description = titles[name]
            path = "Theorems/Thm_" + full.replace(".", "_") + ".lean"
            proof_path = "Solutions/Sol_" + full.replace(".", "_") + ".lean"
            proof_hash = write(proof_path, proof)["sha256"]
            theorems.append({"id": full, "definitions": [definition], "imports": deps,
                **write(path, preamble + "\n\n" + statement + "\n"), "proof_path": proof_path, "proof_sha256": proof_hash,
                "payload": dict(common, theorem_name=full, theorem_title=title, preamble=preamble,
                    formal_statement=statement, natural_language_statement=description,
                    source=source(key) + "; Colding-Minicozzi, https://arxiv.org/pdf/0707.0108#page=" +
                           ("3, equation (1.4)." if key == "AreaEnergy" else "5, Section 1.3.")),
                "explanation": description + " The submitted proof preserves the reviewed OpenGA source; only imports and the solution binding are adapted."})

    existing = []
    for name, id in [("OpenGA.areaDensity_eq_normDet", "eddc764e-527d-4d07-a812-94f60b637407"),
                     ("OpenGA.integral_areaDensity_le_energyDensity", "d81e3640-8579-4396-babb-69edac82be33")]:
        path = "Theorems/Thm_" + name.replace(".", "_") + ".lean"
        data = (REPOSITORY / "PoincareConjecture" / path).read_bytes()
        (DIRECTORY / path).write_bytes(data)
        existing.append({"name": name, "id": id, "path": path, "sha256": digest(data)})
    defpath = "Definitions/Def_OpenGA_AreaEnergyDensities.lean"
    data = (REPOSITORY / "PoincareConjecture" / defpath).read_bytes()
    (DIRECTORY / defpath).write_bytes(data)
    existing.append({"name": "OpenGA_AreaEnergyDensities", "id": "caf5e7f7-144e-4bc2-9730-695304525ad0", "path": defpath, "sha256": digest(data)})
    graph = [json.loads(line) for line in (DIRECTORY / "Metadata/declaration_graph.jsonl").read_text().splitlines()]
    (DIRECTORY / "Metadata/selected_declaration_graph.json").write_text(json.dumps(graph, indent=2) + "\n")
    tracked_sources = list(paths.values()) + [density_path] + list((DIRECTORY / "Metadata").glob("*_facts.jsonl"))
    record = {"schema_version": 1, "batch": "euclidean_varifolds", "mission_id": MISSION,
              "mathlib_rev": ENV, "toolchain": "leanprover/lean4:v4.33.1", "source_revision": revision,
              "source_reviewed": True, "sources": [{"path": str(p.relative_to(REPOSITORY)), "sha256": digest(p.read_bytes())} for p in tracked_sources],
              "definitions": definitions, "theorems": theorems, "existing": existing,
              "status": "STAGED", "validation": {"status": "required"},
              "scope": "Euclidean Radon varifolds, qualitative convergence and C1 parametrizations with supplied measurable tangent lifts. Not the manifold/Sobolev CM min-max or finite-extinction theorem."}
    record_path.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
    print("Staged five definition bundles and six theorem/solution pairs.")


if __name__ == "__main__":
    main()
