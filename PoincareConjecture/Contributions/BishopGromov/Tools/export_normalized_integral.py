#!/usr/bin/env python3
"""Append the OpenGA corollary using Lean syntax ranges, preserving earlier receipts."""

import json
from export_ratio_integral import DIRECTORY, REPOSITORY, SOURCE, PREFIX, edited, digest


def main():
    path = DIRECTORY / "publication.json"
    record = json.loads(path.read_text())
    name = "antitoneOn_lintegral_Ioc_div"
    if any(entry["id"] == name for entry in record["theorems"]):
        raise RuntimeError("The corollary is already exported")
    local = REPOSITORY / "OpenGALib/Analysis/IntegralComparison.lean"
    source = local.read_bytes()
    facts_path = DIRECTORY / "Metadata/normalized_integral_facts.jsonl"
    facts = [json.loads(line) for line in facts_path.read_text().splitlines()]
    fact, = [f for f in facts if f["kind"] == "decl" and f["nameText"] == name]
    start, end, value = (fact[k]["offset"] for k in ("declStart", "declEnd", "valStart"))
    binding, = [f for f in facts if f["kind"] == "ref" and f["const"] == "OpenGA." + name
                and start <= f["start"]["offset"] < f["end"]["offset"] <= value]
    bstart, bend = binding["start"]["offset"], binding["end"]["offset"]
    doc = fact["docstring"]
    declaration_edits = [(doc["start"]["offset"] - start, doc["end"]["offset"] - start, b"")]
    statement = edited(source[start:value], declaration_edits +
                       [(bstart - start, bend - start, ("OpenGA." + name).encode())]).decode().strip()
    proof = edited(source[start:end], declaration_edits +
                   [(bstart - start, bend - start, b"solution")]).decode().strip()
    header, = [f for f in facts if f["kind"] == "header"]
    prefix_edits = [(header["start"]["offset"], header["end"]["offset"],
                     b"import Definitions.Def_DifferentialGeometry_RadialCrossComparison")]
    for command in facts:
        if command["kind"] == "command" and command["end"]["offset"] <= start and command["syntaxKind"] in (
                "Lean.Parser.Command.moduleDoc", "Lean.Parser.Command.namespace"):
            prefix_edits.append((command["start"]["offset"], command["end"]["offset"], b""))
    preamble = edited(source[:start], prefix_edits).decode().strip()
    statement += " := by sorry"
    child = "Theorems.Thm_" + PREFIX.replace(".", "_") + "_lintegral_cross_le"
    exact_statement = preamble + "\n\n" + statement + "\n"
    exact_proof = "import " + child + "\n" + preamble + "\n\n" + proof + "\n"
    theorem_path = "Theorems/Thm_OpenGA_" + name + ".lean"
    proof_path = "Solutions/Sol_OpenGA_" + name + ".lean"
    (DIRECTORY / theorem_path).write_text(exact_statement)
    (DIRECTORY / proof_path).write_text(exact_proof)
    record["theorems"].append({
        "id": name, "path": theorem_path, "sha256": digest(exact_statement.encode()),
        "proof_path": proof_path, "proof_sha256": digest(exact_proof.encode()),
        "definitions": ["radial_cross_comparison"], "imports": ["lintegral_cross_le"],
        "payload": {
            "env": record["mathlib_rev"], "theorem_name": "OpenGA." + name,
            "theorem_title": "Monotonicity of normalized radial integrals",
            "preamble": preamble, "formal_statement": statement,
            "natural_language_statement": (
                "Let $\\mu$ be a measure on $\\mathbb R$, and let $f,g:\\mathbb R\\to[0,\\infty]$ "
                "be almost-everywhere measurable on $(0,R]$. Assume $f(b)g(a)\\le f(a)g(b)$ "
                "whenever $0<a\\le b\\le R$. Write $F(r)=\\int_{(0,r]} f\\,d\\mu$ and "
                "$G(r)=\\int_{(0,r]} g\\,d\\mu$, and assume $0<G(r)<\\infty$ for every "
                "$0<r\\le R$. Then\n\n"
                "$$\\frac{F(s)}{G(s)}\\le\\frac{F(r)}{G(r)}\\qquad(0<r\\le s\\le R).$$\n\n"
                "The numerator may be infinite. This is the analytic normalized-volume monotonicity "
                "step; its application to Riemannian balls additionally requires geometric density "
                "comparison and polar integration."
            ),
            "source": "OpenGA, OpenGALib/Analysis/IntegralComparison.lean, derived from "
                      "DifferentialGeometry.Geometry.Riemannian.VolumeComparison.lintegral_cross_le "
                      "(DifferentialGeometry v0.1.2). "
                      "https://github.com/MathNetwork/OpenGA/blob/feat/prove2me-differential-geometry/"
                      "OpenGALib/Analysis/IntegralComparison.lean",
            "tags": ["bishop-gromov", "differential-geometry", "measure-theory"],
        },
        "explanation": (
            "Fix $0<r\\le s\\le R$. Restrict measurability and the density comparison to $(0,s]$. "
            "The proved radial integral comparison gives\n\n"
            "$$F(s)G(r)\\le F(r)G(s).$$\n\n"
            "Both $G(r)$ and $G(s)$ are positive and finite. Division by these factors therefore "
            "preserves the inequality even for extended nonnegative numerators, yielding "
            "$F(s)/G(s)\\le F(r)/G(r)$. The Lean proof imports the separately verified "
            "radial comparison theorem, so this dependency is visible in the proof graph."
        ),
    })
    for source_path in (local, facts_path):
        record["sources"].append({"path": str(source_path.relative_to(REPOSITORY)),
                                  "sha256": digest(source_path.read_bytes())})
    record["validation"] = {"status": "required"}
    record["status"] = "EXPORTED_NOT_VALIDATED"
    path.write_text(json.dumps(record, ensure_ascii=False, indent=2, sort_keys=True) + "\n")

    # Resolve the sole imported theorem to its audited complete proof for a no-sorry axiom audit.
    upstream_facts = [json.loads(line) for line in
                      (DIRECTORY / "Metadata/ratio_integral_facts.jsonl").read_text().splitlines()]
    child_fact, = [f for f in upstream_facts if f["kind"] == "decl" and f["nameText"] == "lintegral_cross_le"]
    lo, hi, val = (child_fact[k]["offset"] for k in ("declStart", "declEnd", "valStart"))
    child_binding, = [f for f in upstream_facts if f["kind"] == "ref" and
                      f["const"] == PREFIX + ".lintegral_cross_le" and lo <= f["start"]["offset"] < val]
    child_proof = edited(SOURCE.read_bytes()[lo:hi], [
        (child_binding["start"]["offset"] - lo, child_binding["end"]["offset"] - lo,
         (PREFIX + ".lintegral_cross_le").encode())]).decode()
    child_entry, = [entry for entry in record["theorems"] if entry["id"] == "lintegral_cross_le"]
    audit_tail = """
open Lean in
run_meta do
  let target ← Lean.getConstInfo `OpenGA.antitoneOn_lintegral_Ioc_div
  let solved ← Lean.getConstInfo `solution
  unless ← Lean.Meta.isDefEq target.type solved.type do
    throwError "The solution type does not match its target"
  let axioms ← Lean.collectAxioms `solution
  for name in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains name do
      throwError "Unexpected proof axiom: {name}"
  Lean.logInfo m!"Exact target type matched after resolving the audited child proof; axioms: {axioms}"
"""
    audit = ("import Lean\nimport Theorems.Thm_OpenGA_" + name + "\n" +
             child_entry["payload"]["preamble"] + "\n\n" + child_proof + "\n\n" + proof + audit_tail)
    (DIRECTORY / ("Tools/Audit_" + name + ".lean")).write_text(audit)
    print("Exported normalized radial integral monotonicity with one tracked theorem dependency.")


if __name__ == "__main__":
    main()
