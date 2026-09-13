#!/usr/bin/env python3
"""Export the first Bishop-Gromov dependency using Lean-reported source ranges."""

import hashlib
import json
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parents[1]
REPOSITORY = DIRECTORY.parents[2]
SOURCE = REPOSITORY / ".lake/packages/DifferentialGeometry/DifferentialGeometry/Geometry/Comparison/Volume/RatioIntegral.lean"
PREFIX = "DifferentialGeometry.Geometry.Riemannian.VolumeComparison"
REVISION = "1b535dd102b94cc42b107cca27059687888f08b3"
ENVIRONMENT = "0df444a360eaa60ab8c11dca51a86af692955474"
DEFINITION_NAME = "DifferentialGeometry_RadialCrossComparison"
NOTICE = (
    "/-\nCopyright 2026 The DifferentialGeometry contributors.\n"
    "Licensed under Apache-2.0. Adapted from qinz1yang/differential-geometry,\n"
    f"commit {REVISION}.\n"
    "Only declaration placement and platform imports are changed.\n-/\n\n"
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def edited(source, edits):
    """Apply disjoint edits to UTF-8 bytes; offsets come from Lean, not text searches."""
    boundary = len(source)
    for start, end, replacement in sorted(edits, reverse=True):
        if not 0 <= start <= end <= boundary:
            raise ValueError("Overlapping or invalid source edits")
        source = source[:start] + replacement + source[end:]
        boundary = start
    return source


def main():
    path = DIRECTORY / "publication.json"
    if path.exists():
        existing = json.loads(path.read_text())
        if any(entry.get("publication") or entry.get("submission")
               for entry in existing.get("definitions", []) + existing.get("theorems", [])):
            raise RuntimeError("Refusing to overwrite publication receipts")
    source = SOURCE.read_bytes()
    facts_path = DIRECTORY / "Metadata/ratio_integral_facts.jsonl"
    facts = [json.loads(line) for line in facts_path.read_text().splitlines()]
    declarations = [fact for fact in facts if fact["kind"] == "decl"]
    by_name = {fact["nameText"]: fact for fact in declarations}
    namespace_commands = [fact for fact in facts if fact["kind"] == "command" and
                          fact["syntaxKind"] in ("Lean.Parser.Command.namespace", "Lean.Parser.Command.end")]

    def source_url(fact):
        return (f"https://github.com/qinz1yang/differential-geometry/blob/{REVISION}/"
                "DifferentialGeometry/Geometry/Comparison/Volume/RatioIntegral.lean"
                f"#L{fact['declStart']['line']}-L{fact['declEnd']['line']}")

    def save(relative, content):
        (DIRECTORY / relative).write_text(content)
        return {"path": relative, "sha256": digest(content.encode())}

    definition_edits = [(d["declStart"]["offset"], d["declEnd"]["offset"], b"")
                        for d in declarations if d["nameText"] != "CrossAnti"]
    definition = NOTICE + edited(source, definition_edits).decode().strip() + "\n"
    definition_entry = {
        "id": "radial_cross_comparison",
        **save(f"Definitions/Def_{DEFINITION_NAME}.lean", definition),
        "payload": {
            "definition_name": DEFINITION_NAME,
            "definition_title": "Cross-multiplied comparison of radial densities",
            "definition": definition,
            "natural_language_statement": (
                "Let $R\\in\\mathbb R$ and let $f,g:\\mathbb R\\to[0,\\infty]$. "
                "The cross-comparison condition requires\n\n"
                "$$f(b)g(a)\\le f(a)g(b)\\qquad(0<a\\le b\\le R).$$\n\n"
                "When $g$ is finite and positive, this expresses that $f/g$ is "
                "nonincreasing. The cross-multiplied formulation also permits "
                "vanishing or infinite densities without division. It is an "
                "analytic input for radial volume comparison."
            ),
            "source": source_url(by_name["CrossAnti"]),
            "tags": ["bishop-gromov", "differential-geometry", "measure-theory"],
            "env": ENVIRONMENT,
        },
    }

    metadata = {
        "lintegral_Iic_cross": {
            "title": "Integral comparison on nested lower intervals",
            "description": (
                "Let $X$ be a linearly ordered topological measurable space in "
                "which open sets are measurable and lower intervals $(-\\infty,r]$ "
                "are closed. Let $\\mu$ be a measure on $X$ and let "
                "$f,g:X\\to[0,\\infty]$ be almost-everywhere measurable on "
                "$(-\\infty,R]$. Assume $f(b)g(a)\\le f(a)g(b)$ whenever "
                "$a\\le b\\le R$. Then, for every $s\\le R$,\n\n"
                "$$\\left(\\int_{(-\\infty,R]} f\\,d\\mu\\right)"
                "\\left(\\int_{(-\\infty,s]} g\\,d\\mu\\right)"
                "\\le\\left(\\int_{(-\\infty,s]} f\\,d\\mu\\right)"
                "\\left(\\int_{(-\\infty,R]} g\\,d\\mu\\right).$$\n\n"
                "All integrals are extended nonnegative integrals; no finiteness "
                "or sigma-finiteness assumption is imposed. This transfers a "
                "pointwise density comparison to a comparison of accumulated "
                "mass, as used in the upstream Bishop–Gromov proof."
            ),
        },
        "lintegral_cross_le": {
            "title": "Radial density comparison implies integrated comparison",
            "description": (
                "Let $\\mu$ be a measure on $\\mathbb R$, let $0\\le s\\le R$, "
                "and let $f,g:\\mathbb R\\to[0,\\infty]$ be almost-everywhere "
                "measurable on $(0,R]$. Assume $f(b)g(a)\\le f(a)g(b)$ for "
                "$0<a\\le b\\le R$. Then\n\n"
                "$$\\left(\\int_{(0,R]} f\\,d\\mu\\right)"
                "\\left(\\int_{(0,s]} g\\,d\\mu\\right)"
                "\\le\\left(\\int_{(0,s]} f\\,d\\mu\\right)"
                "\\left(\\int_{(0,R]} g\\,d\\mu\\right).$$\n\n"
                "The endpoint $s=0$ is included. This is the analytic "
                "density-to-volume step of radial comparison; identifying "
                "these integrals with Riemannian ball volumes requires the "
                "separate geometric polar integration theorem."
            ),
        },
    }
    theorems = []
    for name, meta in metadata.items():
        fact = by_name[name]
        start, end, value = (fact[k]["offset"] for k in ("declStart", "declEnd", "valStart"))
        full_name = PREFIX + "." + name
        bindings = [f for f in facts if f["kind"] == "ref" and f["const"] == full_name
                    and start <= f["start"]["offset"] < f["end"]["offset"] <= value]
        if len(bindings) != 1:
            raise ValueError("Expected one binding occurrence: " + full_name)
        binding = bindings[0]
        bstart, bend = binding["start"]["offset"], binding["end"]["offset"]
        if source[bstart:bend].decode() != name:
            raise ValueError("The binding span no longer matches the source")
        prefix_edits = [(d["declStart"]["offset"], d["declEnd"]["offset"], b"")
                        for d in declarations if d["declEnd"]["offset"] <= start]
        for command in namespace_commands:
            if command["end"]["offset"] <= start:
                prefix_edits.append((command["start"]["offset"], command["end"]["offset"], b""))
        preamble = edited(source[:start], prefix_edits).decode().strip()
        definitions = []
        if name == "lintegral_cross_le":
            definitions = [definition_entry["id"]]
            preamble = f"import Definitions.Def_{DEFINITION_NAME}\n" + preamble
            preamble += "\nopen " + PREFIX
        preamble += "\nset_option autoImplicit false"
        statement = edited(source[start:value], [(bstart-start, bend-start, full_name.encode())]).decode()
        statement = statement.rstrip() + " := by sorry"
        proof = edited(source[start:end], [(bstart-start, bend-start, b"solution")]).decode()
        slug = full_name.replace(".", "_")
        exact_statement = preamble + "\n\n" + statement + "\n"
        exact_proof = NOTICE + preamble + "\n\n" + proof + "\n"
        proof_info = save(f"Solutions/Sol_{slug}.lean", exact_proof)
        theorems.append({
            "id": name,
            **save(f"Theorems/Thm_{slug}.lean", exact_statement),
            "proof_path": proof_info["path"], "proof_sha256": proof_info["sha256"],
            "definitions": definitions, "imports": [],
            "payload": {
                "theorem_name": full_name, "theorem_title": meta["title"],
                "preamble": preamble, "formal_statement": statement,
                "natural_language_statement": meta["description"],
                "source": source_url(fact),
                "tags": ["bishop-gromov", "differential-geometry", "measure-theory"],
                "env": ENVIRONMENT,
            },
            "explanation": (
                "The cross-comparison hypothesis passes to integrals:\n\n"
                "$$F(R)G(s)\\le F(s)G(R).$$\n\n"
                "Here $F$ and $G$ are the accumulated integrals of $f$ and $g$ "
                "over the intervals in the statement. Split the outer interval "
                "into the inner interval $A$ and the disjoint remainder $B$. "
                "Every $a\\in A$ precedes every $b\\in B$, so the hypothesis "
                "gives $f(b)g(a)\\le f(a)g(b)$. Integrating this inequality first "
                "over $a$ and then over $b$ gives\n\n"
                "$$\\left(\\int_B f\\,d\\mu\\right)"
                "\\left(\\int_A g\\,d\\mu\\right)"
                "\\le\\left(\\int_A f\\,d\\mu\\right)"
                "\\left(\\int_B g\\,d\\mu\\right).$$\n\n"
                "Add the common product of the two inner integrals and use "
                "additivity over the disjoint union. The proof works with "
                "extended nonnegative integrals, including infinite values.\n\n"
                "Proof adapted from DifferentialGeometry v0.1.2, "
                "RatioIntegral.lean; the original argument and hypotheses are preserved."
            ),
        })
    record = {
        "schema_version": 1, "status": "EXPORTED_NOT_VALIDATED", "phase": "radial_integral_prerequisites",
        "mission_id": "29133a9f-c412-4f19-968e-3deae9a335b5",
        "milestone_id": "cb96ab98-d517-4ecc-964b-b4b39a2d07a3",
        "mathlib_rev": ENVIRONMENT, "toolchain": "leanprover/lean4:v4.33.1",
        "upstream_commit": REVISION,
        "source_reviewed": True,
        "sources": [{"path": str(SOURCE.relative_to(REPOSITORY)), "sha256": digest(source)},
                    {"path": str(facts_path.relative_to(REPOSITORY)), "sha256": digest(facts_path.read_bytes())}],
        "scope": "Analytic prerequisites only. The full geometric Bishop-Gromov milestone remains Open.",
        "definitions": [definition_entry], "theorems": theorems,
    }
    path.write_text(json.dumps(record, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print("Exported one definition and two upstream integral-comparison theorems.")


if __name__ == "__main__":
    main()
