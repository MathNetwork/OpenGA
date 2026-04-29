# Axiom Status

Central registry of `axiom` declarations in OpenGA. Every axiom carries a
classification + repair plan. CI snapshots this list; new axiom additions
require updating this file.

## Classification

* **PRE-PAPER** — gap in Mathlib API or framework primitive; closure path
  is framework self-build or Mathlib upstream.
* **CITED-BLACK-BOX** — theorem quoted from a paper, body never proven in
  the framework.
* **PAPER-INTERNAL** — proof obligation owned by an application paper, not
  the library.
* **CONJECTURAL** — open mathematics.

## Current axioms

**Total**: **0** axioms.

The previous `tangentBundle_symmL_smoothAt` axiom (Phase 4.7.5.C, in
`Riemannian/Metric/Smooth.lean`) has been converted to a `theorem`
declaration in Phase 5 (C'2); the body is currently `sorry`'d (tracked
in `SORRY_CATALOG.md`) with a detailed Mathlib-`Pullback.lean`-based
proof outline. The closure of this sorry remains a Phase 4.8 follow-up.

## Notes

* This catalog tracks **public-facing** axioms (those in OpenGA's
  Algebraic / Riemannian / GeometricMeasureTheory / MinMax / Regularity
  packages). Application papers (e.g., AltRegularity) maintain their own
  catalogs.
* `private theorem ... := by sorry` declarations are **not** axioms (they
  are unfinished proofs, tracked in `SORRY_CATALOG.md`).
* Updating this file: when adding a new `axiom`, add an entry with
  classification + repair plan. When closing an axiom (replacing with a
  real proof), remove its entry + record in `CHANGELOG.md` (Phase 6).
