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

| # | File | Identifier | Classification | Repair plan |
|---|------|-----------|---------------|-------------|
| 1 | `Riemannian/Metric.lean:421` | `tangentBundle_symmL_smoothAt` | PRE-PAPER | Mathlib lacks a non-dependent flat-CLM smoothness lemma for `Trivialization.symmL` on the tangent bundle (`E →L[ℝ] TangentSpace I y` has dependent codomain incompatible with `MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)`). Closure path: (a) Mathlib upstream PR adding non-dependent form, OR (b) framework redesign of `RiemannianMetric.smoothMetric` to bundle-section form, then `clm_bundle_apply₂` resolves the chart-bridge internally. Tracked as Phase 4.8 architectural follow-up. |

**Total**: 1 axiom (Riemannian: 1, GMT: 0, MinMax: 0, Regularity: 0).

## Notes

* This catalog tracks **public-facing** axioms (those in OpenGA's
  Riemannian / GeometricMeasureTheory / MinMax / Regularity packages).
  Application papers (e.g., AltRegularity) maintain their own catalogs.
* `private theorem ... := by sorry` declarations are **not** axioms (they
  are unfinished proofs, tracked in `SORRY_CATALOG.md`).
* Updating this file: when adding a new `axiom`, add a row with
  classification + repair plan. When closing an axiom (replacing with a
  real proof), remove its row + record in `CHANGELOG.md` (Phase 6).
