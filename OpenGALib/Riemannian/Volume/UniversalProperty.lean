import OpenGALib.Riemannian.Volume.ChartPullback

/-!
# Universal property of the Riemannian volume

Phase 5 of the `riemannian-volume` Layer 3a sub-project: uniqueness
characterization of `vol_g` as the unique Borel measure on `M` satisfying
the chart-pullback formula.

  Among all Borel measures `μ` on `M`, the Riemannian volume `vol_g` is
  uniquely characterized by:

    *(chart-pullback)* In any chart `(U, φ)` and any open `A ⊆ U`,
        `μ(A) = ∫_{φ(A)} √det(g_ij ∘ φ⁻¹)(y) dy`.

Equivalently (using Mathlib's measure-equality discipline): two Borel
measures `μ_1`, `μ_2` agreeing on the chart-pullback formula on every
open chart-coordinate set are equal.

Ground truth: implicit in do Carmo Ch.1, Lee Ch.16; explicit
universal-property treatment in Bourbaki *Variétés Différentielles*.

This file lands the **uniqueness companion** to the chart-pullback
construction: anyone who builds a measure satisfying the chart formula
can conclude their measure IS the canonical `vol_g`.
-/

open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SigmaCompactSpace M]

/-- **Math.** **Uniqueness of the Riemannian volume**: any Borel measure
on `M` that agrees with `volumeMeasure g` on every open chart-coordinate
set equals `volumeMeasure g` everywhere.

This is the universal property: `vol_g` is the unique Borel measure
satisfying the chart-pullback characterization
(`volumeMeasure_chart_pullback_eq`, to be declared in Phase 1 follow-up).

Ground truth: standard measure-theoretic uniqueness on a generating
π-system (Mathlib `MeasureTheory.ext_of_generateFrom_of_iUnion` or
similar). Combined with the fact that open chart-coordinate sets
generate the Borel σ-algebra of a charted space.

PRE-PAPER (Phase 5). **Repair plan**: invoke Mathlib's measure
extension uniqueness on a chart-open-set generating set. Requires the
Phase 1 follow-up `volumeMeasure_chart_pullback_eq` characterization
theorem; chain is

  μ = vol_g  ⟸  μ agrees with vol_g on chart-coordinate opens
               ⟸  Mathlib `Measure.ext_of_iUnion` on π-system of opens.

Estimated 30-50 LOC. -/
theorem volumeMeasure_unique
    (g : RiemannianMetric I M) (μ : MeasureTheory.Measure M)
    (_hμ : ∀ x : M, ∀ U : Set M, IsOpen U → x ∈ U →
              ∃ (V : Set M) (_ : V ⊆ U) (_ : IsOpen V) (_ : x ∈ V),
              μ V = volumeMeasure g V) :
    μ = volumeMeasure g := by
  sorry

end Riemannian
