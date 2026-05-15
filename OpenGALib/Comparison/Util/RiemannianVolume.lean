import Mathlib.MeasureTheory.Measure.Hausdorff
import OpenGALib.Util.Attributes

/-!
# Riemannian-volume predicate

`IsRiemannianVolume n μ` asserts that `μ` agrees, up to a positive finite
scalar, with the `n`-dimensional Hausdorff measure of the metric on `X`.
Generic over the carrier `X` (just needs an `EMetricSpace` + Borel
σ-algebra) — the Riemannian-specific instantiation (`X = M`,
`n = Module.finrank ℝ E`) happens at the headline-theorem site.

Ground truth: Federer §3.2.46.
-/

open scoped ENNReal

namespace OpenGA.Comparison.BishopGromov

/-- **Math.** `μ` is a positive finite scalar multiple of the
`n`-dimensional Hausdorff measure on `X`. -/
def IsRiemannianVolume {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (n : ℕ) (μ : MeasureTheory.Measure X) : Prop :=
  ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧
    μ = c • MeasureTheory.Measure.hausdorffMeasure (n : ℝ)

end OpenGA.Comparison.BishopGromov
