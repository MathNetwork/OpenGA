import Mathlib.MeasureTheory.Measure.Hausdorff
import OpenGALib.Util.Attributes

/-!
# `Measure.IsRiemannianVolume` predicate

`μ.IsRiemannianVolume n` asserts that `μ` agrees, up to a positive finite
scalar, with the `n`-dimensional Hausdorff measure on `X`.

Ground truth: Federer §3.2.46.
-/

open scoped ENNReal MeasureTheory

namespace MeasureTheory.Measure

/-- **Math.** `μ` is a positive finite scalar multiple of the
`n`-dimensional Hausdorff measure on `X`. -/
def IsRiemannianVolume {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) (n : ℕ) : Prop :=
  ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ μ = c • μH[(n : ℝ)]

end MeasureTheory.Measure
