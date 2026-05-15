import Mathlib.MeasureTheory.Measure.Hausdorff
import OpenGALib.Util.Attributes

/-!
# `Measure.IsScalarMultipleOfHausdorff` predicate

`μ.IsScalarMultipleOfHausdorff n` asserts that `μ` is a positive finite
scalar multiple of the `n`-dimensional Hausdorff measure on `X`.

This is a **generic measure-theoretic** predicate; it does **not** pin down
a canonical Riemannian volume. On a Riemannian manifold the canonical
volume `vol_g` (defined chart-wise by `√det(g_ij) · Lebesgue`) is a
*specific* scalar multiple (the Federer–Hausdorff normalization
`α(n) = ω_n / 2^n` for Mathlib's diameter-based Hausdorff convention),
but the predicate here is satisfied by *any* positive multiple. Suitable
for downstream theorems whose conclusion is scale-invariant (e.g.
Bishop–Gromov volume comparison); not suitable as the definition of
"the Riemannian volume", which belongs in Layer 3a
(`OpenGALib/Riemannian/Util/RiemannianVolume.lean`, pending).

Ground truth: Federer §3.2.46.
-/

open scoped ENNReal MeasureTheory

namespace MeasureTheory.Measure

/-- **Math.** `μ` is a positive finite scalar multiple of the
`n`-dimensional Hausdorff measure on `X`. -/
def IsScalarMultipleOfHausdorff {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (n : ℕ) : Prop :=
  ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ μ = c • μH[(n : ℝ)]

end MeasureTheory.Measure
