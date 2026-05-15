import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import OpenGALib.Util.Attributes

/-!
# Space-form geometry helpers for Bishop–Gromov

Snake function, space-form ball volume, admissible-radii set.
Ground truth: Petersen Ch.6 §2, do Carmo Ch.10 §1–2.
-/

open scoped Real ENNReal

namespace OpenGA.Comparison.BishopGromov

/-- **Math.** Snake function `s_K(r)`: `sin(√K·r)/√K` (K>0), `r` (K=0),
`sinh(√(-K)·r)/√(-K)` (K<0). -/
noncomputable def snakeFunction (K r : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * r) / Real.sqrt K
  else if K < 0 then Real.sinh (Real.sqrt (-K) * r) / Real.sqrt (-K)
  else r

/-- **Math.** `V_K^n(r) = n · ω_n · ∫₀^r max(s_K(t),0)^(n-1) dt`. -/
noncomputable def spaceFormBallVolume (n : ℕ) (K r : ℝ) : ℝ :=
  let ωₙ : ℝ :=
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
  (n : ℝ) * ωₙ * ∫ t in (0 : ℝ)..r, max 0 (snakeFunction K t) ^ (n - 1)

/-- **Math.** Admissible radii `𝒟_K`: `(0, π/√K)` if K>0, `(0,∞)` otherwise. -/
noncomputable def spaceFormAdmissibleRadii (K : ℝ) : Set ℝ :=
  if 0 < K then Set.Ioo 0 (Real.pi / Real.sqrt K) else Set.Ioi 0

end OpenGA.Comparison.BishopGromov
