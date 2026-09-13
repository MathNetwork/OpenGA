import Definitions.Def_OpenGA_WeightedMapVarifold
import Definitions.Def_OpenGA_EuclideanVarifold
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Varifolds induced by weighted measurable maps

Push a finite weighted measure through `x ↦ (f x, P x)`, retaining both the
position and the plane. `J` is a nonnegative density; when it is the Jacobian
and `P` is the differential's image, this is the parametrized-surface construction.
The latter identification is made separately in `Varifold.Parametrization`.

The choice of plane where `J = 0` does not affect the varifold. This is the
extension-independence needed at degenerate differentials in CM Section 1.3.
Reference: Colding-Minicozzi, arXiv:0707.0108, Section 1.3, p. 5.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal CompactlySupported

namespace OpenGA.Varifold

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}











/-- Planes chosen differently on the zero-density set induce the same varifold. -/
theorem _root_.solution (μ : Measure X) (f : X → E)
    (P Q : X → Grassmannian E k) (J : X → ℝ≥0) (hf : Measurable f)
    (hP : Measurable P) (hQ : Measurable Q) (hJ : Measurable J)
    (hfinite : (∫⁻ x, (J x : ℝ≥0∞) ∂μ) < ∞)
    (hPQ : ∀ᵐ x ∂μ, J x ≠ 0 → P x = Q x) :
    ofWeightedMap μ f P J hf hP hfinite = ofWeightedMap μ f Q J hf hQ hfinite := by
  apply ext
  apply Measure.map_congr
  apply (ae_withDensity_iff hJ.coe_nnreal_ennreal).mpr
  filter_upwards [hPQ] with x hx hJx
  exact congrArg (fun S => (f x, S)) (hx (by simpa using hJx))

end OpenGA.Varifold
