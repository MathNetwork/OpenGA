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









/-- The integral formula retains the plane observable and weights it by the density. -/
theorem _root_.solution (μ : Measure X) (f : X → E)
    (P : X → Grassmannian E k) (J : X → ℝ≥0) (hf : Measurable f) (hP : Measurable P)
    (hJ : Measurable J) (hfinite : (∫⁻ x, (J x : ℝ≥0∞) ∂μ) < ∞)
    (φ : C_c(E × Grassmannian E k, ℝ)) :
    (ofWeightedMap μ f P J hf hP hfinite).testIntegral φ =
      ∫ x, (J x : ℝ) * φ (f x, P x) ∂μ := by
  calc
    _ = ∫ x, φ (f x, P x) ∂μ.withDensity (fun x => (J x : ℝ≥0∞)) :=
      integral_map (hf.prodMk hP).aemeasurable φ.continuous.aestronglyMeasurable
    _ = _ := integral_withDensity_eq_integral_smul hJ _



end OpenGA.Varifold
