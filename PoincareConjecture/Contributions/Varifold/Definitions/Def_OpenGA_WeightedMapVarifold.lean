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

/-- A finite weighted measure lifted to positions and planes. -/
def ofWeightedMap (μ : Measure X) (f : X → E) (P : X → Grassmannian E k)
    (J : X → ℝ≥0) (hf : Measurable f) (hP : Measurable P)
    (hfinite : (∫⁻ x, (J x : ℝ≥0∞) ∂μ) < ∞) : Varifold E k := by
  let ν := μ.withDensity (fun x => (J x : ℝ≥0∞))
  haveI : IsFiniteMeasure (ν.map (fun x => (f x, P x))) := ⟨by
    rw [Measure.map_apply (hf.prodMk hP) MeasurableSet.univ]
    simpa [ν, withDensity_apply] using hfinite⟩
  exact ⟨ν.map (fun x => (f x, P x)), inferInstance⟩

@[simp] theorem measure_ofWeightedMap (μ : Measure X) (f : X → E)
    (P : X → Grassmannian E k) (J : X → ℝ≥0) (hf : Measurable f) (hP : Measurable P)
    (hfinite : (∫⁻ x, (J x : ℝ≥0∞) ∂μ) < ∞) :
    (ofWeightedMap μ f P J hf hP hfinite).measure =
      (μ.withDensity (fun x => (J x : ℝ≥0∞))).map (fun x => (f x, P x)) := rfl

theorem mass_ofWeightedMap (μ : Measure X) (f : X → E)
    (P : X → Grassmannian E k) (J : X → ℝ≥0) (hf : Measurable f) (hP : Measurable P)
    (hfinite : (∫⁻ x, (J x : ℝ≥0∞) ∂μ) < ∞) :
    (ofWeightedMap μ f P J hf hP hfinite).mass = ∫⁻ x, (J x : ℝ≥0∞) ∂μ := by
  rw [mass, measure_ofWeightedMap, Measure.map_apply (hf.prodMk hP) MeasurableSet.univ]
  simp [withDensity_apply]

theorem weightMeasure_ofWeightedMap (μ : Measure X) (f : X → E)
    (P : X → Grassmannian E k) (J : X → ℝ≥0) (hf : Measurable f) (hP : Measurable P)
    (hfinite : (∫⁻ x, (J x : ℝ≥0∞) ∂μ) < ∞) :
    (ofWeightedMap μ f P J hf hP hfinite).weightMeasure =
      (μ.withDensity (fun x => (J x : ℝ≥0∞))).map f := by
  rw [weightMeasure, measure_ofWeightedMap, Measure.map_map measurable_fst (hf.prodMk hP)]
  rfl





end OpenGA.Varifold
