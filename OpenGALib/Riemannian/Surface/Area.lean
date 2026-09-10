import OpenGALib.Riemannian.Surface.InducedMetric
import OpenGALib.Riemannian.VolumeVariation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Global area of a smooth immersed surface

Area is the Riemannian measure of the induced metric on the domain surface.
It counts multiplicity and uses no global frame or orientation. Chart gluing
and independence of the partition of unity are inherited from the upstream
Riemannian measure construction. Compact surfaces have finite area.

Branch points are excluded by the injectivity assumption on the differential.
-/

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Integral.Measure

namespace OpenGA.Surface

abbrev Model := EuclideanSpace ℝ (Fin 2)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Model N]
  [IsManifold 𝓘(ℝ, Model) ∞ N] [T2Space N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

/-- The induced area measure on the domain of an immersed surface. -/
def areaMeasure [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I M) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Model) I f x)) : Measure N :=
  riemannianVolumeMeasure (I := 𝓘(ℝ, Model)) (M := N) (inducedMetric g f hf hinj)

/-- Total area, with multiplicity, of a fixed immersed surface. -/
def area [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I M) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Model) I f x)) : ℝ :=
  totalRiemannianVolume (inducedMetric g f hf hinj)

theorem areaMeasure_finite [CompactSpace N]
    (g : SmoothRiemannianMetric I M) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Model) I f x)) :
    IsFiniteMeasure (areaMeasure g f hf hinj) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (inducedMetric g f hf hinj)

theorem area_eq_measure_univ [CompactSpace N]
    (g : SmoothRiemannianMetric I M) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Model) I f x)) :
    area g f hf hinj = (areaMeasure g f hf hinj Set.univ).toReal := by
  change (∫ _ : N, (1 : ℝ) ∂(areaMeasure g f hf hinj)) = _
  simp [Measure.real]

theorem area_nonneg [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I M) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Model) I f x)) :
    0 ≤ area g f hf hinj := integral_nonneg (fun _ => zero_le_one)

theorem area_pos [CompactSpace N] [Nonempty N]
    (g : SmoothRiemannianMetric I M) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Model) I f x)) :
    0 < area g f hf hinj := by
  have : IsFiniteMeasure (areaMeasure g f hf hinj) := areaMeasure_finite g f hf hinj
  have : Measure.IsOpenPosMeasure (areaMeasure g f hf hinj) :=
    riemannianVolumeMeasure_isOpenPosMeasure (inducedMetric g f hf hinj)
  rw [area_eq_measure_univ]
  exact ENNReal.toReal_pos (ne_of_gt (isOpen_univ.measure_pos _ Set.univ_nonempty))
    (measure_ne_top _ _)

end OpenGA.Surface
