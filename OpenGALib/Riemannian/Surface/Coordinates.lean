import OpenGALib.Riemannian.Surface.InducedMetric
import OpenGALib.Interoperability.RicciFlow.SurfaceArea

/-!
# Compatibility of induced metrics with parameter-patch area

Pulling the ambient metric back to a surface and then parametrizing that
surface gives exactly the existing area density of the composed map into the
ambient manifold. Both constructions use the actual manifold derivative.
-/

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff
open DifferentialGeometry OpenGA.RicciFlow

namespace OpenGA.Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]

theorem surfaceMetricMatrix_inducedMetric
    (g : SmoothRiemannianMetric J M) (f : N → M) (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (p : SurfaceParameter → N) {u : SurfaceParameter}
    (hp : MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I p u) :
    surfaceMetricMatrix (inducedMetric g f hf hinj) p u =
      surfaceMetricMatrix g (f ∘ p) u := by
  ext i j
  simp only [surfaceMetricMatrix, inducedMetric_inner, surfaceTangent]
  rw [mfderiv_comp u (hf.mdifferentiable (by simp) (p u)) hp]
  rfl

theorem surfaceDensity_inducedMetric
    (g : SmoothRiemannianMetric J M) (f : N → M) (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (p : SurfaceParameter → N) {u : SurfaceParameter}
    (hp : MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I p u) :
    surfaceDensity (inducedMetric g f hf hinj) p u = surfaceDensity g (f ∘ p) u := by
  unfold surfaceDensity
  rw [surfaceMetricMatrix_inducedMetric g f hf hinj p hp]

/-- Local patch area agrees with the area density of the global induced metric. -/
theorem patchArea_inducedMetric
    (g : SmoothRiemannianMetric J M) (f : N → M) (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (p : SurfaceParameter → N) (A : Set SurfaceParameter) (hA : MeasurableSet A)
    (hp : ∀ u ∈ A, MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I p u) :
    patchArea (inducedMetric g f hf hinj) p A = patchArea g (f ∘ p) A := by
  apply setIntegral_congr_fun hA
  intro u hu
  exact surfaceDensity_inducedMetric g f hf hinj p (hp u hu)

end OpenGA.Surface
