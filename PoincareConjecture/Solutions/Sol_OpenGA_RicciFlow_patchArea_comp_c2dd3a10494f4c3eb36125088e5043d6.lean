import Theorems.Thm_OpenGA_RicciFlow_surfaceDensity_comp
import Definitions.Def_OpenGA_SurfaceArea
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section

open Bundle Matrix MeasureTheory Set Filter

open scoped Manifold ContDiff Topology

open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open OpenGA.RicciFlow

/-- An injective differentiable change of parameters preserves patch area.
The image map itself need not be injective: area is counted with multiplicity. -/
theorem solution
    (g : SmoothRiemannianMetric I M) (f : SurfaceParameter → M)
    {φ : SurfaceParameter → SurfaceParameter} {Ω : Set SurfaceParameter}
    (hΩ : MeasurableSet Ω) (hφ : ∀ u ∈ Ω, DifferentiableAt ℝ φ u)
    (hinj : Set.InjOn φ Ω)
    (hf : ∀ v ∈ φ '' Ω, MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I f v) :
    patchArea g (f ∘ φ) Ω = patchArea g f (φ '' Ω) := by
  unfold patchArea
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hΩ
    (fun u hu => (hφ u hu).hasFDerivAt.hasFDerivWithinAt) hinj]
  apply setIntegral_congr_fun hΩ
  intro u hu
  simpa only [LinearMap.det_toMatrix, smul_eq_mul] using
    surfaceDensity_comp g f (hφ u hu).hasFDerivAt (hf (φ u) ⟨u, hu, rfl⟩)
