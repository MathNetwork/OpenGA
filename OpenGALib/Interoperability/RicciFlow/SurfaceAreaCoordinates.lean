import OpenGALib.Interoperability.RicciFlow.SurfaceArea
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of parameters for surface area density

The transformation law uses the actual derivative of a change of parameters.
It permits orientation reversal and degenerate derivatives; it does not require
a global frame on the image surface. This is the pointwise compatibility needed
before gluing local area integrals over overlapping charts.
-/

noncomputable section

open Bundle Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry

namespace OpenGA.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The induced metric transforms by congruence with the parameter derivative. -/
theorem surfaceMetricMatrix_comp
    (g : SmoothRiemannianMetric I M) (f : SurfaceParameter → M)
    {φ : SurfaceParameter → SurfaceParameter} {u : SurfaceParameter}
    {A : SurfaceParameter →L[ℝ] SurfaceParameter} (hφ : HasFDerivAt φ A u)
    (hf : MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I f (φ u)) :
    surfaceMetricMatrix g (f ∘ φ) u =
      (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearMap).transpose *
      surfaceMetricMatrix g f (φ u) *
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearMap := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let B := LinearMap.toMatrix b b A.toLinearMap
  have ht (i : Fin 2) : surfaceTangent (I := I) (f ∘ φ) u i =
      ∑ k, B k i • surfaceTangent (I := I) f (φ u) k := by
    unfold surfaceTangent
    rw [mfderiv_comp u hf hφ.hasMFDerivAt.mdifferentiableAt,
      hφ.hasMFDerivAt.mfderiv]
    change mfderiv 𝓘(ℝ, SurfaceParameter) I f (φ u) (A (b i)) = _
    let df : SurfaceParameter →L[ℝ] TangentSpace I (f (φ u)) :=
      mfderiv 𝓘(ℝ, SurfaceParameter) I f (φ u)
    have hs := congrArg df (b.sum_repr (A (b i)))
    simpa only [map_sum, map_smul, B, b, df, LinearMap.toMatrix_apply] using! hs.symm
  ext i j
  dsimp only [surfaceMetricMatrix]
  rw [ht i, ht j]
  simp only [map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Fin.sum_univ_two, surfaceMetricMatrix]
  dsimp only [B, b, Function.comp_apply]
  ring

/-- Area density transforms by the absolute Jacobian of the parameter map. -/
theorem surfaceDensity_comp
    (g : SmoothRiemannianMetric I M) (f : SurfaceParameter → M)
    {φ : SurfaceParameter → SurfaceParameter} {u : SurfaceParameter}
    {A : SurfaceParameter →L[ℝ] SurfaceParameter} (hφ : HasFDerivAt φ A u)
    (hf : MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I f (φ u)) :
    surfaceDensity g (f ∘ φ) u =
      |(LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearMap).det| *
      surfaceDensity g f (φ u) := by
  unfold surfaceDensity
  rw [surfaceMetricMatrix_comp g f hφ hf, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  rw [show ∀ a b : ℝ, a * b * a = a ^ 2 * b by intros; ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- An injective differentiable change of parameters preserves patch area.
The image map itself need not be injective: area is counted with multiplicity. -/
theorem patchArea_comp
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

end OpenGA.RicciFlow
