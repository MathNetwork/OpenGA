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

namespace OpenGA.RicciFlow

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

end OpenGA.RicciFlow

/-- Area density transforms by the absolute Jacobian of the parameter map. -/
theorem OpenGA.RicciFlow.surfaceDensity_comp
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
