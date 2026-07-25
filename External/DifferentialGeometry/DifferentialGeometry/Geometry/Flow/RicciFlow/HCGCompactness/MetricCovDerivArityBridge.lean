import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ProductMFoldNorm
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false





















noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M]





def acEquiv : (m : ℕ) → Fin (2 + m) ≃ Fin (m + 2)
  | 0 => Equiv.refl _
  | (m + 1) => Tensor0SBundle.frontExtendEquiv (acEquiv m)



omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivStep_eq_covStep
    [FiniteDimensional Real E]
    (gRef : SmoothRiemannianMetric I M) (a : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) gRef a A = covStep (I := I) gRef (a + 2) A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricCovDerivStep_apply, covStep_apply]




omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eq_iterCov
    [FiniteDimensional Real E]
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) (m : ℕ) :
    covDerivOfField (I := I) gRef A0 m =
      MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (∞ : WithTop ℕ∞) (acEquiv m)
        (iterCov (I := I) gRef 2 A0 m) := by
  induction m with
  | zero =>
      simp only [acEquiv]
      rfl
  | succ m ih =>
      rw [covDerivOfField_succ, ih, metricCovDerivStep_eq_covStep, covStep_domDomCongr,
        ← iterCov_succ]
      rfl





omit [Module.Finite ℝ E] [IsManifold I 1 M] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivNorm_eq_iterCov
    [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (h gRef : SmoothRiemannianMetric I M) (N : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    metricCovDerivNorm (I := I) N h gRef x =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) h) N x)) := by
  unfold metricCovDerivNorm
  rw [metricCovDeriv_eq_covDerivOfField, covDerivOfField_eq_iterCov]
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (N + 2)
      (ContinuousMultilinearMap.domDomCongr (acEquiv N)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) h) N x))) =
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
      (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) h) N x))
  rw [normSq0S_domDomCongr (I := I) gRef x basis hinv (acEquiv N)
      (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) h) N x)]







omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricDerivNorm_eq_iterCov
    [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gk gInf gRef : SmoothRiemannianMetric I M) (N : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    metricDerivNorm (I := I) N gk gInf gRef x =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
        (iterCov (I := I) gRef 2
          (Tensor0SBundle.metricTensorField (I := I) gk
            - Tensor0SBundle.metricTensorField (I := I) gInf) N x)) := by
  unfold metricDerivNorm metricDiffCovDerivAt
  have hsub : metricCovDeriv (I := I) gk gRef N x - metricCovDeriv (I := I) gInf gRef N x
      = covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) gk
            - Tensor0SBundle.metricTensorField (I := I) gInf) N x := by
    rw [covDerivOfField_sub, metricCovDeriv_eq_covDerivOfField (I := I) gk gRef N,
      metricCovDeriv_eq_covDerivOfField (I := I) gInf gRef N]
    rfl
  rw [hsub, covDerivOfField_eq_iterCov]
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (N + 2)
      (ContinuousMultilinearMap.domDomCongr (acEquiv N)
        (iterCov (I := I) gRef 2
          (Tensor0SBundle.metricTensorField (I := I) gk
            - Tensor0SBundle.metricTensorField (I := I) gInf) N x))) =
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
      (iterCov (I := I) gRef 2
        (Tensor0SBundle.metricTensorField (I := I) gk
          - Tensor0SBundle.metricTensorField (I := I) gInf) N x))
  rw [normSq0S_domDomCongr (I := I) gRef x basis hinv (acEquiv N)
      (iterCov (I := I) gRef 2
        (Tensor0SBundle.metricTensorField (I := I) gk
          - Tensor0SBundle.metricTensorField (I := I) gInf) N x)]



omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem diffNorm_zero_change
    [FiniteDimensional Real E]
    (A B gNorm gBase : SmoothRiemannianMetric I M) (x : M) {C : Real}
    (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * gBase.inner x v v ≤ gNorm.inner x v v ∧
        gNorm.inner x v v ≤ C * gBase.inner x v v) :
    metricDerivNorm (I := I) 0 A B gNorm x ≤
      Real.sqrt (C ^ 2) * metricDerivNorm (I := I) 0 A B gBase x := by
  unfold metricDerivNorm metricDiffCovDerivAt
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gNorm x 2
      (Tensor0SBundle.metricTensorField (I := I) A x -
        Tensor0SBundle.metricTensorField (I := I) B x)) ≤
    Real.sqrt (C ^ 2) *
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x 2
        (Tensor0SBundle.metricTensorField (I := I) A x -
          Tensor0SBundle.metricTensorField (I := I) B x))
  exact Tensor0SBundle.sqrt_normSq0S_le_of_metric_equiv
    (I := I) gBase gNorm x 2 hC hequiv _



omit [Module.Finite ℝ E] [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricDerivNorm_self
    [FiniteDimensional Real E]
    (a : Nat) (g gRef : SmoothRiemannianMetric I M) (x : M) :
    metricDerivNorm (I := I) a g g gRef x = 0 := by
  classical
  unfold metricDerivNorm
  have h0 : metricDiffCovDerivAt (I := I) a g g gRef x = 0 := sub_self _
  rw [h0]
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' i j
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x (a + 2) basis hinv 0]
  simp

end HCGCompactness
end DifferentialGeometry
