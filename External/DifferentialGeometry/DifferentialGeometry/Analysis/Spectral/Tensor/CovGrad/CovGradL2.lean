import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradMetricBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2Inner_covGrad_self_eq_dirichlet
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  change tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x))
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x)) =
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x
  exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s S S x).symm


omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_l2NormSq_le_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ^ 2 ≤ ‖S‖ ^ 2 := by
  have h_coe_norm :
      ‖((covGrad (I := I) (M := M) g r s S.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)‖ =
        ‖(covGrad (I := I) (M := M) g r s S.toCcTensor :
          SmoothCcTensor g r (s + 1))‖ :=
    UniformSpace.Completion.norm_coe _
  rw [h_coe_norm]
  rw [SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)
    (covGrad (I := I) (M := M) g r s S.toCcTensor)]
  rw [tensorL2Inner_covGrad_self_eq_dirichlet (I := I) (M := M) g r s S.toCcTensor]
  rw [SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S]
  rw [tensorH1Inner_def]
  have h_l2_nonneg :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
            S.toCcTensor.toFun S.toCcTensor.toFun :=
    tensorL2Inner_nonneg (I := I) (M := M) g r s S.toCcTensor.toFun
  linarith


omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_l2Norm_le_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ≤ ‖S‖ := by
  have h_sq := covGrad_l2NormSq_le_h1NormSq (I := I) (M := M) g r s S
  have h_rhs_nn : 0 ≤ ‖S‖ := norm_nonneg _
  exact (abs_le_of_sq_le_sq' h_sq h_rhs_nn).2


omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_l2Norm_le_one_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ≤ 1 * ‖S‖ := by
  rw [one_mul]
  exact covGrad_l2Norm_le_h1Norm (I := I) (M := M) g r s S

noncomputable def covGradL2Lin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] TensorL2 r (s + 1) g where
  toFun w :=
    ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
  map_add' w₁ w₂ := by
    change ((covGrad (I := I) (M := M) g r s (w₁ + w₂).toCcTensor :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) =
        ((covGrad (I := I) (M := M) g r s w₁.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) +
          ((covGrad (I := I) (M := M) g r s w₂.toCcTensor :
              SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
    rw [SmoothCcTensorH1.toCcTensor_add,
      covGrad_add (I := I) (M := M) g r s w₁.toCcTensor w₂.toCcTensor]
    exact UniformSpace.Completion.coe_add _ _
  map_smul' c w := by
    change ((covGrad (I := I) (M := M) g r s (c • w).toCcTensor :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) =
        c • ((covGrad (I := I) (M := M) g r s w.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
    rw [SmoothCcTensorH1.toCcTensor_smul,
      covGrad_smul (I := I) (M := M) g r s c w.toCcTensor]
    exact UniformSpace.Completion.coe_smul _ _

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covGradL2Lin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    covGradL2Lin (I := I) (M := M) g r s w =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := rfl


omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradL2Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    ‖covGradL2Lin (I := I) (M := M) g r s w‖ ≤ 1 * ‖w‖ := by
  rw [covGradL2Lin_apply]
  exact covGrad_l2Norm_le_one_mul_h1Norm (I := I) (M := M) g r s w

noncomputable def tensorCovGradL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r (s + 1) g :=
  (covGradL2Lin (I := I) (M := M) g r s).mkContinuous 1
    (fun w => covGradL2Lin_norm_le (I := I) (M := M) g r s w)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorCovGradL2_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2 (I := I) (M := M) g r s w =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

noncomputable def tensorCovGradL2Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorL2 r (s + 1) g :=
  ContinuousLinearMap.extend (tensorCovGradL2 (I := I) (M := M) g r s)
    (smoothToTensorH1Compl (I := I) (M := M) g r s)

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovGradL2Compl_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2Compl (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
      tensorCovGradL2 (I := I) (M := M) g r s w := by
  unfold tensorCovGradL2Compl
  exact ContinuousLinearMap.extend_eq
    (tensorCovGradL2 (I := I) (M := M) g r s)
    (e := smoothToTensorH1Compl (I := I) (M := M) g r s)
    (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s)
    (isUniformInducing_smoothToTensorH1Compl (I := I) (M := M) g r s) w

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2Compl (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := by
  rw [tensorCovGradL2Compl_smoothToTensorH1Compl (I := I) (M := M) g r s w,
    tensorCovGradL2_apply]


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovGradL2_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ‖tensorCovGradL2 (I := I) (M := M) g r s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le (covGradL2Lin (I := I) (M := M) g r s)
    zero_le_one (fun w => covGradL2Lin_norm_le (I := I) (M := M) g r s w)


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovGradL2Compl_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : TensorH1Compl g r s) :
    ‖tensorCovGradL2Compl (I := I) (M := M) g r s x‖ ≤ ‖x‖ := by
  have h_closed :
      IsClosed {y : TensorH1Compl g r s |
        ‖tensorCovGradL2Compl (I := I) (M := M) g r s y‖ ≤ ‖y‖} :=
    isClosed_le
      ((tensorCovGradL2Compl (I := I) (M := M) g r s).continuous.norm)
      continuous_norm
  have h_dense :
      ∀ w : SmoothCcTensorH1 g r s,
        ‖tensorCovGradL2Compl (I := I) (M := M) g r s
            (smoothToTensorH1Compl (I := I) (M := M) g r s w)‖ ≤
          ‖smoothToTensorH1Compl (I := I) (M := M) g r s w‖ := by
    intro w
    have h_rhs :
        ‖smoothToTensorH1Compl (I := I) (M := M) g r s w‖ = ‖w‖ := by
      rw [smoothToTensorH1Compl_apply, UniformSpace.Completion.norm_coe]
    have h_lhs :
        tensorCovGradL2Compl (I := I) (M := M) g r s
            (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
          ((covGrad (I := I) (M := M) g r s w.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) :=
      tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe (I := I) (M := M)
        g r s w
    rw [h_lhs, h_rhs]
    exact covGrad_l2Norm_le_h1Norm (I := I) (M := M) g r s w
  exact (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s).induction_on
    x h_closed h_dense


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovGradL2Compl_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ‖tensorCovGradL2Compl (I := I) (M := M) g r s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by
      rw [one_mul]
      exact tensorCovGradL2Compl_apply_norm_le (I := I) (M := M) g r s x)


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovGradL2_inner_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) (T : SmoothCcTensor g r (s + 1)) :
    ⟪tensorCovGradL2 (I := I) (M := M) g r s w, (T : TensorL2 r (s + 1) g)⟫_ℝ =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          ((covGrad (I := I) (M := M) g r s w.toCcTensor).toFun x)
          (T.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorCovGradL2_apply]
  rw [UniformSpace.Completion.inner_coe,
    SmoothCcTensor.inner_def
      (covGrad (I := I) (M := M) g r s w.toCcTensor) T]
  rfl

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example : SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r (s + 1) g :=
  tensorCovGradL2 (I := I) (M := M) g r s

example : TensorH1Compl g r s →L[ℝ] TensorL2 r (s + 1) g :=
  tensorCovGradL2Compl (I := I) (M := M) g r s

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
