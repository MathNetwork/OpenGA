import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion
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

abbrev TensorH1Compl (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  UniformSpace.Completion (SmoothCcTensorH1 g r s)

noncomputable def smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s :=
  UniformSpace.Completion.toComplL

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothToTensorH1Compl_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothToTensorH1Compl (I := I) (M := M) g r s S =
      (S : TensorH1Compl g r s) :=
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma SmoothCcTensor.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    ‖S‖ ^ 2 = tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
  have h := real_inner_self_eq_norm_sq S
  rw [SmoothCcTensor.inner_def] at h
  exact h.symm


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma SmoothCcTensorH1.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S‖ ^ 2 =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor := by
  have h := real_inner_self_eq_norm_sq S
  rw [SmoothCcTensorH1.inner_def] at h
  exact h.symm


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma SmoothCcTensorH1.l2NormSq_le_h1NormSq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ^ 2 ≤ ‖S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M) S.toCcTensor,
    SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S,
    tensorH1Inner_def]
  have h_grad_nonneg :
      0 ≤ ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
              S.toCcTensor S.toCcTensor x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s
      S.toCcTensor x
  linarith


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma SmoothCcTensorH1.l2Norm_le_h1Norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ≤ ‖S‖ := by
  have h_sq := SmoothCcTensorH1.l2NormSq_le_h1NormSq (I := I) (M := M) S
  have h_rhs_nn : 0 ≤ ‖S‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ≤ 1 * ‖S‖ := by
  rw [one_mul]; exact SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S

noncomputable def smoothCcTensorH1ToTensorL2Lin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] TensorL2 r s g where
  toFun S := (S.toCcTensor : TensorL2 r s g)
  map_add' S T := by
    change ((S + T).toCcTensor : TensorL2 r s g) =
      (S.toCcTensor : TensorL2 r s g) + (T.toCcTensor : TensorL2 r s g)
    rw [SmoothCcTensorH1.toCcTensor_add]
    exact UniformSpace.Completion.coe_add _ _
  map_smul' c S := by
    change ((c • S).toCcTensor : TensorL2 r s g) =
      c • (S.toCcTensor : TensorL2 r s g)
    rw [SmoothCcTensorH1.toCcTensor_smul]
    exact UniformSpace.Completion.coe_smul _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma smoothCcTensorH1ToTensorL2Lin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S =
      (S.toCcTensor : TensorL2 r s g) := rfl


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma smoothCcTensorH1ToTensorL2Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S‖ ≤ 1 * ‖S‖ := by
  have h_coe_norm :
      ‖(S.toCcTensor : TensorL2 r s g)‖ = ‖S.toCcTensor‖ :=
    UniformSpace.Completion.norm_coe _
  calc ‖smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S‖
      = ‖(S.toCcTensor : TensorL2 r s g)‖ := rfl
    _ = ‖S.toCcTensor‖ := h_coe_norm
    _ ≤ 1 * ‖S‖ :=
      SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm (I := I) (M := M) S

noncomputable def smoothCcTensorH1ToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r s g :=
  (smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s).mkContinuous 1
    (fun S => smoothCcTensorH1ToTensorL2Lin_norm_le (I := I) (M := M) g r s S)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothCcTensorH1ToTensorL2_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s S =
      (S.toCcTensor : TensorL2 r s g) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_toComplL_smoothCcTensorH1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange
      (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s) := by
  rw [show (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_toComplL_smoothCcTensorH1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s) := by
  rw [show (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

noncomputable def TensorH1ComplToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorL2 r s g :=
  ContinuousLinearMap.extend (smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s)
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma TensorH1ComplToTensorL2_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s S := by
  unfold TensorH1ComplToTensorL2
  exact ContinuousLinearMap.extend_eq
    (smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothCcTensorH1 (I := I) (M := M) g r s)
    (isUniformInducing_toComplL_smoothCcTensorH1 (I := I) (M := M) g r s) S

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      (S.toCcTensor : TensorL2 r s g) := by
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl,
    smoothCcTensorH1ToTensorL2_apply]

section InstanceTests

example (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ := TensorH1Compl g r s

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    NormedAddCommGroup (TensorH1Compl g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (TensorH1Compl g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    CompleteSpace (TensorH1Compl g r s) := inferInstance

end InstanceTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
