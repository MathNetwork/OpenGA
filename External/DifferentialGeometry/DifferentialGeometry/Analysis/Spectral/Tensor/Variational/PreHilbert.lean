import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivSupport
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.Continuity
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Operator.Gradient
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn


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
open DifferentialGeometry.Integral.DivergenceTheorem
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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorH1Inner_symm (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s S T =
      tensorH1Inner (I := I) (M := M) g r s T S := by
  unfold tensorH1Inner
  congr 1
  · exact tensorL2Inner_symm (I := I) (M := M) g r s S.toFun T.toFun
  · refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact tensorCovDerivPointwiseInner_symm (I := I) (M := M) g r s S T x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorH1Inner_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    0 ≤ tensorH1Inner (I := I) (M := M) g r s S S := by
  unfold tensorH1Inner
  refine add_nonneg ?_ ?_
  · exact tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun
  · refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s S x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorH1Inner_add_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (S₁ + S₂) T =
      tensorH1Inner (I := I) (M := M) g r s S₁ T +
        tensorH1Inner (I := I) (M := M) g r s S₂ T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂).toFun T.toFun =
        tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun +
          tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun S₂.toFun T.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (S₁ + S₂) T x) =
      (fun x : M => tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S₁ T x +
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₂ T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_add_left
      (I := I) (M := M) g r s S₁ S₂ T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_add
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₁ T)
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₂ T)]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorH1Inner_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (c • S) T =
      c * tensorH1Inner (I := I) (M := M) g r s S T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (c • S).toFun T.toFun =
        c * tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_smul]
    exact tensorL2Inner_smul_left (I := I) (M := M) g r s c S.toFun T.toFun
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (c • S) T x) =
      (fun x : M => c * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_smul_left
      (I := I) (M := M) g r s c S T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_const_mul]
  ring

structure SmoothCcTensorH1 (g : SmoothRiemannianMetric I M) (r s : ℕ) where

  toCcTensor : SmoothCcTensor g r s

namespace SmoothCcTensorH1

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[ext] theorem ext {S T : SmoothCcTensorH1 g r s}
    (h : S.toCcTensor = T.toCcTensor) : S = T := by
  cases S; cases T; congr

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma toCcTensor_injective :
    Function.Injective (fun S : SmoothCcTensorH1 g r s => S.toCcTensor) := by
  intro S T h
  exact ext h

instance : Zero (SmoothCcTensorH1 g r s) := ⟨⟨0⟩⟩
instance : Add (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor + T.toCcTensor⟩⟩
instance : Neg (SmoothCcTensorH1 g r s) := ⟨fun S => ⟨-S.toCcTensor⟩⟩
instance : Sub (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor - T.toCcTensor⟩⟩
instance : SMul ℝ (SmoothCcTensorH1 g r s) :=
  ⟨fun c S => ⟨c • S.toCcTensor⟩⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_zero :
    (0 : SmoothCcTensorH1 g r s).toCcTensor = 0 := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_add (S T : SmoothCcTensorH1 g r s) :
    (S + T).toCcTensor = S.toCcTensor + T.toCcTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_neg (S : SmoothCcTensorH1 g r s) :
    (-S).toCcTensor = -S.toCcTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_sub (S T : SmoothCcTensorH1 g r s) :
    (S - T).toCcTensor = S.toCcTensor - T.toCcTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_smul (c : ℝ) (S : SmoothCcTensorH1 g r s) :
    (c • S).toCcTensor = c • S.toCcTensor := rfl

instance : SMul ℕ (SmoothCcTensorH1 g r s) := ⟨nsmulRec⟩
instance : SMul ℤ (SmoothCcTensorH1 g r s) := ⟨zsmulRec⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_nsmul (S : SmoothCcTensorH1 g r s) (n : ℕ) :
    (n • S).toCcTensor = n • S.toCcTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toCcTensor = (0 : ℕ) • S.toCcTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toCcTensor = (n + 1) • S.toCcTensor
      change (nsmulRec n S + S).toCcTensor = (n + 1) • S.toCcTensor
      have hn : (nsmulRec n S).toCcTensor = n • S.toCcTensor := ih
      rw [toCcTensor_add, hn, succ_nsmul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_zsmul (S : SmoothCcTensorH1 g r s) (z : ℤ) :
    (z • S).toCcTensor = z • S.toCcTensor := by
  rcases z with n | n
  · change (n • S).toCcTensor = (Int.ofNat n) • S.toCcTensor
    rw [toCcTensor_nsmul]; simp
  · change (-((n + 1) • S)).toCcTensor = (Int.negSucc n) • S.toCcTensor
    rw [toCcTensor_neg, toCcTensor_nsmul]
    show -((n + 1) • S.toCcTensor) = Int.negSucc n • S.toCcTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.addCommGroup
    (fun S => S.toCcTensor)
    toCcTensor_zero
    toCcTensor_add
    toCcTensor_neg
    toCcTensor_sub
    toCcTensor_nsmul
    toCcTensor_zsmul

def toCcTensorAddHom : SmoothCcTensorH1 g r s →+ SmoothCcTensor g r s where
  toFun := fun S => S.toCcTensor
  map_zero' := toCcTensor_zero
  map_add' := toCcTensor_add

instance : Module ℝ (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.module ℝ toCcTensorAddHom toCcTensor_smul

end SmoothCcTensorH1


noncomputable instance instPreInnerProductSpaceCore
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    PreInnerProductSpace.Core ℝ (SmoothCcTensorH1 g r s) where
  inner S T := tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
  conj_inner_symm S T := by
    change (tensorH1Inner (I := I) (M := M) g r s T.toCcTensor S.toCcTensor : ℝ) =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    exact tensorH1Inner_symm (I := I) (M := M) g r s T.toCcTensor S.toCcTensor
  re_inner_nonneg S := by
    change (0 : ℝ) ≤ tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor
    exact tensorH1Inner_nonneg (I := I) (M := M) g r s S.toCcTensor
  add_left S₁ S₂ T := by
    change tensorH1Inner (I := I) (M := M) g r s
        (S₁ + S₂).toCcTensor T.toCcTensor =
      tensorH1Inner (I := I) (M := M) g r s S₁.toCcTensor T.toCcTensor +
        tensorH1Inner (I := I) (M := M) g r s S₂.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_add]
    exact tensorH1Inner_add_left (I := I) (M := M) g r s
      S₁.toCcTensor S₂.toCcTensor T.toCcTensor
  smul_left S T c := by
    change tensorH1Inner (I := I) (M := M) g r s
        (c • S).toCcTensor T.toCcTensor =
      c * tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_smul]
    exact tensorH1Inner_smul_left (I := I) (M := M) g r s
      c S.toCcTensor T.toCcTensor


noncomputable instance instSeminormedAddCommGroup
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)


noncomputable instance instInnerProductSpace
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.ofCore _


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem SmoothCcTensorH1.inner_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensorH1 g r s) :
    ⟪S, T⟫_ℝ =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor := rfl


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem SmoothCcTensorH1.norm_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S‖ = Real.sqrt (tensorH1Inner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor) := rfl

section InstanceTests

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) := inferInstance

end InstanceTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
