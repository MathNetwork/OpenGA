import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FreeDirectionReduction


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def covGradRoughLapCurv
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 0 3 :=
  rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) -
    covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T₀)

theorem covGradRoughLap_commutator_eq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) =
      covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T₀)
        + covGradRoughLapCurv (I := I) (M := M) g T₀ := by
  rw [covGradRoughLapCurv]
  rw [add_comm]
  rw [sub_add_cancel]

noncomputable def fixedFrameSwapTraceUnit
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  (∑ i : Fin (Module.finrank ℝ E),
      (tensorCov (I := I) g 0 2).toFun
        (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => T₀.toSection y))) x
        (smoothExtensionTangent (I := I) x w x))
    (unitZeroSec (I := I) (M := M) x)

noncomputable def covGradRoughLapMovingFrameResidual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      tensorCovDerivAt (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
      (unitZeroSec (I := I) (M := M) x) -
    fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w

omit [CompactSpace M] in
lemma covGradRoughLapMovingFrameResidual_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
          (unitZeroSec (I := I) (M := M) x) -
        fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w := rfl

omit [CompactSpace M] in
theorem rhs_curry_eq_swap_add_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
        (unitZeroSec (I := I) (M := M) x) =
      fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w +
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  rw [covGradRoughLapMovingFrameResidual_def]
  rw [add_comm]
  rw [sub_add_cancel]

theorem covGrad_rawConnLap_curry_eq_swap_add_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w +
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w]
  exact rhs_curry_eq_swap_add_residual (I := I) (M := M) g T₀ x w

theorem frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      tensor0S_curry (I := I) (M := M) 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g 0 2
              (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  rw [frame_trace_third_eq_swap_unit (I := I) (M := M) g T₀ x w]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 2).toFun
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) =
        fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w from rfl]
  rw [show fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w =
        tensor0S_curry (I := I) (M := M) 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
              (covGrad (I := I) (M := M) g 0 2
                (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
              (unitZeroSec (I := I) (M := M) x)) w -
          covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w from by
      rw [covGrad_rawConnLap_curry_eq_swap_add_residual (I := I) (M := M) g T₀ x w]
      rw [add_sub_cancel_right]]

noncomputable def covGradRoughLapCurv_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s T₀) -
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s T₀)

lemma covGrad_rawConnLap_unit_eval_curry_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth g 0 s T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth g 0 s T₀) x w)
        (unitZeroSec (I := I) (M := M) x) :=
  curry_covGrad_unit_eval_general (I := I) (M := M) g s
    (rawTensorConnLapSmooth g 0 s T₀) x w

noncomputable def fixedFrameSwapTraceUnit_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace s I x :=
  (∑ i : Fin (Module.finrank ℝ E),
      (tensorCov (I := I) g 0 s).toFun
        (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => T₀.toSection y))) x
        (smoothExtensionTangent (I := I) x w x))
    (unitZeroSec (I := I) (M := M) x)

noncomputable def covGradRoughLapMovingFrameResidual_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace s I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s T₀) x w)
      (unitZeroSec (I := I) (M := M) x) -
    fixedFrameSwapTraceUnit_gen (I := I) (M := M) g s T₀ x w

omit [CompactSpace M] in
lemma covGradRoughLapMovingFrameResidual_gen_def
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s T₀ x w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T₀) x w)
          (unitZeroSec (I := I) (M := M) x) -
        fixedFrameSwapTraceUnit_gen (I := I) (M := M) g s T₀ x w := rfl

omit [CompactSpace M] in
theorem rhs_curry_eq_swap_add_residual_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s T₀) x w)
        (unitZeroSec (I := I) (M := M) x) =
      fixedFrameSwapTraceUnit_gen (I := I) (M := M) g s T₀ x w +
        covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s T₀ x w := by
  rw [covGradRoughLapMovingFrameResidual_gen_def]
  rw [add_comm]
  rw [sub_add_cancel]

theorem covGrad_rawConnLap_curry_eq_swap_add_residual_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth g 0 s T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      fixedFrameSwapTraceUnit_gen (I := I) (M := M) g s T₀ x w +
        covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s T₀ x w := by
  rw [covGrad_rawConnLap_unit_eval_curry_gen (I := I) (M := M) g s T₀ x w]
  exact rhs_curry_eq_swap_add_residual_gen (I := I) (M := M) g s T₀ x w

omit [CompactSpace M] [I.Boundaryless] in
lemma frame_trace_third_eq_swap_unit_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 s)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  have hT₀ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b (T₀.toSection b)) :=
    T₀.toSection.contMDiff
  have hswap := frame_trace_thirdCovDeriv_swap (I := I) g 0 s
    (W := smoothExtensionTangent (I := I) x w) (T := fun y : M => T₀.toSection y) (x := x)
    hW hT₀
  have happ := congrArg
    (fun (φ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) =>
      φ (unitZeroSec (I := I) (M := M) x)) hswap
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply] using happ

theorem frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 s)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth g 0 s T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  rw [frame_trace_third_eq_swap_unit_gen (I := I) (M := M) g s T₀ x w]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) =
        fixedFrameSwapTraceUnit_gen (I := I) (M := M) g s T₀ x w from rfl]
  rw [show fixedFrameSwapTraceUnit_gen (I := I) (M := M) g s T₀ x w =
        tensor0S_curry (I := I) (M := M) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (covGrad (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth g 0 s T₀)).toSection x)
              (unitZeroSec (I := I) (M := M) x)) w -
          covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s T₀ x w from by
      rw [covGrad_rawConnLap_curry_eq_swap_add_residual_gen (I := I) (M := M) g s T₀ x w]
      rw [add_sub_cancel_right]]

end Connection
end Integral
end DifferentialGeometry

end
