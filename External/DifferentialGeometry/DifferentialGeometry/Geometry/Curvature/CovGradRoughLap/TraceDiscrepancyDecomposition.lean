import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.Slot0FrameTraceMatching

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

noncomputable def covGradRoughLapTraceDiscrepancy
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  tensor0S_curry (I := I) (M := M) 2 x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) w -
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
      (unitZeroSec (I := I) (M := M) x)

lemma covGradRoughLapTraceDiscrepancy_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapTraceDiscrepancy (I := I) (M := M) g T₀ x w =
      tensor0S_curry (I := I) (M := M) 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (rawTensorConnLapSmooth (I := I) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        (∑ i : Fin (Module.finrank ℝ E),
            (tensorCov (I := I) g 0 2).toFun
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (covApply (tensorCov (I := I) g 0 2)
                  (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
              (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) := rfl

theorem covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      covGradRoughLapTraceDiscrepancy (I := I) (M := M) g T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  have hdef : (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x := by
    rw [covGradRoughLapCurv, SmoothCcTensor.toSection_sub]; rfl
  rw [hdef]
  rw [ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w]
  have hswap := frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv
    (I := I) (M := M) g T₀ x w
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w] at hswap
  rw [covGradRoughLapTraceDiscrepancy_def (I := I) (M := M) g T₀ x w]
  rw [hswap]
  abel

noncomputable def covGradRoughLapTraceDiscrepancy_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace s I x :=
  tensor0S_curry (I := I) (M := M) s x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T₀)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) w -
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 s)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
      (unitZeroSec (I := I) (M := M) x)

lemma covGradRoughLapTraceDiscrepancy_gen_def
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapTraceDiscrepancy_gen (I := I) (M := M) g s T₀ x w =
      tensor0S_curry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        (∑ i : Fin (Module.finrank ℝ E),
            (tensorCov (I := I) g 0 s).toFun
              (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                (covApply (tensorCov (I := I) g 0 s)
                  (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
              (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) := rfl

theorem covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGradRoughLapCurv_gen (I := I) (M := M) g s T₀).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      covGradRoughLapTraceDiscrepancy_gen (I := I) (M := M) g s T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        covGradRoughLapMovingFrameResidual_gen (I := I) (M := M) g s T₀ x w := by
  have hdef : (covGradRoughLapCurv_gen (I := I) (M := M) g s T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s T₀)).toSection x := by
    rw [covGradRoughLapCurv_gen, SmoothCcTensor.toSection_sub]; rfl
  rw [hdef]
  rw [ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
  rw [covGrad_rawConnLap_unit_eval_curry_gen (I := I) (M := M) g s T₀ x w]
  have hswap := frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv_gen
    (I := I) (M := M) g s T₀ x w
  rw [covGrad_rawConnLap_unit_eval_curry_gen (I := I) (M := M) g s T₀ x w] at hswap
  rw [covGradRoughLapTraceDiscrepancy_gen_def (I := I) (M := M) g s T₀ x w]
  rw [hswap]
  abel

end Connection
end Integral
end DifferentialGeometry

end
