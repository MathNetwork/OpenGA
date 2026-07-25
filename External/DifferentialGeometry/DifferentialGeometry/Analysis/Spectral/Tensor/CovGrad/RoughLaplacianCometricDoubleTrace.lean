import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_toModel_unitEval
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g₀ 0 s) (x : M)
    (v : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s W x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) v := rfl


private lemma secondCovDeriv_frame_unitEval_eq_iteratedCovGrad
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => S.toSection z) x)
          (unitZeroSec (I := I) (M := M) x)) v =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x)) v)) := by
  have hiter : iteratedCovGrad (I := I) g₀ 0 2 2 S =
      covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 S) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hbridge := tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
    (I := I) (M := M) g₀ 2 S
    (X := smoothOrthoFrame (I := I) g₀ x i)
    (Y := smoothOrthoFrame (I := I) g₀ x i)
    (smoothOrthoFrame_smooth (I := I) g₀ x i) (smoothOrthoFrame_smooth (I := I) g₀ x i) x v
  rw [unitModel_eq_toModel_unitEval, hiter]
  exact hbridge.symm


private lemma unitModel_rawTensorConnLapSmooth_eq_frame_sum
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v =
      ∑ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x)) v)) := by
  classical
  rw [unitModel_eq_toModel_unitEval]
  have hsec : (rawTensorConnLapSmooth (I := I) g₀ 0 2 S).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => S.toSection z) x) := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) g₀ 0 2 S x,
      rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g₀ 0 2
        (fun z : M => S.toSection z) x]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2
            (smoothOrthoFrame (I := I) g₀ x i) (smoothOrthoFrame (I := I) g₀ x i)
            (fun z : M => S.toSection z) x)
          (unitZeroSec (I := I) (M := M) x) from by
    rw [hsec, ContinuousLinearMap.sum_apply]]
  rw [← Tensor0SSpace.toModelL_apply (s := 2) (x := x),
    map_sum (Tensor0SSpace.toModelL 2 x)]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  exact secondCovDeriv_frame_unitEval_eq_iteratedCovGrad (I := I) g₀ S x v i


theorem rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v := by
  classical
  rw [ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian (I := I) (M := M) g₀ g₀
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v]
  rw [unitModel_rawTensorConnLapSmooth_eq_frame_sum (I := I) g₀ S x v]
  exact (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometric_dualTrace_eq_orthoFrame_diag
    (I := I) g₀ (s := 2) x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x) v).symm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
