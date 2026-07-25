import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameBracketFold
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldContractionBound
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_genuineCurvPureRSection_l2Norm_le_covGrad
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖genuineCurvatureOnlySection (I := I) (M := M) g s S‖ ≤
        Cr * ‖covGrad (I := I) (M := M) g 0 s S‖ := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_pureRGenuineDiffOp (I := I) (M := M) g
  refine ⟨Real.sqrt (kappa 0 (s + 1)), Real.sqrt_nonneg _, fun S => ?_⟩
  have hsec : genuineCurvatureOnlySection (I := I) (M := M) g s S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) :=
    (pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S).symm

  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x) ≤
        (Real.sqrt (kappa 0 (s + 1))) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
    intro x
    rw [Real.sq_sqrt (hkappa_nn 0 (s + 1)), hsec]
    have h := hkappa 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) x
    rw [Finset.sum_range_one,
      DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero] at h
    exact h

  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 s S) (0 : SmoothCcTensor g 0 (s + 1))
    (genuineCurvatureOnlySection (I := I) (M := M) g s S) (Real.sqrt (kappa 0 (s + 1))) (Real.sqrt_nonneg _)
    (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((0 : SmoothCcTensor g 0 (s + 1)).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 (s + 1) x
    rw [hz, add_zero]; exact hpt x

theorem exists_genuineDiffCurvSection_l2Norm_le_self
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖genuineDiffCurvSection (I := I) (M := M) g s S‖ ≤ Cd * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g
    (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun S => ?_⟩
  have hsec : genuineDiffCurvSection (I := I) (M := M) g s S =
      operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S := rfl
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x) ≤
        (Real.sqrt C) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
    intro x
    rw [Real.sq_sqrt hC_nn, hsec]
    exact hC S x
  have hbound := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    S (0 : SmoothCcTensor g 0 s)
    (genuineDiffCurvSection (I := I) (M := M) g s S) (Real.sqrt C) (Real.sqrt_nonneg _)
    (fun x => ?_)
  · rw [norm_zero, add_zero] at hbound; exact hbound
  · have hz : riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((0 : SmoothCcTensor g 0 s).toSection x) = 0 := by
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g 0 s x
    rw [hz, add_zero]; exact hpt x

theorem exists_ricTraceSection_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cric : ℝ, 0 ≤ Cric ∧ ∀ S : SmoothCcTensor g 0 s,
      ‖ricTraceSection (I := I) (M := M) g s S‖ ≤
        Cric * (‖covGrad (I := I) (M := M) g 0 s S‖ + ‖S‖) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_ricTraceSection_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨C s, hC_nn s, fun S => ?_⟩
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 s S) S
    (ricTraceSection (I := I) (M := M) g s S) (C s) (hC_nn s)
    (fun x => hC s S x)

theorem exists_integrated_curvatureCrossBound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ S : SmoothCcTensor g 0 s,
        - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S) -
                covGrad (I := I) (M := M) g 0 s
                  (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun ≤
          Ccross *
            (tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 s S.toFun *
                tensorL2Norm (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S).toFun) := by
  classical
  obtain ⟨K_R, K_dR, hK_R_nn, hK_dR_nn, hfibre⟩ :=
    exists_pointwiseTensorCurv_fiberNormSq_bound (I := I) (M := M) g s

  set C : ℝ := Real.sqrt 2 * max K_R K_dR with hC_def
  have hmax_nn : 0 ≤ max K_R K_dR := le_max_of_le_left hK_R_nn
  have hC_nn : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hmax_nn
  refine ⟨C, hC_nn, fun S => ?_⟩
  set gradS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hgradS_def

  have hCurvFun : (pointwiseTensorCurv (I := I) (M := M) g s S).toFun =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S) -
        covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun := rfl

  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
        C ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
    intro x
    set rC : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) with hrC_def
    set rG : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hrG_def
    set rS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hrS_def
    have hrC_nn : 0 ≤ rC := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hrG_nn : 0 ≤ rG := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
    have hrS_nn : 0 ≤ rS := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _
    have hsqrtC : Real.sqrt rC ≤ K_R * Real.sqrt rG + K_dR * Real.sqrt rS := hfibre S x

    have hsqrtC' : Real.sqrt rC ≤ max K_R K_dR * (Real.sqrt rG + Real.sqrt rS) := by
      refine le_trans hsqrtC ?_
      have h1 : K_R * Real.sqrt rG ≤ max K_R K_dR * Real.sqrt rG :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      have h2 : K_dR * Real.sqrt rS ≤ max K_R K_dR * Real.sqrt rS :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
      nlinarith [h1, h2]
    have hrC_eq : rC = Real.sqrt rC ^ 2 := (Real.sq_sqrt hrC_nn).symm
    have hrG_eq : rG = Real.sqrt rG ^ 2 := (Real.sq_sqrt hrG_nn).symm
    have hrS_eq : rS = Real.sqrt rS ^ 2 := (Real.sq_sqrt hrS_nn).symm
    have hC_sq : C ^ 2 = 2 * max K_R K_dR ^ 2 := by
      rw [hC_def, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hC_sq, hrC_eq, hrG_eq, hrS_eq]
    have hsqrtrC_nn : 0 ≤ Real.sqrt rC := Real.sqrt_nonneg _
    have hsum_nn : 0 ≤ max K_R K_dR * (Real.sqrt rG + Real.sqrt rS) :=
      mul_nonneg hmax_nn (by positivity)
    nlinarith [hsqrtC', sq_nonneg (Real.sqrt rG - Real.sqrt rS),
      mul_nonneg hmax_nn hmax_nn, Real.sqrt_nonneg rG, Real.sqrt_nonneg rS,
      mul_le_mul hsqrtC' hsqrtC' hsqrtrC_nn hsum_nn]

  have hL2 : ‖pointwiseTensorCurv (I := I) (M := M) g s S‖ ≤
      C * (‖covGrad (I := I) (M := M) g 0 s S‖ + ‖S‖) :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 s S) S
      (pointwiseTensorCurv (I := I) (M := M) g s S) C hC_nn hpt

  rw [SmoothCcTensor.norm_def (I := I) (M := M) (pointwiseTensorCurv (I := I) (M := M) g s S),
    SmoothCcTensor.norm_def (I := I) (M := M) (covGrad (I := I) (M := M) g 0 s S),
    SmoothCcTensor.norm_def (I := I) (M := M) S] at hL2

  have hcs : |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun| ≤
      tensorL2Norm (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun *
        tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun :=
    abs_tensorL2Inner_le (I := I) (M := M) g 0 (s + 1)
      (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) (pointwiseTensorCurv (I := I) (M := M) g s S))
      (SmoothCcTensor.memL2_toFun (I := I) (M := M) gradS)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (pointwiseTensorCurv (I := I) (M := M) g s S) gradS)

  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1) gradS.toFun with hnGrad_def
  set nS : ℝ := tensorL2Norm (I := I) (M := M) g 0 s S.toFun with hnS_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1)
    (pointwiseTensorCurv (I := I) (M := M) g s S).toFun with hnCurv_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  have hnS_nn : 0 ≤ nS := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _

  have hval_eq :
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S) -
          covGrad (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun := by
    rw [← hgradS_def, ← hCurvFun]
  rw [hval_eq]

  have hneg_le : - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun ≤
      |tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun| := neg_le_abs _
  have hstep1 : - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun ≤
      nCurv * nGrad :=
    le_trans hneg_le hcs
  calc - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun gradS.toFun
      ≤ nCurv * nGrad := hstep1
    _ ≤ (C * (nGrad + nS)) * nGrad := mul_le_mul_of_nonneg_right hL2 hnGrad_nn
    _ = C * (nGrad ^ 2 + nS * nGrad) := by ring

end Connection
end Integral
end DifferentialGeometry

end
