import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapSecondGradientL2Bound


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
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


theorem rawConnLap_three_l2Inner_covGrad_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3)
    (hcomm :
      rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T) =
        covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T)
          + Curv) :
    tensorL2Inner (I := I) (M := M) g 0 3
        (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T)).toFun
        (covGrad (I := I) (M := M) g 0 2 T).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun ^ 2 +
        tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun
          (covGrad (I := I) (M := M) g 0 2 T).toFun := by
  classical
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T with hS_def
  set GΔ : SmoothCcTensor g 0 3 :=
    covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T) with hGΔ_def
  rw [hcomm]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 3 GΔ.toFun Curv.toFun S.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Curv S)]
  rw [hGΔ_def, hS_def]
  rw [covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq (I := I) (M := M) g T]


theorem secondCovGrad_l2NormSq_le_rawConnLap_add_self
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hcomm :
      rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T) =
        covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T)
          + Curv)
    (hcurv :
      tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun ≤
        C₀ * tensorL2Norm (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T).toFun) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T)).toFun ^ 2 ≤
      (1 + C₀ / 2) *
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 2 T.toFun ^ 2) := by
  classical
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T with hS_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 S.toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g 0 2 T.toFun with hnT_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun with hnCurv_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 3
            (rawTensorConnLapSmooth (I := I) g 0 3 S).toFun S.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (3 + 1)
      (covGrad (I := I) (M := M) g 0 3 S)]
    rw [hS_def]
    exact covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner (I := I) (M := M) g T
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3 S).toFun S.toFun =
        - nLap ^ 2 +
          tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun := by
    rw [hS_def, hnLap_def]
    exact rawConnLap_three_l2Inner_covGrad_eq (I := I) (M := M) g T Curv hcomm
  have hcombined :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 =
        nLap ^ 2 - tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun := by
    rw [hgreen, hsplit]; ring
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 3 Curv.toFun S.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) Curv)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Curv S)
  have hcross_le :
      - tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun ≤ nCurv * nGrad := by
    rw [hnCurv_def, hnGrad_def]
    exact le_trans (neg_le_abs _) hcs
  have hcurv' : nCurv ≤ C₀ * nGrad := by rw [hnCurv_def, hnGrad_def]; exact hcurv
  have hgrad_sq_nn : 0 ≤ nGrad := hnGrad_nn
  have hstep1 :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 ≤
        nLap ^ 2 + C₀ * nGrad ^ 2 := by
    rw [hcombined]
    have : nCurv * nGrad ≤ C₀ * nGrad * nGrad :=
      mul_le_mul_of_nonneg_right hcurv' hnGrad_nn
    nlinarith [hcross_le, this]
  have horder1 : nGrad ^ 2 ≤ nLap * nT := by
    rw [hnGrad_def, hS_def, hnLap_def, hnT_def]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  have hyoung : nLap * nT ≤ (nLap ^ 2 + nT ^ 2) / 2 := by nlinarith [sq_nonneg (nLap - nT)]
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
    (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 with hnHess_def
  have hstep1' : nHess ≤ nLap ^ 2 + C₀ * nGrad ^ 2 := hstep1
  have hgrad_le : C₀ * nGrad ^ 2 ≤ C₀ * ((nLap ^ 2 + nT ^ 2) / 2) := by
    have h1 : C₀ * nGrad ^ 2 ≤ C₀ * (nLap * nT) := by nlinarith [horder1, hC₀]
    have h2 : C₀ * (nLap * nT) ≤ C₀ * ((nLap ^ 2 + nT ^ 2) / 2) := by nlinarith [hyoung, hC₀]
    linarith [h1, h2]
  nlinarith [hstep1', hgrad_le, sq_nonneg nT, hC₀]

end Connection
end Integral
end DifferentialGeometry

end
