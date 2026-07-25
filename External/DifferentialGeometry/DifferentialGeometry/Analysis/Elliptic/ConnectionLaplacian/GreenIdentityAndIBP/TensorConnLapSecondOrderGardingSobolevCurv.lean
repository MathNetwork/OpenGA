import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapSecondOrderGardingL2Bound


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


theorem secondCovGrad_l2NormSq_le_rawConnLap_gen
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hcomm :
      rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T) =
        covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T)
          + Curv)
    (hcurv :
      tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun ≤
        C₀ * (tensorL2Norm (I := I) (M := M) g 0 2 T.toFun +
          tensorL2Norm (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T).toFun +
          tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
            (covGrad (I := I) (M := M) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T)).toFun)) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T)).toFun ^ 2 ≤
      (2 + 3 * C₀ + 2 * C₀ ^ 2) *
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
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
    (covGrad (I := I) (M := M) g 0 3 S).toFun with hnHess_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnCurv_nn : 0 ≤ nCurv := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (3 + 1) _
  have hgreen :
      nHess ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 3
            (rawTensorConnLapSmooth (I := I) g 0 3 S).toFun S.toFun := by
    rw [hnHess_def]
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
      nHess ^ 2 =
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
  have hcurv' : nCurv ≤ C₀ * (nT + nGrad + nHess) := by
    rw [hnCurv_def, hnT_def, hnGrad_def, hnHess_def, hS_def]
    exact hcurv
  have hstep1 :
      nHess ^ 2 ≤ nLap ^ 2 + C₀ * (nT + nGrad + nHess) * nGrad := by
    rw [hcombined]
    have hprod : nCurv * nGrad ≤ C₀ * (nT + nGrad + nHess) * nGrad :=
      mul_le_mul_of_nonneg_right hcurv' hnGrad_nn
    linarith [hcross_le, hprod]
  have horder1 : nGrad ^ 2 ≤ nLap * nT := by
    rw [hnGrad_def, hS_def, hnLap_def, hnT_def]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  clear_value nGrad nLap nT nCurv nHess
  have hgrad_sq_le : nGrad ^ 2 ≤ (nLap ^ 2 + nT ^ 2) / 2 := by
    have hy : nLap * nT ≤ (nLap ^ 2 + nT ^ 2) / 2 := by nlinarith [sq_nonneg (nLap - nT)]
    linarith [horder1, hy]
  have hyoung_hess : C₀ * nHess * nGrad ≤ nHess ^ 2 / 2 + C₀ ^ 2 * nGrad ^ 2 / 2 := by
    nlinarith [sq_nonneg (nHess - C₀ * nGrad), hC₀]
  have hyoung_TG : nT * nGrad ≤ (nT ^ 2 + nGrad ^ 2) / 2 := by
    nlinarith [sq_nonneg (nT - nGrad)]
  have hstep2 :
      nHess ^ 2 ≤ nLap ^ 2 + nHess ^ 2 / 2 +
        C₀ * (nT * nGrad) + C₀ * nGrad ^ 2 + C₀ ^ 2 * nGrad ^ 2 / 2 := by
    have hexpand : C₀ * (nT + nGrad + nHess) * nGrad =
        C₀ * (nT * nGrad) + C₀ * nGrad ^ 2 + C₀ * nHess * nGrad := by ring
    have hbound := hstep1
    rw [hexpand] at hbound
    linarith [hbound, hyoung_hess]
  have hstep3 :
      nHess ^ 2 ≤ 2 * nLap ^ 2 + 2 * C₀ * (nT * nGrad)
        + 2 * C₀ * nGrad ^ 2 + C₀ ^ 2 * nGrad ^ 2 := by
    linarith [hstep2]
  have hTG_bound : nT * nGrad ≤ nLap ^ 2 / 4 + 3 * nT ^ 2 / 4 := by
    have h1 : nT * nGrad ≤ (nT ^ 2 + nGrad ^ 2) / 2 := hyoung_TG
    linarith [h1, hgrad_sq_le]
  have hgrad_term1 : 2 * C₀ * nGrad ^ 2 ≤ C₀ * nLap ^ 2 + C₀ * nT ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hgrad_sq_le hC₀
    have he : C₀ * ((nLap ^ 2 + nT ^ 2) / 2) = (C₀ * nLap ^ 2 + C₀ * nT ^ 2) / 2 := by ring
    rw [he] at h
    linarith [h]
  have hgrad_term2 : C₀ ^ 2 * nGrad ^ 2 ≤ C₀ ^ 2 * nLap ^ 2 / 2 + C₀ ^ 2 * nT ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hgrad_sq_le (sq_nonneg C₀)
    have he : C₀ ^ 2 * ((nLap ^ 2 + nT ^ 2) / 2) =
        C₀ ^ 2 * nLap ^ 2 / 2 + C₀ ^ 2 * nT ^ 2 / 2 := by ring
    rw [he] at h
    linarith [h]
  have hTG_term : 2 * C₀ * (nT * nGrad) ≤ C₀ * nLap ^ 2 / 2 + 3 * C₀ * nT ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hTG_bound hC₀
    have he : C₀ * (nLap ^ 2 / 4 + 3 * nT ^ 2 / 4) = C₀ * nLap ^ 2 / 4 + 3 * C₀ * nT ^ 2 / 4 := by
      ring
    rw [he] at h
    linarith [h]
  have hslack_lap : 0 ≤ (3 * C₀ / 2 + 3 * C₀ ^ 2 / 2) * nLap ^ 2 := by
    apply mul_nonneg
    · nlinarith [hC₀, sq_nonneg C₀]
    · positivity
  have hslack_T : 0 ≤ (C₀ / 2 + 3 * C₀ ^ 2 / 2) * nT ^ 2 := by
    apply mul_nonneg
    · nlinarith [hC₀, sq_nonneg C₀]
    · positivity
  have htarget_eq : (2 + 3 * C₀ + 2 * C₀ ^ 2) * (nLap ^ 2 + nT ^ 2) =
      2 * nLap ^ 2 + 2 * nT ^ 2 + 3 * C₀ * nLap ^ 2 + 3 * C₀ * nT ^ 2
        + 2 * C₀ ^ 2 * nLap ^ 2 + 2 * C₀ ^ 2 * nT ^ 2 := by ring
  have hslack_lap' : 0 ≤ 3 * C₀ * nLap ^ 2 / 2 + 3 * C₀ ^ 2 * nLap ^ 2 / 2 := by
    have he : (3 * C₀ / 2 + 3 * C₀ ^ 2 / 2) * nLap ^ 2 =
        3 * C₀ * nLap ^ 2 / 2 + 3 * C₀ ^ 2 * nLap ^ 2 / 2 := by ring
    rw [he] at hslack_lap; exact hslack_lap
  have hslack_T' : 0 ≤ C₀ * nT ^ 2 / 2 + 3 * C₀ ^ 2 * nT ^ 2 / 2 := by
    have he : (C₀ / 2 + 3 * C₀ ^ 2 / 2) * nT ^ 2 =
        C₀ * nT ^ 2 / 2 + 3 * C₀ ^ 2 * nT ^ 2 / 2 := by ring
    rw [he] at hslack_T; exact hslack_T
  rw [htarget_eq]
  linarith [hstep3, hgrad_term1, hgrad_term2, hTG_term, hslack_lap', hslack_T',
    sq_nonneg nT]

end Connection
end Integral
end DifferentialGeometry

end
