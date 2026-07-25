import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.IntegratedOrder2WeitzenbockCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGradientL2Bound

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
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


lemma tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun S.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen (I := I) (M := M) g s S S


theorem covGrad_l2NormSq_le_rawConnLap_mul_self_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Norm (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun *
        tensorL2Norm (I := I) (M := M) g 0 s S.toFun := by
  set ΔS : SmoothCcTensor g 0 s := rawTensorConnLapSmooth (I := I) g 0 s S with hΔS_def
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 s ΔS.toFun S.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S)]
    rw [hΔS_def]
    exact tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g s S
  rw [hgreen]
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 s ΔS.toFun S.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔS)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔS S)
  have hneg_le :
      - tensorL2Inner (I := I) (M := M) g 0 s ΔS.toFun S.toFun ≤
        |tensorL2Inner (I := I) (M := M) g 0 s ΔS.toFun S.toFun| :=
    neg_le_abs _
  exact le_trans hneg_le hcs


theorem secondCovGrad_l2NormSq_le_of_cross_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Ccross : ℝ) (hCcross : 0 ≤ Ccross)
    (hcross :
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
                (covGrad (I := I) (M := M) g 0 s S).toFun)) :
    tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 ≤
      (2 + 2 * Ccross) *
        (tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 s S.toFun ^ 2) := by
  classical
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
    (covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S)).toFun with hnHess_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 (s + 1)
    (covGrad (I := I) (M := M) g 0 s S).toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S).toFun with hnLap_def
  set nS : ℝ := tensorL2Norm (I := I) (M := M) g 0 s S.toFun with hnS_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _
  have hnS_nn : 0 ≤ nS := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _
  have hweitz :
      nHess ^ 2 =
        nLap ^ 2 -
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                (covGrad (I := I) (M := M) g 0 s S) -
              covGrad (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [hnHess_def, hnLap_def]
    exact weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g s S
  have horder1 : nGrad ^ 2 ≤ nLap * nS := by
    rw [hnGrad_def, hnLap_def, hnS_def]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self_gen (I := I) (M := M) g s S
  have hstep1 : nHess ^ 2 ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nS * nGrad) := by
    have hcross' :
        - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S) -
                covGrad (I := I) (M := M) g 0 s
                  (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun ≤
          Ccross * (nGrad ^ 2 + nS * nGrad) := by
      rw [hnGrad_def, hnS_def]; exact hcross
    rw [hweitz]
    linarith [hcross']
  have hyoung_ls : nLap * nS ≤ (nLap ^ 2 + nS ^ 2) / 2 := by
    nlinarith [sq_nonneg (nLap - nS)]
  have hyoung_sg : nS * nGrad ≤ (nS ^ 2 + nGrad ^ 2) / 2 := by
    nlinarith [sq_nonneg (nS - nGrad)]
  have hbracket : nGrad ^ 2 + nS * nGrad ≤ 2 * (nLap ^ 2 + nS ^ 2) := by
    have h1 : nGrad ^ 2 ≤ (nLap ^ 2 + nS ^ 2) / 2 := le_trans horder1 hyoung_ls
    have h2 : nS * nGrad ≤ (nS ^ 2 + nGrad ^ 2) / 2 := hyoung_sg
    have h3 : nGrad ^ 2 ≤ (nLap ^ 2 + nS ^ 2) / 2 := h1
    nlinarith [h1, h2, h3]
  have hkey : Ccross * (nGrad ^ 2 + nS * nGrad) ≤ Ccross * (2 * (nLap ^ 2 + nS ^ 2)) :=
    mul_le_mul_of_nonneg_left hbracket hCcross
  have hnLapSq_nn : 0 ≤ nLap ^ 2 := sq_nonneg _
  have hnSSq_nn : 0 ≤ nS ^ 2 := sq_nonneg _
  calc nHess ^ 2
      ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nS * nGrad) := hstep1
    _ ≤ nLap ^ 2 + Ccross * (2 * (nLap ^ 2 + nS ^ 2)) := by linarith [hkey]
    _ ≤ (2 + 2 * Ccross) * (nLap ^ 2 + nS ^ 2) := by nlinarith [hnLapSq_nn, hnSSq_nn]

end Connection
end Integral
end DifferentialGeometry

end
