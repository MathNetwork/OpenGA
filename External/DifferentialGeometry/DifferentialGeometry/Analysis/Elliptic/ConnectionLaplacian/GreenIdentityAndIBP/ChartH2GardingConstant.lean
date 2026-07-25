import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Bound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebey
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedCurvatureCrossBound

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
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow

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

theorem exists_Ccross_for_secondCovGrad
    (g : SmoothRiemannianMetric I M) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ T : SmoothCcTensor g 0 2,
        - tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
              (rawTensorConnLapSmooth (I := I) g 0 (2 + 1)
                  (covGrad (I := I) (M := M) g 0 2 T) -
                covGrad (I := I) (M := M) g 0 2
                  (rawTensorConnLapSmooth (I := I) g 0 2 T)).toFun
              (covGrad (I := I) (M := M) g 0 2 T).toFun ≤
          Ccross *
            (tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
                (covGrad (I := I) (M := M) g 0 2 T).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 2 T.toFun *
                tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
                  (covGrad (I := I) (M := M) g 0 2 T).toFun) :=
  exists_integrated_curvatureCrossBound (I := I) (M := M) g 2


theorem exists_secondCovGrad_l2NormSq_le_rawConnLap
    (g : SmoothRiemannianMetric I M) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ T : SmoothCcTensor g 0 2,
        tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
            (covGrad (I := I) (M := M) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T)).toFun ^ 2 ≤
          Cg *
            (tensorL2Norm (I := I) (M := M) g 0 2
                (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 2 T.toFun ^ 2) := by
  obtain ⟨Ccross, hCcross, hcross⟩ := exists_Ccross_for_secondCovGrad (I := I) (M := M) g
  refine ⟨2 + 2 * Ccross, by positivity, fun T => ?_⟩
  exact secondCovGrad_l2NormSq_le_of_cross_bound (I := I) (M := M) g 2 T Ccross hCcross (hcross T)


theorem exists_secondCovGrad_l2Norm_le_rawConnLap_add_self
    (g : SmoothRiemannianMetric I M) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ T : SmoothCcTensor g 0 2,
        tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
            (covGrad (I := I) (M := M) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T)).toFun ≤
          Cg *
            (tensorL2Norm (I := I) (M := M) g 0 2
                (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun +
              tensorL2Norm (I := I) (M := M) g 0 2 T.toFun) := by
  obtain ⟨Cg, hCg, hbound⟩ := exists_secondCovGrad_l2NormSq_le_rawConnLap (I := I) (M := M) g
  refine ⟨Real.sqrt Cg, Real.sqrt_nonneg _, fun T => ?_⟩
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
    (covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T)).toFun with hnHess_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g 0 2 T.toFun with hnT_def
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (3 + 1) _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hsq : nHess ^ 2 ≤ Cg * (nLap ^ 2 + nT ^ 2) := hbound T
  have hkey : nHess ^ 2 ≤ (Real.sqrt Cg * (nLap + nT)) ^ 2 := by
    have hsqrtCg : Real.sqrt Cg ^ 2 = Cg := Real.sq_sqrt hCg
    have hexpand : (Real.sqrt Cg * (nLap + nT)) ^ 2 =
        Cg * (nLap ^ 2 + 2 * (nLap * nT) + nT ^ 2) := by
      rw [mul_pow, hsqrtCg]; ring
    rw [hexpand]
    have hcross_nn : 0 ≤ 2 * (nLap * nT) := by positivity
    nlinarith [hsq, mul_le_mul_of_nonneg_left hcross_nn hCg, hCg]
  have hrhs_nn : 0 ≤ Real.sqrt Cg * (nLap + nT) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  exact le_of_sq_le_sq hkey hrhs_nn


theorem exists_tensorPouSobolevHsNorm_one_le_rawConnLap_add_self
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 2,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
          C * (‖SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ +
            ‖SmoothCcTensor.toL2 T‖) := by
  classical
  obtain ⟨Cb, hCb, hbridge⟩ :=
    exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g 0 2 1
  obtain ⟨Cg, hCg, hHess⟩ :=
    exists_secondCovGrad_l2Norm_le_rawConnLap_add_self (I := I) (M := M) g
  refine ⟨Cb * (1 + Cg + 1), by positivity, fun T => ?_⟩
  set nLap : ℝ := ‖SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ with hnLap_def
  set nT : ℝ := ‖SmoothCcTensor.toL2 T‖ with hnT_def
  have hnLap_nn : 0 ≤ nLap := norm_nonneg _
  have hnT_nn : 0 ≤ nT := norm_nonneg _

  have hnLap_eq : nLap =
      tensorL2Norm (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun := by
    rw [hnLap_def, SmoothCcTensor.norm_toL2,
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g
        (rawTensorConnLapSmooth (I := I) g 0 2 T)]
  have hnT_eq : nT = tensorL2Norm (I := I) (M := M) g 0 2 T.toFun := by
    rw [hnT_def, SmoothCcTensor.norm_toL2, tensorL2Norm_toFun_eq_norm (I := I) (M := M) g T]

  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
    (iteratedCovGrad g 0 2 1 T).toFun with hnGrad_def
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (2 + 1 + 1)
    (iteratedCovGrad g 0 2 2 T).toFun with hnHess_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + 1) _
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + 1 + 1) _

  have hsum_eq :
      (∑ j ∈ Finset.range (2 * 1 + 1),
        tensorL2Norm (I := I) (M := M) g 0 (2 + j)
          (iteratedCovGrad g 0 2 j T).toFun) = nT + nGrad + nHess := by
    have h2 : (2 * 1 + 1 : ℕ) = 3 := by norm_num
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      iteratedCovGrad_zero]
    rw [show tensorL2Norm (I := I) (M := M) g 0 (2 + 0) T.toFun = nT from by rw [hnT_eq]]
  have hbridge_T := hbridge T
  rw [hsum_eq] at hbridge_T

  have hnGrad_cov : nGrad =
      tensorL2Norm (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T).toFun := by
    rw [hnGrad_def, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hnHess_cov : nHess =
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T)).toFun := by
    rw [hnHess_def, iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]

  have horder1 : nGrad ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun *
        tensorL2Norm (I := I) (M := M) g 0 2 T.toFun := by
    rw [hnGrad_cov]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  have horder1' : nGrad ^ 2 ≤ nLap * nT := by rw [hnLap_eq, hnT_eq]; exact horder1
  have hgrad_le : nGrad ≤ (nLap + nT) / 2 := by
    have hyoung : nLap * nT ≤ ((nLap + nT) / 2) ^ 2 := by nlinarith [sq_nonneg (nLap - nT)]
    have hgrad_sq : nGrad ^ 2 ≤ ((nLap + nT) / 2) ^ 2 := le_trans horder1' hyoung
    have hhalf_nn : 0 ≤ (nLap + nT) / 2 := by linarith
    exact le_of_sq_le_sq hgrad_sq hhalf_nn

  have hHess_le : nHess ≤ Cg * (nLap + nT) := by
    have := hHess T
    rw [← hnHess_cov, ← hnLap_eq, ← hnT_eq] at this
    exact this

  have hsum_le : nT + nGrad + nHess ≤ (1 + Cg + 1) * (nLap + nT) := by
    have hnT_le : nT ≤ 1 * (nLap + nT) := by rw [one_mul]; linarith
    have hgrad_le' : nGrad ≤ 1 * (nLap + nT) := by
      rw [one_mul]; linarith [hgrad_le]
    nlinarith [hnT_le, hgrad_le', hHess_le, hCg, hnLap_nn, hnT_nn]
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal
      ≤ Cb * (nT + nGrad + nHess) := hbridge_T
    _ ≤ Cb * ((1 + Cg + 1) * (nLap + nT)) :=
        mul_le_mul_of_nonneg_left hsum_le hCb
    _ = Cb * (1 + Cg + 1) * (nLap + nT) := by ring


theorem exists_tensorPouSobolevHsNorm_one_le_sum_rawConnLapIter
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 2,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
          C * ∑ j ∈ Finset.range (1 + 1),
            ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_tensorPouSobolevHsNorm_one_le_rawConnLap_add_self (I := I) (M := M) g
  refine ⟨C, hC, fun T => ?_⟩
  have hsum_eq :
      (∑ j ∈ Finset.range (1 + 1),
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖) =
      ‖SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ +
        ‖SmoothCcTensor.toL2 T‖ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one,
      rawTensorConnLapIter_zero (I := I) (M := M) g 0 2 T,
      rawTensorConnLapIter_one (I := I) (M := M) g 0 2 T]
    ring
  rw [hsum_eq]
  exact hbound T

end Connection
end Integral
end DifferentialGeometry

end
