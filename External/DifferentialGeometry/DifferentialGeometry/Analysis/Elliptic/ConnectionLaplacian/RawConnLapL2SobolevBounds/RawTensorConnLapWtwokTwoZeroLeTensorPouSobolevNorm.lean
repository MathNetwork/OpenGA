import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawConnLapChartCoeffsUniformBoundT0Uniform
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.IteratedFDerivChartPushedRawBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapWtwokTwoZeroBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIntrinsicL2LePouSobolevNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedNorm
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma ennreal_sq_finset_sum_le_card_mul_sq_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, (f i) ^ 2 := by
  classical
  by_cases h_top : ∃ j ∈ s, f j = ⊤
  · obtain ⟨j, hj, hj_top⟩ := h_top
    have h_sum_top : ∑ i ∈ s, f i = ⊤ := by
      rw [ENNReal.sum_eq_top]; exact ⟨j, hj, hj_top⟩
    rw [h_sum_top]
    rw [show ((⊤ : ℝ≥0∞)) ^ 2 = ⊤ from by
      rw [sq]; exact ENNReal.top_mul_top]
    by_cases hs : s.card = 0
    · rw [Finset.card_eq_zero] at hs
      subst hs
      simp at hj
    · have hs_pos : 0 < s.card := Nat.pos_of_ne_zero hs
      have h_card_ne : ((s.card : ℝ≥0∞)) ≠ 0 := by
        rw [Ne, Nat.cast_eq_zero]; exact hs
      have h_sum_sq_top : ∑ i ∈ s, (f i) ^ 2 = ⊤ := by
        rw [ENNReal.sum_eq_top]
        refine ⟨j, hj, ?_⟩
        rw [hj_top]
        rw [show ((⊤ : ℝ≥0∞)) ^ 2 = ⊤ from by rw [sq]; exact ENNReal.top_mul_top]
      rw [h_sum_sq_top]
      rw [ENNReal.mul_top h_card_ne]
  · have hf_ne_top : ∀ i ∈ s, f i ≠ ⊤ := by
      intro i hi h_eq_top
      exact h_top ⟨i, hi, h_eq_top⟩
    have h_sum_ne_top : ∑ i ∈ s, f i ≠ ⊤ := by
      intro h_sum_top
      rw [ENNReal.sum_eq_top] at h_sum_top
      obtain ⟨i, hi, h_eq_top⟩ := h_sum_top
      exact hf_ne_top i hi h_eq_top
    have hf_sq_ne_top : ∀ i ∈ s, (f i) ^ 2 ≠ ⊤ := by
      intro i hi
      rw [sq]
      exact ENNReal.mul_ne_top (hf_ne_top i hi) (hf_ne_top i hi)
    have h_sum_sq_ne_top : ∑ i ∈ s, (f i) ^ 2 ≠ ⊤ := by
      intro h_eq_top
      rw [ENNReal.sum_eq_top] at h_eq_top
      obtain ⟨i, hi, h_top⟩ := h_eq_top
      exact hf_sq_ne_top i hi h_top
    set a : ι → ℝ := fun i => (f i).toReal with ha_def
    have ha_nn : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
    have hfi_eq : ∀ i ∈ s, f i = ENNReal.ofReal (a i) := by
      intro i hi
      rw [ha_def]
      exact (ENNReal.ofReal_toReal (hf_ne_top i hi)).symm
    have h_sum_eq : ∑ i ∈ s, f i = ENNReal.ofReal (∑ i ∈ s, a i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha_nn i)]
      exact Finset.sum_congr rfl hfi_eq
    have hfsq_eq : ∀ i ∈ s, (f i) ^ 2 = ENNReal.ofReal ((a i) ^ 2) := by
      intro i hi
      rw [hfi_eq i hi]
      rw [← ENNReal.ofReal_pow (ha_nn i) 2]
    have h_sumsq_eq : ∑ i ∈ s, (f i) ^ 2 = ENNReal.ofReal (∑ i ∈ s, (a i) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
      exact Finset.sum_congr rfl hfsq_eq
    rw [h_sum_eq]
    rw [← ENNReal.ofReal_pow (Finset.sum_nonneg (fun i _ => ha_nn i)) 2]
    rw [h_sumsq_eq]
    have h_card_eq :
        (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := by
      rw [ENNReal.ofReal_natCast]
    rw [h_card_eq]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have h_double_sum : ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 =
        2 * ((s.card : ℝ) * (∑ i ∈ s, (a i) ^ 2) -
              (∑ i ∈ s, a i) ^ 2) := by
      classical
      set S₀ : ℝ := ∑ i ∈ s, a i with hS₀_def
      set Q₀ : ℝ := ∑ i ∈ s, (a i) ^ 2 with hQ₀_def
      have h_inner : ∀ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 =
          (s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀ := by
        intro i _
        have hexp : ∀ j, (a i - a j) ^ 2 =
            (a i) ^ 2 - 2 * (a i) * (a j) + (a j) ^ 2 := by
          intro j; ring
        calc ∑ j ∈ s, (a i - a j) ^ 2
            = ∑ j ∈ s, ((a i) ^ 2 - 2 * (a i) * (a j) + (a j) ^ 2) :=
              Finset.sum_congr rfl (fun j _ => hexp j)
          _ = (∑ _j ∈ s, (a i) ^ 2) - (∑ j ∈ s, 2 * (a i) * (a j))
              + (∑ j ∈ s, (a j) ^ 2) := by
                rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          _ = (s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀ := by
                rw [Finset.sum_const]
                rw [show (∑ j ∈ s, 2 * (a i) * (a j)) = 2 * (a i) * S₀ from by
                  rw [show (fun j => 2 * (a i) * (a j)) =
                    (fun j => (2 * (a i)) * (a j)) from by funext j; ring]
                  rw [← Finset.mul_sum, ← hS₀_def]]
                rw [← hQ₀_def, nsmul_eq_mul]
      calc ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2
          = ∑ i ∈ s, ((s.card : ℝ) * (a i) ^ 2 - 2 * (a i) * S₀ + Q₀) :=
            Finset.sum_congr rfl h_inner
        _ = (∑ i ∈ s, (s.card : ℝ) * (a i) ^ 2)
            - (∑ i ∈ s, 2 * (a i) * S₀) + (∑ i ∈ s, Q₀) := by
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        _ = (s.card : ℝ) * Q₀ - 2 * S₀ * S₀ + (s.card : ℝ) * Q₀ := by
              rw [show (∑ i ∈ s, (s.card : ℝ) * (a i) ^ 2) =
                  (s.card : ℝ) * Q₀ from by
                rw [← Finset.mul_sum, ← hQ₀_def]]
              rw [show (∑ i ∈ s, 2 * (a i) * S₀) = 2 * S₀ * S₀ from by
                rw [show (fun i => 2 * (a i) * S₀) =
                  (fun i => (2 * S₀) * (a i)) from by funext i; ring]
                rw [← Finset.mul_sum, ← hS₀_def]]
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = 2 * ((s.card : ℝ) * Q₀ - S₀ ^ 2) := by ring
    have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [h_double_sum] at h_nn
    nlinarith

private lemma sq_eLpNorm_two_eq_lintegral_ofReal_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  classical
  have h_rpow : eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
      (1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
  have h_two_toReal : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [h_rpow, h_two_toReal]
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ with hI_def
  have hI_eq : I = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
    refine lintegral_congr ?_
    intro x
    rw [show ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ ((2 : ℕ) : ℝ) from by norm_num,
      ENNReal.rpow_natCast]
    rw [show ((f x) ^ 2 : ℝ) = ‖f x‖ ^ 2 from by
      rw [Real.norm_eq_abs, sq_abs]]
    rw [← ofReal_norm_eq_enorm]
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
  have h_step1 : (I ^ ((1 : ℝ) / 2)) ^ 2 = (I ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) := by
    rw [ENNReal.rpow_natCast]
  rw [h_step1]
  rw [← ENNReal.rpow_mul]
  have h_eq : ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [h_eq, ENNReal.rpow_one, hI_eq]

private noncomputable def tensorPouSobolevNormSqAgg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  ∑' α : M,
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range 3,
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume : Measure EuclN)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma tensorPouSobolevNorm_one_sq_eq_agg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) :
    (tensorPouSobolevNorm (I := I) (M := M) g 1 T) ^ 2 =
      tensorPouSobolevNormSqAgg (I := I) (M := M) g T := by
  classical
  rw [tensorPouSobolevNorm_eq]
  set BigSum : ℝ≥0∞ :=
    ∑' α : M,
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * 1 + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume : Measure EuclN) with hBigSum_def
  have hBigSum_eq : BigSum = tensorPouSobolevNormSqAgg (I := I) (M := M) g T := by
    rw [hBigSum_def]; simp only [tensorPouSobolevNormSqAgg]
  have h_pow : (BigSum ^ (1 / 2 : ℝ)) ^ 2 = BigSum := by
    rw [← ENNReal.rpow_natCast (BigSum ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
    have h1 : (1 / 2 : ℝ) * (2 : ℕ) = 1 := by push_cast; ring
    rw [h1]; exact ENNReal.rpow_one BigSum
  rw [h_pow, hBigSum_eq]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma tensorPouSobolevNormSqAgg_eq_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) :
    tensorPouSobolevNormSqAgg (I := I) (M := M) g T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range 3,
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN) := by
  classical
  unfold tensorPouSobolevNormSqAgg
  rw [tsum_eq_sum (s := chartAtlasPOU_finset (I := I) (M := M))]
  intro α hα
  have hρ_zero : ∀ x : M,
      (chartAtlasPOU I M α : M → ℝ) x = 0 := fun x =>
    chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  refine Finset.sum_eq_zero (fun IJ _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_integrand_zero : ∀ y : EuclN,
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2) = 0 := by
    intro y; rw [hρ_zero]; simp
  have heq : (fun y : EuclN =>
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2)) = (fun _ => 0) := by
    funext y; exact h_integrand_zero y
  rw [heq]; simp

private lemma wtwokTwoNorm_zero_rawTensorConnLap_collapsed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g 0
        (rawTensorConnLapSmooth (I := I) g r s T) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            eLpNorm
              (tensorChartComp (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  rw [wtwokTwoNorm_eq_tsum (I := I) (M := M) g 0
    (rawTensorConnLapSmooth (I := I) g r s T)]
  rw [show (2 * 0 : ℕ) = 0 from by norm_num]
  rw [tsum_eq_sum
    (s := chartAtlasPOU_finset (I := I) (M := M))
    (f := fun α : M =>
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))]
  · refine Finset.sum_congr rfl (fun α _ => ?_)
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    exact wkpNorm_zero (d := Module.finrank ℝ E) 2
      (tensorChartComp (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α)
  · intro α hα
    refine Finset.sum_eq_zero ?_
    intro Idx _
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    have hPOU_zero : ∀ x : M,
        (chartAtlasPOU I M α : M → ℝ) x = 0 := fun x =>
      chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    have h_comp_zero :
        tensorChartComp (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx =
          (fun _ => (0 : ℝ)) := by
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
      · rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx hy]
        unfold tensorChartComponentPou
        rw [hPOU_zero _]
        ring
      · exact tensorChartComp_apply_of_notMem (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx hy
    rw [h_comp_zero]
    exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)

private noncomputable def chainLmax : ℝ :=
  max 1 (‖((toEuclidean (E := E)).symm :
      EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 4)

omit [NeZero (Module.finrank ℝ E)] in
private lemma chainLmax_nonneg : (0 : ℝ) ≤ chainLmax (E := E) := by
  unfold chainLmax
  exact le_trans (by linarith : (0 : ℝ) ≤ 1) (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma one_le_chainLmax : (1 : ℝ) ≤ chainLmax (E := E) := by
  unfold chainLmax; exact le_max_left _ _

omit [NeZero (Module.finrank ℝ E)] in
private lemma chain_Lop_two_le_Lmax :
    ‖((toEuclidean (E := E)).symm :
        EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 2 ≤ chainLmax (E := E) := by
  set Lop : ℝ := ‖((toEuclidean (E := E)).symm :
      EuclN ≃L[ℝ] E).toContinuousLinearMap‖ with hLop_def
  have hLop_nn : 0 ≤ Lop := by rw [hLop_def]; exact norm_nonneg _
  by_cases h_Lop_le_one : Lop ≤ 1
  · have h_Lop2_le_one : Lop ^ 2 ≤ 1 := by
      have h_sq : Lop ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hLop_nn h_Lop_le_one 2
      simpa using h_sq
    exact le_trans h_Lop2_le_one (one_le_chainLmax (E := E))
  · have h_one_lt_Lop : (1 : ℝ) < Lop := lt_of_not_ge h_Lop_le_one
    have h_one_le_Lop : (1 : ℝ) ≤ Lop := le_of_lt h_one_lt_Lop
    have h_Lop2_le_Lop4 : Lop ^ 2 ≤ Lop ^ 4 :=
      pow_le_pow_right₀ h_one_le_Lop (by norm_num : 2 ≤ 4)
    unfold chainLmax
    exact le_trans h_Lop2_le_Lop4 (le_max_right _ _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma chain_Lop_four_le_Lmax :
    ‖((toEuclidean (E := E)).symm :
        EuclN ≃L[ℝ] E).toContinuousLinearMap‖ ^ 4 ≤ chainLmax (E := E) := by
  unfold chainLmax; exact le_max_right _ _

theorem tensorChartComp_rawConnLap_sq_le_pou_pouSobolev_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN),
        (tensorChartComp (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y) ^ 2 ≤
          K *
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
                ∑ j ∈ Finset.range 3,
                  ‖iteratedFDeriv ℝ j
                      ((tensorChartComponentRaw (I := I) (M := M) g r s
                            T α IJ'.1 IJ'.2)
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  have h_each : ∀ idx : Fin r → Fin n, ∀ jdx : Fin s → Fin n,
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ (T₀ : SmoothCcTensor g r s),
          ∀ (b : M),
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              chartLeviCivitaGoodSet (I := I) α →
            (tensorChartComponentRaw (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b) ^ 2 ≤
              K * (∑ Idx' : Fin r → Fin n,
                    ∑ Jdx' : Fin s → Fin n,
                      ((‖iteratedFDeriv ℝ 2
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                              T₀ α Idx' Jdx'))
                          ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                      (‖fderiv ℝ
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                              T₀ α Idx' Jdx'))
                          ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                      (chartPushedRaw I α
                         (tensorChartComponentRaw (I := I) (M := M) g r s
                           T₀ α Idx' Jdx')
                         ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) :=
    fun idx jdx =>
      rawTensorConnLap_chartα_coeffs_uniform_bound_on_pouTsupport_T0_uniform
        (I := I) (M := M) g r s α idx jdx
  choose K_pt hK_pt_nn hK_pt_le using h_each
  set K_max : ℝ :=
    (Finset.univ : Finset ((Fin r → Fin n) × (Fin s → Fin n))).sup'
      Finset.univ_nonempty (fun p => K_pt p.1 p.2) with hK_max_def
  have hK_max_nn : 0 ≤ K_max := by
    rw [hK_max_def]
    obtain ⟨p₀, hp₀⟩ :=
      (Finset.univ_nonempty : (Finset.univ : Finset
        ((Fin r → Fin n) × (Fin s → Fin n))).Nonempty)
    exact le_trans (hK_pt_nn p₀.1 p₀.2)
      (Finset.le_sup' (f := fun p => K_pt p.1 p.2) hp₀)
  have hK_pt_le_max : ∀ idx jdx, K_pt idx jdx ≤ K_max := by
    intro idx jdx
    rw [hK_max_def]
    exact Finset.le_sup' (f := fun p => K_pt p.1 p.2)
      (Finset.mem_univ (⟨idx, jdx⟩ : (Fin r → Fin n) × (Fin s → Fin n)))
  set Lmax : ℝ := chainLmax (E := E) with hLmax_def
  have hLmax_nn : 0 ≤ Lmax := chainLmax_nonneg
  have h_one_le_Lmax : (1 : ℝ) ≤ Lmax := one_le_chainLmax
  refine ⟨K_max * Lmax * 3, by positivity, ?_⟩
  intro T Idx Jdx y
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) b with hρ_def
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α b
  have hρ_le_one : ρ ≤ 1 := (chartAtlasPOU I M).le_one α b
  set RHS_pouSobolev : ℝ :=
    ∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
      ∑ j ∈ Finset.range 3,
        ‖iteratedFDeriv ℝ j
            ((tensorChartComponentRaw (I := I) (M := M) g r s
                  T α IJ'.1 IJ'.2)
              ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2 with hRHS_def
  have hRHS_nn : 0 ≤ RHS_pouSobolev := by
    rw [hRHS_def]
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    exact sq_nonneg _
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  swap
  · have h_zero :
        tensorChartComp (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y = 0 :=
      tensorChartComp_apply_of_notMem (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx hy
    rw [h_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    refine mul_nonneg ?_ (mul_nonneg hρ_nn hRHS_nn)
    positivity
  have hb_chart_src : b ∈ (chartAt H α).source := by
    rw [hb_def]
    have h_in_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm] at hy
      exact hy
    have h_ext : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        (extChartAt I α).source := (extChartAt I α).map_target h_in_target
    rwa [extChartAt_source] at h_ext
  have hb_extSrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart_src
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α]
    exact hb_extSrc
  have h_lhs_eq :
      tensorChartComp (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y =
        ρ * tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx b := by
    rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx hy]
    unfold tensorChartComponentPou
    rfl
  have h_lhs_sq_eq :
      (tensorChartComp (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y) ^ 2 =
        ρ ^ 2 *
          (tensorChartComponentRaw (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx b) ^ 2 := by
    rw [h_lhs_eq, mul_pow]
  by_cases hb_supp : b ∈ tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  swap
  · have hρ_zero : ρ = 0 := image_eq_zero_of_notMem_tsupport hb_supp
    have h_LHS_zero :
        (tensorChartComp (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y) ^ 2 = 0 := by
      rw [h_lhs_sq_eq, hρ_zero]; ring
    rw [h_LHS_zero]
    refine mul_nonneg ?_ (mul_nonneg hρ_nn hRHS_nn)
    positivity
  have hb_inter : b ∈ tsupport
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        chartLeviCivitaGoodSet (I := I) α := ⟨hb_supp, hb_good⟩
  have h_raw_sq_bound := hK_pt_le Idx Jdx T b hb_inter
  have h_extAt_b : (extChartAt I α) b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]
    have h_in_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm] at hy
      exact hy
    exact (extChartAt I α).right_inv h_in_target
  have h_to_b : (toEuclidean (E := E)) ((extChartAt I α) b) = y := by
    rw [h_extAt_b]
    exact (toEuclidean (E := E)).apply_symm_apply y
  have h_per_pair : ∀ Idx' : Fin r → Fin n, ∀ Jdx' : Fin s → Fin n,
      (‖iteratedFDeriv ℝ 2
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s
              T α Idx' Jdx'))
          ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
      (‖fderiv ℝ
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s
              T α Idx' Jdx'))
          ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
      (chartPushedRaw I α
         (tensorChartComponentRaw (I := I) (M := M) g r s
           T α Idx' Jdx')
         ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2 ≤
      Lmax *
        ∑ j ∈ Finset.range 3,
          ‖iteratedFDeriv ℝ j
              ((tensorChartComponentRaw (I := I) (M := M) g r s
                  T α Idx' Jdx')
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
    intro Idx' Jdx'
    rw [h_to_b]
    have hcontDiff :
        ContDiffOn ℝ ∞
          ((tensorChartComponentRaw (I := I) (M := M) g r s
              T α Idx' Jdx') ∘ (extChartAt I α).symm)
          (extChartAt I α).target := by
      have hraw_src : ContMDiffOn I 𝓘(ℝ) ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')
          ((chartAt H α).source) :=
        tensorChartComponentRaw_contMDiffOn_chart_source (I := I) (M := M)
          g r s T α Idx' Jdx'
      have hraw_extsrc : ContMDiffOn I 𝓘(ℝ) ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')
          ((extChartAt I α).source) := by
        rw [extChartAt_source]; exact hraw_src
      have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
          (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
      have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
          (extChartAt I α).source := fun y' hy' => (extChartAt I α).map_target hy'
      exact (hraw_extsrc.comp hsymm hmaps).contDiffOn
    have h0 :
        (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') y) ^ 2 =
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')
              ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y) ^ 2 := by
      have := chartPushedRaw_sq_eq_compositionSq (I := I) (M := M)
        (E := E) (α := α)
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') hy
      simp only [Function.comp] at this ⊢
      exact this
    have hcontDiff1 :
        ContDiffOn ℝ 1
          ((tensorChartComponentRaw (I := I) (M := M) g r s
              T α Idx' Jdx') ∘ (extChartAt I α).symm)
          (extChartAt I α).target :=
      hcontDiff.of_le (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
    have h1 :
        ‖fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')) y‖
          ^ 2 ≤
        (‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖) ^ 2 *
        ‖fderiv ℝ
            ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
              (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2 :=
      fderiv_chartPushedRaw_sq_le_compFderivSq (I := I) (M := M) (E := E) α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')
        hcontDiff1 hy
    have hcontDiff2 :
        ContDiffOn ℝ 2
          ((tensorChartComponentRaw (I := I) (M := M) g r s
              T α Idx' Jdx') ∘ (extChartAt I α).symm)
          (extChartAt I α).target :=
      hcontDiff.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    have h2 :
        ‖iteratedFDeriv ℝ 2
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')) y‖
          ^ 2 ≤
        (‖((toEuclidean (E := E)).symm :
            EuclN ≃L[ℝ] E).toContinuousLinearMap‖) ^ 4 *
        ‖iteratedFDeriv ℝ 2
            ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
              (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2 :=
      iteratedFDeriv_two_chartPushedRaw_sq_le_compIterSq (I := I) (M := M) (E := E) α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')
        hcontDiff2 hy
    have hLop2_le_Lmax := chain_Lop_two_le_Lmax (E := E)
    have hLop4_le_Lmax := chain_Lop_four_le_Lmax (E := E)
    have h_iterFD0 :
        ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
            (extChartAt I α).symm) ((toEuclidean (E := E)).symm y) =
          iteratedFDeriv ℝ 0
            ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
              (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y) 0 := by
      rw [iteratedFDeriv_zero_apply]
    have h_iterFD0_norm :
        ‖iteratedFDeriv ℝ 0
            ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
              (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ =
          ‖((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
              (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ := by
      rw [norm_iteratedFDeriv_zero]
    have h0_le :
        (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') y) ^ 2 ≤
          Lmax *
            ‖iteratedFDeriv ℝ 0
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                  (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
      rw [h0]
      have h_abs_sq :
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
              (extChartAt I α).symm) ((toEuclidean (E := E)).symm y) ^ 2 =
            ‖((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                (extChartAt I α).symm) ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [h_abs_sq, ← h_iterFD0_norm]
      calc ‖iteratedFDeriv ℝ 0
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2
          = 1 * ‖iteratedFDeriv ℝ 0
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2 := by ring
        _ ≤ Lmax * ‖iteratedFDeriv ℝ 0
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right one_le_chainLmax (sq_nonneg _)
    have h_fderiv_eq_iterFD1 :
        ‖fderiv ℝ
            ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
              (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ =
          ‖iteratedFDeriv ℝ 1
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ := by
      rw [norm_iteratedFDeriv_one]
    have h1_le :
        ‖fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')) y‖
          ^ 2 ≤
        Lmax *
          ‖iteratedFDeriv ℝ 1
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
      refine le_trans h1 ?_
      rw [← h_fderiv_eq_iterFD1]
      exact mul_le_mul_of_nonneg_right hLop2_le_Lmax (sq_nonneg _)
    have h2_le :
        ‖iteratedFDeriv ℝ 2
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')) y‖
          ^ 2 ≤
        Lmax *
          ‖iteratedFDeriv ℝ 2
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
      refine le_trans h2 ?_
      exact mul_le_mul_of_nonneg_right hLop4_le_Lmax (sq_nonneg _)
    have h_sum_three :
        Lmax *
            ‖iteratedFDeriv ℝ 0
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                  (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2 +
          (Lmax *
              ‖iteratedFDeriv ℝ 1
                  ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                    (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2 +
            Lmax *
              ‖iteratedFDeriv ℝ 2
                  ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                    (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) =
          Lmax *
            (∑ j ∈ Finset.range 3,
              ‖iteratedFDeriv ℝ j
                  ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                    (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
      rw [show (Finset.range 3) =
          (insert 0 (insert 1 ({2} : Finset ℕ))) from by decide]
      rw [Finset.sum_insert (by decide : (0 : ℕ) ∉ insert 1 ({2} : Finset ℕ))]
      rw [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ))]
      rw [Finset.sum_singleton]
      ring
    calc (‖iteratedFDeriv ℝ 2
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')) y‖) ^ 2 +
          (‖fderiv ℝ
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx')) y‖) ^ 2 +
          (chartPushedRaw I α
             (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') y) ^ 2
        ≤ Lmax *
            ‖iteratedFDeriv ℝ 2
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                  (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2 +
          (Lmax *
            ‖iteratedFDeriv ℝ 1
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                  (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2 +
          Lmax *
            ‖iteratedFDeriv ℝ 0
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                  (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
            have := add_le_add (add_le_add h2_le h1_le) h0_le
            linarith
      _ = Lmax *
            (∑ j ∈ Finset.range 3,
              ‖iteratedFDeriv ℝ j
                  ((tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx') ∘
                    (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
            rw [show (Finset.range 3) =
                (insert 0 (insert 1 ({2} : Finset ℕ))) from by decide]
            rw [Finset.sum_insert (by decide : (0 : ℕ) ∉ insert 1 ({2} : Finset ℕ))]
            rw [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ))]
            rw [Finset.sum_singleton]
            ring
  have h_sum_pairs :
      ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
        ((‖iteratedFDeriv ℝ 2
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                T α Idx' Jdx'))
            ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
        (‖fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                T α Idx' Jdx'))
            ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
        (chartPushedRaw I α
           (tensorChartComponentRaw (I := I) (M := M) g r s
             T α Idx' Jdx')
           ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2) ≤
        Lmax * RHS_pouSobolev := by
    have h_sum :
        ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
          ((‖iteratedFDeriv ℝ 2
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  T α Idx' Jdx'))
              ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
          (‖fderiv ℝ
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  T α Idx' Jdx'))
              ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
          (chartPushedRaw I α
             (tensorChartComponentRaw (I := I) (M := M) g r s
               T α Idx' Jdx')
             ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2) ≤
          ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
            Lmax *
              ∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s
                        T α Idx' Jdx')
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
      refine Finset.sum_le_sum (fun Idx' _ => ?_)
      refine Finset.sum_le_sum (fun Jdx' _ => ?_)
      exact h_per_pair Idx' Jdx'
    refine le_trans h_sum ?_
    rw [show (fun Idx' : Fin r → Fin n => ∑ Jdx' : Fin s → Fin n,
        Lmax *
          ∑ j ∈ Finset.range 3,
            ‖iteratedFDeriv ℝ j
                ((tensorChartComponentRaw (I := I) (M := M) g r s
                    T α Idx' Jdx')
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2) =
        (fun Idx' : Fin r → Fin n =>
          Lmax * ∑ Jdx' : Fin s → Fin n,
            ∑ j ∈ Finset.range 3,
              ‖iteratedFDeriv ℝ j
                  ((tensorChartComponentRaw (I := I) (M := M) g r s
                      T α Idx' Jdx')
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) from by
      funext Idx'
      rw [Finset.mul_sum]]
    rw [show ∑ Idx' : Fin r → Fin n,
            Lmax * ∑ Jdx' : Fin s → Fin n,
              ∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s
                        T α Idx' Jdx')
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2 =
        Lmax * ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
            ∑ j ∈ Finset.range 3,
              ‖iteratedFDeriv ℝ j
                  ((tensorChartComponentRaw (I := I) (M := M) g r s
                      T α Idx' Jdx')
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2 from by
      rw [Finset.mul_sum]]
    refine mul_le_mul_of_nonneg_left ?_ hLmax_nn
    rw [hRHS_def]
    rw [← Finset.sum_product']
    exact le_refl _
  have h_K_pt_le_max_idxJdx : K_pt Idx Jdx ≤ K_max := hK_pt_le_max Idx Jdx
  have h_Spairs_nn :
      0 ≤ ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
        ((‖iteratedFDeriv ℝ 2
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                T α Idx' Jdx'))
            ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
        (‖fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                T α Idx' Jdx'))
            ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
        (chartPushedRaw I α
           (tensorChartComponentRaw (I := I) (M := M) g r s
             T α Idx' Jdx')
           ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2) := by
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    positivity
  have h_raw_sq_bound_max :
      (tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx b) ^ 2 ≤
        K_max *
          ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
            ((‖iteratedFDeriv ℝ 2
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                    T α Idx' Jdx'))
                ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
            (‖fderiv ℝ
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                    T α Idx' Jdx'))
                ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
            (chartPushedRaw I α
               (tensorChartComponentRaw (I := I) (M := M) g r s
                 T α Idx' Jdx')
               ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2) :=
    le_trans h_raw_sq_bound
      (mul_le_mul_of_nonneg_right h_K_pt_le_max_idxJdx h_Spairs_nn)
  have hρ_sq_nn : 0 ≤ ρ ^ 2 := sq_nonneg _
  have h_lhs_sq_le_pre :
      (tensorChartComp (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y) ^ 2 ≤
        ρ ^ 2 *
          (K_max *
            ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
              ((‖iteratedFDeriv ℝ 2
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                      T α Idx' Jdx'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
              (‖fderiv ℝ
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                      T α Idx' Jdx'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
              (chartPushedRaw I α
                 (tensorChartComponentRaw (I := I) (M := M) g r s
                   T α Idx' Jdx')
                 ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) := by
    rw [h_lhs_sq_eq]
    exact mul_le_mul_of_nonneg_left h_raw_sq_bound_max hρ_sq_nn
  have hρ_sq_le_ρ : ρ ^ 2 ≤ ρ := by
    have h_mul : ρ * ρ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hρ_le_one hρ_nn
    rw [mul_one] at h_mul
    have h_sq_eq : ρ ^ 2 = ρ * ρ := sq ρ
    rw [h_sq_eq]
    exact h_mul
  have h_K_max_nn := hK_max_nn
  have h_chain_bound :
      ρ ^ 2 *
        (K_max *
          ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
            ((‖iteratedFDeriv ℝ 2
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                    T α Idx' Jdx'))
                ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
            (‖fderiv ℝ
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                    T α Idx' Jdx'))
                ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
            (chartPushedRaw I α
               (tensorChartComponentRaw (I := I) (M := M) g r s
                 T α Idx' Jdx')
               ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) ≤
        ρ ^ 2 * (K_max * (Lmax * RHS_pouSobolev)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h_sum_pairs h_K_max_nn) hρ_sq_nn
  have h_step1 :
      ρ ^ 2 * (K_max * (Lmax * RHS_pouSobolev)) =
        K_max * Lmax * (ρ ^ 2 * RHS_pouSobolev) := by ring
  have h_step2 :
      K_max * Lmax * (ρ ^ 2 * RHS_pouSobolev) ≤
        K_max * Lmax * (ρ * RHS_pouSobolev) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hρ_sq_le_ρ hRHS_nn)
      (mul_nonneg h_K_max_nn hLmax_nn)
  have h_step3 :
      K_max * Lmax * (ρ * RHS_pouSobolev) ≤
        K_max * Lmax * 3 * (ρ * RHS_pouSobolev) := by
    have h_ρRHS_nn : 0 ≤ ρ * RHS_pouSobolev := mul_nonneg hρ_nn hRHS_nn
    have h : K_max * Lmax ≤ K_max * Lmax * 3 := by
      have : K_max * Lmax * 1 ≤ K_max * Lmax * 3 := by
        refine mul_le_mul_of_nonneg_left (by norm_num) ?_
        exact mul_nonneg h_K_max_nn hLmax_nn
      simpa using this
    exact mul_le_mul_of_nonneg_right h h_ρRHS_nn
  calc (tensorChartComp (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y) ^ 2
      ≤ ρ ^ 2 *
          (K_max *
            ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
              ((‖iteratedFDeriv ℝ 2
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                      T α Idx' Jdx'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
              (‖fderiv ℝ
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                      T α Idx' Jdx'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
              (chartPushedRaw I α
                 (tensorChartComponentRaw (I := I) (M := M) g r s
                   T α Idx' Jdx')
                 ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) :=
        h_lhs_sq_le_pre
    _ ≤ ρ ^ 2 * (K_max * (Lmax * RHS_pouSobolev)) := h_chain_bound
    _ = K_max * Lmax * (ρ ^ 2 * RHS_pouSobolev) := h_step1
    _ ≤ K_max * Lmax * (ρ * RHS_pouSobolev) := h_step2
    _ ≤ K_max * Lmax * 3 * (ρ * RHS_pouSobolev) := h_step3
    _ = K_max * Lmax * 3 * (ρ * RHS_pouSobolev) := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma pouWeightedSummand_aemeasurable_on_chartTarget
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) :
    AEMeasurable
      (fun y : EuclN => ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_iterFD_cont :
      ContinuousOn
        (fun y' : E => iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 ∘
            (extChartAt I α).symm)
          y')
        ((extChartAt I α).target) :=
    iteratedFDeriv_tensorChartComponentRaw_comp_symm_continuousOn
      (I := I) (M := M) g r s T α IJ.1 IJ.2 j
  have h_toEucl_symm_cont : Continuous ((toEuclidean (E := E)).symm) :=
    (toEuclidean (E := E)).symm.continuous
  have h_eq_preimage :
      chartTargetEuclid (I := I) (M := M) α =
        (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target :=
    chartTargetEuclid_eq_preimage_symm (I := I) (M := M) α
  have h_maps :
      Set.MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) ((extChartAt I α).target) := by
    intro y hy
    rw [h_eq_preimage] at hy
    exact hy
  have h_iterFD_comp_cont :
      ContinuousOn
        (fun y : EuclN => iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 ∘
            (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_iterFD_cont.comp h_toEucl_symm_cont.continuousOn h_maps
  have h_norm_sq_cont :
      ContinuousOn
        (fun y : EuclN => ‖iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 ∘
            (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_iterFD_comp_cont.norm.pow 2
  have h_pou_cont : Continuous (fun b : M => (chartAtlasPOU I M α : M → ℝ) b) :=
    (chartAtlasPOU I M α).contMDiff.continuous
  have h_extSymm_cont :
      ContinuousOn (fun y : E => (extChartAt I α).symm y) ((extChartAt I α).target) :=
    continuousOn_extChartAt_symm (I := I) α
  have h_pou_comp_cont :
      ContinuousOn
        (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_inner_cont :
        ContinuousOn
          (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTargetEuclid (I := I) (M := M) α) :=
      h_extSymm_cont.comp h_toEucl_symm_cont.continuousOn h_maps
    exact h_pou_cont.comp_continuousOn h_inner_cont
  have h_prod_cont :
      ContinuousOn
        (fun y : EuclN =>
          ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_pou_comp_cont.mul h_norm_sq_cont
  have h_meas_set :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_prod_aemeas :
      AEMeasurable
        (fun y : EuclN =>
          ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 ∘
                (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    h_prod_cont.aemeasurable h_meas_set
  exact ENNReal.measurable_ofReal.comp_aemeasurable h_prod_aemeas

private lemma sq_eLpNorm_tensorChartComp_le_pou_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm
            (tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 ≤
          ENNReal.ofReal K *
            (∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range 3,
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      ‖iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2
                            ∘ (extChartAt I α).symm)
                          ((toEuclidean (E := E)).symm y)‖ ^ 2)
                  ∂(volume : Measure EuclN)) := by
  classical
  obtain ⟨K, hK_nn, hK_bound⟩ :=
    tensorChartComp_rawConnLap_sq_le_pou_pouSobolev_summand
      (I := I) (M := M) g r s α
  refine ⟨K, hK_nn, ?_⟩
  intro T Idx Jdx
  have h_sq_eLp :
      (eLpNorm
          (tensorChartComp (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))) ^ 2 =
      ∫⁻ y, ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y) ^ 2)
          ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
    sq_eLpNorm_two_eq_lintegral_ofReal_sq _ _
  rw [h_sq_eLp]
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have h_pt : ∀ y : EuclN,
      ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y) ^ 2) ≤
        ENNReal.ofReal
          (K *
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
                ∑ j ∈ Finset.range 3,
                  ‖iteratedFDeriv ℝ j
                      ((tensorChartComponentRaw (I := I) (M := M) g r s
                            T α IJ'.1 IJ'.2)
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)) := by
    intro y
    exact ENNReal.ofReal_le_ofReal (hK_bound T Idx Jdx y)
  have h_int_le :
      ∫⁻ y, ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx y) ^ 2) ∂μ ≤
      ∫⁻ y, ENNReal.ofReal
          (K *
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
                ∑ j ∈ Finset.range 3,
                  ‖iteratedFDeriv ℝ j
                      ((tensorChartComponentRaw (I := I) (M := M) g r s
                            T α IJ'.1 IJ'.2)
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)) ∂μ :=
    lintegral_mono h_pt
  refine le_trans h_int_le ?_
  have h_pou_nn : ∀ y : EuclN,
      0 ≤ (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := fun y =>
    (chartAtlasPOU I M).nonneg α _
  have h_summand_nn : ∀ y : EuclN, ∀ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)), ∀ j ∈ Finset.range 3,
      0 ≤ ‖iteratedFDeriv ℝ j
          ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
            ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2 := fun _ _ _ _ => sq_nonneg _
  have h_inner_sum_nn : ∀ y : EuclN,
      0 ≤ ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range 3,
          ‖iteratedFDeriv ℝ j
              ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2 := fun y => by
    refine Finset.sum_nonneg (fun IJ' _ => ?_)
    refine Finset.sum_nonneg (fun j hj => ?_)
    exact h_summand_nn y IJ' j hj
  have h_prod_inner_nn : ∀ y : EuclN,
      0 ≤ ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2 := fun y =>
    mul_nonneg (h_pou_nn y) (h_inner_sum_nn y)
  have h_ofReal_mul : ∀ y : EuclN,
      ENNReal.ofReal
        (K *
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)) =
      ENNReal.ofReal K *
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) := fun y =>
    ENNReal.ofReal_mul hK_nn
  have h_distrib : ∀ y : EuclN,
      ((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range 3,
            ‖iteratedFDeriv ℝ j
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2 =
      ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range 3,
          ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖iteratedFDeriv ℝ j
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2 := fun y => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun IJ' _ => ?_)
    rw [Finset.mul_sum]
  have h_inner_summand_nn : ∀ y : EuclN, ∀ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)), ∀ j ∈ Finset.range 3,
      0 ≤ ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖iteratedFDeriv ℝ j
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2 :=
    fun y IJ' j _ => mul_nonneg (h_pou_nn y) (sq_nonneg _)
  have h_integrand_eq : ∀ y : EuclN,
      ENNReal.ofReal
        (K *
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)) =
      ENNReal.ofReal K *
        ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range 3,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
    intro y
    rw [h_ofReal_mul y, h_distrib y]
    have h_outer_nn : ∀ IJ' ∈ (Finset.univ :
        Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)))),
        0 ≤ ∑ j ∈ Finset.range 3,
          ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖iteratedFDeriv ℝ j
                ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
      intro IJ' _
      refine Finset.sum_nonneg (fun j hj => ?_)
      exact h_inner_summand_nn y IJ' j hj
    rw [ENNReal.ofReal_sum_of_nonneg h_outer_nn]
    refine congrArg (fun z => ENNReal.ofReal K * z) ?_
    refine Finset.sum_congr rfl (fun IJ' _ => ?_)
    refine (ENNReal.ofReal_sum_of_nonneg (fun j hj =>
      h_inner_summand_nn y IJ' j hj))
  rw [show
      (fun y : EuclN => ENNReal.ofReal
        (K *
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range 3,
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2))) =
      (fun y : EuclN => ENNReal.ofReal K *
        ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range 3,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)) from by
    funext y; exact h_integrand_eq y]
  rw [lintegral_const_mul' (ENNReal.ofReal K) _ ENNReal.ofReal_ne_top]
  refine mul_le_mul_right ?_ _
  have h_swap_IJ :
      ∫⁻ y, ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range 3,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) ∂μ =
        ∑ IJ' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∫⁻ y,
            ∑ j ∈ Finset.range 3,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2) ∂μ := by
    refine lintegral_finset_sum' _ (fun IJ' _ => ?_)
    refine Finset.aemeasurable_fun_sum _ (fun j _ => ?_)
    exact pouWeightedSummand_aemeasurable_on_chartTarget
      (I := I) (M := M) g r s T α IJ' j
  rw [h_swap_IJ]
  refine Finset.sum_le_sum (fun IJ' _ => ?_)
  have h_swap_j :
      ∫⁻ y, ∑ j ∈ Finset.range 3,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) ∂μ =
        ∑ j ∈ Finset.range 3,
          ∫⁻ y, ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    ((tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2)
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2) ∂μ := by
    refine lintegral_finset_sum' _ (fun j _ => ?_)
    exact pouWeightedSummand_aemeasurable_on_chartTarget
      (I := I) (M := M) g r s T α IJ' j
  rw [h_swap_j]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem wtwokTwoNorm_zero_rawTensorConnLap_le_tensorPouSobolevNorm_one
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (T : SmoothCcTensor g r s),
        wtwokTwoNorm (I := I) (M := M) g 0
            (rawTensorConnLapSmooth (I := I) g r s T) ≤
          C * tensorPouSobolevNorm (I := I) (M := M) g 1 T := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have h_each : ∀ α : M, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s)
        (Idx : Fin r → Fin n)
        (Jdx : Fin s → Fin n),
        (eLpNorm
            (tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))) ^ 2 ≤
          ENNReal.ofReal K *
            (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
              ∑ j ∈ Finset.range 3,
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      ‖iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ'.1 IJ'.2
                            ∘ (extChartAt I α).symm)
                          ((toEuclidean (E := E)).symm y)‖ ^ 2)
                  ∂(volume : Measure EuclN)) := fun α =>
    sq_eLpNorm_tensorChartComp_le_pou_summand (I := I) (M := M) g r s α
  choose K_pt hK_pt_nn hK_pt_bound using h_each
  set K_max : ℝ := if hSne : S.Nonempty then S.sup' hSne K_pt else 1 with hK_max_def
  have hK_max_nn : 0 ≤ K_max := by
    rw [hK_max_def]
    by_cases hSne : S.Nonempty
    · rw [dif_pos hSne]
      obtain ⟨α₀, hα₀⟩ := hSne
      exact le_trans (hK_pt_nn α₀) (Finset.le_sup' K_pt hα₀)
    · rw [dif_neg hSne]; linarith
  have hK_le_max : ∀ α ∈ S, K_pt α ≤ K_max := by
    intro α hα
    rw [hK_max_def]
    have hSne : S.Nonempty := ⟨α, hα⟩
    rw [dif_pos hSne]
    exact Finset.le_sup' K_pt hα
  set nIJ : ℕ :=
    Fintype.card ((Fin r → Fin n) × (Fin s → Fin n)) with hnIJ_def
  set Nflat : ℕ := S.card * nIJ with hNflat_def
  set C_sq : ℝ := (Nflat : ℝ) * (nIJ : ℝ) * K_max with hC_sq_def
  have hC_sq_nn : 0 ≤ C_sq := by
    rw [hC_sq_def]
    refine mul_nonneg (mul_nonneg ?_ ?_) hK_max_nn
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  set C : ℝ := Real.sqrt C_sq with hC_def
  have hC_nn : 0 ≤ C := Real.sqrt_nonneg _
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
  intro T
  set LHS : ℝ≥0∞ := wtwokTwoNorm (I := I) (M := M) g 0
    (rawTensorConnLapSmooth (I := I) g r s T) with hLHS_def
  set W₁ : ℝ≥0∞ := tensorPouSobolevNorm (I := I) (M := M) g 1 T with hW₁_def
  set FS : ℝ≥0∞ :=
    ∑ α ∈ S,
      ∑ Idx : Fin r → Fin n,
        ∑ Jdx : Fin s → Fin n,
          eLpNorm
            (tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) with hFS_def
  have hLHS_eq : LHS = FS := by
    rw [hLHS_def, hFS_def]
    exact wtwokTwoNorm_zero_rawTensorConnLap_collapsed
      (I := I) (M := M) g r s T
  set f : M × ((Fin r → Fin n) × (Fin s → Fin n)) → ℝ≥0∞ := fun p =>
    eLpNorm
      (tensorChartComp (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) p.1 p.2.1 p.2.2) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) p.1)) with hf_def
  have hFS_flat :
      FS = ∑ p ∈ (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))), f p := by
    rw [hFS_def, hf_def]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [show (Finset.univ : Finset ((Fin r → Fin n) × (Fin s → Fin n))) =
        (Finset.univ : Finset (Fin r → Fin n)) ×ˢ
          (Finset.univ : Finset (Fin s → Fin n)) from rfl]
    rw [Finset.sum_product]
  have h_card_flat :
      (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))).card =
        Nflat := by
    rw [Finset.card_product, hNflat_def, hnIJ_def]
    rfl
  have h_CS : FS ^ 2 ≤ (Nflat : ℝ≥0∞) *
      ∑ p ∈ (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))), (f p) ^ 2 := by
    rw [hFS_flat]
    have hCS_pre := ennreal_sq_finset_sum_le_card_mul_sq_finset_sum
      (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))) f
    rw [h_card_flat] at hCS_pre
    exact hCS_pre
  have h_per_p : ∀ p ∈ (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))),
      (f p) ^ 2 ≤
        ENNReal.ofReal K_max *
          (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) p.1,
                ENNReal.ofReal
                  (((chartAtlasPOU I M p.1 : M → ℝ)
                      ((extChartAt I p.1).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                          T p.1 IJ'.1 IJ'.2
                          ∘ (extChartAt I p.1).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN)) := by
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hα, _⟩ := hp
    have h_bound := hK_pt_bound p.1 T p.2.1 p.2.2
    have h_K_le : ENNReal.ofReal (K_pt p.1) ≤ ENNReal.ofReal K_max :=
      ENNReal.ofReal_le_ofReal (hK_le_max p.1 hα)
    refine le_trans h_bound ?_
    refine mul_le_mul_left h_K_le _
  have h_sum_p_bd : ∑ p ∈ (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))), (f p) ^ 2 ≤
        ∑ p ∈ (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))),
          ENNReal.ofReal K_max *
            (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
              ∑ j ∈ Finset.range 3,
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) p.1,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M p.1 : M → ℝ)
                        ((extChartAt I p.1).symm ((toEuclidean (E := E)).symm y))) *
                      ‖iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                            T p.1 IJ'.1 IJ'.2
                            ∘ (extChartAt I p.1).symm)
                          ((toEuclidean (E := E)).symm y)‖ ^ 2)
                  ∂(volume : Measure EuclN)) :=
    Finset.sum_le_sum h_per_p
  have h_pull_K :
      ∑ p ∈ (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))),
          ENNReal.ofReal K_max *
            (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
              ∑ j ∈ Finset.range 3,
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) p.1,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M p.1 : M → ℝ)
                        ((extChartAt I p.1).symm ((toEuclidean (E := E)).symm y))) *
                      ‖iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                            T p.1 IJ'.1 IJ'.2
                            ∘ (extChartAt I p.1).symm)
                          ((toEuclidean (E := E)).symm y)‖ ^ 2)
                  ∂(volume : Measure EuclN)) =
      ENNReal.ofReal K_max *
        ∑ p ∈ (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))),
          (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) p.1,
                ENNReal.ofReal
                  (((chartAtlasPOU I M p.1 : M → ℝ)
                      ((extChartAt I p.1).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                          T p.1 IJ'.1 IJ'.2
                          ∘ (extChartAt I p.1).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN)) := by
    rw [Finset.mul_sum]
  have h_sum_collapse_p :
      ∑ p ∈ (S ×ˢ (Finset.univ :
            Finset ((Fin r → Fin n) × (Fin s → Fin n)))),
          (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) p.1,
                ENNReal.ofReal
                  (((chartAtlasPOU I M p.1 : M → ℝ)
                      ((extChartAt I p.1).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                          T p.1 IJ'.1 IJ'.2
                          ∘ (extChartAt I p.1).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN)) =
      (nIJ : ℝ≥0∞) *
        ∑ α ∈ S,
          (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                          T α IJ'.1 IJ'.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN)) := by
    rw [Finset.sum_product]
    have h_inner : ∀ α : M,
        (∑ _IJ : (Fin r → Fin n) × (Fin s → Fin n),
          (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                          T α IJ'.1 IJ'.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN))) =
          (nIJ : ℝ≥0∞) *
            (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
              ∑ j ∈ Finset.range 3,
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      ‖iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                            T α IJ'.1 IJ'.2
                            ∘ (extChartAt I α).symm)
                          ((toEuclidean (E := E)).symm y)‖ ^ 2)
                  ∂(volume : Measure EuclN)) := by
      intro α
      rw [Finset.sum_const, Finset.card_univ, ← hnIJ_def, nsmul_eq_mul]
    rw [show
        (fun α : M => ∑ _IJ : (Fin r → Fin n) × (Fin s → Fin n),
          (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                          T α IJ'.1 IJ'.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN))) =
        (fun α : M => (nIJ : ℝ≥0∞) *
          (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ j ∈ Finset.range 3,
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    ‖iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                          T α IJ'.1 IJ'.2
                          ∘ (extChartAt I α).symm)
                        ((toEuclidean (E := E)).symm y)‖ ^ 2)
                ∂(volume : Measure EuclN))) from by
      funext α; exact h_inner α]
    rw [← Finset.mul_sum]
  have h_inner_eq :
      ∑ α ∈ S,
        (∑ IJ' : (Fin r → Fin n) × (Fin s → Fin n),
          ∑ j ∈ Finset.range 3,
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                        T α IJ'.1 IJ'.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume : Measure EuclN)) =
      W₁ ^ 2 := by
    rw [hW₁_def, tensorPouSobolevNorm_one_sq_eq_agg (I := I) (M := M) g T,
        tensorPouSobolevNormSqAgg_eq_finset_sum (I := I) (M := M) g T, ← hS_def]
  have h_FS_sq_le : FS ^ 2 ≤
      (Nflat : ℝ≥0∞) * (ENNReal.ofReal K_max *
        ((nIJ : ℝ≥0∞) * W₁ ^ 2)) := by
    refine le_trans h_CS ?_
    refine mul_le_mul_right ?_ _
    refine le_trans h_sum_p_bd ?_
    rw [h_pull_K, h_sum_collapse_p, h_inner_eq]
  have h_rearrange :
      (Nflat : ℝ≥0∞) * (ENNReal.ofReal K_max *
          ((nIJ : ℝ≥0∞) * W₁ ^ 2)) =
        ENNReal.ofReal C_sq * W₁ ^ 2 := by
    have h_C_sq_ofReal :
        ENNReal.ofReal C_sq =
          (Nflat : ℝ≥0∞) * (nIJ : ℝ≥0∞) * ENNReal.ofReal K_max := by
      rw [hC_sq_def]
      rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [h_C_sq_ofReal]
    ring
  rw [h_rearrange] at h_FS_sq_le
  have h_C_sq_eq : C_sq = C ^ 2 := by
    rw [hC_def, sq, Real.mul_self_sqrt hC_sq_nn]
  have h_ofReal_C_sq : ENNReal.ofReal C_sq = (ENNReal.ofReal C) ^ 2 := by
    rw [h_C_sq_eq, ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  rw [h_ofReal_C_sq] at h_FS_sq_le
  have h_mul_sq : (ENNReal.ofReal C) ^ 2 * W₁ ^ 2 =
      (ENNReal.ofReal C * W₁) ^ 2 := by
    rw [mul_pow]
  rw [h_mul_sq] at h_FS_sq_le
  rw [hLHS_eq]
  exact (ENNReal.pow_le_pow_left_iff (a := FS)
    (b := ENNReal.ofReal C * W₁) (n := 2) (by norm_num)).mp h_FS_sq_le

end Connection
end Integral
end DifferentialGeometry

end
