import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.FractionalPower
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SemigroupLaw
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def tensorSmoothingConst (μ : ℝ) : ℝ :=
  max 1 ((μ / 2) ^ μ * Real.exp (-μ) * Real.exp 2)

lemma one_le_tensorSmoothingConst (μ : ℝ) : 1 ≤ tensorSmoothingConst μ :=
  le_max_left _ _

lemma tensorSmoothingConst_pos (μ : ℝ) : 0 < tensorSmoothingConst μ :=
  lt_of_lt_of_le one_pos (one_le_tensorSmoothingConst μ)

lemma tensorSmoothingConst_nonneg (μ : ℝ) : 0 ≤ tensorSmoothingConst μ :=
  (tensorSmoothingConst_pos μ).le

private lemma mul_exp_neg_le_exp_neg_one (z : ℝ) :
    z * Real.exp (-z) ≤ Real.exp (-1) := by
  have h1 : z ≤ Real.exp (z - 1) := by
    have h := Real.add_one_le_exp (z - 1)
    linarith
  have hexp_pos : 0 < Real.exp (-z) := Real.exp_pos _
  have h_mul : z * Real.exp (-z) ≤ Real.exp (z - 1) * Real.exp (-z) :=
    mul_le_mul_of_nonneg_right h1 hexp_pos.le
  rw [← Real.exp_add] at h_mul
  have h_sum : z - 1 + -z = -1 := by ring
  rwa [h_sum] at h_mul

private lemma rpow_mul_exp_neg_le (μ : ℝ) (hμ : 0 ≤ μ) {c y : ℝ}
    (hc : 0 < c) (hy : 0 < y) :
    y ^ μ * Real.exp (-(c * y)) ≤ (μ / c) ^ μ * Real.exp (-μ) := by
  rcases eq_or_lt_of_le hμ with hμ0 | hμ_pos
  · subst hμ0
    rw [Real.rpow_zero, Real.rpow_zero, one_mul, one_mul, neg_zero,
      Real.exp_zero]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * y := mul_nonneg hc.le hy.le
    linarith
  · set z : ℝ := c * y / μ with hz_def
    have hz_nn : 0 ≤ z := by
      rw [hz_def]
      exact div_nonneg (mul_nonneg hc.le hy.le) hμ_pos.le
    have hμ_ne : μ ≠ 0 := hμ_pos.ne'
    have hc_ne : c ≠ 0 := hc.ne'
    have hy_eq : y = (μ / c) * z := by
      rw [hz_def]; field_simp
    have hcy_eq : c * y = μ * z := by
      rw [hz_def]; field_simp
    have hzz : z * Real.exp (-z) ≤ Real.exp (-1) :=
      mul_exp_neg_le_exp_neg_one z
    have hzz_nn : 0 ≤ z * Real.exp (-z) :=
      mul_nonneg hz_nn (Real.exp_pos _).le
    have h_pow : (z * Real.exp (-z)) ^ μ ≤ (Real.exp (-1)) ^ μ :=
      Real.rpow_le_rpow hzz_nn hzz hμ
    have hμc_nn : 0 ≤ μ / c := div_nonneg hμ_pos.le hc.le
    have h_exp_mz : Real.exp (-(μ * z)) = Real.exp (-z) ^ μ := by
      rw [← Real.exp_mul]
      congr 1
      ring
    have h_exp_m1 : (Real.exp (-1)) ^ μ = Real.exp (-μ) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    have h_step1 :
        y ^ μ * Real.exp (-(c * y)) =
          ((μ / c) * z) ^ μ * Real.exp (-(μ * z)) := by
      have hy_pow : y ^ μ = ((μ / c) * z) ^ μ := by rw [hy_eq]
      have hy_exp : Real.exp (-(c * y)) = Real.exp (-(μ * z)) := by
        rw [hcy_eq]
      rw [hy_pow, hy_exp]
    calc
      y ^ μ * Real.exp (-(c * y))
          = ((μ / c) * z) ^ μ * Real.exp (-(μ * z)) := h_step1
      _ = (μ / c) ^ μ * z ^ μ * Real.exp (-(μ * z)) := by
            rw [Real.mul_rpow hμc_nn hz_nn]
      _ = (μ / c) ^ μ * (z ^ μ * Real.exp (-z) ^ μ) := by
            rw [h_exp_mz]; ring
      _ = (μ / c) ^ μ * (z * Real.exp (-z)) ^ μ := by
            rw [← Real.mul_rpow hz_nn (Real.exp_pos _).le]
      _ ≤ (μ / c) ^ μ * (Real.exp (-1)) ^ μ :=
            mul_le_mul_of_nonneg_left h_pow (Real.rpow_nonneg hμc_nn μ)
      _ = (μ / c) ^ μ * Real.exp (-μ) := by rw [h_exp_m1]

theorem tensorSmoothingScalarBound {μ : ℝ} (hμ : 0 ≤ μ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    (1 + lam) ^ μ * Real.exp (-(2 * lam * t)) ≤
      tensorSmoothingConst μ * t ^ (-μ) := by
  have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
  have ht_pow_pos : (0 : ℝ) < t ^ (-μ) := Real.rpow_pos_of_pos ht _
  have ht_pow_ge_one : (1 : ℝ) ≤ t ^ (-μ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (neg_nonpos_of_nonneg hμ)
  rcases le_or_gt μ (2 * t) with hμle | hμgt
  · have h_le_one : (1 + lam) ^ μ * Real.exp (-(2 * lam * t)) ≤ 1 := by
      have h_base_le_exp : 1 + lam ≤ Real.exp lam := by
        have := Real.add_one_le_exp lam
        linarith
      have h_pow_le : (1 + lam) ^ μ ≤ (Real.exp lam) ^ μ :=
        Real.rpow_le_rpow hbase_pos.le h_base_le_exp hμ
      have h_exp_pow : (Real.exp lam) ^ μ = Real.exp (lam * μ) :=
        (Real.exp_mul lam μ).symm
      have h_exp_mono : Real.exp (lam * μ) ≤ Real.exp (lam * (2 * t)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hμle hlam
      have h_arg : lam * (2 * t) = 2 * lam * t := by ring
      have h_pow_le' : (1 + lam) ^ μ ≤ Real.exp (2 * lam * t) := by
        rw [h_exp_pow] at h_pow_le
        calc (1 + lam) ^ μ ≤ Real.exp (lam * μ) := h_pow_le
          _ ≤ Real.exp (lam * (2 * t)) := h_exp_mono
          _ = Real.exp (2 * lam * t) := by rw [h_arg]
      have hexp_neg_pos : 0 < Real.exp (-(2 * lam * t)) := Real.exp_pos _
      calc
        (1 + lam) ^ μ * Real.exp (-(2 * lam * t))
            ≤ Real.exp (2 * lam * t) * Real.exp (-(2 * lam * t)) :=
              mul_le_mul_of_nonneg_right h_pow_le' hexp_neg_pos.le
        _ = Real.exp (2 * lam * t + -(2 * lam * t)) := by
              rw [← Real.exp_add]
        _ = 1 := by rw [add_neg_cancel, Real.exp_zero]
    calc
      (1 + lam) ^ μ * Real.exp (-(2 * lam * t)) ≤ 1 := h_le_one
      _ ≤ 1 * t ^ (-μ) := by rw [one_mul]; exact ht_pow_ge_one
      _ ≤ tensorSmoothingConst μ * t ^ (-μ) :=
            mul_le_mul_of_nonneg_right (one_le_tensorSmoothingConst μ)
              ht_pow_pos.le
  · have h2t_pos : (0 : ℝ) < 2 * t := by linarith
    have h_exp_split :
        Real.exp (-(2 * lam * t)) =
          Real.exp (-(2 * t * (1 + lam))) * Real.exp (2 * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h_core :
        (1 + lam) ^ μ * Real.exp (-(2 * t * (1 + lam))) ≤
          (μ / (2 * t)) ^ μ * Real.exp (-μ) :=
      rpow_mul_exp_neg_le μ hμ h2t_pos hbase_pos
    have h_exp2t : Real.exp (2 * t) ≤ Real.exp 2 := by
      apply Real.exp_le_exp.mpr
      linarith
    have h_rpow_split : (μ / (2 * t)) ^ μ = (μ / 2) ^ μ * t ^ (-μ) := by
      have hμ2t_nn : 0 ≤ μ / (2 * t) := div_nonneg hμ h2t_pos.le
      have hμ2_nn : 0 ≤ μ / 2 := by positivity
      have h_factor : μ / (2 * t) = (μ / 2) * t⁻¹ := by
        field_simp
      rw [h_factor, Real.mul_rpow hμ2_nn (by positivity)]
      congr 1
      rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    have hC2_nn : 0 ≤ (μ / 2) ^ μ * Real.exp (-μ) * Real.exp 2 :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) μ)
        (Real.exp_pos _).le) (Real.exp_pos _).le
    have h_le_C2 :
        (1 + lam) ^ μ * Real.exp (-(2 * lam * t)) ≤
          ((μ / 2) ^ μ * Real.exp (-μ) * Real.exp 2) * t ^ (-μ) := by
      calc
        (1 + lam) ^ μ * Real.exp (-(2 * lam * t))
            = (1 + lam) ^ μ * Real.exp (-(2 * t * (1 + lam))) *
                Real.exp (2 * t) := by
              rw [h_exp_split]; ring
        _ ≤ ((μ / (2 * t)) ^ μ * Real.exp (-μ)) * Real.exp 2 := by
              apply mul_le_mul h_core h_exp2t (Real.exp_pos _).le
              exact mul_nonneg (Real.rpow_nonneg
                (div_nonneg hμ h2t_pos.le) μ) (Real.exp_pos _).le
        _ = ((μ / 2) ^ μ * t ^ (-μ)) * Real.exp (-μ) * Real.exp 2 := by
              rw [h_rpow_split]
        _ = ((μ / 2) ^ μ * Real.exp (-μ) * Real.exp 2) * t ^ (-μ) := by
              ring
    refine le_trans h_le_C2 ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) ht_pow_pos.le

theorem tensorSmoothingScalarBound_of_pos {μ : ℝ} (hμ : 0 ≤ μ) {t : ℝ}
    (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    (1 + lam) ^ μ * Real.exp (-(2 * lam * t)) ≤
      tensorSmoothingConst μ * (min t 1) ^ (-μ) := by
  set t' : ℝ := min t 1 with ht'_def
  have ht'_pos : 0 < t' := lt_min ht one_pos
  have ht'_le_one : t' ≤ 1 := min_le_right _ _
  have ht'_le_t : t' ≤ t := min_le_left _ _
  have h_exp_mono :
      Real.exp (-(2 * lam * t)) ≤ Real.exp (-(2 * lam * t')) := by
    apply Real.exp_le_exp.mpr
    have h : 2 * lam * t' ≤ 2 * lam * t :=
      mul_le_mul_of_nonneg_left ht'_le_t (by positivity)
    linarith
  have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ μ :=
    Real.rpow_nonneg (by linarith) μ
  calc
    (1 + lam) ^ μ * Real.exp (-(2 * lam * t))
        ≤ (1 + lam) ^ μ * Real.exp (-(2 * lam * t')) :=
          mul_le_mul_of_nonneg_left h_exp_mono hbase_nn
    _ ≤ tensorSmoothingConst μ * t' ^ (-μ) :=
          tensorSmoothingScalarBound hμ ht'_pos ht'_le_one hlam

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorHeat_weight_term_le {g : SmoothRiemannianMetric I M}
    {r s : ℕ} (i : TensorEigenIdx (I := I) (M := M) g r s)
    (a b : ℝ) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i b *
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) * c) ^ 2 ≤
      max 1 (tensorSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) *
        (tensorSobolevWeight (I := I) (M := M) i a * c ^ 2) := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
  set K : ℝ :=
    max 1 (tensorSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) with hK_def
  have hK_ge_one : (1 : ℝ) ≤ K := le_max_left _ _
  have h_weight_split :
      tensorSobolevWeight (I := I) (M := M) i b =
        tensorSobolevWeight (I := I) (M := M) i a *
          (1 + lam) ^ (b - a) := by
    unfold tensorSobolevWeight
    rw [hlam_def, ← Real.rpow_add hbase_pos]
    congr 1
    ring
  have h_pe_le :
      (1 + lam) ^ (b - a) *
          Real.exp (-(lam * t) * 2) ≤ K := by
    rcases le_or_gt 0 (b - a) with hba | hba
    · have h_arg : -(lam * t) * 2 = -(2 * lam * t) := by ring
      rw [h_arg]
      have h := tensorSmoothingScalarBound_of_pos hba ht hlam_nn
      exact le_trans h (le_max_right _ _)
    · have h_w_le_one : (1 + lam) ^ (b - a) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hba.le
      have h_exp_le_one : Real.exp (-(lam * t) * 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ lam * t := mul_nonneg hlam_nn ht.le
        nlinarith
      calc
        (1 + lam) ^ (b - a) * Real.exp (-(lam * t) * 2)
            ≤ 1 * 1 :=
              mul_le_mul (le_trans h_w_le_one (le_refl 1)) h_exp_le_one
                (Real.exp_pos _).le (by norm_num)
        _ = 1 := by norm_num
        _ ≤ K := hK_ge_one
  have hwa_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hexp_sq :
      (Real.exp (-lam * t)) ^ 2 = Real.exp (-(lam * t) * 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    tensorSobolevWeight (I := I) (M := M) i b *
          (Real.exp (-lam * t) * c) ^ 2
        = (tensorSobolevWeight (I := I) (M := M) i a * c ^ 2) *
            ((1 + lam) ^ (b - a) * (Real.exp (-lam * t)) ^ 2) := by
          rw [h_weight_split]; ring
    _ = (tensorSobolevWeight (I := I) (M := M) i a * c ^ 2) *
          ((1 + lam) ^ (b - a) * Real.exp (-(lam * t) * 2)) := by
          rw [hexp_sq]
    _ ≤ (tensorSobolevWeight (I := I) (M := M) i a * c ^ 2) * K := by
          apply mul_le_mul_of_nonneg_left h_pe_le
          have : 0 ≤ c ^ 2 := sq_nonneg c
          positivity
    _ = K * (tensorSobolevWeight (I := I) (M := M) i a * c ^ 2) := by ring

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma heatHs_weighted_summable {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : tensorHs (I := I) (M := M) g r s a) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i b *
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          T.coeff i) ^ 2) := by
  set K : ℝ :=
    max 1 (tensorSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) with hK_def
  refine Summable.of_nonneg_of_le ?_ ?_ (T.weighted_summable.mul_left K)
  · intro i
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i b :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i b
    positivity
  · intro i
    exact tensorHeat_weight_term_le (I := I) (M := M) i a b ht (T.coeff i)

def heatHsFun {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : tensorHs (I := I) (M := M) g r s a) :
    tensorHs (I := I) (M := M) g r s b where
  coeff i := Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
    T.coeff i
  weighted_summable := heatHs_weighted_summable (I := I) (M := M) b ht T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma heatHsFun_coeff {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : tensorHs (I := I) (M := M) g r s a)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (heatHsFun (I := I) (M := M) b ht T).coeff i =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma heatHsFun_add {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (S T : tensorHs (I := I) (M := M) g r s a) :
    heatHsFun (I := I) (M := M) b ht (S + T) =
      heatHsFun (I := I) (M := M) b ht S +
        heatHsFun (I := I) (M := M) b ht T := by
  ext i
  simp only [heatHsFun_coeff, add_coeff]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma heatHsFun_smul {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s a) :
    heatHsFun (I := I) (M := M) b ht (c • T) =
      c • heatHsFun (I := I) (M := M) b ht T := by
  ext i
  simp only [heatHsFun_coeff, smul_coeff]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_heatHsFun_le_smoothing {a b : ℝ} (hab : a ≤ b) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (T : tensorHs (I := I) (M := M) g r s a) :
    ‖heatHsFun (I := I) (M := M) b ht T‖ ≤
      Real.sqrt (tensorSmoothingConst (b - a)) *
        t ^ (-((b - a) / 2)) * ‖T‖ := by
  have hba_nn : 0 ≤ b - a := by linarith
  have hC_nn : 0 ≤ tensorSmoothingConst (b - a) :=
    tensorSmoothingConst_nonneg (b - a)
  have h_b_sq : ‖heatHsFun (I := I) (M := M) b ht T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i b *
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (heatHsFun (I := I) (M := M) b ht T)
    simpa only [heatHsFun_coeff] using h
  have h_a_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_term_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i b *
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2 ≤
        (tensorSmoothingConst (b - a) * t ^ (-(b - a))) *
          (tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2) := by
    intro i
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have h_weight_split :
        tensorSobolevWeight (I := I) (M := M) i b =
          tensorSobolevWeight (I := I) (M := M) i a *
            (1 + lam) ^ (b - a) := by
      unfold tensorSobolevWeight
      rw [hlam_def, ← Real.rpow_add hbase_pos]
      congr 1
      ring
    have hexp_sq :
        (Real.exp (-lam * t)) ^ 2 = Real.exp (-(2 * lam * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h_scalar :
        (1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t)) ≤
          tensorSmoothingConst (b - a) * t ^ (-(b - a)) :=
      tensorSmoothingScalarBound hba_nn ht ht1 hlam_nn
    have hwa_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i a
    have hc2_nn : 0 ≤ (T.coeff i) ^ 2 := sq_nonneg _
    calc
      tensorSobolevWeight (I := I) (M := M) i b *
            (Real.exp (-lam * t) * T.coeff i) ^ 2
          = (tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2) *
              ((1 + lam) ^ (b - a) * (Real.exp (-lam * t)) ^ 2) := by
            rw [h_weight_split]; ring
      _ = (tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2) *
            ((1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t))) := by
            rw [hexp_sq]
      _ ≤ (tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2) *
            (tensorSmoothingConst (b - a) * t ^ (-(b - a))) := by
            apply mul_le_mul_of_nonneg_left h_scalar
            positivity
      _ = (tensorSmoothingConst (b - a) * t ^ (-(b - a))) *
            (tensorSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) := by ring
  have h_summ_b :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i b *
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2) :=
    heatHs_weighted_summable (I := I) (M := M) b ht T
  have h_summ_dom :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (tensorSmoothingConst (b - a) * t ^ (-(b - a))) *
          (tensorSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2)) :=
    T.weighted_summable.mul_left _
  have h_tsum_le :
      ∑' i, tensorSobolevWeight (I := I) (M := M) i b *
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2 ≤
        ∑' i, (tensorSmoothingConst (b - a) * t ^ (-(b - a))) *
          (tensorSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2) :=
    Summable.tsum_le_tsum h_term_le h_summ_b h_summ_dom
  have h_tsum_factor :
      ∑' i, (tensorSmoothingConst (b - a) * t ^ (-(b - a))) *
          (tensorSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2) =
        (tensorSmoothingConst (b - a) * t ^ (-(b - a))) *
          ∑' i, (tensorSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2) :=
    tsum_mul_left
  have h_sq_le : ‖heatHsFun (I := I) (M := M) b ht T‖ ^ 2 ≤
      (tensorSmoothingConst (b - a) * t ^ (-(b - a))) * ‖T‖ ^ 2 := by
    rw [h_b_sq, h_a_sq]
    calc
      ∑' i, tensorSobolevWeight (I := I) (M := M) i b *
            (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
              T.coeff i) ^ 2
          ≤ ∑' i, (tensorSmoothingConst (b - a) * t ^ (-(b - a))) *
              (tensorSobolevWeight (I := I) (M := M) i a *
                (T.coeff i) ^ 2) := h_tsum_le
      _ = (tensorSmoothingConst (b - a) * t ^ (-(b - a))) *
            ∑' i, (tensorSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) := h_tsum_factor
  have h_rhs_sq :
      (Real.sqrt (tensorSmoothingConst (b - a)) * t ^ (-((b - a) / 2))) ^ 2 =
        tensorSmoothingConst (b - a) * t ^ (-(b - a)) := by
    have h_sqrt_sq :
        Real.sqrt (tensorSmoothingConst (b - a)) ^ 2 =
          tensorSmoothingConst (b - a) :=
      Real.sq_sqrt hC_nn
    have h_t_sq : (t ^ (-((b - a) / 2))) ^ 2 = t ^ (-(b - a)) := by
      rw [← Real.rpow_natCast (t ^ (-((b - a) / 2))) 2,
        ← Real.rpow_mul ht.le]
      congr 1
      push_cast
      ring
    calc
      (Real.sqrt (tensorSmoothingConst (b - a)) * t ^ (-((b - a) / 2))) ^ 2
          = Real.sqrt (tensorSmoothingConst (b - a)) ^ 2 *
              (t ^ (-((b - a) / 2))) ^ 2 := by ring
      _ = tensorSmoothingConst (b - a) * t ^ (-(b - a)) := by
            rw [h_sqrt_sq, h_t_sq]
  have h_final_sq : ‖heatHsFun (I := I) (M := M) b ht T‖ ^ 2 ≤
      (Real.sqrt (tensorSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
        ‖T‖) ^ 2 := by
    have h_expand :
        (Real.sqrt (tensorSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
            ‖T‖) ^ 2 =
          (Real.sqrt (tensorSmoothingConst (b - a)) *
              t ^ (-((b - a) / 2))) ^ 2 * ‖T‖ ^ 2 := by
      ring
    rw [h_expand, h_rhs_sq]
    exact h_sq_le
  have h_lhs_nn : 0 ≤ ‖heatHsFun (I := I) (M := M) b ht T‖ := norm_nonneg _
  have h_rhs_nn :
      0 ≤ Real.sqrt (tensorSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
        ‖T‖ := by
    have h1 : 0 ≤ Real.sqrt (tensorSmoothingConst (b - a)) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ ‖T‖ := norm_nonneg T
    have h3 : 0 ≤ t ^ (-((b - a) / 2)) := (Real.rpow_pos_of_pos ht _).le
    positivity
  nlinarith [h_final_sq, h_lhs_nn, h_rhs_nn]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_heatHsFun_le_self {a : ℝ} {t : ℝ} (ht : 0 < t)
    (T : tensorHs (I := I) (M := M) g r s a) :
    ‖heatHsFun (I := I) (M := M) a ht T‖ ≤ ‖T‖ := by
  have h_a_sq_heat : ‖heatHsFun (I := I) (M := M) a ht T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i a *
        (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (heatHsFun (I := I) (M := M) a ht T)
    simpa only [heatHsFun_coeff] using h
  have h_a_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_term_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i a *
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 := by
    intro i
    set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hwa_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i a
    have h_exp_le_one :
        Real.exp (-lam * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ lam * t := mul_nonneg hlam_nn ht.le
      nlinarith
    have h_exp_nn : 0 ≤ Real.exp (-lam * t) := (Real.exp_pos _).le
    have h_sq_le : (Real.exp (-lam * t) * T.coeff i) ^ 2 ≤ (T.coeff i) ^ 2 := by
      have h_exp_sq_le : (Real.exp (-lam * t)) ^ 2 ≤ 1 := by
        nlinarith [h_exp_le_one, h_exp_nn]
      have hc2 : 0 ≤ (T.coeff i) ^ 2 := sq_nonneg _
      calc
        (Real.exp (-lam * t) * T.coeff i) ^ 2
            = (Real.exp (-lam * t)) ^ 2 * (T.coeff i) ^ 2 := by ring
        _ ≤ 1 * (T.coeff i) ^ 2 :=
              mul_le_mul_of_nonneg_right h_exp_sq_le hc2
        _ = (T.coeff i) ^ 2 := one_mul _
    exact mul_le_mul_of_nonneg_left h_sq_le hwa_nn
  have h_summ_heat :
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i a *
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2) :=
    heatHs_weighted_summable (I := I) (M := M) a ht T
  have h_tsum_le :
      ∑' i, tensorSobolevWeight (I := I) (M := M) i a *
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2 ≤
        ∑' i, tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_term_le h_summ_heat T.weighted_summable
  have h_sq_le : ‖heatHsFun (I := I) (M := M) a ht T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_a_sq_heat, h_a_sq]
    exact h_tsum_le
  have h1 : 0 ≤ ‖heatHsFun (I := I) (M := M) a ht T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end tensorHs

def tensorHeatSemigroupHs {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {t : ℝ} (ht : 0 < t)
    {a b : ℝ} :
    tensorHs (I := I) (M := M) g r s a →L[ℝ]
      tensorHs (I := I) (M := M) g r s b :=
  LinearMap.mkContinuous
    { toFun := tensorHs.heatHsFun (I := I) (M := M) b ht
      map_add' := tensorHs.heatHsFun_add (I := I) (M := M) b ht
      map_smul' := fun c T =>
        tensorHs.heatHsFun_smul (I := I) (M := M) b ht c T }
    (max 1 (tensorSmoothingConst (b - a) * (min t 1) ^ (-(b - a))))
    (fun T => by
      change ‖tensorHs.heatHsFun (I := I) (M := M) b ht T‖ ≤ _
      set K : ℝ :=
        max 1 (tensorSmoothingConst (b - a) * (min t 1) ^ (-(b - a)))
        with hK_def
      have hK_ge_one : (1 : ℝ) ≤ K := le_max_left _ _
      have hK_nn : 0 ≤ K := le_trans zero_le_one hK_ge_one
      have h_b_sq : ‖tensorHs.heatHsFun (I := I) (M := M) b ht T‖ ^ 2 =
          ∑' i, tensorSobolevWeight (I := I) (M := M) i b *
            (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
              T.coeff i) ^ 2 := by
        have h := tensorHs.norm_sq_eq_tsum (I := I) (M := M)
          (tensorHs.heatHsFun (I := I) (M := M) b ht T)
        simpa only [tensorHs.heatHsFun_coeff] using h
      have h_a_sq : ‖T‖ ^ 2 =
          ∑' i, tensorSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2 :=
        tensorHs.norm_sq_eq_tsum (I := I) (M := M) T
      have h_term_le : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          tensorSobolevWeight (I := I) (M := M) i b *
              (Real.exp
                  (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
                T.coeff i) ^ 2 ≤
            K * (tensorSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) := by
        intro i
        exact tensorHeat_weight_term_le (I := I) (M := M) i a b ht
          (T.coeff i)
      have h_summ_b :
          Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
            tensorSobolevWeight (I := I) (M := M) i b *
              (Real.exp
                  (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
                T.coeff i) ^ 2) :=
        tensorHs.heatHs_weighted_summable (I := I) (M := M) b ht T
      have h_summ_dom :
          Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
            K * (tensorSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2)) :=
        T.weighted_summable.mul_left K
      have h_tsum_le :
          ∑' i, tensorSobolevWeight (I := I) (M := M) i b *
              (Real.exp
                  (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
                T.coeff i) ^ 2 ≤
            ∑' i, K * (tensorSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) :=
        Summable.tsum_le_tsum h_term_le h_summ_b h_summ_dom
      have h_tsum_factor :
          ∑' i, K * (tensorSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) =
            K * ∑' i, (tensorSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) :=
        tsum_mul_left
      have h_sq_le :
          ‖tensorHs.heatHsFun (I := I) (M := M) b ht T‖ ^ 2 ≤
            K * ‖T‖ ^ 2 := by
        rw [h_b_sq, h_a_sq]
        rw [← h_tsum_factor]
        exact h_tsum_le
      have h_sqrtK_sq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK_nn
      have h_final_sq :
          ‖tensorHs.heatHsFun (I := I) (M := M) b ht T‖ ^ 2 ≤
            (Real.sqrt K * ‖T‖) ^ 2 := by
        have h_expand : (Real.sqrt K * ‖T‖) ^ 2 = K * ‖T‖ ^ 2 := by
          rw [mul_pow, h_sqrtK_sq]
        rw [h_expand]
        exact h_sq_le
      have h1 : 0 ≤ ‖tensorHs.heatHsFun (I := I) (M := M) b ht T‖ :=
        norm_nonneg _
      have h2 : 0 ≤ ‖T‖ := norm_nonneg T
      have h_sqrtK_nn : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
      have h_norm_le_sqrt :
          ‖tensorHs.heatHsFun (I := I) (M := M) b ht T‖ ≤
            Real.sqrt K * ‖T‖ := by
        nlinarith [h_final_sq, h1, mul_nonneg h_sqrtK_nn h2]
      have h_sqrtK_le_K : Real.sqrt K ≤ K := by
        have h_K_le_sq : K ≤ K ^ 2 := by nlinarith [hK_ge_one]
        calc Real.sqrt K ≤ Real.sqrt (K ^ 2) :=
              Real.sqrt_le_sqrt h_K_le_sq
          _ = K := Real.sqrt_sq hK_nn
      calc
        ‖tensorHs.heatHsFun (I := I) (M := M) b ht T‖ ≤ Real.sqrt K * ‖T‖ :=
          h_norm_le_sqrt
        _ ≤ K * ‖T‖ := mul_le_mul_of_nonneg_right h_sqrtK_le_K h2)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorHeatSemigroupHs_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {t : ℝ}
    (ht : 0 < t) {a b : ℝ}
    (T : tensorHs (I := I) (M := M) g r s a) :
    tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) ht (a := a) (b := b) T =
      tensorHs.heatHsFun (I := I) (M := M) b ht T := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHeatSemigroupHs_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {t : ℝ}
    (ht : 0 < t) {a b : ℝ}
    (T : tensorHs (I := I) (M := M) g r s a)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) ht (a := a) (b := b)
        T).coeff i =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHs_opNorm_le {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    {a b : ℝ} (hab : a ≤ b) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) ht (a := a) (b := b)‖ ≤
      Real.sqrt (tensorSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) := by
  have h_bound_nn :
      0 ≤ Real.sqrt (tensorSmoothingConst (b - a)) *
        t ^ (-((b - a) / 2)) := by
    have h1 : 0 ≤ Real.sqrt (tensorSmoothingConst (b - a)) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ t ^ (-((b - a) / 2)) :=
      (Real.rpow_pos_of_pos ht _).le
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h_bound_nn (fun T => ?_)
  rw [tensorHeatSemigroupHs_apply]
  exact tensorHs.norm_heatHsFun_le_smoothing (I := I) (M := M) hab ht ht1 T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHs_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {a : ℝ}
    {t : ℝ} (ht : 0 < t) :
    ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) ht (a := a) (b := a)‖ ≤
      1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => ?_)
  rw [tensorHeatSemigroupHs_apply, one_mul]
  exact tensorHs.norm_heatHsFun_le_self (I := I) (M := M) ht T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHs_add {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) {a b c : ℝ}
    (T : tensorHs (I := I) (M := M) g r s a) :
    tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) (show (0:ℝ) < t + u by
        linarith) (a := a) (b := b) T =
      tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) ht (a := c) (b := b)
        (tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) hu (a := a) (b := c)
          T) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHeatSemigroupHs_coeff, tensorHeatSemigroupHs_coeff,
    tensorHeatSemigroupHs_coeff]
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have h_exp_add :
      Real.exp (-lam * (t + u)) =
        Real.exp (-lam * t) * Real.exp (-lam * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_exp_add]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHs_add_comp {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) {a : ℝ} :
    tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (0:ℝ) < t + u by linarith) (a := a) (b := a) =
      (tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) ht
          (a := a) (b := a)).comp
        (tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) hu
          (a := a) (b := a)) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rw [ContinuousLinearMap.comp_apply]
  exact tensorHeatSemigroupHs_add (I := I) (M := M) ht hu
    (a := a) (b := a) (c := a) T

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {t : ℝ} (ht : 0 < t)
    (a b : ℝ) :
    tensorHs (I := I) (M := M) g r s a →L[ℝ]
      tensorHs (I := I) (M := M) g r s b :=
  tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := r) (s := s) ht (a := a) (b := b)

example {μ : ℝ} (hμ : 0 ≤ μ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (1 + lam) ^ μ * Real.exp (-(2 * lam * t)) ≤
      tensorSmoothingConst μ * t ^ (-μ) :=
  tensorSmoothingScalarBound hμ ht ht1 hlam

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
