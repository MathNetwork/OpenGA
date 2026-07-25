import DifferentialGeometry.Analysis.Sobolev.Hs.Inclusion
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingConst
import DifferentialGeometry.Analysis.Heat.Semigroup.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.Spectral
open DifferentialGeometry.Analysis.SpectralBounds

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def heatCoeffFun {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) (t : ℝ) (c : ℝ) : ℝ :=
  Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) * c

omit [NeZero (Module.finrank ℝ E)] in
private lemma heatHk_weight_term_le {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g)
    (a b : ℝ) {t : ℝ} (ht : 0 < t) (c : ℝ) :
    scalarSobolevWeight (I := I) (M := M) i b *
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) * c) ^ 2 ≤
      max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) *
        (scalarSobolevWeight (I := I) (M := M) i a * c ^ 2) := by
  set lam := EigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nn : 0 ≤ lam := EigenIdx.lambda_nonneg (I := I) (M := M) i
  have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
  set K : ℝ :=
    max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) with hK_def
  have hK_ge_one : (1 : ℝ) ≤ K := le_max_left _ _
  have h_weight_split :
      scalarSobolevWeight (I := I) (M := M) i b =
        scalarSobolevWeight (I := I) (M := M) i a *
          (1 + lam) ^ (b - a) := by
    unfold scalarSobolevWeight
    rw [hlam_def, ← Real.rpow_add hbase_pos]
    congr 1
    ring
  have h_pe_le :
      (1 + lam) ^ (b - a) *
          Real.exp (-(lam * t) * 2) ≤ K := by
    rcases le_or_gt 0 (b - a) with hba | hba
    · have h_arg : -(lam * t) * 2 = -(2 * lam * t) := by ring
      rw [h_arg]
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
      have hbase_nn : (0 : ℝ) ≤ (1 + lam) ^ (b - a) :=
        Real.rpow_nonneg (by linarith) (b - a)
      have h_at_t' : (1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t')) ≤
          spectralSmoothingConst (b - a) * t' ^ (-(b - a)) :=
        spectralSmoothingScalarBound hba ht'_pos ht'_le_one hlam_nn
      calc
        (1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t))
            ≤ (1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t')) :=
              mul_le_mul_of_nonneg_left h_exp_mono hbase_nn
        _ ≤ spectralSmoothingConst (b - a) * t' ^ (-(b - a)) := h_at_t'
        _ ≤ K := le_max_right _ _
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
  have hwa_nn : 0 ≤ scalarSobolevWeight (I := I) (M := M) i a :=
    scalarSobolevWeight_nonneg (I := I) (M := M) i a
  have hexp_sq :
      (Real.exp (-lam * t)) ^ 2 = Real.exp (-(lam * t) * 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    scalarSobolevWeight (I := I) (M := M) i b *
          (Real.exp (-lam * t) * c) ^ 2
        = (scalarSobolevWeight (I := I) (M := M) i a * c ^ 2) *
            ((1 + lam) ^ (b - a) * (Real.exp (-lam * t)) ^ 2) := by
          rw [h_weight_split]; ring
    _ = (scalarSobolevWeight (I := I) (M := M) i a * c ^ 2) *
          ((1 + lam) ^ (b - a) * Real.exp (-(lam * t) * 2)) := by
          rw [hexp_sq]
    _ ≤ (scalarSobolevWeight (I := I) (M := M) i a * c ^ 2) * K := by
          apply mul_le_mul_of_nonneg_left h_pe_le
          have : 0 ≤ c ^ 2 := sq_nonneg c
          positivity
    _ = K * (scalarSobolevWeight (I := I) (M := M) i a * c ^ 2) := by ring

namespace scalarHs

variable {g : SmoothRiemannianMetric I M}

omit [NeZero (Module.finrank ℝ E)] in
lemma heatHk_weighted_summable {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : scalarHs (I := I) (M := M) g a) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i b *
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          T.coeff i) ^ 2) := by
  set K : ℝ :=
    max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a))) with hK_def
  refine Summable.of_nonneg_of_le ?_ ?_ (T.weighted_summable.mul_left K)
  · intro i
    have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i b :=
      scalarSobolevWeight_nonneg (I := I) (M := M) i b
    positivity
  · intro i
    exact heatHk_weight_term_le (I := I) (M := M) i a b ht (T.coeff i)

def heatHkFun {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : scalarHs (I := I) (M := M) g a) :
    scalarHs (I := I) (M := M) g b where
  coeff i := Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
    T.coeff i
  weighted_summable := heatHk_weighted_summable (I := I) (M := M) b ht T

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma heatHkFun_coeff {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (T : scalarHs (I := I) (M := M) g a)
    (i : EigenIdx (I := I) (M := M) g) :
    (heatHkFun (I := I) (M := M) b ht T).coeff i =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        T.coeff i := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma heatHkFun_add {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t)
    (S T : scalarHs (I := I) (M := M) g a) :
    heatHkFun (I := I) (M := M) b ht (S + T) =
      heatHkFun (I := I) (M := M) b ht S +
        heatHkFun (I := I) (M := M) b ht T := by
  ext i
  simp only [heatHkFun_coeff, add_coeff]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma heatHkFun_smul {a : ℝ} (b : ℝ) {t : ℝ} (ht : 0 < t) (c : ℝ)
    (T : scalarHs (I := I) (M := M) g a) :
    heatHkFun (I := I) (M := M) b ht (c • T) =
      c • heatHkFun (I := I) (M := M) b ht T := by
  ext i
  simp only [heatHkFun_coeff, smul_coeff]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_heatHkFun_le_smoothing {a b : ℝ} (hab : a ≤ b) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (T : scalarHs (I := I) (M := M) g a) :
    ‖heatHkFun (I := I) (M := M) b ht T‖ ≤
      Real.sqrt (spectralSmoothingConst (b - a)) *
        t ^ (-((b - a) / 2)) * ‖T‖ := by
  have hba_nn : 0 ≤ b - a := by linarith
  have hC_nn : 0 ≤ spectralSmoothingConst (b - a) :=
    spectralSmoothingConst_nonneg (b - a)
  have h_b_sq : ‖heatHkFun (I := I) (M := M) b ht T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i b *
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (heatHkFun (I := I) (M := M) b ht T)
    simpa only [heatHkFun_coeff] using h
  have h_a_sq : ‖T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_term_le : ∀ i : EigenIdx (I := I) (M := M) g,
      scalarSobolevWeight (I := I) (M := M) i b *
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2 ≤
        (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          (scalarSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2) := by
    intro i
    set lam := EigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := EigenIdx.lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have h_weight_split :
        scalarSobolevWeight (I := I) (M := M) i b =
          scalarSobolevWeight (I := I) (M := M) i a *
            (1 + lam) ^ (b - a) := by
      unfold scalarSobolevWeight
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
          spectralSmoothingConst (b - a) * t ^ (-(b - a)) :=
      spectralSmoothingScalarBound hba_nn ht ht1 hlam_nn
    have hwa_nn : 0 ≤ scalarSobolevWeight (I := I) (M := M) i a :=
      scalarSobolevWeight_nonneg (I := I) (M := M) i a
    have hc2_nn : 0 ≤ (T.coeff i) ^ 2 := sq_nonneg _
    calc
      scalarSobolevWeight (I := I) (M := M) i b *
            (Real.exp (-lam * t) * T.coeff i) ^ 2
          = (scalarSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2) *
              ((1 + lam) ^ (b - a) * (Real.exp (-lam * t)) ^ 2) := by
            rw [h_weight_split]; ring
      _ = (scalarSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2) *
            ((1 + lam) ^ (b - a) * Real.exp (-(2 * lam * t))) := by
            rw [hexp_sq]
      _ ≤ (scalarSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2) *
            (spectralSmoothingConst (b - a) * t ^ (-(b - a))) := by
            apply mul_le_mul_of_nonneg_left h_scalar
            positivity
      _ = (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
            (scalarSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) := by ring
  have h_summ_b :
      Summable (fun i : EigenIdx (I := I) (M := M) g =>
        scalarSobolevWeight (I := I) (M := M) i b *
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2) :=
    heatHk_weighted_summable (I := I) (M := M) b ht T
  have h_summ_dom :
      Summable (fun i : EigenIdx (I := I) (M := M) g =>
        (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          (scalarSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2)) :=
    T.weighted_summable.mul_left _
  have h_tsum_le :
      ∑' i, scalarSobolevWeight (I := I) (M := M) i b *
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2 ≤
        ∑' i, (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          (scalarSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2) :=
    Summable.tsum_le_tsum h_term_le h_summ_b h_summ_dom
  have h_tsum_factor :
      ∑' i, (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          (scalarSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2) =
        (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
          ∑' i, (scalarSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2) :=
    tsum_mul_left
  have h_sq_le : ‖heatHkFun (I := I) (M := M) b ht T‖ ^ 2 ≤
      (spectralSmoothingConst (b - a) * t ^ (-(b - a))) * ‖T‖ ^ 2 := by
    rw [h_b_sq, h_a_sq]
    calc
      ∑' i, scalarSobolevWeight (I := I) (M := M) i b *
            (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
              T.coeff i) ^ 2
          ≤ ∑' i, (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
              (scalarSobolevWeight (I := I) (M := M) i a *
                (T.coeff i) ^ 2) := h_tsum_le
      _ = (spectralSmoothingConst (b - a) * t ^ (-(b - a))) *
            ∑' i, (scalarSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) := h_tsum_factor
  have h_rhs_sq :
      (Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2))) ^ 2 =
        spectralSmoothingConst (b - a) * t ^ (-(b - a)) := by
    have h_sqrt_sq :
        Real.sqrt (spectralSmoothingConst (b - a)) ^ 2 =
          spectralSmoothingConst (b - a) :=
      Real.sq_sqrt hC_nn
    have h_t_sq : (t ^ (-((b - a) / 2))) ^ 2 = t ^ (-(b - a)) := by
      rw [← Real.rpow_natCast (t ^ (-((b - a) / 2))) 2,
        ← Real.rpow_mul ht.le]
      congr 1
      push_cast
      ring
    calc
      (Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2))) ^ 2
          = Real.sqrt (spectralSmoothingConst (b - a)) ^ 2 *
              (t ^ (-((b - a) / 2))) ^ 2 := by ring
      _ = spectralSmoothingConst (b - a) * t ^ (-(b - a)) := by
            rw [h_sqrt_sq, h_t_sq]
  have h_final_sq : ‖heatHkFun (I := I) (M := M) b ht T‖ ^ 2 ≤
      (Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
        ‖T‖) ^ 2 := by
    have h_expand :
        (Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
            ‖T‖) ^ 2 =
          (Real.sqrt (spectralSmoothingConst (b - a)) *
              t ^ (-((b - a) / 2))) ^ 2 * ‖T‖ ^ 2 := by
      ring
    rw [h_expand, h_rhs_sq]
    exact h_sq_le
  have h_lhs_nn : 0 ≤ ‖heatHkFun (I := I) (M := M) b ht T‖ := norm_nonneg _
  have h_rhs_nn :
      0 ≤ Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) *
        ‖T‖ := by
    have h1 : 0 ≤ Real.sqrt (spectralSmoothingConst (b - a)) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ ‖T‖ := norm_nonneg T
    have h3 : 0 ≤ t ^ (-((b - a) / 2)) := (Real.rpow_pos_of_pos ht _).le
    positivity
  nlinarith [h_final_sq, h_lhs_nn, h_rhs_nn]

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_heatHkFun_le_self {a : ℝ} {t : ℝ} (ht : 0 < t)
    (T : scalarHs (I := I) (M := M) g a) :
    ‖heatHkFun (I := I) (M := M) a ht T‖ ≤ ‖T‖ := by
  have h_a_sq_heat : ‖heatHkFun (I := I) (M := M) a ht T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i a *
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (heatHkFun (I := I) (M := M) a ht T)
    simpa only [heatHkFun_coeff] using h
  have h_a_sq : ‖T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_term_le : ∀ i : EigenIdx (I := I) (M := M) g,
      scalarSobolevWeight (I := I) (M := M) i a *
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2 ≤
        scalarSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 := by
    intro i
    set lam := EigenIdx.lambda (I := I) (M := M) i with hlam_def
    have hlam_nn : 0 ≤ lam := EigenIdx.lambda_nonneg (I := I) (M := M) i
    have hwa_nn : 0 ≤ scalarSobolevWeight (I := I) (M := M) i a :=
      scalarSobolevWeight_nonneg (I := I) (M := M) i a
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
      Summable (fun i : EigenIdx (I := I) (M := M) g =>
        scalarSobolevWeight (I := I) (M := M) i a *
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2) :=
    heatHk_weighted_summable (I := I) (M := M) a ht T
  have h_tsum_le :
      ∑' i, scalarSobolevWeight (I := I) (M := M) i a *
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) ^ 2 ≤
        ∑' i, scalarSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_term_le h_summ_heat T.weighted_summable
  have h_sq_le : ‖heatHkFun (I := I) (M := M) a ht T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_a_sq_heat, h_a_sq]
    exact h_tsum_le
  have h1 : 0 ≤ ‖heatHkFun (I := I) (M := M) a ht T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end scalarHs

def heatSemigroupHs {g : SmoothRiemannianMetric I M}
    {t : ℝ} (ht : 0 < t) {a b : ℝ} :
    scalarHs (I := I) (M := M) g a →L[ℝ]
      scalarHs (I := I) (M := M) g b :=
  LinearMap.mkContinuous
    { toFun := scalarHs.heatHkFun (I := I) (M := M) b ht
      map_add' := scalarHs.heatHkFun_add (I := I) (M := M) b ht
      map_smul' := fun c T =>
        scalarHs.heatHkFun_smul (I := I) (M := M) b ht c T }
    (max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a))))
    (fun T => by
      change ‖scalarHs.heatHkFun (I := I) (M := M) b ht T‖ ≤ _
      set K : ℝ :=
        max 1 (spectralSmoothingConst (b - a) * (min t 1) ^ (-(b - a)))
        with hK_def
      have hK_ge_one : (1 : ℝ) ≤ K := le_max_left _ _
      have hK_nn : 0 ≤ K := le_trans zero_le_one hK_ge_one
      have h_b_sq : ‖scalarHs.heatHkFun (I := I) (M := M) b ht T‖ ^ 2 =
          ∑' i, scalarSobolevWeight (I := I) (M := M) i b *
            (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
              T.coeff i) ^ 2 := by
        have h := scalarHs.norm_sq_eq_tsum (I := I) (M := M)
          (scalarHs.heatHkFun (I := I) (M := M) b ht T)
        simpa only [scalarHs.heatHkFun_coeff] using h
      have h_a_sq : ‖T‖ ^ 2 =
          ∑' i, scalarSobolevWeight (I := I) (M := M) i a *
            (T.coeff i) ^ 2 :=
        scalarHs.norm_sq_eq_tsum (I := I) (M := M) T
      have h_term_le : ∀ i : EigenIdx (I := I) (M := M) g,
          scalarSobolevWeight (I := I) (M := M) i b *
              (Real.exp
                  (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
                T.coeff i) ^ 2 ≤
            K * (scalarSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) := by
        intro i
        exact heatHk_weight_term_le (I := I) (M := M) i a b ht (T.coeff i)
      have h_summ_b :
          Summable (fun i : EigenIdx (I := I) (M := M) g =>
            scalarSobolevWeight (I := I) (M := M) i b *
              (Real.exp
                  (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
                T.coeff i) ^ 2) :=
        scalarHs.heatHk_weighted_summable (I := I) (M := M) b ht T
      have h_summ_dom :
          Summable (fun i : EigenIdx (I := I) (M := M) g =>
            K * (scalarSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2)) :=
        T.weighted_summable.mul_left K
      have h_tsum_le :
          ∑' i, scalarSobolevWeight (I := I) (M := M) i b *
              (Real.exp
                  (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
                T.coeff i) ^ 2 ≤
            ∑' i, K * (scalarSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) :=
        Summable.tsum_le_tsum h_term_le h_summ_b h_summ_dom
      have h_tsum_factor :
          ∑' i, K * (scalarSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) =
            K * ∑' i, (scalarSobolevWeight (I := I) (M := M) i a *
              (T.coeff i) ^ 2) :=
        tsum_mul_left
      have h_sq_le :
          ‖scalarHs.heatHkFun (I := I) (M := M) b ht T‖ ^ 2 ≤
            K * ‖T‖ ^ 2 := by
        rw [h_b_sq, h_a_sq]
        rw [← h_tsum_factor]
        exact h_tsum_le
      have h_sqrtK_sq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK_nn
      have h_final_sq :
          ‖scalarHs.heatHkFun (I := I) (M := M) b ht T‖ ^ 2 ≤
            (Real.sqrt K * ‖T‖) ^ 2 := by
        have h_expand : (Real.sqrt K * ‖T‖) ^ 2 = K * ‖T‖ ^ 2 := by
          rw [mul_pow, h_sqrtK_sq]
        rw [h_expand]
        exact h_sq_le
      have h1 : 0 ≤ ‖scalarHs.heatHkFun (I := I) (M := M) b ht T‖ :=
        norm_nonneg _
      have h2 : 0 ≤ ‖T‖ := norm_nonneg T
      have h_sqrtK_nn : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
      have h_norm_le_sqrt :
          ‖scalarHs.heatHkFun (I := I) (M := M) b ht T‖ ≤
            Real.sqrt K * ‖T‖ := by
        nlinarith [h_final_sq, h1, mul_nonneg h_sqrtK_nn h2]
      have h_sqrtK_le_K : Real.sqrt K ≤ K := by
        have h_K_le_sq : K ≤ K ^ 2 := by nlinarith [hK_ge_one]
        calc Real.sqrt K ≤ Real.sqrt (K ^ 2) :=
              Real.sqrt_le_sqrt h_K_le_sq
          _ = K := Real.sqrt_sq hK_nn
      calc
        ‖scalarHs.heatHkFun (I := I) (M := M) b ht T‖ ≤ Real.sqrt K * ‖T‖ :=
          h_norm_le_sqrt
        _ ≤ K * ‖T‖ := mul_le_mul_of_nonneg_right h_sqrtK_le_K h2)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma heatSemigroupHs_apply {g : SmoothRiemannianMetric I M}
    {t : ℝ} (ht : 0 < t) {a b : ℝ}
    (T : scalarHs (I := I) (M := M) g a) :
    heatSemigroupHs (I := I) (M := M) (g := g) ht (a := a) (b := b) T =
      scalarHs.heatHkFun (I := I) (M := M) b ht T := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem heatSemigroupHs_coeff {g : SmoothRiemannianMetric I M}
    {t : ℝ} (ht : 0 < t) {a b : ℝ}
    (T : scalarHs (I := I) (M := M) g a)
    (i : EigenIdx (I := I) (M := M) g) :
    (heatSemigroupHs (I := I) (M := M) (g := g) ht (a := a) (b := b)
        T).coeff i =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        T.coeff i := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHs_opNorm_le {g : SmoothRiemannianMetric I M}
    {a b : ℝ} (hab : a ≤ b) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖heatSemigroupHs (I := I) (M := M) (g := g) ht (a := a) (b := b)‖ ≤
      Real.sqrt (spectralSmoothingConst (b - a)) * t ^ (-((b - a) / 2)) := by
  have h_bound_nn :
      0 ≤ Real.sqrt (spectralSmoothingConst (b - a)) *
        t ^ (-((b - a) / 2)) := by
    have h1 : 0 ≤ Real.sqrt (spectralSmoothingConst (b - a)) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ t ^ (-((b - a) / 2)) :=
      (Real.rpow_pos_of_pos ht _).le
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h_bound_nn (fun T => ?_)
  rw [heatSemigroupHs_apply]
  exact scalarHs.norm_heatHkFun_le_smoothing (I := I) (M := M) hab ht ht1 T

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHs_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {a : ℝ} {t : ℝ} (ht : 0 < t) :
    ‖heatSemigroupHs (I := I) (M := M) (g := g) ht (a := a) (b := a)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => ?_)
  rw [heatSemigroupHs_apply, one_mul]
  exact scalarHs.norm_heatHkFun_le_self (I := I) (M := M) ht T

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHs_add {g : SmoothRiemannianMetric I M}
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) {a : ℝ} :
    heatSemigroupHs (I := I) (M := M) (g := g)
        (show (0:ℝ) < t + s by linarith) (a := a) (b := a) =
      (heatSemigroupHs (I := I) (M := M) (g := g) ht (a := a) (b := a)).comp
        (heatSemigroupHs (I := I) (M := M) (g := g) hs (a := a) (b := a)) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rw [ContinuousLinearMap.comp_apply]
  refine scalarHs.ext ?_
  funext i
  rw [heatSemigroupHs_coeff, heatSemigroupHs_coeff, heatSemigroupHs_coeff]
  set lam := EigenIdx.lambda (I := I) (M := M) i with hlam_def
  have h_exp_add :
      Real.exp (-lam * (t + s)) =
        Real.exp (-lam * t) * Real.exp (-lam * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_exp_add]
  ring

private theorem scalarL2Coeff_heatSemigroup
    {g : SmoothRiemannianMetric I M} {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (i : EigenIdx (I := I) (M := M) g) :
    scalarL2Coeff (I := I) (M := M)
        (DifferentialGeometry.Analysis.HeatEquation.heatSemigroup
          (I := I) (M := M) g t u) i =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        scalarL2Coeff (I := I) (M := M) u i := by
  classical
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g with hb
  have h_coeff_as_inner :
      ∀ v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
        scalarL2Coeff (I := I) (M := M) v i = ⟪b i, v⟫_ℝ := by
    intro v
    unfold scalarL2Coeff
    exact HilbertBasis.repr_apply_apply _ _ _
  rw [h_coeff_as_inner, h_coeff_as_inner]
  rw [DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_apply_of_nonneg
        (I := I) (M := M) g ht u]
  have h_summable :=
    DifferentialGeometry.Analysis.HeatEquation.summable_heatTerm
      (I := I) (M := M) g ht u
  have h_hsum := h_summable.hasSum
  have h_inner_hsum := h_hsum.mapL (innerSL ℝ (b i))
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq : ∀ j : EigenIdx (I := I) (M := M) g,
      ⟪b i, b j⟫_ℝ = if j = i then (1 : ℝ) else 0 := by
    intro j
    rw [show ⟪b i, b j⟫_ℝ = ⟪b j, b i⟫_ℝ from real_inner_comm _ _]
    exact (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
  have h_summand_eq : ∀ j : EigenIdx (I := I) (M := M) g,
      (innerSL ℝ (b i))
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) •
            ⟪b j, u⟫_ℝ • b j) =
        if j = i then
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) *
            ⟪b j, u⟫_ℝ
        else 0 := by
    intro j
    change ⟪b i,
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) •
          ⟪b j, u⟫_ℝ • b j⟫_ℝ = _
    rw [real_inner_smul_right, real_inner_smul_right, h_inner_eq]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  have h_inner_hsum' : HasSum (fun j =>
      if j = i then
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) *
          ⟪b j, u⟫_ℝ
      else 0)
      ((innerSL ℝ (b i))
        (∑' j, Real.exp
            (-(EigenIdx.lambda (I := I) (M := M) j) * t) •
          ⟪b j, u⟫_ℝ • b j)) := by
    convert h_inner_hsum using 1
    funext j
    exact (h_summand_eq j).symm
  have h_tsum_ite :
      ∑' j : EigenIdx (I := I) (M := M) g,
        (if j = i then
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t) *
            ⟪b j, u⟫_ℝ
        else 0) =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪b i, u⟫_ℝ := by
    rw [tsum_ite_eq i]
  have h_eq := h_inner_hsum'.tsum_eq
  rw [h_tsum_ite] at h_eq
  change (innerSL ℝ (b i))
      (∑' j, Real.exp
            (-(EigenIdx.lambda (I := I) (M := M) j) * t) •
          ⟪b j, u⟫_ℝ • b j) = _
  exact h_eq.symm

theorem heatSemigroupHs_zeroEquivL2_apply
    {g : SmoothRiemannianMetric I M}
    {t : ℝ} (ht : 0 < t) (T : scalarHs (I := I) (M := M) g 0) :
    scalarHsZeroEquivL2 (I := I) (M := M) g
        (heatSemigroupHs (I := I) (M := M) (g := g) ht (a := 0) (b := 0) T) =
      DifferentialGeometry.Analysis.HeatEquation.heatSemigroup
        (I := I) (M := M) g t
        (scalarHsZeroEquivL2 (I := I) (M := M) g T) := by
  classical
  refine (resolventHilbertEigenbasisSigma
    (I := I) (M := M) g).repr.injective ?_
  ext i
  have hlhs : ((resolventHilbertEigenbasisSigma
        (I := I) (M := M) g).repr
      (scalarHsZeroEquivL2 (I := I) (M := M) g
        (heatSemigroupHs (I := I) (M := M) (g := g) ht
          (a := 0) (b := 0) T))) i =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        T.coeff i := by
    have h := scalarHs.scalarHsZeroEquivL2_scalarL2Coeff (I := I) (M := M)
      (heatSemigroupHs (I := I) (M := M) (g := g) ht
        (a := 0) (b := 0) T) i
    rw [heatSemigroupHs_coeff] at h
    simpa only [scalarL2Coeff] using h
  have hrhs : ((resolventHilbertEigenbasisSigma
        (I := I) (M := M) g).repr
      (DifferentialGeometry.Analysis.HeatEquation.heatSemigroup
        (I := I) (M := M) g t
        (scalarHsZeroEquivL2 (I := I) (M := M) g T))) i =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        T.coeff i := by
    have h := scalarL2Coeff_heatSemigroup (I := I) (M := M) ht.le
      (scalarHsZeroEquivL2 (I := I) (M := M) g T) i
    rw [scalarHs.scalarHsZeroEquivL2_scalarL2Coeff] at h
    simpa only [scalarL2Coeff] using h
  rw [hlhs, hrhs]

theorem heatSemigroupHs_zeroEquivL2 {g : SmoothRiemannianMetric I M}
    {t : ℝ} (ht : 0 < t) :
    (scalarHsZeroEquivL2 (I := I) (M := M) g).symm.toLinearIsometry.toContinuousLinearMap.comp
        ((DifferentialGeometry.Analysis.HeatEquation.heatSemigroup
            (I := I) (M := M) g t).comp
          (scalarHsZeroEquivL2 (I := I) (M := M) g).toLinearIsometry.toContinuousLinearMap) =
      heatSemigroupHs (I := I) (M := M) (g := g) ht (a := 0) (b := 0) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  change (scalarHsZeroEquivL2 (I := I) (M := M) g).symm
      (DifferentialGeometry.Analysis.HeatEquation.heatSemigroup
        (I := I) (M := M) g t
        (scalarHsZeroEquivL2 (I := I) (M := M) g T)) =
    heatSemigroupHs (I := I) (M := M) (g := g) ht (a := 0) (b := 0) T
  rw [← heatSemigroupHs_zeroEquivL2_apply (I := I) (M := M) ht T]
  exact (scalarHsZeroEquivL2 (I := I) (M := M) g).symm_apply_apply _

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
