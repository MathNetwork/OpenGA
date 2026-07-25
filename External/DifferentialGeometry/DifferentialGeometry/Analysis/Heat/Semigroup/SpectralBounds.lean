import DifferentialGeometry.Analysis.Heat.Semigroup.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private noncomputable def heatPowerCoeffBound (k : ℕ) (t : ℝ) : ℝ :=
  (k / t : ℝ) ^ k * Real.exp (-(k : ℝ))

private lemma heatPowerCoeffBound_nonneg (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ heatPowerCoeffBound k t := by
  unfold heatPowerCoeffBound
  apply mul_nonneg
  · exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) ht.le) k
  · exact (Real.exp_pos _).le

private lemma lambda_pow_mul_exp_le
    (k : ℕ) {t : ℝ} (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam ^ k * Real.exp (-(lam * t)) ≤ heatPowerCoeffBound k t := by
  unfold heatPowerCoeffBound
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero, Real.exp_zero,
      mul_one]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ lam * t := mul_nonneg hlam ht.le
    linarith
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have h_tk_pos : (0 : ℝ) < t / k := div_pos ht hk_real_pos
  have h_aux : lam * Real.exp (-((t / (k : ℝ)) * lam)) ≤
      (k / t : ℝ) * Real.exp (-1) := by
    set s : ℝ := (t / k : ℝ) * lam with hs_def
    have hs_nn : 0 ≤ s := mul_nonneg h_tk_pos.le hlam
    have hs_bound : s * Real.exp (-s) ≤ Real.exp (-1) := by
      have h1 : s ≤ Real.exp (s - 1) := by
        have h := Real.add_one_le_exp (s - 1)
        linarith
      have hexp_pos : 0 < Real.exp (-s) := Real.exp_pos _
      have h_mul : s * Real.exp (-s) ≤ Real.exp (s - 1) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right h1 hexp_pos.le
      rw [← Real.exp_add] at h_mul
      have h_sum : s - 1 + -s = -1 := by ring
      rw [h_sum] at h_mul
      exact h_mul
    have h_lam_eq : lam = (k / t : ℝ) * s := by
      simp only [hs_def]
      have ht_ne : (t : ℝ) ≠ 0 := ht.ne'
      have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
      field_simp
    have h_arg_eq : -((t / k : ℝ) * lam) = -s := by
      simp only [hs_def]
    rw [h_arg_eq, h_lam_eq]
    have h_kt_nn : 0 ≤ (k / t : ℝ) := div_nonneg hk_real_pos.le ht.le
    calc (k / t : ℝ) * s * Real.exp (-s)
        = (k / t : ℝ) * (s * Real.exp (-s)) := by ring
      _ ≤ (k / t : ℝ) * Real.exp (-1) :=
            mul_le_mul_of_nonneg_left hs_bound h_kt_nn
  have h_lhs_nn : 0 ≤ lam * Real.exp (-((t / (k : ℝ)) * lam)) :=
    mul_nonneg hlam (Real.exp_pos _).le
  have h_pow_le : (lam * Real.exp (-((t / (k : ℝ)) * lam))) ^ k ≤
      ((k / t : ℝ) * Real.exp (-1)) ^ k :=
    pow_le_pow_left₀ h_lhs_nn h_aux k
  have h_lhs_eq : (lam * Real.exp (-((t / (k : ℝ)) * lam))) ^ k =
      lam ^ k * Real.exp (-(lam * t)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have h_arg : (k : ℝ) * -((t / (k : ℝ)) * lam) = -(lam * t) := by
      have hk_ne : (k : ℝ) ≠ 0 := hk_real_pos.ne'
      field_simp
    rw [h_arg]
  have h_rhs_eq : ((k / t : ℝ) * Real.exp (-1)) ^ k =
      (k / t : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  rw [h_lhs_eq] at h_pow_le
  rw [h_rhs_eq] at h_pow_le
  exact h_pow_le

private lemma lambda_pow_mul_exp_sq_le
    (k : ℕ) {t : ℝ} (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    (lam ^ k * Real.exp (-(lam * t))) ^ 2 ≤ (heatPowerCoeffBound k t) ^ 2 := by
  have h_lhs_nn : 0 ≤ lam ^ k * Real.exp (-(lam * t)) :=
    mul_nonneg (pow_nonneg hlam k) (Real.exp_pos _).le
  have h_le : lam ^ k * Real.exp (-(lam * t)) ≤ heatPowerCoeffBound k t :=
    lambda_pow_mul_exp_le k ht hlam
  exact pow_le_pow_left₀ h_lhs_nn h_le 2

private lemma summable_heatPower_coeff_sq
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ) ^ 2) := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  refine Summable.of_nonneg_of_le ?_ ?_
    ((summable_basis_coeff_sq (I := I) (M := M) g u).mul_left
      ((heatPowerCoeffBound k t) ^ 2))
  · intro i; positivity
  · intro i
    have h_coeff_sq_le :
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤
          (heatPowerCoeffBound k t) ^ 2 := by
      have hlam : 0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
        lambda_nonneg (I := I) (M := M) i
      have h_arg :
          -(EigenIdx.lambda (I := I) (M := M) i) * t =
            -(EigenIdx.lambda (I := I) (M := M) i * t) := by ring
      rw [h_arg]
      exact lambda_pow_mul_exp_sq_le k ht hlam
    have h_inner_sq_nn : 0 ≤ (⟪b i, u⟫_ℝ) ^ 2 := sq_nonneg _
    calc
      ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ) ^ 2
          = ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
                Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 *
              (⟪b i, u⟫_ℝ) ^ 2 := by ring
      _ ≤ (heatPowerCoeffBound k t) ^ 2 * (⟪b i, u⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h_coeff_sq_le h_inner_sq_nn

private lemma summable_heatPowerTerm
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
        resolventHilbertEigenbasisSigma (I := I) (M := M) g i) := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ (fun _ : EigenIdx (I := I) (M := M) g => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : EigenIdx (I := I) (M := M) g =>
      (EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        ⟪b i, u⟫_ℝ)
  have h_sq_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        ‖(EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ‖ ^ 2) =
      (fun i =>
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ) ^ 2) := by
    funext i
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_sq_eq] at h_iff
  have h_sq_summable := summable_heatPower_coeff_sq (I := I) (M := M) g k ht u
  have h_summable_V := h_iff.mpr h_sq_summable
  have h_map_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        LinearIsometry.toSpanSingleton ℝ
          (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
          (h_orthonormal.1 i)
          ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
            ⟪b i, u⟫_ℝ)) =
      (fun i =>
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, u⟫_ℝ • b i) := by
    funext i
    rw [LinearIsometry.toSpanSingleton_apply]
    rw [mul_smul]
  rw [h_map_eq] at h_summable_V
  exact h_summable_V

private lemma norm_sq_heatPowerTerm_sum_le
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖∑' i : EigenIdx (I := I) (M := M) g,
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i‖ ^ 2 ≤
      (heatPowerCoeffBound k t) ^ 2 * ‖u‖ ^ 2 := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_summand_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, u⟫_ℝ • b i) =
      (fun i =>
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ) • b i) := by
    funext i; rw [smul_smul]
  rw [h_summand_eq]
  set f : EigenIdx (I := I) (M := M) g → ℝ := fun i =>
    (EigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
      ⟪b i, u⟫_ℝ
  have hC_nn : 0 ≤ heatPowerCoeffBound k t := heatPowerCoeffBound_nonneg k ht
  have h_f_sq_le : ∀ i, (f i) ^ 2 ≤
      (heatPowerCoeffBound k t) ^ 2 * (⟪b i, u⟫_ℝ) ^ 2 := by
    intro i
    have hlam : 0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
      lambda_nonneg (I := I) (M := M) i
    have h_arg :
        -(EigenIdx.lambda (I := I) (M := M) i) * t =
          -(EigenIdx.lambda (I := I) (M := M) i * t) := by ring
    have h_coeff_sq_le :
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 ≤
          (heatPowerCoeffBound k t) ^ 2 := by
      rw [h_arg]
      exact lambda_pow_mul_exp_sq_le k ht hlam
    have h_inner_sq_nn : 0 ≤ (⟪b i, u⟫_ℝ) ^ 2 := sq_nonneg _
    change (f i) ^ 2 ≤ _
    calc
      (f i) ^ 2
          = ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
                Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) ^ 2 *
              (⟪b i, u⟫_ℝ) ^ 2 := by
                change ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
                  Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
                  ⟪b i, u⟫_ℝ) ^ 2 = _
                ring
      _ ≤ (heatPowerCoeffBound k t) ^ 2 * (⟪b i, u⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h_coeff_sq_le h_inner_sq_nn
  have h_summable_f_sq : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (f i) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_
      ((summable_basis_coeff_sq (I := I) (M := M) g u).mul_left
        ((heatPowerCoeffBound k t) ^ 2))
    · intro i; positivity
    · intro i; exact h_f_sq_le i
  have h_norm_sq_eq := orthonormal_norm_sq_eq_tsum_sq (I := I) (M := M) g f h_summable_f_sq
  change ‖∑' i, f i • b i‖ ^ 2 ≤ _
  rw [h_norm_sq_eq]
  have h_dom : ∑' i : EigenIdx (I := I) (M := M) g, (f i) ^ 2 ≤
      (heatPowerCoeffBound k t) ^ 2 *
        ∑' i, (⟪b i, u⟫_ℝ) ^ 2 := by
    have h_summable_dom :
        Summable (fun i : EigenIdx (I := I) (M := M) g =>
          (heatPowerCoeffBound k t) ^ 2 * (⟪b i, u⟫_ℝ) ^ 2) :=
      (summable_basis_coeff_sq (I := I) (M := M) g u).mul_left _
    have h_step : ∑' i : EigenIdx (I := I) (M := M) g, (f i) ^ 2 ≤
        ∑' i, (heatPowerCoeffBound k t) ^ 2 * (⟪b i, u⟫_ℝ) ^ 2 :=
      Summable.tsum_le_tsum h_f_sq_le h_summable_f_sq h_summable_dom
    have h_tsum_eq :
        (∑' i : EigenIdx (I := I) (M := M) g,
          (heatPowerCoeffBound k t) ^ 2 * (⟪b i, u⟫_ℝ) ^ 2) =
        (heatPowerCoeffBound k t) ^ 2 *
          ∑' i, (⟪b i, u⟫_ℝ) ^ 2 :=
      tsum_mul_left
    linarith [h_tsum_eq, h_step]
  refine le_trans h_dom ?_
  rw [parseval_norm_sq (I := I) (M := M) g u]

private lemma norm_heatPowerTerm_sum_le
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖∑' i : EigenIdx (I := I) (M := M) g,
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i‖ ≤
      heatPowerCoeffBound k t * ‖u‖ := by
  have h_sq := norm_sq_heatPowerTerm_sum_le (I := I) (M := M) g k ht u
  have hC_nn : 0 ≤ heatPowerCoeffBound k t := heatPowerCoeffBound_nonneg k ht
  have h_u_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have h_rhs_sq : (heatPowerCoeffBound k t * ‖u‖) ^ 2 =
      (heatPowerCoeffBound k t) ^ 2 * ‖u‖ ^ 2 := by ring
  rw [← h_rhs_sq] at h_sq
  have h_rhs_nn : 0 ≤ heatPowerCoeffBound k t * ‖u‖ := mul_nonneg hC_nn h_u_nn
  exact (abs_le_of_sq_le_sq' h_sq h_rhs_nn).2

private noncomputable def heatPowerFun
    (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ∑' i : EigenIdx (I := I) (M := M) g,
    ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
      ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
      resolventHilbertEigenbasisSigma (I := I) (M := M) g i

private lemma heatPowerFun_add
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatPowerFun (I := I) (M := M) g k t (u + v) =
      heatPowerFun (I := I) (M := M) g k t u +
        heatPowerFun (I := I) (M := M) g k t v := by
  unfold heatPowerFun
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_summand_eq : ∀ i : EigenIdx (I := I) (M := M) g,
      ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, u + v⟫_ℝ • b i =
      (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, u⟫_ℝ • b i) +
      (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, v⟫_ℝ • b i) := by
    intro i
    rw [inner_add_right, add_smul, smul_add]
  have h_sum_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, u + v⟫_ℝ • b i) =
      (fun i =>
        (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, u⟫_ℝ • b i) +
        (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, v⟫_ℝ • b i)) := by
    funext i; exact h_summand_eq i
  rw [h_sum_eq]
  rw [Summable.tsum_add (summable_heatPowerTerm (I := I) (M := M) g k ht u)
    (summable_heatPowerTerm (I := I) (M := M) g k ht v)]

private lemma heatPowerFun_smul
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t) (c : ℝ)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatPowerFun (I := I) (M := M) g k t (c • u) =
      c • heatPowerFun (I := I) (M := M) g k t u := by
  unfold heatPowerFun
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_summand_eq : ∀ i : EigenIdx (I := I) (M := M) g,
      ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, c • u⟫_ℝ • b i =
      c • (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, u⟫_ℝ • b i) := by
    intro i
    rw [real_inner_smul_right]
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have h_sum_eq :
      (fun i : EigenIdx (I := I) (M := M) g =>
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, c • u⟫_ℝ • b i) =
      (fun i => c • (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        ⟪b i, u⟫_ℝ • b i)) := by
    funext i; exact h_summand_eq i
  rw [h_sum_eq]
  exact (summable_heatPowerTerm (I := I) (M := M) g k ht u).tsum_const_smul c

noncomputable def heatPower
    (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  by_cases hk : k = 0
  · exact heatSemigroup (I := I) (M := M) g t
  by_cases ht : 0 < t
  · refine LinearMap.mkContinuous
      { toFun := heatPowerFun (I := I) (M := M) g k t
        map_add' := heatPowerFun_add (I := I) (M := M) g k ht
        map_smul' := fun c u => heatPowerFun_smul (I := I) (M := M) g k ht c u }
        (heatPowerCoeffBound k t) ?_
    intro u
    exact norm_heatPowerTerm_sum_le (I := I) (M := M) g k ht u
  · exact 0

@[simp]
theorem heatPower_zero (g : SmoothRiemannianMetric I M) (t : ℝ) :
    heatPower (I := I) (M := M) g 0 t = heatSemigroup (I := I) (M := M) g t := by
  unfold heatPower
  rw [dif_pos rfl]

theorem heatPower_apply_of_pos_one_le
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatPower (I := I) (M := M) g k t u =
      ∑' i : EigenIdx (I := I) (M := M) g,
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i := by
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  unfold heatPower
  rw [dif_neg hk_ne, dif_pos ht]
  rfl

theorem heatPower_eq_zero_of_one_le_of_nonpos
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : t ≤ 0) :
    heatPower (I := I) (M := M) g k t = 0 := by
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  unfold heatPower
  rw [dif_neg hk_ne, dif_neg (not_lt.mpr ht)]

theorem heatPower_apply_of_pos
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatPower (I := I) (M := M) g k t u =
      ∑' i : EigenIdx (I := I) (M := M) g,
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ •
          resolventHilbertEigenbasisSigma (I := I) (M := M) g i := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    rw [heatPower_zero, heatSemigroup_apply_of_nonneg (I := I) (M := M) g ht.le u]
    apply tsum_congr
    intro i; rw [pow_zero, one_mul]
  · exact heatPower_apply_of_pos_one_le (I := I) (M := M) g hk_pos ht u

theorem heatPower_opNorm_le
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) :
    ‖heatPower (I := I) (M := M) g k t‖ ≤
      (k / t : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  unfold heatPower
  rw [dif_neg hk_ne, dif_pos ht]
  have hC_nn : 0 ≤ heatPowerCoeffBound k t := heatPowerCoeffBound_nonneg k ht
  exact LinearMap.mkContinuous_norm_le _ hC_nn _

theorem heatPower_apply_basis_pos
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (i : EigenIdx (I := I) (M := M) g) :
    heatPower (I := I) (M := M) g k t
        (resolventHilbertEigenbasisSigma (I := I) (M := M) g i) =
      ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
        resolventHilbertEigenbasisSigma (I := I) (M := M) g i := by
  classical
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  rw [heatPower_apply_of_pos (I := I) (M := M) g k ht]
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq : ∀ j : EigenIdx (I := I) (M := M) g,
      ⟪b j, b i⟫_ℝ = if j = i then 1 else 0 := by
    intro j
    exact (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
  have h_summand_eq : ∀ j : EigenIdx (I := I) (M := M) g,
      ((EigenIdx.lambda (I := I) (M := M) j) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t)) •
        ⟪b j, b i⟫_ℝ • b j =
      if j = i then
        ((EigenIdx.lambda (I := I) (M := M) j) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t)) • b j
      else 0 := by
    intro j
    rw [h_inner_eq]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  have h_sum_eq :
      (fun j : EigenIdx (I := I) (M := M) g =>
        ((EigenIdx.lambda (I := I) (M := M) j) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t)) •
          ⟪b j, b i⟫_ℝ • b j) =
      (fun j =>
        if j = i then
          ((EigenIdx.lambda (I := I) (M := M) j) ^ k *
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) j) * t)) • b j
        else 0) := by
    funext j; exact h_summand_eq j
  rw [h_sum_eq]
  rw [tsum_ite_eq i]

theorem heatPower_isSelfAdjoint (g : SmoothRiemannianMetric I M) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    IsSelfAdjoint (heatPower (I := I) (M := M) g k t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  change ⟪(heatPower (I := I) (M := M) g k t) u, v⟫_ℝ =
      ⟪u, (heatPower (I := I) (M := M) g k t) v⟫_ℝ
  rw [heatPower_apply_of_pos (I := I) (M := M) g k ht u,
      heatPower_apply_of_pos (I := I) (M := M) g k ht v]
  let φv : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
    (innerSL ℝ).flip v
  let φu : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
    innerSL ℝ u
  have h_lhs : ⟪∑' i : EigenIdx (I := I) (M := M) g,
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, u⟫_ℝ • b i, v⟫_ℝ =
      ∑' i : EigenIdx (I := I) (M := M) g,
        (EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
    have h_summable := summable_heatPowerTerm (I := I) (M := M) g k ht u
    have h_hsum := h_summable.hasSum
    have h_inner_hsum := h_hsum.mapL φv
    have h_summand_eq : ∀ i : EigenIdx (I := I) (M := M) g,
        φv (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i) =
        (EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
      intro i
      change ⟪((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i, v⟫_ℝ = _
      rw [real_inner_smul_left, real_inner_smul_left]
      ring
    have h_inner_hsum' : HasSum (fun i =>
        (EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ)
        (φv (∑' i, ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i)) := by
      convert h_inner_hsum using 1
      funext i; exact (h_summand_eq i).symm
    have h_apply : φv (∑' i : EigenIdx (I := I) (M := M) g,
          ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i) =
        ⟪∑' i, ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i, v⟫_ℝ := rfl
    rw [h_apply] at h_inner_hsum'
    exact h_inner_hsum'.tsum_eq.symm
  have h_rhs : ⟪u, ∑' i : EigenIdx (I := I) (M := M) g,
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          ⟪b i, v⟫_ℝ • b i⟫_ℝ =
      ∑' i : EigenIdx (I := I) (M := M) g,
        (EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
    have h_summable := summable_heatPowerTerm (I := I) (M := M) g k ht v
    have h_hsum := h_summable.hasSum
    have h_inner_hsum := h_hsum.mapL φu
    have h_summand_eq : ∀ i : EigenIdx (I := I) (M := M) g,
        φu (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i) =
        (EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ := by
      intro i
      change ⟪u, ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i⟫_ℝ = _
      rw [real_inner_smul_right, real_inner_smul_right,
          show ⟪u, b i⟫_ℝ = ⟪b i, u⟫_ℝ from real_inner_comm _ _]
      ring
    have h_inner_hsum' : HasSum (fun i =>
        (EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
          ⟪b i, u⟫_ℝ * ⟪b i, v⟫_ℝ)
        (φu (∑' i, ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i)) := by
      convert h_inner_hsum using 1
      funext i; exact (h_summand_eq i).symm
    have h_apply : φu (∑' i : EigenIdx (I := I) (M := M) g,
          ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i) =
        ⟪u, ∑' i, ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, v⟫_ℝ • b i⟫_ℝ := rfl
    rw [h_apply] at h_inner_hsum'
    exact h_inner_hsum'.tsum_eq.symm
  rw [h_lhs, h_rhs]

theorem heatPower_comp_heatSemigroup
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    {s : ℝ} (hs : 0 ≤ s) :
    (heatPower (I := I) (M := M) g k t).comp
        (heatSemigroup (I := I) (M := M) g s) =
      heatPower (I := I) (M := M) g k (t + s) := by
  apply ContinuousLinearMap.ext
  intro u
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have hts_pos : 0 < t + s := by linarith
  rw [ContinuousLinearMap.comp_apply,
      heatSemigroup_apply_of_nonneg (I := I) (M := M) g hs u,
      heatPower_apply_of_pos (I := I) (M := M) g k hts_pos]
  have h_summable_s := summable_heatTerm (I := I) (M := M) g hs u
  have h_pull :
      heatPower (I := I) (M := M) g k t
          (∑' i : EigenIdx (I := I) (M := M) g,
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) •
              ⟪b i, u⟫_ℝ • b i) =
      ∑' i : EigenIdx (I := I) (M := M) g,
        heatPower (I := I) (M := M) g k t
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) •
            ⟪b i, u⟫_ℝ • b i) := by
    have h_hsum := h_summable_s.hasSum
    exact (h_hsum.mapL (heatPower (I := I) (M := M) g k t)).tsum_eq.symm
  rw [h_pull]
  apply tsum_congr
  intro i
  rw [(heatPower (I := I) (M := M) g k t).map_smul,
      (heatPower (I := I) (M := M) g k t).map_smul]
  have h_basis_apply :
      heatPower (I := I) (M := M) g k t (b i) =
      ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) • b i :=
    heatPower_apply_basis_pos (I := I) (M := M) g k ht i
  rw [h_basis_apply]
  rw [show (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) •
        (⟪b i, u⟫_ℝ • ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) • b i)) =
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) *
          ⟪b i, u⟫_ℝ *
          ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t))) • b i from by
    rw [smul_smul, smul_smul]]
  rw [show ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + s))) •
        ⟪b i, u⟫_ℝ • b i =
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + s)) *
          ⟪b i, u⟫_ℝ) • b i from by rw [smul_smul]]
  congr 1
  have h_exp_add :
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + s)) =
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) := by
    rw [show -(EigenIdx.lambda (I := I) (M := M) i) * (t + s) =
        -(EigenIdx.lambda (I := I) (M := M) i) * t +
        -(EigenIdx.lambda (I := I) (M := M) i) * s from by ring,
        Real.exp_add]
  rw [h_exp_add]
  ring

theorem heatSemigroup_comp_heatPower
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    {s : ℝ} (hs : 0 ≤ s) :
    (heatSemigroup (I := I) (M := M) g s).comp
        (heatPower (I := I) (M := M) g k t) =
      heatPower (I := I) (M := M) g k (t + s) := by
  apply ContinuousLinearMap.ext
  intro u
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have hts_pos : 0 < t + s := by linarith
  rw [ContinuousLinearMap.comp_apply,
      heatPower_apply_of_pos (I := I) (M := M) g k ht u,
      heatPower_apply_of_pos (I := I) (M := M) g k hts_pos]
  have h_summable_t := summable_heatPowerTerm (I := I) (M := M) g k ht u
  have h_pull :
      heatSemigroup (I := I) (M := M) g s
          (∑' i : EigenIdx (I := I) (M := M) g,
            ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
                Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
              ⟪b i, u⟫_ℝ • b i) =
      ∑' i : EigenIdx (I := I) (M := M) g,
        heatSemigroup (I := I) (M := M) g s
          (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i) := by
    have h_hsum := h_summable_t.hasSum
    exact (h_hsum.mapL (heatSemigroup (I := I) (M := M) g s)).tsum_eq.symm
  rw [h_pull]
  apply tsum_congr
  intro i
  rw [(heatSemigroup (I := I) (M := M) g s).map_smul,
      (heatSemigroup (I := I) (M := M) g s).map_smul]
  have h_basis_apply :
      heatSemigroup (I := I) (M := M) g s (b i) =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) • b i := by
    have hh := heatSemigroup_apply_basis (I := I) (M := M) g hs i
    have h_eq : resolventEigenbasisSigma (I := I) (M := M) g i = b i :=
      (resolventEigenbasisSigma_eq_resolventEigenbasisVec (I := I) (M := M) g i).trans
        (resolventHilbertEigenbasisSigma_apply (I := I) (M := M) g i).symm
    rw [h_eq] at hh
    exact hh
  rw [h_basis_apply]
  rw [show (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
          (⟪b i, u⟫_ℝ • Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) •
            b i)) =
        (((EigenIdx.lambda (I := I) (M := M) i) ^ k *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) *
          ⟪b i, u⟫_ℝ *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s)) • b i from by
    rw [smul_smul, smul_smul]]
  rw [show ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + s))) •
        ⟪b i, u⟫_ℝ • b i =
        ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + s)) *
          ⟪b i, u⟫_ℝ) • b i from by rw [smul_smul]]
  congr 1
  have h_exp_add :
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + s)) =
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * s) := by
    rw [show -(EigenIdx.lambda (I := I) (M := M) i) * (t + s) =
        -(EigenIdx.lambda (I := I) (M := M) i) * t +
        -(EigenIdx.lambda (I := I) (M := M) i) * s from by ring,
        Real.exp_add]
  rw [h_exp_add]
  ring

private lemma exp_neg_taylor_bound
    (k : ℕ) {t : ℝ} (ht : 0 < t) {h : ℝ} (hh : |h| ≤ t / 2)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    |lam ^ k * (Real.exp (-(lam * (t + h))) - Real.exp (-(lam * t)) +
        lam * h * Real.exp (-(lam * t)))| ≤
      heatPowerCoeffBound (k + 2) (t / 2) * h ^ 2 := by
  have h_factor :
      Real.exp (-(lam * (t + h))) - Real.exp (-(lam * t)) +
          lam * h * Real.exp (-(lam * t)) =
        Real.exp (-(lam * t)) *
          (Real.exp (-(lam * h)) - 1 - (-(lam * h))) := by
    have h_neg : -(lam * h) = -(lam * (t + h)) - (-(lam * t)) := by ring
    rw [show -(lam * (t + h)) = -(lam * t) + -(lam * h) from by ring,
      Real.exp_add]
    ring
  rw [h_factor]
  have h_taylor : ∀ s : ℝ, |Real.exp s - 1 - s| ≤ s ^ 2 * Real.exp |s| := by
    intro s
    have hc :=
      Complex.norm_exp_sub_sum_le_norm_mul_exp (s : ℂ) 2
    have h_sum : ∑ m ∈ Finset.range 2, (s : ℂ) ^ m / (m.factorial : ℂ) =
        1 + (s : ℂ) := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [h_sum] at hc
    have hc' : ‖Complex.exp (s : ℂ) - (1 + (s : ℂ))‖ ≤
        ‖(s : ℂ)‖ ^ 2 * Real.exp ‖(s : ℂ)‖ := hc
    have h_eq : Complex.exp (s : ℂ) - (1 + (s : ℂ)) =
        ((Real.exp s - 1 - s : ℝ) : ℂ) := by
      have h_exp_real : Complex.exp (s : ℂ) = ((Real.exp s : ℝ) : ℂ) :=
        (Complex.ofReal_exp s).symm
      rw [h_exp_real]
      push_cast
      ring
    rw [h_eq] at hc'
    have h_lhs_norm : ‖((Real.exp s - 1 - s : ℝ) : ℂ)‖ =
        |Real.exp s - 1 - s| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h_lhs_norm] at hc'
    have h_rhs_norm : ‖(s : ℂ)‖ = |s| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h_rhs_norm] at hc'
    convert hc' using 1
    rw [sq_abs]
  have h_step1 :
      |Real.exp (-(lam * h)) - 1 - (-(lam * h))| ≤
        (-(lam * h)) ^ 2 * Real.exp |-(lam * h)| :=
    h_taylor (-(lam * h))
  have h_neg_sq : (-(lam * h)) ^ 2 = (lam * h) ^ 2 := by ring
  have h_neg_abs : |-(lam * h)| = |lam * h| := abs_neg _
  have h_lam_h_abs : |lam * h| = lam * |h| := by
    rw [abs_mul, abs_of_nonneg hlam]
  rw [h_neg_sq, h_neg_abs, h_lam_h_abs] at h_step1
  have h_exp_t_pos : 0 < Real.exp (-(lam * t)) := Real.exp_pos _
  rw [show lam ^ k * (Real.exp (-(lam * t)) *
      (Real.exp (-(lam * h)) - 1 - (-(lam * h)))) =
      Real.exp (-(lam * t)) *
      (lam ^ k * (Real.exp (-(lam * h)) - 1 - (-(lam * h)))) from by ring]
  rw [abs_mul]
  rw [abs_of_pos h_exp_t_pos]
  rw [abs_mul]
  rw [show |lam ^ k| = lam ^ k from abs_of_nonneg (pow_nonneg hlam k)]
  have h_step2 :
      Real.exp (-(lam * t)) *
        (lam ^ k * |Real.exp (-(lam * h)) - 1 - (-(lam * h))|) ≤
      Real.exp (-(lam * t)) *
        (lam ^ k * ((lam * h) ^ 2 * Real.exp (lam * |h|))) := by
    apply mul_le_mul_of_nonneg_left _ h_exp_t_pos.le
    apply mul_le_mul_of_nonneg_left h_step1 (pow_nonneg hlam k)
  refine le_trans h_step2 ?_
  have h_t_minus_h_pos : 0 < t - |h| := by
    have ht_half_pos : 0 < t / 2 := by linarith
    have : |h| ≤ t / 2 := hh
    linarith
  have h_t_minus_h_ge : t / 2 ≤ t - |h| := by linarith
  have h_combine : Real.exp (-(lam * t)) *
      (lam ^ k * ((lam * h) ^ 2 * Real.exp (lam * |h|))) =
      lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) := by
    rw [show -(lam * (t - |h|)) = -(lam * t) + lam * |h| from by ring]
    rw [Real.exp_add]
    rw [show (lam * h) ^ 2 = lam ^ 2 * h ^ 2 from by ring]
    rw [pow_add]
    ring
  rw [h_combine]
  have h_lam_pow_exp_le :
      lam ^ (k + 2) * Real.exp (-(lam * (t - |h|))) ≤
        lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam _)
    apply Real.exp_le_exp.mpr
    have : -(lam * (t - |h|)) ≤ -(lam * (t / 2)) := by
      have hlt : lam * (t / 2) ≤ lam * (t - |h|) :=
        mul_le_mul_of_nonneg_left h_t_minus_h_ge hlam
      linarith
    exact this
  have h_h_sq_nn : 0 ≤ h ^ 2 := sq_nonneg _
  have h_step3 : lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) ≤
      lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) * h ^ 2 := by
    have hp : lam ^ (k + 2) * h ^ 2 * Real.exp (-(lam * (t - |h|))) =
        lam ^ (k + 2) * Real.exp (-(lam * (t - |h|))) * h ^ 2 := by ring
    rw [hp]
    exact mul_le_mul_of_nonneg_right h_lam_pow_exp_le h_h_sq_nn
  refine le_trans h_step3 ?_
  have h_t2_pos : 0 < t / 2 := by linarith
  have h_final :
      lam ^ (k + 2) * Real.exp (-(lam * (t / 2))) ≤
        heatPowerCoeffBound (k + 2) (t / 2) :=
    lambda_pow_mul_exp_le (k + 2) h_t2_pos hlam
  exact mul_le_mul_of_nonneg_right h_final h_h_sq_nn

private lemma norm_heatPower_taylor_remainder
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    {h : ℝ} (hh : |h| ≤ t / 2)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖heatPower (I := I) (M := M) g k (t + h) u -
        heatPower (I := I) (M := M) g k t u +
        h • heatPower (I := I) (M := M) g (k + 1) t u‖ ≤
      heatPowerCoeffBound (k + 2) (t / 2) * h ^ 2 * ‖u‖ := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_th_pos : 0 < t + h := by
    have : -h ≤ t / 2 := by
      have := abs_le.mp hh
      linarith [this.1]
    linarith
  rw [heatPower_apply_of_pos (I := I) (M := M) g k h_th_pos u,
      heatPower_apply_of_pos (I := I) (M := M) g k ht u,
      heatPower_apply_of_pos (I := I) (M := M) g (k + 1) ht u]
  have h_sum_th := summable_heatPowerTerm (I := I) (M := M) g k h_th_pos u
  have h_sum_t := summable_heatPowerTerm (I := I) (M := M) g k ht u
  have h_sum_t1 := summable_heatPowerTerm (I := I) (M := M) g (k + 1) ht u
  set A : EigenIdx (I := I) (M := M) g →
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) := fun i =>
    ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + h))) •
      ⟪b i, u⟫_ℝ • b i with hA_def
  set B : EigenIdx (I := I) (M := M) g →
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) := fun i =>
    ((EigenIdx.lambda (I := I) (M := M) i) ^ k *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
      ⟪b i, u⟫_ℝ • b i with hB_def
  set C : EigenIdx (I := I) (M := M) g →
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) := fun i =>
    ((EigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
      ⟪b i, u⟫_ℝ • b i with hC_def
  have h_hsum_combined :
      HasSum (fun i => A i - B i + h • C i)
        ((∑' i, A i) - (∑' i, B i) + h • (∑' i, C i)) := by
    have hA := h_sum_th.hasSum
    have hB := h_sum_t.hasSum
    have hC := h_sum_t1.hasSum
    exact (hA.sub hB).add (hC.const_smul h)
  set ψ : EigenIdx (I := I) (M := M) g → ℝ := fun i =>
    (EigenIdx.lambda (I := I) (M := M) i) ^ k *
        (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + h)) -
          Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) +
      h * ((EigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
        Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) with hψ_def
  have h_combined_eq : ∀ i,
      A i - B i + h • C i = ψ i • ⟪b i, u⟫_ℝ • b i := by
    intro i
    simp only [hA_def, hB_def, hC_def, hψ_def]
    rw [show h • ((EigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) •
            ⟪b i, u⟫_ℝ • b i =
          (h * ((EigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t))) •
            ⟪b i, u⟫_ℝ • b i from by rw [smul_smul]]
    rw [← sub_smul, ← add_smul]
    congr 1
    ring
  have h_combined_sum_eq :
      (∑' i : EigenIdx (I := I) (M := M) g, (A i - B i + h • C i)) =
      ∑' i : EigenIdx (I := I) (M := M) g, ψ i • ⟪b i, u⟫_ℝ • b i :=
    tsum_congr h_combined_eq
  have h_combined_sum :
      (∑' i, A i) - (∑' i, B i) + h • (∑' i, C i) =
      ∑' i : EigenIdx (I := I) (M := M) g, ψ i • ⟪b i, u⟫_ℝ • b i := by
    have h := h_hsum_combined.tsum_eq
    rw [← h]
    exact h_combined_sum_eq
  rw [show ((∑' i, A i) : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
      - (∑' i, B i) + h • (∑' i, C i) = _ from h_combined_sum]
  have h_psi_bound : ∀ i, |ψ i| ≤ heatPowerCoeffBound (k + 2) (t / 2) * h ^ 2 := by
    intro i
    simp only [hψ_def]
    have hlam : 0 ≤ EigenIdx.lambda (I := I) (M := M) i :=
      lambda_nonneg (I := I) (M := M) i
    have h_taylor := exp_neg_taylor_bound
      (k := k) (t := t) ht (h := h) hh hlam
    have h_paren_eq : ∀ x y : ℝ,
        Real.exp (-x * y) = Real.exp (-(x * y)) := by
      intro x y; congr 1; ring
    have h_lhs_eq :
        (EigenIdx.lambda (I := I) (M := M) i) ^ k *
            (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * (t + h)) -
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) +
          h * ((EigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t)) =
        (EigenIdx.lambda (I := I) (M := M) i) ^ k *
          (Real.exp (-(EigenIdx.lambda (I := I) (M := M) i * (t + h))) -
            Real.exp (-(EigenIdx.lambda (I := I) (M := M) i * t)) +
            EigenIdx.lambda (I := I) (M := M) i * h *
              Real.exp (-(EigenIdx.lambda (I := I) (M := M) i * t))) := by
      rw [h_paren_eq (EigenIdx.lambda (I := I) (M := M) i) (t + h),
          h_paren_eq (EigenIdx.lambda (I := I) (M := M) i) t]
      rw [pow_succ]
      ring
    rw [h_lhs_eq]
    exact h_taylor
  set Cψ : ℝ := heatPowerCoeffBound (k + 2) (t / 2) * h ^ 2 with hCψ_def
  have hCψ_nn : 0 ≤ Cψ := by
    simp only [hCψ_def]
    apply mul_nonneg
    · exact heatPowerCoeffBound_nonneg (k + 2) (by linarith : (0 : ℝ) < t / 2)
    · exact sq_nonneg _
  have h_summand_eq :
      (fun i : EigenIdx (I := I) (M := M) g => ψ i • ⟪b i, u⟫_ℝ • b i) =
      (fun i => (ψ i * ⟪b i, u⟫_ℝ) • b i) := by
    funext i; rw [mul_smul]
  rw [h_summand_eq]
  have h_psi_sq_le : ∀ i, (ψ i) ^ 2 ≤ Cψ ^ 2 := by
    intro i
    have h_abs := h_psi_bound i
    have h_sq_le : (ψ i) ^ 2 ≤ Cψ ^ 2 := by
      have h_abs_nn : 0 ≤ |ψ i| := abs_nonneg _
      have h_sq_eq : (ψ i) ^ 2 = |ψ i| ^ 2 := (sq_abs _).symm
      rw [h_sq_eq]
      exact pow_le_pow_left₀ h_abs_nn h_abs 2
    exact h_sq_le
  have h_f_sq_le : ∀ i, (ψ i * ⟪b i, u⟫_ℝ) ^ 2 ≤ Cψ ^ 2 * (⟪b i, u⟫_ℝ) ^ 2 := by
    intro i
    have h_inner_sq_nn : 0 ≤ (⟪b i, u⟫_ℝ) ^ 2 := sq_nonneg _
    calc (ψ i * ⟪b i, u⟫_ℝ) ^ 2
        = (ψ i) ^ 2 * (⟪b i, u⟫_ℝ) ^ 2 := by ring
      _ ≤ Cψ ^ 2 * (⟪b i, u⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (h_psi_sq_le i) h_inner_sq_nn
  have h_summable_f_sq :
      Summable (fun i : EigenIdx (I := I) (M := M) g =>
        (ψ i * ⟪b i, u⟫_ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ h_f_sq_le
      ((summable_basis_coeff_sq (I := I) (M := M) g u).mul_left (Cψ ^ 2))
    intro i; positivity
  have h_norm_sq_eq := orthonormal_norm_sq_eq_tsum_sq (I := I) (M := M) g
    (fun i => ψ i * ⟪b i, u⟫_ℝ) h_summable_f_sq
  change ‖∑' i, (ψ i * ⟪b i, u⟫_ℝ) • b i‖ ≤ Cψ * ‖u‖
  have h_norm_sq_le : ‖∑' i, (ψ i * ⟪b i, u⟫_ℝ) • b i‖ ^ 2 ≤
      Cψ ^ 2 * ‖u‖ ^ 2 := by
    rw [h_norm_sq_eq]
    have h_dom : ∑' i : EigenIdx (I := I) (M := M) g,
        (ψ i * ⟪b i, u⟫_ℝ) ^ 2 ≤
          Cψ ^ 2 * ∑' i, (⟪b i, u⟫_ℝ) ^ 2 := by
      have h_step : ∑' i : EigenIdx (I := I) (M := M) g,
          (ψ i * ⟪b i, u⟫_ℝ) ^ 2 ≤
            ∑' i, Cψ ^ 2 * (⟪b i, u⟫_ℝ) ^ 2 :=
        Summable.tsum_le_tsum h_f_sq_le h_summable_f_sq
          ((summable_basis_coeff_sq (I := I) (M := M) g u).mul_left (Cψ ^ 2))
      rw [tsum_mul_left] at h_step
      exact h_step
    refine le_trans h_dom ?_
    rw [parseval_norm_sq (I := I) (M := M) g u]
  have h_lhs_nn : 0 ≤ ‖∑' i, (ψ i * ⟪b i, u⟫_ℝ) • b i‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ Cψ * ‖u‖ := mul_nonneg hCψ_nn (norm_nonneg _)
  have h_rhs_sq : (Cψ * ‖u‖) ^ 2 = Cψ ^ 2 * ‖u‖ ^ 2 := by ring
  rw [← h_rhs_sq] at h_norm_sq_le
  exact (abs_le_of_sq_le_sq' h_norm_sq_le h_rhs_nn).2

theorem hasDerivAt_heatPower
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatPower (I := I) (M := M) g k s)
      (-heatPower (I := I) (M := M) g (k + 1) t) t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have ht2_pos : (0 : ℝ) < t / 2 := by linarith
  set C := heatPowerCoeffBound (k + 2) (t / 2) with hC_def
  have hC_nn : 0 ≤ C := heatPowerCoeffBound_nonneg (k + 2) ht2_pos
  have hC1_pos : 0 < C + 1 := by linarith
  set δ : ℝ := min (t / 2) (ε / (C + 1)) with hδ_def
  have hδ_pos : 0 < δ := by
    apply lt_min ht2_pos
    exact div_pos hε hC1_pos
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Metric.ball (0 : ℝ) δ, Metric.ball_mem_nhds 0 hδ_pos, ?_⟩
  intro h hh
  rw [Metric.mem_ball] at hh
  rw [dist_zero_right, Real.norm_eq_abs] at hh
  have h_abs_le_t2 : |h| ≤ t / 2 := by
    have := min_le_left (t / 2) (ε / (C + 1))
    linarith [hh]
  have h_abs_lt_eC : |h| < ε / (C + 1) := by
    have := min_le_right (t / 2) (ε / (C + 1))
    linarith [hh]
  have h_op_bound :
      ‖heatPower (I := I) (M := M) g k (t + h) -
          heatPower (I := I) (M := M) g k t -
          h • -heatPower (I := I) (M := M) g (k + 1) t‖ ≤
        C * h ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    have h_eq : heatPower (I := I) (M := M) g k (t + h) -
            heatPower (I := I) (M := M) g k t -
            h • -heatPower (I := I) (M := M) g (k + 1) t =
        heatPower (I := I) (M := M) g k (t + h) -
            heatPower (I := I) (M := M) g k t +
            h • heatPower (I := I) (M := M) g (k + 1) t := by
      rw [show h • -heatPower (I := I) (M := M) g (k + 1) t =
          -(h • heatPower (I := I) (M := M) g (k + 1) t) from by
        rw [smul_neg]]
      abel
    rw [h_eq]
    rw [show (heatPower (I := I) (M := M) g k (t + h) -
          heatPower (I := I) (M := M) g k t +
            h • heatPower (I := I) (M := M) g (k + 1) t) u =
        heatPower (I := I) (M := M) g k (t + h) u -
          heatPower (I := I) (M := M) g k t u +
            h • heatPower (I := I) (M := M) g (k + 1) t u from rfl]
    have h_taylor := norm_heatPower_taylor_remainder (I := I) (M := M) g k ht
      h_abs_le_t2 u
    rw [show C * h ^ 2 * ‖u‖ =
        (heatPowerCoeffBound (k + 2) (t / 2) * h ^ 2) * ‖u‖ from rfl]
    exact h_taylor
  refine le_trans h_op_bound ?_
  have h_h2_eq : h ^ 2 = |h| * |h| := by
    rw [sq]; rw [show h * h = |h| * |h| from by rw [← abs_mul]; rw [abs_mul_self]]
  rw [h_h2_eq]
  rw [show C * (|h| * |h|) = C * |h| * |h| from by ring]
  rw [show ε * ‖h‖ = ε * |h| from by rw [Real.norm_eq_abs]]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have h_step : (C + 1) * |h| < ε := by
    have h_lt : |h| < ε / (C + 1) := h_abs_lt_eC
    have h_mul_lt : (C + 1) * |h| < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left h_lt hC1_pos
    rw [mul_div_cancel₀ ε (ne_of_gt hC1_pos)] at h_mul_lt
    exact h_mul_lt
  linarith [abs_nonneg h, h_step]

theorem hasDerivAt_heatSemigroup
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatSemigroup (I := I) (M := M) g s)
      (-heatPower (I := I) (M := M) g 1 t) t := by
  have h := hasDerivAt_heatPower (I := I) (M := M) g 0 ht
  have h_funext : (fun s : ℝ => heatPower (I := I) (M := M) g 0 s) =
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s) := by
    funext s; exact heatPower_zero (I := I) (M := M) g s
  rw [h_funext] at h
  exact h

theorem differentiableAt_heatPower
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun s : ℝ => heatPower (I := I) (M := M) g k s) t :=
  (hasDerivAt_heatPower (I := I) (M := M) g k ht).differentiableAt

theorem differentiableOn_heatPower_Ioi
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    DifferentiableOn ℝ (fun s : ℝ => heatPower (I := I) (M := M) g k s)
      (Set.Ioi 0) := by
  intro t ht
  exact (differentiableAt_heatPower (I := I) (M := M) g k ht).differentiableWithinAt

theorem continuousAt_heatPower
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => heatPower (I := I) (M := M) g k s) t :=
  (hasDerivAt_heatPower (I := I) (M := M) g k ht).continuousAt

theorem continuousOn_heatPower_Ioi
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ContinuousOn (fun s : ℝ => heatPower (I := I) (M := M) g k s) (Set.Ioi 0) :=
  fun _ ht => (continuousAt_heatPower (I := I) (M := M) g k ht).continuousWithinAt

theorem deriv_heatPower
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s : ℝ => heatPower (I := I) (M := M) g k s) t =
      -heatPower (I := I) (M := M) g (k + 1) t :=
  (hasDerivAt_heatPower (I := I) (M := M) g k ht).deriv

theorem iteratedDerivWithin_heatSemigroup_Ioi
    (g : SmoothRiemannianMetric I M) :
    ∀ j : ℕ, ∀ {t : ℝ}, 0 < t →
      iteratedDerivWithin j
          (fun s : ℝ => heatSemigroup (I := I) (M := M) g s) (Set.Ioi 0) t =
        (-1 : ℝ) ^ j • heatPower (I := I) (M := M) g j t := by
  intro j
  induction j with
  | zero =>
    intro t ht
    simp only [iteratedDerivWithin_zero, pow_zero, one_smul]
    rw [heatPower_zero]
  | succ j ih =>
    intro t ht
    have hOi_unique : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ)) := uniqueDiffOn_Ioi 0
    have ht_mem : t ∈ Set.Ioi (0 : ℝ) := ht
    rw [iteratedDerivWithin_succ]
    have h_eq_on : Set.EqOn
        (iteratedDerivWithin j (fun s : ℝ =>
          heatSemigroup (I := I) (M := M) g s) (Set.Ioi 0))
        (fun s : ℝ => (-1 : ℝ) ^ j • heatPower (I := I) (M := M) g j s)
        (Set.Ioi 0) := by
      intro s hs
      exact ih hs
    have h_dw_eq :
        derivWithin (iteratedDerivWithin j
          (fun s : ℝ => heatSemigroup (I := I) (M := M) g s) (Set.Ioi 0))
          (Set.Ioi 0) t =
        derivWithin (fun s : ℝ => (-1 : ℝ) ^ j •
          heatPower (I := I) (M := M) g j s) (Set.Ioi 0) t :=
      derivWithin_congr h_eq_on (h_eq_on ht_mem)
    rw [h_dw_eq]
    have hd : HasDerivAt
        (fun s : ℝ => (-1 : ℝ) ^ j • heatPower (I := I) (M := M) g j s)
        ((-1 : ℝ) ^ j • -heatPower (I := I) (M := M) g (j + 1) t) t := by
      have hbase := hasDerivAt_heatPower (I := I) (M := M) g j ht
      exact hbase.const_smul ((-1 : ℝ) ^ j)
    have hd_within :
        HasDerivWithinAt
          (fun s : ℝ => (-1 : ℝ) ^ j • heatPower (I := I) (M := M) g j s)
          ((-1 : ℝ) ^ j • -heatPower (I := I) (M := M) g (j + 1) t)
          (Set.Ioi 0) t :=
      hd.hasDerivWithinAt
    have h_unique : UniqueDiffWithinAt ℝ (Set.Ioi (0 : ℝ)) t :=
      hOi_unique t ht
    rw [hd_within.derivWithin h_unique]
    rw [pow_succ]
    rw [show (-1 : ℝ) ^ j * -1 = -((-1 : ℝ) ^ j) from by ring]
    rw [neg_smul, smul_neg]

theorem contDiffOn_heatPower_Ioi
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun s : ℝ => heatPower (I := I) (M := M) g k s)
      (Set.Ioi 0) := by
  rw [contDiffOn_infty]
  intro n
  induction n generalizing k with
  | zero =>
    change ContDiffOn ℝ 0 (fun s : ℝ => heatPower (I := I) (M := M) g k s)
      (Set.Ioi 0)
    rw [contDiffOn_zero]
    exact continuousOn_heatPower_Ioi (I := I) (M := M) g k
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 from by
        push_cast; rfl]
    rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ioi 0)]
    refine ⟨?_, ?_, ?_⟩
    · exact (differentiableOn_heatPower_Ioi (I := I) (M := M) g k)
    · intro h_omega
      exfalso
      simp at h_omega
    · have h_deriv_eq : Set.EqOn
          (derivWithin (fun s : ℝ => heatPower (I := I) (M := M) g k s)
            (Set.Ioi 0))
          (fun s : ℝ => -heatPower (I := I) (M := M) g (k + 1) s)
          (Set.Ioi 0) := by
        intro s hs
        have hd := hasDerivAt_heatPower (I := I) (M := M) g k hs
        have hd_within :
            HasDerivWithinAt
              (fun s : ℝ => heatPower (I := I) (M := M) g k s)
              (-heatPower (I := I) (M := M) g (k + 1) s)
              (Set.Ioi 0) s :=
          hd.hasDerivWithinAt
        rw [hd_within.derivWithin ((uniqueDiffOn_Ioi 0) s hs)]
      apply ContDiffOn.congr _ h_deriv_eq
      have h_neg : (fun s : ℝ => -heatPower (I := I) (M := M) g (k + 1) s) =
          (fun s : ℝ => -1 • heatPower (I := I) (M := M) g (k + 1) s) := by
        funext s; rw [neg_one_smul]
      rw [h_neg]
      exact (ih (k + 1)).const_smul _

theorem contDiffOn_heatSemigroup_Ioi
    (g : SmoothRiemannianMetric I M) :
    ContDiffOn ℝ ∞ (fun s : ℝ => heatSemigroup (I := I) (M := M) g s)
      (Set.Ioi 0) := by
  have h := contDiffOn_heatPower_Ioi (I := I) (M := M) g 0
  have h_eq : (fun s : ℝ => heatPower (I := I) (M := M) g 0 s) =
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g s) := by
    funext s; exact heatPower_zero (I := I) (M := M) g s
  rw [h_eq] at h
  exact h

end HeatEquation
end Analysis
end DifferentialGeometry

end
