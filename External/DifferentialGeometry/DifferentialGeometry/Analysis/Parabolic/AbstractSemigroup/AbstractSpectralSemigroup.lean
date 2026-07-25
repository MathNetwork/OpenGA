import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.BoundedC0Semigroup
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp


noncomputable section

open Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace BigOperators ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X]

def heatCoeff (lam : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  Real.exp (-(lam i) * t)

lemma heatCoeff_def (lam : ι → ℝ) (t : ℝ) (i : ι) :
    heatCoeff lam t i = Real.exp (-(lam i) * t) := rfl

lemma heatCoeff_mem_unit_interval {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    0 < heatCoeff lam t i ∧ heatCoeff lam t i ≤ 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [heatCoeff, Real.exp_le_one_iff]
  have hl := hlam i
  nlinarith

private lemma heatCoeff_sq_le_one {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    (heatCoeff lam t i) ^ 2 ≤ 1 := by
  obtain ⟨h_pos, h_le⟩ := heatCoeff_mem_unit_interval hlam ht i
  nlinarith [sq_nonneg (heatCoeff lam t i - 1), h_pos.le]

private lemma summable_basis_coeff_sq (b : HilbertBasis ι ℝ X) (v : X) :
    Summable (fun i : ι => ‖⟪b i, v⟫_ℝ‖ ^ 2) := by
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ (fun _ : ι => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ X (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_summable_smul : Summable (fun i : ι => ⟪b i, v⟫_ℝ • b i) := by
    have h_hsum : HasSum (fun i => b.repr v i • b i) v := b.hasSum_repr v
    have h_eq : (fun i => b.repr v i • b i) = (fun i => ⟪b i, v⟫_ℝ • b i) := by
      funext i; rw [b.repr_apply_apply]
    rw [h_eq] at h_hsum
    exact h_hsum.summable
  have h_iff := h_orthFam.summable_iff_norm_sq_summable (fun i : ι => ⟪b i, v⟫_ℝ)
  have h_map_eq : (fun i : ι =>
        LinearIsometry.toSpanSingleton ℝ X (h_orthonormal.1 i) (⟪b i, v⟫_ℝ)) =
      (fun i => ⟪b i, v⟫_ℝ • b i) := by
    funext i; rw [LinearIsometry.toSpanSingleton_apply]
  rw [h_map_eq] at h_iff
  exact h_iff.mp h_summable_smul

lemma summable_basis_coeff_sq' (b : HilbertBasis ι ℝ X) (v : X) :
    Summable (fun i : ι => (⟪b i, v⟫_ℝ) ^ 2) := by
  have h := summable_basis_coeff_sq b v
  have h_eq : (fun i : ι => ‖⟪b i, v⟫_ℝ‖ ^ 2) = (fun i => (⟪b i, v⟫_ℝ) ^ 2) := by
    funext i; rw [Real.norm_eq_abs, sq_abs]
  rwa [h_eq] at h

omit [CompleteSpace X] in
private lemma parseval_norm_sq (b : HilbertBasis ι ℝ X) (v : X) :
    ‖v‖ ^ 2 = ∑' i : ι, (⟪b i, v⟫_ℝ) ^ 2 := by
  have h_par := b.tsum_inner_mul_inner v v
  have h_sq : ⟪v, v⟫_ℝ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  have h_eq : (fun i : ι => ⟪v, b i⟫_ℝ * ⟪b i, v⟫_ℝ) =
      (fun i => (⟪b i, v⟫_ℝ) ^ 2) := by
    funext i
    rw [show ⟪v, b i⟫_ℝ = ⟪b i, v⟫_ℝ from real_inner_comm _ _, sq]
  rw [h_eq] at h_par
  linarith [h_par, h_sq]

lemma summable_heatTerm (b : HilbertBasis ι ℝ X) {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) (v : X) :
    Summable (fun i : ι => heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i) := by
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ (fun _ : ι => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ X (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_sq_summable : Summable
      (fun i : ι => (heatCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (summable_basis_coeff_sq' b v)
    · intro i; positivity
    · intro i
      have h_sq_le : (heatCoeff lam t i) ^ 2 ≤ 1 := heatCoeff_sq_le_one hlam ht i
      have h_inner_sq_nn : 0 ≤ (⟪b i, v⟫_ℝ) ^ 2 := sq_nonneg _
      calc (heatCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2
          = (heatCoeff lam t i) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 := by ring
        _ ≤ 1 * (⟪b i, v⟫_ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h_sq_le h_inner_sq_nn
        _ = (⟪b i, v⟫_ℝ) ^ 2 := one_mul _
  have h_iff := h_orthFam.summable_iff_norm_sq_summable
    (fun i : ι => heatCoeff lam t i * ⟪b i, v⟫_ℝ)
  have h_sq_eq : (fun i : ι => ‖heatCoeff lam t i * ⟪b i, v⟫_ℝ‖ ^ 2) =
      (fun i => (heatCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2) := by
    funext i; rw [Real.norm_eq_abs, sq_abs]
  rw [h_sq_eq] at h_iff
  have h_map_eq : (fun i : ι =>
        LinearIsometry.toSpanSingleton ℝ X (h_orthonormal.1 i)
          (heatCoeff lam t i * ⟪b i, v⟫_ℝ)) =
      (fun i => heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i) := by
    funext i; rw [LinearIsometry.toSpanSingleton_apply, mul_smul]
  have h_summable_V := h_iff.mpr h_sq_summable
  rw [h_map_eq] at h_summable_V
  exact h_summable_V

lemma orthonormal_norm_sq_eq_tsum_sq (b : HilbertBasis ι ℝ X)
    (f : ι → ℝ) (h_summable : Summable (fun i => (f i) ^ 2)) :
    ‖∑' i : ι, f i • b i‖ ^ 2 = ∑' i, (f i) ^ 2 := by
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_orthFam :
      OrthogonalFamily ℝ (fun _ : ι => ℝ)
        (fun i => LinearIsometry.toSpanSingleton ℝ X (h_orthonormal.1 i)) :=
    h_orthonormal.orthogonalFamily
  have h_memℓp : Memℓp (fun i : ι => f i) 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq : (fun i : ι => ‖f i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => (f i) ^ 2) := by
      funext i; rw [hpr, Real.norm_eq_abs, ← sq_abs]; norm_cast
    rw [h_eq]; exact h_summable
  set f_lp : lp (fun _ : ι => ℝ) 2 := ⟨fun i => f i, h_memℓp⟩
  have h_iso_norm : ‖h_orthFam.linearIsometry f_lp‖ = ‖f_lp‖ :=
    h_orthFam.linearIsometry.norm_map f_lp
  have h_iso_apply : h_orthFam.linearIsometry f_lp =
      ∑' i : ι, f i • b i := by
    rw [h_orthFam.linearIsometry_apply f_lp]
    apply tsum_congr
    intro i; rw [LinearIsometry.toSpanSingleton_apply]
  have h_lp_norm_sq : ‖f_lp‖ ^ 2 = ∑' i : ι, (f i) ^ 2 := by
    have h_norm_sq := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℝ)
      (by norm_num) f_lp
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [hpr] at h_norm_sq
    have h_lhs : ‖f_lp‖ ^ (2 : ℝ) = ‖f_lp‖ ^ 2 := by norm_cast
    rw [h_lhs] at h_norm_sq
    have h_rhs_eq : (∑' i : ι, ‖(f_lp : ι → ℝ) i‖ ^ (2 : ℝ)) =
        ∑' i, (f i) ^ 2 := by
      apply tsum_congr
      intro i
      have h_eq_pt : (f_lp : ι → ℝ) i = f i := rfl
      rw [h_eq_pt, Real.norm_eq_abs, ← sq_abs]; norm_cast
    rw [h_rhs_eq] at h_norm_sq
    exact h_norm_sq
  have h_eq1 : ∑' i : ι, f i • b i = h_orthFam.linearIsometry f_lp :=
    h_iso_apply.symm
  rw [h_eq1, h_iso_norm, h_lp_norm_sq]

private lemma norm_sq_heatTerm_sum_le (b : HilbertBasis ι ℝ X) {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) (v : X) :
    ‖∑' i : ι, heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have h_summand_eq :
      (fun i : ι => heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i) =
      (fun i => (heatCoeff lam t i * ⟪b i, v⟫_ℝ) • b i) := by
    funext i; rw [mul_smul]
  rw [h_summand_eq]
  set f : ι → ℝ := fun i => heatCoeff lam t i * ⟪b i, v⟫_ℝ
  have h_coeff_sq_summable := summable_basis_coeff_sq' b v
  have h_f_sq_le : ∀ i : ι, (f i) ^ 2 ≤ (⟪b i, v⟫_ℝ) ^ 2 := by
    intro i
    have h_sq_le : (heatCoeff lam t i) ^ 2 ≤ 1 := heatCoeff_sq_le_one hlam ht i
    have h_inner_sq_nn : 0 ≤ (⟪b i, v⟫_ℝ) ^ 2 := sq_nonneg _
    change (heatCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2 ≤ (⟪b i, v⟫_ℝ) ^ 2
    calc (heatCoeff lam t i * ⟪b i, v⟫_ℝ) ^ 2
        = (heatCoeff lam t i) ^ 2 * (⟪b i, v⟫_ℝ) ^ 2 := by ring
      _ ≤ 1 * (⟪b i, v⟫_ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right h_sq_le h_inner_sq_nn
      _ = (⟪b i, v⟫_ℝ) ^ 2 := one_mul _
  have h_summable_f_sq : Summable (fun i : ι => (f i) ^ 2) := by
    refine Summable.of_nonneg_of_le ?_ ?_ h_coeff_sq_summable
    · intro i; positivity
    · exact h_f_sq_le
  have h_norm_sq_eq := orthonormal_norm_sq_eq_tsum_sq b f h_summable_f_sq
  change ‖∑' i, f i • b i‖ ^ 2 ≤ ‖v‖ ^ 2
  rw [h_norm_sq_eq]
  have h_dom : ∑' i : ι, (f i) ^ 2 ≤ ∑' i, (⟪b i, v⟫_ℝ) ^ 2 :=
    Summable.tsum_le_tsum h_f_sq_le h_summable_f_sq h_coeff_sq_summable
  refine le_trans h_dom ?_
  rw [← parseval_norm_sq b v]

private lemma norm_heatTerm_sum_le (b : HilbertBasis ι ℝ X) {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) (v : X) :
    ‖∑' i : ι, heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i‖ ≤ ‖v‖ := by
  have h_sq := norm_sq_heatTerm_sum_le b hlam ht v
  exact (abs_le_of_sq_le_sq' h_sq (norm_nonneg v)).2

private def abstractSpectralSemigroupFun (b : HilbertBasis ι ℝ X)
    (lam : ι → ℝ) (t : ℝ) (v : X) : X :=
  ∑' i : ι, heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i

private lemma abstractSpectralSemigroupFun_add (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t)
    (v₁ v₂ : X) :
    abstractSpectralSemigroupFun b lam t (v₁ + v₂) =
      abstractSpectralSemigroupFun b lam t v₁ +
        abstractSpectralSemigroupFun b lam t v₂ := by
  unfold abstractSpectralSemigroupFun
  have h_sum_eq : (fun i : ι => heatCoeff lam t i • ⟪b i, v₁ + v₂⟫_ℝ • b i) =
      (fun i => (heatCoeff lam t i • ⟪b i, v₁⟫_ℝ • b i) +
        (heatCoeff lam t i • ⟪b i, v₂⟫_ℝ • b i)) := by
    funext i; rw [inner_add_right, add_smul, smul_add]
  rw [h_sum_eq, Summable.tsum_add
    (summable_heatTerm b hlam ht v₁) (summable_heatTerm b hlam ht v₂)]

private lemma abstractSpectralSemigroupFun_smul (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t)
    (c : ℝ) (v : X) :
    abstractSpectralSemigroupFun b lam t (c • v) =
      c • abstractSpectralSemigroupFun b lam t v := by
  unfold abstractSpectralSemigroupFun
  have h_sum_eq : (fun i : ι => heatCoeff lam t i • ⟪b i, c • v⟫_ℝ • b i) =
      (fun i => c • (heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i)) := by
    funext i
    rw [real_inner_smul_right, smul_smul, smul_smul, smul_smul]
    congr 1; ring
  rw [h_sum_eq]
  exact (summable_heatTerm b hlam ht v).tsum_const_smul c

def abstractSpectralSemigroup (b : HilbertBasis ι ℝ X) {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) : X →L[ℝ] X := by
  by_cases ht : 0 ≤ t
  · refine LinearMap.mkContinuous
      { toFun := abstractSpectralSemigroupFun b lam t
        map_add' := abstractSpectralSemigroupFun_add b hlam ht
        map_smul' := fun c v => abstractSpectralSemigroupFun_smul b hlam ht c v }
      1 ?_
    intro v
    change ‖abstractSpectralSemigroupFun b lam t v‖ ≤ 1 * ‖v‖
    rw [one_mul]
    exact norm_heatTerm_sum_le b hlam ht v
  · exact 0

theorem abstractSpectralSemigroup_apply_of_nonneg (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) (v : X) :
    abstractSpectralSemigroup b hlam t v =
      ∑' i : ι, heatCoeff lam t i • ⟪b i, v⟫_ℝ • b i := by
  unfold abstractSpectralSemigroup
  rw [dif_pos ht]; rfl

theorem abstractSpectralSemigroup_of_neg (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : t < 0) :
    abstractSpectralSemigroup b hlam t = 0 := by
  unfold abstractSpectralSemigroup
  rw [dif_neg (not_le.mpr ht)]

theorem abstractSpectralSemigroup_opNorm_le_one (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) :
    ‖abstractSpectralSemigroup b hlam t‖ ≤ 1 := by
  unfold abstractSpectralSemigroup
  by_cases ht : 0 ≤ t
  · rw [dif_pos ht]
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · rw [dif_neg ht, norm_zero]; exact zero_le_one

theorem abstractSpectralSemigroup_apply_basis (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    abstractSpectralSemigroup b hlam t (b i) = heatCoeff lam t i • b i := by
  classical
  rw [abstractSpectralSemigroup_apply_of_nonneg b hlam ht (b i)]
  have h_orthonormal : Orthonormal ℝ b := b.orthonormal
  have h_inner_eq : ∀ j : ι, ⟪b j, b i⟫_ℝ = if j = i then 1 else 0 := by
    intro j; exact (orthonormal_iff_ite (𝕜 := ℝ) (v := b)).mp h_orthonormal j i
  have h_sum_eq : (fun j : ι => heatCoeff lam t j • ⟪b j, b i⟫_ℝ • b j) =
      (fun j => if j = i then heatCoeff lam t j • b j else 0) := by
    funext j
    rw [h_inner_eq]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  rw [h_sum_eq, tsum_ite_eq i]

end Parabolic
end Analysis
end DifferentialGeometry

end
