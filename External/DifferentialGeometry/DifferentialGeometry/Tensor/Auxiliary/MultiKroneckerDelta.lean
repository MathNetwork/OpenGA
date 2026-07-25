import DifferentialGeometry.Tensor.Auxiliary.Perm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Equiv.Perm

namespace Fin

noncomputable def multiKroneckerDelta {R : Type*} [CommRing R] {k n : ℕ}
    (I J : Fin k → Fin n) : R :=
  Matrix.det (fun i j : Fin k => if I i = J j then 1 else 0)

variable {R : Type*} [CommRing R] {k n : ℕ}

theorem multiKroneckerDelta_comp_perm
    {J : Fin k → Fin n} (hJ : Function.Injective J)
    (σ : Equiv.Perm (Fin k)) :
    multiKroneckerDelta (R := R) (J ∘ ⇑σ) J = (Equiv.Perm.sign σ : R) := by
  unfold multiKroneckerDelta
  simp only [Function.comp, hJ.eq_iff]
  rw [show (fun i j : Fin k => if σ i = j then (1 : R) else 0) =
    (1 : Matrix (Fin k) (Fin k) R).submatrix (⇑σ) id from by
    ext i j; simp [Matrix.submatrix_apply, Matrix.one_apply]]
  rw [Matrix.det_permute, Matrix.det_one, mul_one]

theorem multiKroneckerDelta_eq_zero_of_not_injective_left
    {I J : Fin k → Fin n} (hI : ¬Function.Injective I) :
    multiKroneckerDelta (R := R) I J = 0 := by
  unfold multiKroneckerDelta
  obtain ⟨i₁, i₂, heq, hne⟩ := Function.not_injective_iff.mp hI
  exact Matrix.det_zero_of_row_eq hne (funext fun j => by rw [heq])

theorem multiKroneckerDelta_eq_zero_of_not_injective_right
    {I J : Fin k → Fin n} (hJ : ¬Function.Injective J) :
    multiKroneckerDelta (R := R) I J = 0 := by
  unfold multiKroneckerDelta
  obtain ⟨j₁, j₂, heq, hne⟩ := Function.not_injective_iff.mp hJ
  exact Matrix.det_zero_of_column_eq hne (fun r => by rw [heq])

theorem multiKroneckerDelta_eq_zero
    {I J : Fin k → Fin n}
    (h : ∀ σ : Equiv.Perm (Fin k), I ≠ J ∘ ⇑σ) :
    multiKroneckerDelta (R := R) I J = 0 := by
  by_cases hI : Function.Injective I
  · by_cases hJ : Function.Injective J
    · have ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
        by_contra hall
        push Not at hall
        choose f hf using hall
        have hf_inj : Function.Injective f :=
          fun a b hab => hI (by rw [hf a, hf b, hab])
        exact h (Equiv.ofBijective f
          ((Fintype.bijective_iff_injective_and_card f).mpr
            ⟨hf_inj, rfl⟩)) (funext hf)
      unfold multiKroneckerDelta
      exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => if_neg (hi j))
    · exact multiKroneckerDelta_eq_zero_of_not_injective_right hJ
  · exact multiKroneckerDelta_eq_zero_of_not_injective_left hI

theorem multiKroneckerDelta_symm (I J : Fin k → Fin n) :
    multiKroneckerDelta (R := R) I J = multiKroneckerDelta J I := by
  unfold multiKroneckerDelta
  conv_lhs => rw [← Matrix.det_transpose]
  congr 1; ext i j
  simp [Matrix.transpose_apply, eq_comm]

theorem multiKroneckerDelta_comp_perm_left
    (I : Fin k → Fin n) (J : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    multiKroneckerDelta (R := R) (I ∘ ⇑σ) J =
    (Equiv.Perm.sign σ : R) * multiKroneckerDelta I J := by
  unfold multiKroneckerDelta
  set M : Matrix (Fin k) (Fin k) R := fun i j => if I i = J j then 1 else 0
  have : (fun i j : Fin k => if (I ∘ ⇑σ) i = J j then (1 : R) else 0) = M.submatrix σ id := by
    ext i j; simp [Matrix.submatrix_apply, M]
  rw [this, Matrix.det_permute]

theorem multiKroneckerDelta_addCases_comm
    {d m n : ℕ} (I : Fin m → Fin d) (J : Fin n → Fin d)
    (v : Fin (m + n) → Fin d) :
    multiKroneckerDelta (R := R) (Fin.addCases J I)
      (v ∘ ⇑Fin.finAddCongr) =
    (-1 : R) ^ (m * n) *
      multiKroneckerDelta (Fin.addCases I J) v := by
  simp only [multiKroneckerDelta]
  rw [← Matrix.det_reindex_self Fin.finAddCongr]
  set τ := addCasesSwapPerm m n
  set M : Matrix (Fin (m + n)) (Fin (m + n)) R :=
    fun i j => if Fin.addCases I J i = v j then 1 else 0
  have h_eq : (Matrix.reindex Fin.finAddCongr Fin.finAddCongr)
      (fun i j =>
        if Fin.addCases J I i =
          (v ∘ ⇑Fin.finAddCongr) j then (1 : R) else 0) =
      M.submatrix τ id := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Function.comp_apply, Equiv.apply_symm_apply, id, M]
    have h_idx : @Fin.addCases n m (fun _ => Fin d) J I ((@Fin.finAddCongr n m).symm ⟨i, hi⟩) =
        @Fin.addCases m n (fun _ => Fin d) I J (τ ⟨i, hi⟩) := by
      unfold Fin.addCases Fin.finAddCongr finCongr τ addCasesSwapPerm
      simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
      by_cases h1 : i < n
      · simp only [h1, dite_true]
        have h2 : ¬(m + i < m) := by omega
        simp_all
      · simp only [h1, dite_false]
        have h2 : i - n < m := by omega
        simp_all
    rw [h_idx]; rfl
  rw [h_eq, Matrix.det_permute]
  have h_sign : (↑(Equiv.Perm.sign τ) : R) = (-1 : R) ^ (m * n) := by
    rw [addCasesSwapPerm_sign]
    push_cast
    rfl
  rw [h_sign]

theorem multiKroneckerDelta_addCases_assoc
    {d m n p : ℕ} (I : Fin m → Fin d) (J : Fin n → Fin d) (K : Fin p → Fin d)
    (v : Fin (m + n + p) → Fin d) :
    multiKroneckerDelta (R := R)
      (fun i => Fin.addCases I (fun j => Fin.addCases J K j) i)
      (v ∘ ⇑Fin.finAssoc.symm) =
    multiKroneckerDelta
      (fun i => Fin.addCases (fun j => Fin.addCases I J j) K i) v := by
  simp only [multiKroneckerDelta]
  rw [← Matrix.det_reindex_self Fin.finAssoc]
  congr 1; ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.reindex, Matrix.submatrix, Equiv.coe_fn_mk, Matrix.of_apply, Function.comp]
  congr 1
  simp only [Fin.addCases, Fin.finAssoc, Fin.val_castLT, Fin.val_subNat, Fin.val_cast,
    finCongr, Equiv.coe_fn_symm_mk]
  split_ifs <;> simp_all [Fin.ext_iff, Nat.sub_sub] <;> omega

variable {𝕜 : Type*} [Field 𝕜]

open Classical in

theorem multiKroneckerDelta_cauchyBinet [CharZero 𝕜]
    {d m p : ℕ} (I : Fin m → Fin d) (J : Fin p → Fin d) (v : Fin (m + p) → Fin d) :
    ((↑(m.factorial * p.factorial) : 𝕜))⁻¹ •
      ∑ σ : Equiv.Perm (Fin (m + p)),
        Equiv.Perm.sign σ • (multiKroneckerDelta (R := 𝕜) I (v ∘ ⇑σ ∘ Fin.castAdd p) *
          multiKroneckerDelta (R := 𝕜) J (v ∘ ⇑σ ∘ Fin.natAdd m)) =
    multiKroneckerDelta (Fin.addCases I J) v := by
  have h_ne : (↑(m.factorial * p.factorial) : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos p)).ne'
  rw [inv_smul_eq_iff₀ h_ne]
  simp only [multiKroneckerDelta, Function.comp, Matrix.det_apply,
    Units.smul_def, zsmul_eq_mul, Nat.cast_smul_eq_nsmul 𝕜, nsmul_eq_mul]
  set M : Matrix (Fin (m + p)) (Fin (m + p)) 𝕜 :=
    fun a b => if Fin.addCases I J a = v b then 1 else 0 with hM_def
  have h1 : ∀ (α : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin (m + p))) (i : Fin m),
      (if I (α i) = v (σ (Fin.castAdd p i)) then (1 : 𝕜) else 0) =
      M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i)) :=
    fun _ _ _ => by simp [hM_def, Fin.addCases_left]
  have h2 : ∀ (β : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin (m + p))) (j : Fin p),
      (if J (β j) = v (σ (Fin.natAdd m j)) then (1 : 𝕜) else 0) =
      M (Fin.natAdd m (β j)) (σ (Fin.natAdd m j)) :=
    fun _ _ _ => by simp [hM_def, Fin.addCases_right]
  conv_lhs =>
    arg 2; ext σ; arg 2; arg 1; arg 2; ext α; arg 2; arg 2; ext i
    erw [h1 α σ i]
  conv_lhs =>
    arg 2; ext σ; arg 2; arg 2; arg 2; ext β; arg 2; arg 2; ext j
    erw [h2 β σ j]
  have h_inner : ∀ α : Equiv.Perm (Fin m), ∀ β : Equiv.Perm (Fin p),
      ∀ σ : Equiv.Perm (Fin (m + p)),
      ↑↑(Equiv.Perm.sign σ) * (↑↑(Equiv.Perm.sign α) *
        ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
      (↑↑(Equiv.Perm.sign β) *
        ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))) =
      ↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign β) *
      (↑↑(Equiv.Perm.sign σ) *
        ((∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
         (∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))))) := by
    intros; ring
  have h_sum : ∀ α : Equiv.Perm (Fin m), ∀ β : Equiv.Perm (Fin p),
      ∑ σ : Equiv.Perm (Fin (m + p)),
        ↑↑(Equiv.Perm.sign σ) * (↑↑(Equiv.Perm.sign α) *
          ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
        (↑↑(Equiv.Perm.sign β) *
          ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))) =
      M.det := by
    intro α β
    simp_rw [h_inner α β, ← Finset.mul_sum, inner_sum_eq_det M α β]
    have hsα : (↑↑(Equiv.Perm.sign α) : 𝕜) * ↑↑(Equiv.Perm.sign α) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign α) with h | h <;> simp [h]
    have hsβ : (↑↑(Equiv.Perm.sign β) : 𝕜) * ↑↑(Equiv.Perm.sign β) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign β) with h | h <;> simp [h]
    calc ↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign β) *
          (↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign β) * M.det)
        = (↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign α)) *
          ((↑↑(Equiv.Perm.sign β) * ↑↑(Equiv.Perm.sign β)) * M.det) := by ring
      _ = 1 * (1 * M.det) := by rw [hsα, hsβ]
      _ = M.det := by ring
  simp_rw [Fintype.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ (α := Equiv.Perm (Fin (m + p))))]
  simp_rw [show ∀ α : Equiv.Perm (Fin m),
    ∑ σ : Equiv.Perm (Fin (m + p)), ∑ β : Equiv.Perm (Fin p),
      ↑↑(Equiv.Perm.sign σ) *
        ((↑↑(Equiv.Perm.sign α) * ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
          (↑↑(Equiv.Perm.sign β) * ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i)))) =
    ∑ β : Equiv.Perm (Fin p), ∑ σ : Equiv.Perm (Fin (m + p)),
      ↑↑(Equiv.Perm.sign σ) *
        ((↑↑(Equiv.Perm.sign α) * ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
          (↑↑(Equiv.Perm.sign β) * ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))))
    from fun _ => Finset.sum_comm]
  simp_rw [show ∀ (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin p))
    (σ : Equiv.Perm (Fin (m + p))),
    ↑↑(Equiv.Perm.sign σ) *
      ((↑↑(Equiv.Perm.sign α) * ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
        (↑↑(Equiv.Perm.sign β) * ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i)))) =
    ↑↑(Equiv.Perm.sign σ) * (↑↑(Equiv.Perm.sign α) *
      ∏ i, M (Fin.castAdd p (α i)) (σ (Fin.castAdd p i))) *
    (↑↑(Equiv.Perm.sign β) *
      ∏ i, M (Fin.natAdd m (β i)) (σ (Fin.natAdd m i))) from fun _ _ _ => by ring,
    h_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [show M.det = ∑ σ, ↑↑(Equiv.Perm.sign σ) *
    ∏ i, (if Fin.addCases I J (σ i) = v i then (1 : 𝕜) else 0) from by
      rw [Matrix.det_apply]; congr 1; ext σ
      simp [Units.smul_def, zsmul_eq_mul, hM_def]]
  simp only [Finset.smul_sum, nsmul_eq_mul, Nat.cast_mul]
  congr 1; ext σ; ring

end Fin
