import Mathlib.GroupTheory.Perm.Fin
import OpenGALib.Algebraic.Auxiliary.Fin
import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-!
# Shuffle-derivative bijection

For the graded Leibniz rule `d(ω ∧ τ) = dω ∧ τ + (-1)^m ω ∧ dτ`, the proof
needs a sign-preserving bijection between the two double-sum index sets.

Given `k : Fin (m + n + 1)` (derivative position) and
`σ : Perm (Fin m ⊕ Fin n)` (inner shuffle), the combined permutation
`π := (Fin.cycleRange k)⁻¹ * decomposeFin.symm (0, σ_fin)` of `Fin (m + n + 1)`
sends `0 ↦ k` and `(j+1) ↦ k.succAbove (σ_fin j)`, with sign
`(-1)^k * sign σ`. Conjugating by `Φ := finSumFinEquiv.trans Fin.finAddFlipAssoc`
gives the corresponding `τ : Perm (Fin (m+1) ⊕ Fin n)`.
-/

open Equiv

namespace ContinuousAlternatingMap

variable {m n : ℕ}

/-- Transport a permutation of `Fin m ⊕ Fin n` to a permutation of `Fin (m + n)`. -/
noncomputable abbrev permFinOfSum (σ : Equiv.Perm (Fin m ⊕ Fin n)) : Equiv.Perm (Fin (m + n)) :=
  (finSumFinEquiv.permCongr σ : Equiv.Perm (Fin (m + n)))

/-- The identification `Fin (m + 1) ⊕ Fin n ≃ Fin (m + n + 1)`. -/
noncomputable abbrev finSuccSumEquiv : Fin (m + 1) ⊕ Fin n ≃ Fin (m + n + 1) :=
  finSumFinEquiv.trans Fin.finAddFlipAssoc

/-- Forward map. Construction:
1. Transport `σ` to `σ_fin : Perm (Fin (m + n))`.
2. Build `π := (cycleRange k)⁻¹ * decomposeFin.symm (0, σ_fin)`.
3. Conjugate by `finSuccSumEquiv` to get `Perm (Fin (m + 1) ⊕ Fin n)`. -/
noncomputable def derivShuffleLeftFwd
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  let σ_fin := permFinOfSum σ
  let π := (Fin.cycleRange k)⁻¹ * Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), σ_fin)
  finSuccSumEquiv.symm.permCongr π

/-- Always `0` since `cycleRange` places `k` at position `0` (= `inl 0`). -/
def derivShuffleLeftIdx
    (_k : Fin (m + n + 1)) (_σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Fin (m + 1) := 0

/-- Sign of the forward image: `sign τ = (-1)^k * sign σ`. -/
theorem derivShuffleLeftFwd_sign
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (derivShuffleLeftFwd k σ) =
      (-1 : ℤˣ) ^ k.val * Equiv.Perm.sign σ := by
  simp only [derivShuffleLeftFwd, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_inv, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign,
    if_true, one_mul, permFinOfSum]

/-- `decomposeFin.symm (0, ·)` is multiplicative. -/
private theorem decomposeFin_symm_zero_mul (e₁ e₂ : Equiv.Perm (Fin (m + n))) :
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₁) *
      Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₂) =
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₁ * e₂) := by
  ext x; refine Fin.cases ?_ ?_ x
  · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  · intro i
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply]

/-- `decomposeFin.symm (0, ·)` preserves inverses. -/
private theorem decomposeFin_symm_zero_inv (e : Equiv.Perm (Fin (m + n))) :
    (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e))⁻¹ =
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, decomposeFin_symm_zero_mul, mul_inv_cancel]
  ext x; refine Fin.cases (by simp) (fun i => by simp [Equiv.swap_self]) x

/-- `(permCongr e a)⁻¹ * (permCongr e b) = permCongr e (a⁻¹ * b)`. -/
private theorem permCongr_inv_mul {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] (e : α ≃ β) (a b : Equiv.Perm α) :
    (e.permCongr a)⁻¹ * (e.permCongr b) = e.permCongr (a⁻¹ * b) := by
  have hinv : e.permCongr a⁻¹ = (e.permCongr a)⁻¹ := by
    ext x; simp [Equiv.Perm.inv_def, Equiv.permCongr]; rfl
  rw [← hinv, ← Equiv.permCongr_mul]

theorem derivShuffleLeftFwd_wd (k : Fin (m + n + 1))
    (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) σ₁ σ₂) :
    (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range)
      (derivShuffleLeftFwd k σ₁) (derivShuffleLeftFwd k σ₂) := by
  rw [QuotientGroup.leftRel_apply] at h ⊢
  obtain ⟨⟨τ_l, τ_r⟩, hblock⟩ := h
  have hratio : (derivShuffleLeftFwd k σ₁)⁻¹ * (derivShuffleLeftFwd k σ₂) =
      finSuccSumEquiv.symm.permCongr
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)),
          permFinOfSum (σ₁⁻¹ * σ₂))) := by
    simp only [derivShuffleLeftFwd]
    rw [permCongr_inv_mul]; congr 1
    rw [mul_inv_rev, inv_inv, mul_assoc (Equiv.Perm.decomposeFin.symm _ )⁻¹,
        ← mul_assoc (Fin.cycleRange k), mul_inv_cancel, one_mul,
        decomposeFin_symm_zero_inv, decomposeFin_symm_zero_mul]
    have : (permFinOfSum σ₁)⁻¹ * permFinOfSum σ₂ = permFinOfSum (σ₁⁻¹ * σ₂) :=
      permCongr_inv_mul finSumFinEquiv σ₁ σ₂
    rw [this]
  rw [hratio, ← hblock]
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  intro x ⟨a, ha⟩; subst ha
  refine Fin.cases ?_ (fun a' => ?_) a
  · unfold finSuccSumEquiv; aesop
  · simp +decide [ Equiv.Perm.decomposeFin, permFinOfSum ]
    simp +decide [ Fin.finAddFlipAssoc, finSuccEquiv ]
    simp +decide [ finSuccEquiv', finCongr ]
    simp +decide [ Fin.castLE, Fin.castLT, Fin.cons ]
    simp +decide [ Fin.cases, finSumFinEquiv ]
    simp +decide [ Fin.induction, Fin.addCases ]
    simp +decide [ Fin.induction.go ]

/-! ### Rank function and injectivity helpers -/

/-- Rank of derivative position `k` among the left positions of shuffle `σ`. -/
noncomputable def derivShuffleJ (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Fin (m + 1) :=
  ⟨(Finset.univ.filter (fun i : Fin m =>
    (permFinOfSum σ (Fin.castAdd n i)).val < k.val)).card, by
    calc (Finset.univ.filter _).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = m := Finset.card_fin m
      _ < m + 1 := lt_add_one m⟩

/-- Changing the representative by `sumCongr τ_l τ_r` composes the left
block index with `τ_l`. -/
private theorem permFinOfSum_mul_sumCongr_castAdd (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (τ_l : Equiv.Perm (Fin m)) (τ_r : Equiv.Perm (Fin n)) (i : Fin m) :
    permFinOfSum (σ * Equiv.Perm.sumCongr τ_l τ_r) (Fin.castAdd n i) =
      permFinOfSum σ (Fin.castAdd n (τ_l i)) := by
  simp only [permFinOfSum, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl]

/-- Filtering by `P ∘ e` has the same cardinality as filtering by `P`. -/
private theorem card_filter_comp_perm {n : ℕ} (e : Equiv.Perm (Fin n))
    (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter (P ∘ ⇑e)).card = (Finset.univ.filter P).card := by
  have : Finset.univ.filter (P ∘ ⇑e) =
      (Finset.univ.filter P).map e.symm.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply, Function.comp_apply]
    exact ⟨fun h => ⟨e i, h, by simp⟩, fun ⟨j, hj, hji⟩ => by simpa [← hji]⟩
  rw [this, Finset.card_map]

/-- The rank function is well-defined on cosets. -/
theorem derivShuffleJ_wd (k : Fin (m + n + 1))
    (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range σ₁ σ₂) :
    derivShuffleJ k σ₁ = derivShuffleJ k σ₂ := by
  rw [QuotientGroup.leftRel_apply] at h
  obtain ⟨⟨τ_l, τ_r⟩, hblock⟩ := h
  have h_sc : Equiv.Perm.sumCongr τ_l τ_r = σ₁⁻¹ * σ₂ := by
    change (Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r) : Equiv.Perm _) = _; exact hblock
  have h_eq : σ₂ = σ₁ * Equiv.Perm.sumCongr τ_l τ_r := by rw [h_sc]; group
  subst h_eq
  simp only [derivShuffleJ, Fin.mk.injEq]
  show (Finset.univ.filter (fun i =>
    (permFinOfSum σ₁ (Fin.castAdd n i)).val < k.val)).card =
    (Finset.univ.filter (fun i =>
    (permFinOfSum (σ₁ * Equiv.Perm.sumCongr τ_l τ_r) (Fin.castAdd n i)).val < k.val)).card
  simp_rw [permFinOfSum_mul_sumCongr_castAdd]
  exact (card_filter_comp_perm τ_l _).symm

/-- `derivShuffleLeftFwd k` is injective on cosets. -/
theorem derivShuffleLeftFwd_coset_injective (k : Fin (m + n + 1))
    (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range
      (derivShuffleLeftFwd k σ₁) (derivShuffleLeftFwd k σ₂)) :
    QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range σ₁ σ₂ := by
  rw [QuotientGroup.leftRel_apply] at h ⊢
  have hratio : (derivShuffleLeftFwd k σ₁)⁻¹ * (derivShuffleLeftFwd k σ₂) =
      finSuccSumEquiv.symm.permCongr
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)),
          permFinOfSum (σ₁⁻¹ * σ₂))) := by
    simp only [derivShuffleLeftFwd]
    rw [permCongr_inv_mul]; congr 1
    rw [mul_inv_rev, inv_inv, mul_assoc (Equiv.Perm.decomposeFin.symm _ )⁻¹,
        ← mul_assoc (Fin.cycleRange k), mul_inv_cancel, one_mul,
        decomposeFin_symm_zero_inv, decomposeFin_symm_zero_mul]
    have : (permFinOfSum σ₁)⁻¹ * permFinOfSum σ₂ = permFinOfSum (σ₁⁻¹ * σ₂) :=
      permCongr_inv_mul finSumFinEquiv σ₁ σ₂
    rw [this]
  rw [hratio] at h
  obtain ⟨⟨s_l, s_r⟩, hs⟩ := h
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  intro x ⟨a, ha⟩; subst ha
  have h_block : ∀ i : Fin (m + 1),
      ∃ j, finSuccSumEquiv.symm.permCongr
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)),
          permFinOfSum (σ₁⁻¹ * σ₂))) (Sum.inl i) = Sum.inl j := by
    intro i
    have := Equiv.Perm.sumCongrHom_apply (Fin (m + 1)) (Fin n) (s_l, s_r)
    rw [this] at hs
    exact ⟨s_l i, by rw [← hs]; simp [Equiv.sumCongr_apply]⟩
  rcases hga : (σ₁⁻¹ * σ₂) (Sum.inl a) with b | c
  · exact ⟨b, rfl⟩
  · exfalso
    have h_sc : Equiv.Perm.sumCongr s_l s_r = finSuccSumEquiv.symm.permCongr
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)),
          permFinOfSum (σ₁⁻¹ * σ₂))) := by
      rwa [Equiv.Perm.sumCongrHom_apply] at hs
    set e := permFinOfSum (σ₁⁻¹ * σ₂) with he
    set D := Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e) with hD_def
    have hΦ : finSuccSumEquiv (Sum.inl (Fin.succ a)) = (Fin.castAdd n a).succ :=
      Fin.ext (by simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr])
    have hD : D (Fin.castAdd n a).succ = (e (Fin.castAdd n a)).succ := by
      simp [hD_def, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
    have hP : e (Fin.castAdd n a) = Fin.natAdd m c := by
      simp only [he, permFinOfSum, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
        hga, finSumFinEquiv_apply_right]
    have heval : (finSuccSumEquiv.symm.permCongr D) (Sum.inl (Fin.succ a)) =
        finSuccSumEquiv.symm ((Fin.natAdd m c).succ) := by
      simp only [Equiv.permCongr_apply, Equiv.symm_symm, hΦ, hD, hP]
    have h1 := DFunLike.congr_fun h_sc (Sum.inl (Fin.succ a))
    rw [heval] at h1
    simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl] at h1
    apply_fun finSuccSumEquiv at h1
    simp only [Equiv.apply_symm_apply] at h1
    apply_fun Fin.val at h1
    simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr, finSumFinEquiv_apply_left] at h1
    have := (s_l (Fin.succ a)).isLt
    omega

/-- Forward map at the quotient level. -/
private noncomputable def derivShuffleFwd :
    Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n) →
    Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1) :=
  fun p => Quotient.liftOn p.2
    (fun σ => (Quotient.mk'' (derivShuffleLeftFwd p.1 σ), derivShuffleJ p.1 σ))
    (fun σ₁ σ₂ h => Prod.ext
      (Quotient.sound' (derivShuffleLeftFwd_wd p.1 σ₁ σ₂ h))
      (derivShuffleJ_wd p.1 σ₁ σ₂ h))

/-- `derivShuffleLeftFwd k σ` sends `inl 0` to `finSuccSumEquiv.symm k`. -/
private theorem derivShuffleLeftFwd_inl_zero (k : Fin (m + n + 1))
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    derivShuffleLeftFwd k σ (Sum.inl 0) = finSuccSumEquiv.symm k := by
  simp only [derivShuffleLeftFwd, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.Perm.mul_apply]
  congr 1
  have h1 : finSuccSumEquiv (Sum.inl (0 : Fin (m + 1))) =
      (0 : Fin (m + n + 1)) := Fin.ext (by simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr])
  rw [h1, Equiv.Perm.decomposeFin_symm_apply_zero]
  exact (Fin.cycleRange k).symm_apply_eq.mpr (Fin.cycleRange_self k).symm

/-- The forward map is injective.

**Sorry**: PRE-PAPER. Rank-injectivity counting argument: if `k₁ ≠ k₂` lie in
the same image-of-`inl-0` set, the rank `derivShuffleJ` must distinguish them
by counting argument on `Finset`s. Inherited from external lib. -/
private theorem derivShuffleFwd_injective :
    Function.Injective (@derivShuffleFwd m n) := by
  intro ⟨k₁, q₁⟩ ⟨k₂, q₂⟩ h
  refine Quotient.inductionOn₂ q₁ q₂ (fun σ₁ σ₂ (h : derivShuffleFwd (k₁, ⟦σ₁⟧) =
      derivShuffleFwd (k₂, ⟦σ₂⟧)) => ?_) h
  simp only [derivShuffleFwd, Quotient.liftOn_mk] at h
  have h_coset : Quotient.mk'' (derivShuffleLeftFwd k₁ σ₁) =
      Quotient.mk'' (derivShuffleLeftFwd k₂ σ₂) := congr_arg Prod.fst h
  have h_j : derivShuffleJ k₁ σ₁ = derivShuffleJ k₂ σ₂ := congr_arg Prod.snd h
  have h_rel := Quotient.exact' h_coset
  rw [QuotientGroup.leftRel_apply] at h_rel
  obtain ⟨⟨s_l, s_r⟩, hs⟩ := h_rel
  have h_ratio_at_zero : (derivShuffleLeftFwd k₁ σ₁) (Sum.inl (s_l 0)) =
      finSuccSumEquiv.symm k₂ := by
    have h_sc : Equiv.Perm.sumCongr s_l s_r = (derivShuffleLeftFwd k₁ σ₁)⁻¹ *
        (derivShuffleLeftFwd k₂ σ₂) := by
      rwa [Equiv.Perm.sumCongrHom_apply] at hs
    have h_eval := DFunLike.congr_fun h_sc (Sum.inl 0)
    simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, derivShuffleLeftFwd_inl_zero] at h_eval
    apply_fun (derivShuffleLeftFwd k₁ σ₁) at h_eval
    simpa only [Equiv.apply_symm_apply] using h_eval
  have h_k_eq : k₁ = k₂ := by
    by_contra h_ne
    have h_sl_ne : s_l 0 ≠ 0 := by
      intro h_eq; apply h_ne
      have h1 := derivShuffleLeftFwd_inl_zero k₁ σ₁
      rw [h_eq] at h_ratio_at_zero
      rw [h1] at h_ratio_at_zero
      exact finSuccSumEquiv.symm.injective h_ratio_at_zero
    sorry
  subst h_k_eq
  ext1
  · rfl
  · exact Quotient.sound' (derivShuffleLeftFwd_coset_injective k₁ σ₁ σ₂
      (Quotient.exact' h_coset))

/-- The assembled bijection.

**Sorry**: PRE-PAPER. Cardinality balance
`(m+n+1) · C(m+n, m) = C(m+n+1, m+1) · (m+1)`. Inherited from external lib. -/
noncomputable def derivShuffleEquivLeft :
    Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n) ≃
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1) :=
  Equiv.ofBijective derivShuffleFwd
    ((Fintype.bijective_iff_injective_and_card derivShuffleFwd).mpr
      ⟨derivShuffleFwd_injective, by sorry⟩)

/-- Sign preservation.

**Sorry**: PRE-PAPER. Sign of canonical `Quotient.out'` representatives. The
correctly stated form uses `Quotient.out'`, making this concrete. Inherited
from external lib. -/
theorem derivShuffleEquivLeft_sign
    (p : Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n)) :
    ((-1 : ℤˣ) ^ p.1.val * Equiv.Perm.sign p.2.out : ℤˣ) =
      Equiv.Perm.sign (derivShuffleEquivLeft p).1.out *
        (-1) ^ (derivShuffleEquivLeft p).2.val :=
  sorry

end ContinuousAlternatingMap
