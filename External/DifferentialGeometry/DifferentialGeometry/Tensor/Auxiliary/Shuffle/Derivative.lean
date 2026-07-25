




import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Auxiliary.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Tactic

open Equiv

namespace ContinuousAlternatingMap

variable {m n : ℕ}

noncomputable abbrev permFinOfSum (σ : Equiv.Perm (Fin m ⊕ Fin n)) : Equiv.Perm (Fin (m + n)) :=
  (finSumFinEquiv.permCongr σ : Equiv.Perm (Fin (m + n)))

noncomputable abbrev finSuccSumEquiv : Fin (m + 1) ⊕ Fin n ≃ Fin (m + n + 1) :=
  finSumFinEquiv.trans Fin.finAddFlipAssoc

noncomputable def derivShuffleLeftFwd
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  let σ_fin := permFinOfSum σ
  let π := (Fin.cycleRange k)⁻¹ * Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), σ_fin)
  finSuccSumEquiv.symm.permCongr π

theorem derivShuffleLeftFwd_sign
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (derivShuffleLeftFwd k σ) =
      (-1 : ℤˣ) ^ k.val * Equiv.Perm.sign σ := by
  simp only [derivShuffleLeftFwd, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_inv, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign,
    if_true, one_mul, permFinOfSum]
  rfl

private theorem decomposeFin_symm_zero_mul (e₁ e₂ : Equiv.Perm (Fin (m + n))) :
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₁) *
      Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₂) =
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e₁ * e₂) := by
  ext x; refine Fin.cases ?_ ?_ x
  · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  · intro i
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply]

private theorem decomposeFin_symm_zero_inv (e : Equiv.Perm (Fin (m + n))) :
    (Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e))⁻¹ =
    Equiv.Perm.decomposeFin.symm ((0 : Fin (m + n + 1)), e⁻¹) := by
  rw [inv_eq_iff_mul_eq_one, decomposeFin_symm_zero_mul, mul_inv_cancel]
  ext x; refine Fin.cases (by simp) (fun i => by simp [Equiv.swap_self]) x

private theorem permCongr_inv_mul {α β : Type*} (e : α ≃ β) (a b : Equiv.Perm α) :
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
  · unfold finSuccSumEquiv; aesop;
  · simp +decide [ Equiv.Perm.decomposeFin, permFinOfSum ];
    simp +decide [ Fin.finAddFlipAssoc, finSuccEquiv ];
    simp +decide [ finSuccEquiv' ];
    simp +decide [ Fin.cons ];
    simp +decide [ Fin.cases, finSumFinEquiv ];
    simp +decide [ Fin.induction, Fin.addCases ];
    simp +decide [ Fin.induction.go ]

noncomputable def derivShuffleRank (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Fin (m + 1) :=
  ⟨(Finset.univ.filter (fun i : Fin m =>
    (permFinOfSum σ (Fin.castAdd n i)).val < k.val)).card, by
    calc (Finset.univ.filter _).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = m := Finset.card_fin m
      _ < m + 1 := lt_add_one m⟩

private theorem permFinOfSum_mul_sumCongr_castAdd (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (τ_l : Equiv.Perm (Fin m)) (τ_r : Equiv.Perm (Fin n)) (i : Fin m) :
    permFinOfSum (σ * Equiv.Perm.sumCongr τ_l τ_r) (Fin.castAdd n i) =
      permFinOfSum σ (Fin.castAdd n (τ_l i)) := by
  simp only [permFinOfSum, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.Perm.mul_apply, Equiv.sumCongr_apply, Sum.map_inl]

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

theorem derivShuffleJ_wd (k : Fin (m + n + 1))
    (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range σ₁ σ₂) :
    derivShuffleRank k σ₁ = derivShuffleRank k σ₂ := by
  rw [QuotientGroup.leftRel_apply] at h
  obtain ⟨⟨τ_l, τ_r⟩, hblock⟩ := h

  have h_sc : Equiv.Perm.sumCongr τ_l τ_r = σ₁⁻¹ * σ₂ := by
    change (Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r) : Equiv.Perm _) = _; exact hblock
  have h_eq : σ₂ = σ₁ * Equiv.Perm.sumCongr τ_l τ_r := by rw [h_sc]; group
  subst h_eq
  simp only [derivShuffleRank, Fin.mk.injEq]

  change (Finset.univ.filter (fun i =>
    (permFinOfSum σ₁ (Fin.castAdd n i)).val < k.val)).card =
    (Finset.univ.filter (fun i =>
    (permFinOfSum (σ₁ * Equiv.Perm.sumCongr τ_l τ_r) (Fin.castAdd n i)).val < k.val)).card
  simp_rw [permFinOfSum_mul_sumCongr_castAdd]
  exact (card_filter_comp_perm τ_l _).symm

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

private noncomputable def derivShuffleFwd :
    Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n) →
    Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1) :=
  fun p => Quotient.liftOn p.2
    (fun σ => (Quotient.mk'' (derivShuffleLeftFwd p.1 σ), derivShuffleRank p.1 σ))
    (fun σ₁ σ₂ h => Prod.ext
      (Quotient.sound' (derivShuffleLeftFwd_wd p.1 σ₁ σ₂ h))
      (derivShuffleJ_wd p.1 σ₁ σ₂ h))

theorem derivShuffleLeftFwd_inl_zero (k : Fin (m + n + 1))
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    derivShuffleLeftFwd k σ (Sum.inl 0) = finSuccSumEquiv.symm k := by
  simp only [derivShuffleLeftFwd, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.Perm.mul_apply]
  congr 1
  have h1 : finSuccSumEquiv (Sum.inl (0 : Fin (m + 1))) =
      (0 : Fin (m + n + 1)) := Fin.ext (by simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr])
  rw [h1, Equiv.Perm.decomposeFin_symm_apply_zero]
  exact (Fin.cycleRange k).symm_apply_eq.mpr (Fin.cycleRange_self k).symm

theorem derivShuffleLeftFwd_inl_succ
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) (a : Fin m) :
    derivShuffleLeftFwd k σ (Sum.inl (Fin.succ a)) =
      finSuccSumEquiv.symm
        (k.succAbove (permFinOfSum σ (Fin.castAdd n a))) := by
  apply finSuccSumEquiv.injective
  simp only [derivShuffleLeftFwd, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
  have hΦ :
      finSuccSumEquiv (Sum.inl (Fin.succ a)) =
        (Fin.castAdd n a).succ :=
    Fin.ext (by simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr])
  rw [hΦ, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [Equiv.swap_self, Equiv.refl_apply]
  change (Fin.cycleRange k).symm ((permFinOfSum σ (Fin.castAdd n a)).succ) =
    k.succAbove (permFinOfSum σ (Fin.castAdd n a))
  exact Fin.cycleRange_symm_succ k (permFinOfSum σ (Fin.castAdd n a))

theorem derivShuffleLeftFwd_inr
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) (b : Fin n) :
    derivShuffleLeftFwd k σ (Sum.inr b) =
      finSuccSumEquiv.symm
        (k.succAbove (permFinOfSum σ (Fin.natAdd m b))) := by
  apply finSuccSumEquiv.injective
  simp only [derivShuffleLeftFwd, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.Perm.mul_apply, Equiv.apply_symm_apply]
  have hΦ :
      finSuccSumEquiv (Sum.inr b) =
        (Fin.natAdd m b).succ :=
    Fin.ext (by simp [finSuccSumEquiv, Fin.finAddFlipAssoc, finCongr]; omega)
  rw [hΦ, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [Equiv.swap_self, Equiv.refl_apply]
  change (Fin.cycleRange k).symm ((permFinOfSum σ (Fin.natAdd m b)).succ) =
    k.succAbove (permFinOfSum σ (Fin.natAdd m b))
  exact Fin.cycleRange_symm_succ k (permFinOfSum σ (Fin.natAdd m b))

private theorem finset_rank_lt_injective {N : ℕ} (s : Finset (Fin N)) {a b : Fin N}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcard :
      (s.filter fun x => x.val < a.val).card =
      (s.filter fun x => x.val < b.val).card) :
    a = b := by
  by_cases hab : a.val < b.val
  · have hss :
        s.filter (fun x => x.val < a.val) ⊂
          s.filter (fun x => x.val < b.val) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, Nat.lt_trans hx.2 hab⟩
      · intro heq
        have ha_big : a ∈ s.filter (fun x => x.val < b.val) := by
          rw [Finset.mem_filter]
          exact ⟨ha, hab⟩
        have ha_small : a ∈ s.filter (fun x => x.val < a.val) := by
          rw [heq]
          exact ha_big
        rw [Finset.mem_filter] at ha_small
        exact Nat.lt_irrefl _ ha_small.2
    have := Finset.card_lt_card hss
    omega
  · by_cases hba : b.val < a.val
    · have hss :
          s.filter (fun x => x.val < b.val) ⊂
            s.filter (fun x => x.val < a.val) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, Nat.lt_trans hx.2 hba⟩
        · intro heq
          have hb_big : b ∈ s.filter (fun x => x.val < a.val) := by
            rw [Finset.mem_filter]
            exact ⟨hb, hba⟩
          have hb_small : b ∈ s.filter (fun x => x.val < b.val) := by
            rw [heq]
            exact hb_big
          rw [Finset.mem_filter] at hb_small
          exact Nat.lt_irrefl _ hb_small.2
      have := Finset.card_lt_card hss
      omega
    · apply Fin.ext
      omega

private noncomputable def derivShuffleLeftSet
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Finset (Fin (m + n + 1)) :=
  Finset.univ.image fun i : Fin (m + 1) =>
    finSuccSumEquiv (derivShuffleLeftFwd k σ (Sum.inl i))

private theorem derivShuffleLeftSet_eq
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    derivShuffleLeftSet k σ =
      insert k
        (Finset.univ.image fun a : Fin m =>
          k.succAbove (permFinOfSum σ (Fin.castAdd n a))) := by
  classical
  ext y
  constructor
  · intro hy
    rw [derivShuffleLeftSet, Finset.mem_image] at hy
    obtain ⟨i, -, hi⟩ := hy
    obtain (rfl | ⟨a, rfl⟩) := i.eq_zero_or_eq_succ
    · rw [derivShuffleLeftFwd_inl_zero] at hi
      rw [Equiv.apply_symm_apply] at hi
      rw [Finset.mem_insert]
      exact Or.inl hi.symm
    · rw [derivShuffleLeftFwd_inl_succ] at hi
      rw [Equiv.apply_symm_apply] at hi
      rw [Finset.mem_insert, Finset.mem_image]
      exact Or.inr ⟨a, Finset.mem_univ _, hi⟩
  · intro hy
    rw [derivShuffleLeftSet, Finset.mem_image]
    rw [Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with hy | ⟨a, -, ha⟩
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      rw [derivShuffleLeftFwd_inl_zero, hy]
      simp
    · refine ⟨Fin.succ a, Finset.mem_univ _, ?_⟩
      rw [derivShuffleLeftFwd_inl_succ, ha]
      simp

private theorem derivShuffleLeft_succ_position_injective
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Function.Injective fun a : Fin m =>
      k.succAbove (permFinOfSum σ (Fin.castAdd n a)) := by
  intro a b h
  have h₁ := Fin.succAbove_right_injective h
  have h₂ := (permFinOfSum σ).injective h₁
  apply Fin.ext
  apply_fun Fin.val at h₂
  simpa using h₂

private theorem derivShuffleJ_val_eq_rank_leftSet
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (derivShuffleRank k σ).val =
      ((derivShuffleLeftSet k σ).filter fun x => x.val < k.val).card := by
  classical
  rw [derivShuffleLeftSet_eq]
  simp only [Finset.filter_insert, lt_self_iff_false, ↓reduceIte]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective]
  · unfold derivShuffleRank
    change (Finset.univ.filter (fun i : Fin m =>
        (permFinOfSum σ (Fin.castAdd n i)).val < k.val)).card =
      (Finset.univ.filter (fun a : Fin m =>
        (k.succAbove (permFinOfSum σ (Fin.castAdd n a))).val < k.val)).card
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (permFinOfSum σ (Fin.castAdd n a)).castSucc < k ↔
      k.succAbove (permFinOfSum σ (Fin.castAdd n a)) < k
    rw [Fin.succAbove_lt_iff_castSucc_lt]
  · exact derivShuffleLeft_succ_position_injective k σ

private theorem derivShuffleLeftSet_eq_of_rel
    (k₁ k₂ : Fin (m + n + 1))
    (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range
      (derivShuffleLeftFwd k₁ σ₁) (derivShuffleLeftFwd k₂ σ₂)) :
    derivShuffleLeftSet k₁ σ₁ = derivShuffleLeftSet k₂ σ₂ := by
  classical
  rw [QuotientGroup.leftRel_apply] at h
  obtain ⟨⟨s_l, s_r⟩, hs⟩ := h
  have h_sc : Equiv.Perm.sumCongr s_l s_r =
      (derivShuffleLeftFwd k₁ σ₁)⁻¹ * (derivShuffleLeftFwd k₂ σ₂) := by
    rwa [Equiv.Perm.sumCongrHom_apply] at hs
  ext y
  constructor
  · intro hy
    rw [derivShuffleLeftSet, Finset.mem_image] at hy ⊢
    obtain ⟨i, -, hi⟩ := hy
    refine ⟨s_l.symm i, Finset.mem_univ _, ?_⟩
    have h_eval := DFunLike.congr_fun h_sc (Sum.inl (s_l.symm i))
    simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h_eval
    apply_fun (derivShuffleLeftFwd k₁ σ₁) at h_eval
    simp only [Equiv.apply_symm_apply] at h_eval
    rw [← h_eval, hi]
  · intro hy
    rw [derivShuffleLeftSet, Finset.mem_image] at hy ⊢
    obtain ⟨i, -, hi⟩ := hy
    refine ⟨s_l i, Finset.mem_univ _, ?_⟩
    have h_eval := DFunLike.congr_fun h_sc (Sum.inl i)
    simp only [Equiv.Perm.sumCongr_apply, Sum.map_inl, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def] at h_eval
    apply_fun (derivShuffleLeftFwd k₁ σ₁) at h_eval
    simp only [Equiv.apply_symm_apply] at h_eval
    rw [h_eval, hi]

private theorem derivShuffleFwd_injective :
    Function.Injective (@derivShuffleFwd m n) := by
  intro ⟨k₁, q₁⟩ ⟨k₂, q₂⟩ h
  refine Quotient.inductionOn₂ q₁ q₂ (fun σ₁ σ₂ (h : derivShuffleFwd (k₁, ⟦σ₁⟧) =
      derivShuffleFwd (k₂, ⟦σ₂⟧)) => ?_) h
  simp only [derivShuffleFwd, Quotient.liftOn_mk] at h
  have h_coset : Quotient.mk'' (derivShuffleLeftFwd k₁ σ₁) =
      Quotient.mk'' (derivShuffleLeftFwd k₂ σ₂) := congr_arg Prod.fst h
  have h_j : derivShuffleRank k₁ σ₁ = derivShuffleRank k₂ σ₂ := congr_arg Prod.snd h

  have h_rel := Quotient.exact' h_coset
  have h_left_set :
      derivShuffleLeftSet k₁ σ₁ = derivShuffleLeftSet k₂ σ₂ :=
    derivShuffleLeftSet_eq_of_rel k₁ k₂ σ₁ σ₂ h_rel

  have h_k_eq : k₁ = k₂ := by
    let L := derivShuffleLeftSet k₁ σ₁
    have hk₁ : k₁ ∈ L := by
      change k₁ ∈ derivShuffleLeftSet k₁ σ₁
      rw [derivShuffleLeftSet, Finset.mem_image]
      refine ⟨0, Finset.mem_univ _, ?_⟩
      rw [derivShuffleLeftFwd_inl_zero]
      simp
    have hk₂ : k₂ ∈ L := by
      change k₂ ∈ derivShuffleLeftSet k₁ σ₁
      rw [h_left_set, derivShuffleLeftSet, Finset.mem_image]
      refine ⟨0, Finset.mem_univ _, ?_⟩
      rw [derivShuffleLeftFwd_inl_zero]
      simp
    have h_rank : (L.filter fun x => x.val < k₁.val).card =
        (L.filter fun x => x.val < k₂.val).card := by
      have hjv := congr_arg Fin.val h_j
      rw [derivShuffleJ_val_eq_rank_leftSet k₁ σ₁,
        derivShuffleJ_val_eq_rank_leftSet k₂ σ₂] at hjv
      simpa [L, h_left_set] using hjv
    exact finset_rank_lt_injective L hk₁ hk₂ h_rank
  subst h_k_eq

  ext1
  · rfl
  · exact Quotient.sound' (derivShuffleLeftFwd_coset_injective k₁ σ₁ σ₂
      (Quotient.exact' h_coset))

private theorem modSumCongr_range_card_fin (m n : ℕ) :
    Fintype.card { x : Equiv.Perm (Fin m ⊕ Fin n) //
      ∃ a : Equiv.Perm (Fin m), ∃ b : Equiv.Perm (Fin n), Equiv.Perm.sumCongr a b = x } =
    Nat.factorial m * Nat.factorial n := by
  classical
  have h : Fintype.card ((Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) =
      Nat.factorial m * Nat.factorial n := by
    rw [Equiv.Perm.sumCongrHom.card_range]
    simp [Fintype.card_perm]
  simpa [Equiv.Perm.sumCongrHom_apply] using h

private theorem derivShuffleFwd_card :
    Fintype.card
      (Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n)) =
    Fintype.card
      (Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1)) := by
  classical
  have hmn := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range)
  have hm1n := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range)
  have hmn' :
      Nat.factorial (m + n) =
        Fintype.card
          (Equiv.Perm (Fin m ⊕ Fin n) ⧸
            (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) *
          (Nat.factorial m * Nat.factorial n) := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      modSumCongr_range_card_fin] using hmn
  have hm1n' :
      Nat.factorial (m + 1 + n) =
        Fintype.card
          (Equiv.Perm (Fin (m + 1) ⊕ Fin n) ⧸
            (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range) *
          (Nat.factorial (m + 1) * Nat.factorial n) := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      modSumCongr_range_card_fin] using hm1n
  rw [Fintype.card_prod, Fintype.card_fin]
  rw [Fintype.card_prod, Fintype.card_fin]
  change (m + n + 1) *
      Fintype.card
        (Equiv.Perm (Fin m ⊕ Fin n) ⧸
          (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) =
    Fintype.card
        (Equiv.Perm (Fin (m + 1) ⊕ Fin n) ⧸
          (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range) *
      (m + 1)
  rw [show m + 1 + n = m + n + 1 by omega, Nat.factorial_succ] at hm1n'
  rw [Nat.factorial_succ] at hm1n'
  apply Nat.mul_right_cancel (show 0 < Nat.factorial m * Nat.factorial n by positivity)
  calc
    ((m + n + 1) *
        Fintype.card
          (Equiv.Perm (Fin m ⊕ Fin n) ⧸ (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range)) *
        (Nat.factorial m * Nat.factorial n)
        = (m + n + 1) * Nat.factorial (m + n) := by
          nlinarith [hmn']
    _ = Fintype.card
          (Equiv.Perm (Fin (m + 1) ⊕ Fin n) ⧸
            (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range) *
        ((m + 1) * (Nat.factorial m * Nat.factorial n)) := by
          simpa [mul_assoc] using hm1n'
    _ = (Fintype.card
          (Equiv.Perm (Fin (m + 1) ⊕ Fin n) ⧸
            (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range) * (m + 1)) *
        (Nat.factorial m * Nat.factorial n) := by
          ring

noncomputable def derivShuffleEquivLeft :
    Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n) ≃
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1) :=
  Equiv.ofBijective derivShuffleFwd
    ((Fintype.bijective_iff_injective_and_card derivShuffleFwd).mpr
      ⟨derivShuffleFwd_injective, derivShuffleFwd_card⟩)

@[simp] theorem derivShuffleEquivLeft_apply_mk
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    derivShuffleEquivLeft (k, Quotient.mk'' σ) =
      (Quotient.mk'' (derivShuffleLeftFwd k σ), derivShuffleRank k σ) :=
  rfl

noncomputable def derivShuffleLeftFwdRanked
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  derivShuffleLeftFwd k σ *
    Equiv.Perm.sumCongr (Fin.cycleRange (derivShuffleRank k σ)) 1

@[simp] theorem derivShuffleLeftFwdRanked_mk
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (Quotient.mk'' (derivShuffleLeftFwdRanked k σ) :
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
      Quotient.mk'' (derivShuffleLeftFwd k σ) := by
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  refine ⟨⟨(Fin.cycleRange (derivShuffleRank k σ))⁻¹, 1⟩, ?_⟩
  change Equiv.Perm.sumCongr (Fin.cycleRange (derivShuffleRank k σ))⁻¹ 1 =
    (derivShuffleLeftFwdRanked k σ)⁻¹ * derivShuffleLeftFwd k σ
  simp [derivShuffleLeftFwdRanked]

@[simp] theorem derivShuffleEquivLeft_apply_mk_ranked
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    derivShuffleEquivLeft (k, Quotient.mk'' σ) =
      (Quotient.mk'' (derivShuffleLeftFwdRanked k σ), derivShuffleRank k σ) := by
  rw [derivShuffleEquivLeft_apply_mk]
  simp

theorem derivShuffleLeftFwdRanked_sign
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (derivShuffleLeftFwdRanked k σ) =
      (-1 : ℤˣ) ^ k.val * Equiv.Perm.sign σ *
        (-1 : ℤˣ) ^ (derivShuffleRank k σ).val := by
  rw [derivShuffleLeftFwdRanked, Equiv.Perm.sign_mul, Equiv.Perm.sign_sumCongr,
    derivShuffleLeftFwd_sign, Fin.sign_cycleRange]
  simp [mul_assoc]
  rfl

theorem derivShuffleLeftFwdRanked_inl_j
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    derivShuffleLeftFwdRanked k σ (Sum.inl (derivShuffleRank k σ)) =
      finSuccSumEquiv.symm k := by
  rw [derivShuffleLeftFwdRanked]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl]
  rw [Fin.cycleRange_self, derivShuffleLeftFwd_inl_zero]

theorem derivShuffleLeftFwdRanked_inl_succAbove
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) (a : Fin m) :
    derivShuffleLeftFwdRanked k σ (Sum.inl ((derivShuffleRank k σ).succAbove a)) =
      finSuccSumEquiv.symm
        (k.succAbove (permFinOfSum σ (Fin.castAdd n a))) := by
  rw [derivShuffleLeftFwdRanked]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl]
  rw [Fin.cycleRange_succAbove, derivShuffleLeftFwd_inl_succ]

theorem derivShuffleLeftFwdRanked_inr
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) (b : Fin n) :
    derivShuffleLeftFwdRanked k σ (Sum.inr b) =
      finSuccSumEquiv.symm
        (k.succAbove (permFinOfSum σ (Fin.natAdd m b))) := by
  rw [derivShuffleLeftFwdRanked]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr]
  rw [show (1 : Equiv.Perm (Fin n)) b = b from rfl]
  rw [derivShuffleLeftFwd_inr]

theorem derivShuffleEquivLeft_sign_mk
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (derivShuffleLeftFwd k σ) =
      (-1 : ℤˣ) ^ k.val * Equiv.Perm.sign σ :=
  derivShuffleLeftFwd_sign k σ

end ContinuousAlternatingMap
