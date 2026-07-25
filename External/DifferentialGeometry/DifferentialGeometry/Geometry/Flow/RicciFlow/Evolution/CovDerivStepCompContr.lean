import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompLinear

set_option autoImplicit false
set_option linter.style.longLine false



















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]




def contrTail {p q : ℕ}
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real) :
    (Fin (p + q) → Idx) → Real :=
  fun idx =>
    ∑ c : Idx,
      A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
        B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c)

omit [DecidableEq Idx] in
@[simp] theorem contrTail_apply {p q : ℕ}
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real)
    (idx : Fin (p + q) → Idx) :
    contrTail A B idx =
      ∑ c : Idx,
        A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
          B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) := rfl


omit [Fintype Idx] [DecidableEq Idx] in
private theorem castAdd_append {p q : ℕ} (aPart : Fin p → Idx) (bPart : Fin q → Idx)
    (i : Fin p) : (Fin.append aPart bPart) (Fin.castAdd q i) = aPart i := by
  simp [Fin.append_left]

omit [Fintype Idx] [DecidableEq Idx] in
private theorem natAdd_append {p q : ℕ} (aPart : Fin p → Idx) (bPart : Fin q → Idx)
    (j : Fin q) : (Fin.append aPart bPart) (Fin.natAdd p j) = bPart j := by
  simp [Fin.append_right]

private theorem castAdd_ne_natAdd {p q : ℕ} (i : Fin p) (j : Fin q) :
    Fin.castAdd q i ≠ Fin.natAdd p j := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := i.isLt
  omega


omit [Fintype Idx] [DecidableEq Idx] in
private theorem update_append_castAdd {p q : ℕ} (aPart : Fin p → Idx) (bPart : Fin q → Idx)
    (i : Fin p) (v : Idx) :
    Function.update (Fin.append aPart bPart) (Fin.castAdd q i) v =
      Fin.append (Function.update aPart i v) bPart := by
  funext k
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
  · rw [Fin.append_left]
    rcases eq_or_ne i' i with rfl | h
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun he => h (Fin.castAdd_injective _ _ he)),
        Fin.append_left, Function.update_of_ne h]
  · rw [Fin.append_right, Function.update_of_ne (castAdd_ne_natAdd i j').symm, Fin.append_right]


omit [Fintype Idx] [DecidableEq Idx] in
private theorem update_append_natAdd {p q : ℕ} (aPart : Fin p → Idx) (bPart : Fin q → Idx)
    (j : Fin q) (v : Idx) :
    Function.update (Fin.append aPart bPart) (Fin.natAdd p j) v =
      Fin.append aPart (Function.update bPart j v) := by
  funext k
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k
  · rw [Fin.append_left, Function.update_of_ne (castAdd_ne_natAdd i' j), Fin.append_left]
  · rw [Fin.append_right]
    rcases eq_or_ne j' j with rfl | h
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun he => h (Fin.natAdd_injective _ _ he)),
        Fin.append_right, Function.update_of_ne h]



omit [Fintype Idx] [DecidableEq Idx] in
private theorem snoc_cons_zero {p : ℕ} (d : Idx) (Y : Fin p → Idx) (c : Idx) :
    (Fin.snoc (Fin.cons d Y : Fin (p + 1) → Idx) c : Fin (p + 2) → Idx) 0 = d := by
  rw [show (0 : Fin (p + 2)) = Fin.castSucc 0 from by simp, Fin.snoc_castSucc, Fin.cons_zero]

omit [Fintype Idx] [DecidableEq Idx] in
private theorem tail_snoc_cons {p : ℕ} (d : Idx) (Y : Fin p → Idx) (c : Idx) :
    Fin.tail (Fin.snoc (Fin.cons d Y : Fin (p + 1) → Idx) c : Fin (p + 2) → Idx) =
      (Fin.snoc Y c : Fin (p + 1) → Idx) := by
  funext i
  show (Fin.snoc (Fin.cons d Y : Fin (p + 1) → Idx) c : Fin (p + 2) → Idx) i.succ =
    (Fin.snoc Y c : Fin (p + 1) → Idx) i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.cons_succ, Fin.snoc_castSucc]
  · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_last]

omit [Fintype Idx] [DecidableEq Idx] in
private theorem update_snoc_last {p : ℕ} (Y : Fin p → Idx) (c a : Idx) :
    Function.update (Fin.snoc Y c : Fin (p + 1) → Idx) (Fin.last p) a =
      (Fin.snoc Y a : Fin (p + 1) → Idx) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Function.update_self, Fin.snoc_last]

omit [Fintype Idx] [DecidableEq Idx] in
private theorem update_snoc_castSucc {p : ℕ} (Y : Fin p → Idx) (c a : Idx) (j : Fin p) :
    Function.update (Fin.snoc Y c : Fin (p + 1) → Idx) (Fin.castSucc j) a =
      (Fin.snoc (Function.update Y j a) c : Fin (p + 1) → Idx) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    rcases eq_or_ne k j with rfl | hkj
    · rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun h => hkj (Fin.castSucc_injective _ h)),
        Function.update_of_ne hkj, Fin.snoc_castSucc]
  · rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne', Fin.snoc_last, Fin.snoc_last]






def covDerivStepCompU {p : ℕ}
    (ext : (Fin (p + 1) → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A : (Fin (p + 1) → Idx) → Real) : (Fin (p + 2) → Idx) → Real :=
  fun n =>
    ext (Fin.tail n) (n 0) -
      (∑ j : Fin p, ∑ a : Idx,
        chr (n 0) (Fin.tail n (Fin.castSucc j)) a *
          A (Function.update (Fin.tail n) (Fin.castSucc j) a)) +
      (∑ a : Idx,
        chr (n 0) a (Fin.tail n (Fin.last p)) *
          A (Function.update (Fin.tail n) (Fin.last p) a))





omit [DecidableEq Idx] in
theorem contrTail_contracted_cancel {p q : ℕ}
    (chr : Idx → Idx → Idx → Real) (d : Idx)
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real)
    (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    (∑ c : Idx, (∑ a : Idx, chr d a c * A (Fin.snoc aPart a)) * B (Fin.snoc bPart c)) =
      ∑ c : Idx, A (Fin.snoc aPart c) *
        (∑ e : Idx, chr d c e * B (Fin.snoc bPart e)) := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by ring







omit [DecidableEq Idx] in
theorem covDerivStepCompU_contrTail_leibniz {p q : ℕ}
    (extA : (Fin (p + 1) → Idx) → Idx → Real)
    (extB : (Fin (q + 1) → Idx) → Idx → Real)
    (ext : (Fin (p + q) → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real)
    (hext : ∀ (idx : Fin (p + q) → Idx) (d : Idx),
      ext idx d =
        ∑ c : Idx,
          (extA (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) d *
              B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) +
            A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
              extB (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) d))
    (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    covDerivStepComp ext chr (contrTail A B) (Fin.cons d (Fin.append aPart bPart)) =
      contrTail (covDerivStepCompU extA chr A) B
          (Fin.append (Fin.cons d aPart) bPart) +
        contrTail A (covDerivStepComp extB chr B)
          (Fin.append aPart (Fin.cons d bPart)) := by
  classical





















  simp only [covDerivStepComp, covDerivStepCompU, contrTail, Fin.tail_cons, Fin.cons_zero,
    castAdd_append, natAdd_append, snoc_cons_zero, tail_snoc_cons,
    Fin.snoc_castSucc, Fin.snoc_last, update_snoc_castSucc, update_snoc_last]
  rw [hext]
  simp only [castAdd_append, natAdd_append]
  rw [Fin.sum_univ_add]
  simp only [castAdd_append, natAdd_append, update_append_castAdd, update_append_natAdd,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, update_snoc_castSucc, update_snoc_last]

  have hA :
      (∑ x : Fin p, ∑ x_1 : Idx, chr d (aPart x) x_1 *
          ∑ x_2 : Idx, A (Fin.snoc (Function.update aPart x x_1) x_2) * B (Fin.snoc bPart x_2)) =
        ∑ x : Idx, (∑ x_1 : Fin p, ∑ x_2 : Idx, chr d (aPart x_1) x_2 *
            A (Fin.snoc (Function.update aPart x_1 x_2) x)) * B (Fin.snoc bPart x) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm (f := fun x_1 x_2 =>
      chr d (aPart x) x_1 * (A (Fin.snoc (Function.update aPart x x_1) x_2) * B (Fin.snoc bPart x_2))),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun xs _ =>
      Finset.sum_congr rfl fun x1 _ => by ring

  have hB :
      (∑ x : Fin q, ∑ x_1 : Idx, chr d (bPart x) x_1 *
          ∑ x_2 : Idx, A (Fin.snoc aPart x_2) * B (Fin.snoc (Function.update bPart x x_1) x_2)) =
        ∑ x : Idx, A (Fin.snoc aPart x) *
          ∑ x_1 : Fin q, ∑ x_2 : Idx, chr d (bPart x_1) x_2 *
            B (Fin.snoc (Function.update bPart x_1 x_2) x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm (f := fun x_1 x_2 =>
      chr d (bPart x) x_1 * (A (Fin.snoc aPart x_2) * B (Fin.snoc (Function.update bPart x x_1) x_2))),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun xs _ =>
      Finset.sum_congr rfl fun x1 _ => by ring

  have hcancel := contrTail_contracted_cancel (Idx := Idx) chr d A B aPart bPart
  rw [hA, hB]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    mul_sub, mul_add, sub_mul, add_mul]
  simp only [← Finset.sum_mul, ← Finset.mul_sum] at hcancel ⊢
  linarith [hcancel]

end DifferentialGeometry.PDE.RicciFlow
