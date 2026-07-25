import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases









open scoped BigOperators

namespace DifferentialGeometry
namespace Tensor
namespace SlotAlgebra


lemma sum_fin3_fun_eq_triple
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (A B C : ι -> R) (K : ι -> ι -> ι -> R) :
    (∑ r : Fin 3 -> ι, A (r 0) * B (r 1) * C (r 2) * K (r 0) (r 1) (r 2)) =
      ∑ i : ι, ∑ k : ι, ∑ j : ι, A i * B k * C j * K i k j := by
  classical
  let e : (Fin 3 -> ι) ≃ ((ι × ι) × ι) := {
    toFun := fun r => ((r 0, r 1), r 2)
    invFun := fun p q =>
      if q = (0 : Fin 3) then p.1.1
      else if q = (1 : Fin 3) then p.1.2
      else p.2
    left_inv := by
      intro r
      funext q
      fin_cases q <;> simp
    right_inv := by
      intro p
      rcases p with ⟨⟨i, k⟩, j⟩
      simp }
  calc
    (∑ r : Fin 3 -> ι, A (r 0) * B (r 1) * C (r 2) * K (r 0) (r 1) (r 2))
        =
      ∑ p : (ι × ι) × ι,
        A p.1.1 * B p.1.2 * C p.2 * K p.1.1 p.1.2 p.2 := by
        exact Fintype.sum_equiv e _ _ (by
          intro r
          simp [e])
    _ = ∑ i : ι, ∑ k : ι, ∑ j : ι, A i * B k * C j * K i k j := by
      simp [Fintype.sum_prod_type]

lemma update_update_ne_comm
    {ι V : Type*} [DecidableEq ι]
    (slots : ι → V) {p q : ι} (hpq : p ≠ q)
    (A B : V) :
    Function.update (Function.update slots q A) p B =
      Function.update (Function.update slots p B) q A := by
  funext r
  by_cases hrp : r = p
  · subst r
    simp [Function.update, hpq]
  · by_cases hrq : r = q
    · subst r
      simp [Function.update, hrp]
    · simp [Function.update, hrp, hrq]

lemma double_sum_sub_eq_diag_sub_diag_of_offdiag_swap
    {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (F G : ι → ι → A)
    (h : ∀ q p, q ≠ p → F q p = G p q) :
    (∑ q, ∑ p, F q p) - (∑ q, ∑ p, G q p) =
      (∑ q, F q q) - (∑ q, G q q) := by
  classical
  have hdecomp (H : ι → ι → A) :
      (∑ q, ∑ p, H q p) =
        (∑ q, H q q) + (∑ q, ∑ p, if p = q then 0 else H q p) := by
    calc
      (∑ q, ∑ p, H q p)
          =
          ∑ q, ∑ p,
            ((if p = q then H q p else 0) + (if p = q then 0 else H q p)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            refine Finset.sum_congr rfl ?_
            intro p hp
            by_cases hpq : p = q <;> simp [hpq]
      _ =
          ∑ q,
            ((∑ p, if p = q then H q p else 0) +
              (∑ p, if p = q then 0 else H q p)) := by
            simp [Finset.sum_add_distrib]
      _ =
          ∑ q, (H q q + (∑ p, if p = q then 0 else H q p)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            have hsingle :
                (∑ p : ι, if p = q then H q p else (0 : A)) = H q q := by
              simp
            rw [hsingle]
      _ =
          (∑ q, H q q) + (∑ q, ∑ p, if p = q then 0 else H q p) := by
            simp [Finset.sum_add_distrib]
  have hoff :
      (∑ q, ∑ p, if p = q then 0 else F q p) =
        (∑ q, ∑ p, if p = q then 0 else G q p) := by
    calc
      (∑ q, ∑ p, if p = q then 0 else F q p)
          = (∑ p, ∑ q, if p = q then 0 else F q p) := by
            rw [Finset.sum_comm]
      _ = (∑ p, ∑ q, if p = q then 0 else G p q) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            refine Finset.sum_congr rfl ?_
            intro q hq
            by_cases hpq : p = q
            · simp [hpq]
            · have hqp : q ≠ p := fun h' => hpq h'.symm
              simp [hpq, h q p hqp]
      _ = (∑ q, ∑ p, if p = q then 0 else G q p) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            refine Finset.sum_congr rfl ?_
            intro q hq
            by_cases hpq : p = q
            · subst q
              simp
            · have hqp : q ≠ p := fun h' => hpq h'.symm
              simp [hpq, hqp]
  calc
    (∑ q, ∑ p, F q p) - (∑ q, ∑ p, G q p)
        =
        ((∑ q, F q q) + (∑ q, ∑ p, if p = q then 0 else F q p)) -
          ((∑ q, G q q) + (∑ q, ∑ p, if p = q then 0 else G q p)) := by
          rw [hdecomp F, hdecomp G]
    _ = (∑ q, F q q) - (∑ q, G q q) := by
          rw [hoff]
          abel

lemma double_update_sum_cancel_diag
    {ι V A : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A]
    (eval : (ι → V) → A)
    (slots X Y XY YX : ι → V) :
    - (∑ q, ∑ p,
        eval
          (Function.update
            (Function.update slots q (Y q))
            p
            (if p = q then XY q else X p)))
      + (∑ q, ∑ p,
        eval
          (Function.update
            (Function.update slots q (X q))
            p
            (if p = q then YX q else Y p)))
      =
    - (∑ q, eval (Function.update slots q (XY q)))
      + (∑ q, eval (Function.update slots q (YX q))) := by
  classical
  let F : ι → ι → A :=
    fun q p =>
      eval
        (Function.update
          (Function.update slots q (Y q))
          p
          (if p = q then XY q else X p))
  let G : ι → ι → A :=
    fun q p =>
      eval
        (Function.update
          (Function.update slots q (X q))
          p
          (if p = q then YX q else Y p))
  let SF : A := ∑ q, ∑ p, F q p
  let SG : A := ∑ q, ∑ p, G q p
  let DF0 : A := ∑ q, F q q
  let DG0 : A := ∑ q, G q q
  let DF : A := ∑ q, eval (Function.update slots q (XY q))
  let DG : A := ∑ q, eval (Function.update slots q (YX q))
  have hswap : ∀ q p, q ≠ p → F q p = G p q := by
    intro q p hqp
    dsimp [F, G]
    have hpq : p ≠ q := fun h' => hqp h'.symm
    rw [if_neg hpq, if_neg hqp]
    exact congrArg eval
      (update_update_ne_comm slots (p := p) (q := q) hpq (Y q) (X p))
  have hdiag0 : SF - SG = DF0 - DG0 := by
    dsimp [SF, SG, DF0, DG0]
    exact double_sum_sub_eq_diag_sub_diag_of_offdiag_swap F G hswap
  have hDF : DF0 = DF := by
    dsimp [DF0, DF, F]
    refine Finset.sum_congr rfl ?_
    intro q hq
    simp
  have hDG : DG0 = DG := by
    dsimp [DG0, DG, G]
    refine Finset.sum_congr rfl ?_
    intro q hq
    simp
  have hdiag : SF - SG = DF - DG := by
    rw [hdiag0, hDF, hDG]
  change -SF + SG = -DF + DG
  calc
    -SF + SG = -(SF - SG) := by abel
    _ = -(DF - DG) := by rw [hdiag]
    _ = -DF + DG := by abel

lemma update_finCons_zero
    {s : ℕ} {V : Type*}
    (head newHead : V) (tail : Fin s → V) :
    Function.update (Fin.cons head tail : Fin (s + 1) → V)
        (0 : Fin (s + 1)) newHead =
      (Fin.cons newHead tail : Fin (s + 1) → V) := by
  funext a
  refine Fin.cases ?_ ?_ a
  · simp [Function.update]
  · intro q
    have hne : q.succ ≠ (0 : Fin (s + 1)) := Fin.succ_ne_zero q
    simp [Function.update, hne]

lemma update_finCons_succ
    {s : ℕ} {V : Type*}
    (head : V) (tail : Fin s → V) (q : Fin s) (newTail : V) :
    Function.update (Fin.cons head tail : Fin (s + 1) → V) q.succ newTail =
      (Fin.cons head (Function.update tail q newTail) : Fin (s + 1) → V) := by
  funext a
  refine Fin.cases ?_ ?_ a
  · have hne : (0 : Fin (s + 1)) ≠ q.succ := (Fin.succ_ne_zero q).symm
    simp [Function.update, hne]
  · intro r
    by_cases hrq : r = q
    · subst r
      simp
    · simp [hrq]

lemma finCons_update_tail_eq_update_finCons_succ
    {s : ℕ} {V : Type*}
    (head : V) (tail : Fin s → V) (q : Fin s) (newTail : V) :
    (Fin.cons head (Function.update tail q newTail) : Fin (s + 1) → V) =
      Function.update (Fin.cons head tail : Fin (s + 1) → V) q.succ newTail :=
  (update_finCons_succ head tail q newTail).symm

lemma sum_update_finCons
    {s : ℕ} {V A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) → V) → A)
    (head dHead : V) (tail dTail : Fin s → V) :
    (∑ a : Fin (s + 1),
      F (Function.update (Fin.cons head tail : Fin (s + 1) → V) a
        ((Fin.cons dHead dTail : Fin (s + 1) → V) a))) =
      F (Fin.cons dHead tail) +
        ∑ q : Fin s, F (Fin.cons head (Function.update tail q (dTail q))) := by
  rw [Fin.sum_univ_succ]
  have h0 :
      Function.update (Fin.cons head tail : Fin (s + 1) → V)
          (0 : Fin (s + 1)) dHead =
        (Fin.cons dHead tail : Fin (s + 1) → V) := by
    exact update_finCons_zero (s := s) (V := V) head dHead tail
  simp only [Fin.cons_zero]
  rw [h0]
  simp_rw [Fin.cons_succ]
  simp_rw [update_finCons_succ]

lemma sum_update_finCons_raw
    {s : ℕ} {V A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) → V) → A)
    (head : V) (tail : Fin s → V) (d : Fin (s + 1) → V) :
    (∑ a : Fin (s + 1),
      F (Function.update (Fin.cons head tail : Fin (s + 1) → V) a
        (d a))) =
      F (Fin.cons (d 0) tail) +
        ∑ q : Fin s, F (Fin.cons head (Function.update tail q (d q.succ))) := by
  have hd :
      (Fin.cons (d 0) (fun q : Fin s => d q.succ) :
          Fin (s + 1) → V) = d := by
    funext a
    refine Fin.cases ?_ ?_ a
    · simp
    · intro q
      simp
  simpa [hd] using
    sum_update_finCons
      (F := F) (head := head) (dHead := d 0) (tail := tail)
      (dTail := fun q : Fin s => d q.succ)


lemma sum_rotate3
    {ι κ ι' A : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [AddCommMonoid A] (F : ι → κ → ι' → A) :
    (∑ i : ι, ∑ k : κ, ∑ j : ι', F i k j) =
      ∑ j : ι', ∑ i : ι, ∑ k : κ, F i k j := by
  calc
    (∑ i : ι, ∑ k : κ, ∑ j : ι', F i k j)
        = ∑ i : ι, ∑ j : ι', ∑ k : κ, F i k j := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ j : ι', ∑ i : ι, ∑ k : κ, F i k j := by
          rw [Finset.sum_comm]


lemma sum_rotate4
    {ι κ ι' κ' A : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] [AddCommMonoid A] (F : ι → κ → ι' → κ' → A) :
    (∑ i : ι, ∑ k : κ, ∑ l : ι', ∑ m : κ', F i k l m) =
      ∑ m : κ', ∑ i : ι, ∑ k : κ, ∑ l : ι', F i k l m := by
  calc
    (∑ i : ι, ∑ k : κ, ∑ l : ι', ∑ m : κ', F i k l m)
        = ∑ i : ι, ∑ k : κ, ∑ m : κ', ∑ l : ι', F i k l m := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.sum_comm]
    _ = ∑ m : κ', ∑ i : ι, ∑ k : κ, ∑ l : ι', F i k l m := by
          rw [sum_rotate3]


lemma sum_rotate4_two
    {ι κ ι' κ' A : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] [AddCommMonoid A] (F : ι → κ → ι' → κ' → A) :
    (∑ i : ι, ∑ k : κ, ∑ l : ι', ∑ m : κ', F i k l m) =
      ∑ l : ι', ∑ m : κ', ∑ i : ι, ∑ k : κ, F i k l m := by
  calc
    (∑ i : ι, ∑ k : κ, ∑ l : ι', ∑ m : κ', F i k l m)
        = ∑ i : ι, ∑ l : ι', ∑ k : κ, ∑ m : κ', F i k l m := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ l : ι', ∑ i : ι, ∑ k : κ, ∑ m : κ', F i k l m := by
          rw [Finset.sum_comm]
    _ = ∑ l : ι', ∑ m : κ', ∑ i : ι, ∑ k : κ, F i k l m := by
          refine Finset.sum_congr rfl ?_
          intro l _
          rw [sum_rotate3]


lemma sum_mul_right3
    {ι κ ι' R : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Semiring R] (F : ι → κ → ι' → R) (c : ι' → R) :
    (∑ j : ι', (∑ i : ι, ∑ k : κ, F i k j) * c j) =
      ∑ i : ι, ∑ k : κ, ∑ j : ι', F i k j * c j := by
  calc
    (∑ j : ι', (∑ i : ι, ∑ k : κ, F i k j) * c j)
        = ∑ j : ι', ∑ i : ι, ∑ k : κ, F i k j * c j := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simp [Finset.sum_mul]
    _ = ∑ i : ι, ∑ k : κ, ∑ j : ι', F i k j * c j := by
          rw [← sum_rotate3]

end SlotAlgebra
end Tensor
end DifferentialGeometry
