import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Equivalences and index-juggling lemmas for `Fin n`

Helper equivalences and computational lemmas about `Fin n` used in the
multilinear / alternating tensor development.
-/

namespace Fin

variable {m n o : ℕ}

/-- `(m + n) + p ≃ m + (n + p)`. -/
def finAssoc {m n p : ℕ} : Fin (m + n + p) ≃ Fin (m + (n + p)) :=
  finCongr <| Nat.add_assoc m n p

/-- `(m + p) + n ≃ m + (n + p)`. -/
def finAddFlipAssoc {m n p : ℕ} : Fin (m + p + n) ≃ Fin (m + (n + p)) := by
  refine finCongr ?eq
  rw [Nat.add_right_comm]
  exact Nat.add_assoc m n p

theorem finAddFlip_finSumFinEquiv {m n : ℕ} (a : Fin m ⊕ Fin n) :
    finAddFlip (finSumFinEquiv a) = finSumFinEquiv (Equiv.sumComm _ _ a) := by
  refine Eq.symm (DFunLike.congr_arg finSumFinEquiv ?h₂)
  rw [Equiv.congr_arg rfl]
  refine (Equiv.apply_eq_iff_eq (Equiv.sumComm (Fin m) (Fin n))).mpr ?h₂.a
  rw [Equiv.symm_apply_apply]

/-- `Fin (m + n) ≃ Fin (n + m)`. -/
def finAddCongr : Fin (m + n) ≃ Fin (n + m) := finCongr (add_comm m n)

@[simp]
lemma finAddCongr_finAddCongr (i : Fin (m + n)) :
    finAddCongr (finAddCongr i) = i :=
  rfl

@[simp]
lemma finAddCongr_symm_finAddCongr_symm (i : Fin (m + n)) :
    finAddCongr.symm (finAddCongr.symm i) = i :=
  rfl

/-- `Fin m ⊕ Fin n ≃ Fin n ⊕ Fin m` via `Sum.swap`. -/
def finSumCongr : Fin m ⊕ Fin n ≃ Fin n ⊕ Fin m where
  toFun x := x.swap
  invFun x := x.swap
  left_inv := Sum.swap_swap
  right_inv := Sum.swap_swap

@[simp]
lemma finSumCongr_symm_inl_inr (x : Fin m) :
    finSumCongr.symm (Sum.inl x) = (Sum.inr x : Fin n ⊕ Fin m) :=
  rfl

@[simp]
lemma finSumCongr_symm_inr_inl (x : Fin n) :
    finSumCongr.symm (Sum.inr x) = (Sum.inl x : Fin n ⊕ Fin m) :=
  rfl

/-! ## Interaction of `addCases` with `succAbove`

Deleting an element from a concatenated multi-index `addCases f g`. Deleting
from the left block gives `addCases (f ∘ succAbove i) g`; deleting from the
right block gives `addCases f (g ∘ succAbove j)` up to a `Fin.cast`. Used in
the graded Leibniz rule for the interior product on alternating forms. -/

/-- Deleting an element from the left block of `addCases I J` at position
`castAdd i`: the result is `addCases (I ∘ succAbove i) J` up to a `Fin.cast`.
The cast handles the def-eq mismatch `(m + n + 1) ≠ (m + (n + 1))`.

**Sorry**: PRE-PAPER. Mathlib gap. Index-juggling identity, target for
framework self-build via `Fin.addCases` API. Inherited from external lib's
`Tensor/Auxiliary/Fin.lean` (also sorry'd there). -/
theorem addCases_succAbove_castAdd {α : Type*} {m' n' : ℕ}
    (f : Fin (m' + 1) → α) (g : Fin (n' + 1) → α) (i : Fin (m' + 1))
    (k : Fin (m' + n' + 1)) :
    (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
      ((Fin.castAdd (n' + 1) i).succAbove
        (Fin.cast (show m' + n' + 1 = m' + 1 + n' from by omega) k)) =
    (Fin.addCases (f ∘ i.succAbove) g : Fin (m' + (n' + 1)) → α) k := by
  sorry

/-- Deleting an element from the right block of `addCases I J` at position
`natAdd j`: the result is `addCases I (J ∘ succAbove j)`.

**Sorry**: PRE-PAPER. Mathlib gap. See `addCases_succAbove_castAdd`. -/
theorem addCases_succAbove_natAdd {α : Type*} {m' n' : ℕ}
    (f : Fin (m' + 1) → α) (g : Fin (n' + 1) → α) (j : Fin (n' + 1))
    (k : Fin (m' + 1 + n')) :
    (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
      ((Fin.natAdd (m' + 1) j).succAbove k) =
    (Fin.addCases f (g ∘ j.succAbove) : Fin ((m' + 1) + n') → α) k := by
  sorry

/-- Substituting an `ℕ`-equality lets us compare determinants of matrices
indexed by `Fin a` and `Fin b` once their pointwise values agree under the
`Fin.cast`. -/
lemma det_subst_eq {R : Type*} [CommRing R] {a b : ℕ} (h : a = b)
    (f : Fin a → Fin a → R) (g : Fin b → Fin b → R)
    (hfg : ∀ i j, f (Fin.cast h.symm i) (Fin.cast h.symm j) = g i j) :
    Matrix.det f = Matrix.det g := by
  subst h; exact congr_arg _ (funext fun i => funext fun j => hfg i j)

end Fin
