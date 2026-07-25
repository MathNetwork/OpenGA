import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContr

set_option autoImplicit false
set_option linter.style.longLine false












noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]


def compL2Sq {r : ℕ} (T : (Fin r → Idx) → Real) : Real :=
  ∑ idx : Fin r → Idx, (T idx) ^ 2

omit [DecidableEq Idx] in
theorem compL2Sq_nonneg {r : ℕ} (T : (Fin r → Idx) → Real) : 0 ≤ compL2Sq T :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _


omit [DecidableEq Idx] in
private theorem sum_snoc_split {p : ℕ} (F : (Fin (p + 1) → Idx) → Real) :
    (∑ f : Fin (p + 1) → Idx, F f) =
      ∑ g : Fin p → Idx, ∑ c : Idx, F (Fin.snoc g c) := by
  classical
  let e : (Fin (p + 1) → Idx) ≃ (Fin p → Idx) × Idx :=
    { toFun := fun f => (Fin.init f, f (Fin.last p))
      invFun := fun gc => Fin.snoc gc.1 gc.2
      left_inv := fun f => Fin.snoc_init_self f
      right_inv := fun gc => by simp [Fin.init_snoc, Fin.snoc_last] }
  rw [show (∑ g : Fin p → Idx, ∑ c : Idx, F (Fin.snoc g c))
      = ∑ gc : (Fin p → Idx) × Idx, F (Fin.snoc gc.1 gc.2) from
    (Fintype.sum_prod_type (fun gc : (Fin p → Idx) × Idx => F (Fin.snoc gc.1 gc.2))).symm]
  exact Fintype.sum_equiv e F (fun gc => F (Fin.snoc gc.1 gc.2))
    (fun f => by simp only [e, Equiv.coe_fn_mk, Fin.snoc_init_self])


omit [DecidableEq Idx] in
private theorem sum_append_split {p q : ℕ} (F : (Fin (p + q) → Idx) → Real) :
    (∑ idx : Fin (p + q) → Idx, F idx) =
      ∑ a : Fin p → Idx, ∑ b : Fin q → Idx, F (Fin.append a b) := by
  classical
  rw [show (∑ a : Fin p → Idx, ∑ b : Fin q → Idx, F (Fin.append a b))
      = ∑ ab : (Fin p → Idx) × (Fin q → Idx), F (Fin.append ab.1 ab.2) from
    (Fintype.sum_prod_type (fun ab => F (Fin.append ab.1 ab.2))).symm]
  refine Fintype.sum_equiv
    { toFun := fun idx => (fun i => idx (Fin.castAdd q i), fun j => idx (Fin.natAdd p j))
      invFun := fun ab => Fin.append ab.1 ab.2
      left_inv := fun idx => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · simp [Fin.append_left]
        · simp [Fin.append_right]
      right_inv := fun ab => by
        refine Prod.ext ?_ ?_
        · funext i; simp [Fin.append_left]
        · funext j; simp [Fin.append_right] } F (fun ab => F (Fin.append ab.1 ab.2)) ?_
  intro idx
  congr 1
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [Fin.append_left]
  · simp [Fin.append_right]



omit [DecidableEq Idx] in
theorem compL2Sq_contrTail_le {p q : ℕ}
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real) :
    compL2Sq (contrTail A B) ≤ compL2Sq A * compL2Sq B := by
  classical
  have hcs : ∀ idx : Fin (p + q) → Idx,
      (contrTail A B idx) ^ 2 ≤
        (∑ c : Idx, A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) ^ 2) *
          (∑ c : Idx, B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) ^ 2) := by
    intro idx
    rw [contrTail_apply]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc
    compL2Sq (contrTail A B)
        = ∑ idx : Fin (p + q) → Idx, (contrTail A B idx) ^ 2 := rfl
    _ ≤ ∑ idx : Fin (p + q) → Idx,
          (∑ c : Idx, A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) ^ 2) *
            (∑ c : Idx, B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) ^ 2) :=
          Finset.sum_le_sum fun idx _ => hcs idx
    _ = (∑ a : Fin p → Idx, ∑ c : Idx, A (Fin.snoc a c) ^ 2) *
          (∑ b : Fin q → Idx, ∑ c : Idx, B (Fin.snoc b c) ^ 2) := by
          rw [sum_append_split
            (F := fun idx =>
              (∑ c : Idx, A (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) ^ 2) *
                (∑ c : Idx, B (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) ^ 2))]
          simp only [Fin.append_left, Fin.append_right]
          rw [← Finset.sum_mul_sum]
    _ = compL2Sq A * compL2Sq B := by
          rw [compL2Sq, compL2Sq, sum_snoc_split (F := fun f => A f ^ 2),
            sum_snoc_split (F := fun f => B f ^ 2)]


def compL2 {r : ℕ} (T : (Fin r → Idx) → Real) : Real := Real.sqrt (compL2Sq T)

omit [DecidableEq Idx] in
theorem compL2_nonneg {r : ℕ} (T : (Fin r → Idx) → Real) : 0 ≤ compL2 T :=
  Real.sqrt_nonneg _

omit [DecidableEq Idx] in
theorem compL2_sq {r : ℕ} (T : (Fin r → Idx) → Real) : compL2 T ^ 2 = compL2Sq T := by
  rw [compL2, Real.sq_sqrt (compL2Sq_nonneg T)]



omit [DecidableEq Idx] in
theorem compL2Sq_comp_equiv {r r' : ℕ} (T : (Fin r → Idx) → Real) (e : Fin r ≃ Fin r') :
    compL2Sq (fun idx : Fin r' → Idx => T (fun i => idx (e i))) = compL2Sq T := by
  classical
  simp only [compL2Sq]
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Idx))
    (fun idx : Fin r' → Idx => T (fun i => idx (e i)) ^ 2)
    (fun g : Fin r → Idx => T g ^ 2) ?_
  intro idx
  have hfun : (e.symm.arrowCongr (Equiv.refl Idx)) idx = fun i => idx (e i) := by
    funext i
    simp [Equiv.arrowCongr_apply, Equiv.symm_symm]
  rw [hfun]


omit [DecidableEq Idx] in
theorem compL2_comp_equiv {r r' : ℕ} (T : (Fin r → Idx) → Real) (e : Fin r ≃ Fin r') :
    compL2 (fun idx : Fin r' → Idx => T (fun i => idx (e i))) = compL2 T := by
  rw [compL2, compL2, compL2Sq_comp_equiv]


omit [DecidableEq Idx] in
theorem compL2_contrTail_le {p q : ℕ}
    (A : (Fin (p + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real) :
    compL2 (contrTail A B) ≤ compL2 A * compL2 B := by
  rw [compL2, compL2, compL2, ← Real.sqrt_mul (compL2Sq_nonneg A)]
  exact Real.sqrt_le_sqrt (compL2Sq_contrTail_le A B)


omit [DecidableEq Idx] in
theorem compL2_add_le {r : ℕ} (T U : (Fin r → Idx) → Real) :
    compL2 (fun idx => T idx + U idx) ≤ compL2 T + compL2 U := by
  have hCS : (∑ idx : Fin r → Idx, T idx * U idx) ≤ compL2 T * compL2 U := by
    have hle : (∑ idx : Fin r → Idx, T idx * U idx)
        ≤ Real.sqrt ((∑ idx : Fin r → Idx, T idx * U idx) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
    calc ∑ idx : Fin r → Idx, T idx * U idx
        ≤ Real.sqrt ((∑ idx : Fin r → Idx, T idx * U idx) ^ 2) := hle
      _ ≤ Real.sqrt (compL2Sq T * compL2Sq U) :=
            Real.sqrt_le_sqrt
              (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun idx => T idx) (fun idx => U idx))
      _ = compL2 T * compL2 U := by rw [compL2, compL2, Real.sqrt_mul (compL2Sq_nonneg T)]
  have hsq : compL2Sq (fun idx => T idx + U idx) ≤ (compL2 T + compL2 U) ^ 2 := by
    have hexp : compL2Sq (fun idx => T idx + U idx)
        = compL2Sq T + 2 * (∑ idx : Fin r → Idx, T idx * U idx) + compL2Sq U := by
      simp only [compL2Sq]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun idx _ => by ring
    rw [hexp]
    have h1 := compL2_sq T
    have h2 := compL2_sq U
    nlinarith [hCS, compL2_nonneg T, compL2_nonneg U]
  rw [compL2]
  calc Real.sqrt (compL2Sq (fun idx => T idx + U idx))
      ≤ Real.sqrt ((compL2 T + compL2 U) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = compL2 T + compL2 U :=
          Real.sqrt_sq (add_nonneg (compL2_nonneg T) (compL2_nonneg U))


omit [DecidableEq Idx] in
theorem compL2_neg {r : ℕ} (T : (Fin r → Idx) → Real) :
    compL2 (fun idx => -T idx) = compL2 T := by
  simp only [compL2, compL2Sq]
  congr 1
  exact Finset.sum_congr rfl fun idx _ => by ring



omit [DecidableEq Idx] in
theorem compL2_sub_le {r : ℕ} (T U : (Fin r → Idx) → Real) :
    compL2 (fun idx => T idx - U idx) ≤ compL2 T + compL2 U := by
  have h := compL2_add_le T (fun idx => -U idx)
  rw [compL2_neg] at h
  simpa only [sub_eq_add_neg] using h


omit [DecidableEq Idx] in
theorem compL2_smul {r : ℕ} (c : Real) (T : (Fin r → Idx) → Real) :
    compL2 (fun idx => c * T idx) = |c| * compL2 T := by
  rw [compL2, compL2,
    show compL2Sq (fun idx => c * T idx) = c ^ 2 * compL2Sq T from by
      simp only [compL2Sq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun idx _ => by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.HCGCompactness

open scoped BigOperators




theorem pascal_sum (m : ℕ) (g : ℕ → ℝ) :
    (∑ c ∈ Finset.range (m + 1), (m.choose c : ℝ) * g (c + 1)) +
        (∑ c ∈ Finset.range (m + 1), (m.choose c : ℝ) * g c)
      = ∑ c ∈ Finset.range (m + 2), ((m + 1).choose c : ℝ) * g c := by
  rw [Finset.sum_range_succ' (fun c => ((m + 1).choose c : ℝ) * g c) (m + 1),
    Finset.sum_range_succ' (fun c => (m.choose c : ℝ) * g c) m]
  simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_zero_right, Nat.cast_one,
    add_mul, one_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun c => (m.choose (c + 1) : ℝ) * g (c + 1)) m,
    Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  ring




theorem pascal_sum_notop (m : ℕ) (g : ℕ → ℝ) :
    (∑ c ∈ Finset.range m, (m.choose c : ℝ) * g (c + 1)) +
        (∑ c ∈ Finset.range (m + 1), (m.choose c : ℝ) * g c)
      = ∑ c ∈ Finset.range (m + 1), ((m + 1).choose c : ℝ) * g c := by
  have h := pascal_sum m g
  rw [Finset.sum_range_succ (fun c => (m.choose c : ℝ) * g (c + 1)) m,
    show m + 2 = m + 1 + 1 from rfl,
    Finset.sum_range_succ (fun c => ((m + 1).choose c : ℝ) * g c) (m + 1),
    Nat.choose_self, Nat.choose_self] at h
  simp only [Nat.cast_one, one_mul] at h
  linarith

end DifferentialGeometry.HCGCompactness
