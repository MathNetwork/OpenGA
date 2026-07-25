import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

open scoped BigOperators

namespace DifferentialGeometry
namespace Combinatorics

noncomputable def antidiagonalTupleGrid (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (i + 1),
    ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n, b (e m)

lemma antidiagonalTupleGrid_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) :
    0 ≤ antidiagonalTupleGrid b i :=
  Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => hb _)))

lemma antidiagonalTupleGrid_zero (b : ℕ → ℝ) :
    antidiagonalTupleGrid b 0 = 1 := by
  rw [antidiagonalTupleGrid, Finset.sum_range_one,
    Finset.Nat.antidiagonalTuple_zero_zero, Finset.sum_singleton, Fin.prod_univ_zero]

private def consQ (q n : ℕ) (e : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cons q e

private lemma consQ_injective (q n : ℕ) :
    Function.Injective (consQ q n) := by
  intro e₁ e₂ h
  have h₁ : Fin.tail (consQ q n e₁) = Fin.tail (consQ q n e₂) := by rw [h]
  rwa [consQ, consQ, Fin.tail_cons, Fin.tail_cons] at h₁

private lemma consQ_mem (q k n : ℕ) (e : Fin n → ℕ)
    (he : e ∈ Finset.Nat.antidiagonalTuple n k) :
    consQ q n e ∈ Finset.Nat.antidiagonalTuple (n + 1) (k + q) := by
  rw [Finset.Nat.mem_antidiagonalTuple] at he ⊢
  rw [consQ, Fin.sum_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rw [he]; omega

lemma single_factor_mul_antidiagonalTupleGrid_le
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (k q : ℕ) (hq : 1 ≤ q) :
    b q * antidiagonalTupleGrid b k ≤ antidiagonalTupleGrid b (k + q) := by
  classical
  have hterm : ∀ n : ℕ,
      b q * (∑ e ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e m)) ≤
        ∑ e' ∈ Finset.Nat.antidiagonalTuple (n + 1) (k + q), ∏ m : Fin (n + 1), b (e' m) := by
    intro n
    rw [Finset.mul_sum]
    have hcons : ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
        b q * ∏ m : Fin n, b (e m) =
          ∏ m : Fin (n + 1), b (consQ q n e m) := by
      intro e _
      rw [consQ, Fin.prod_univ_succ, Fin.cons_zero]
      refine congrArg (fun t => b q * t) (Finset.prod_congr rfl (fun m _ => ?_))
      rw [Fin.cons_succ]
    rw [Finset.sum_congr rfl hcons]
    rw [← Finset.sum_image
      (f := fun e' : Fin (n + 1) → ℕ => ∏ m : Fin (n + 1), b (e' m))
      (g := consQ q n)
      ((consQ_injective q n).injOn)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun e' _ _ => Finset.prod_nonneg (fun _ _ => hb _))
    intro e' he'
    rw [Finset.mem_image] at he'
    obtain ⟨e, he, rfl⟩ := he'
    exact consQ_mem q k n e he
  have hstep : b q * antidiagonalTupleGrid b k ≤
      ∑ n ∈ Finset.range (k + 1),
        ∑ e' ∈ Finset.Nat.antidiagonalTuple (n + 1) (k + q), ∏ m : Fin (n + 1), b (e' m) := by
    rw [antidiagonalTupleGrid, Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => hterm n)
  refine hstep.trans ?_
  rw [antidiagonalTupleGrid]
  have hshift : ∑ n ∈ Finset.range (k + 1),
        ∑ e' ∈ Finset.Nat.antidiagonalTuple (n + 1) (k + q), ∏ m : Fin (n + 1), b (e' m) =
      ∑ N ∈ Finset.Ico 1 (k + 2),
        ∑ e' ∈ Finset.Nat.antidiagonalTuple N (k + q), ∏ m : Fin N, b (e' m) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by rw [show k + 2 - 1 = k + 1 from by omega]) (fun n _ => ?_)
    rw [show 1 + n = n + 1 from by omega]
  rw [hshift]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun N _ _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun _ _ => hb _)))
  intro N hN
  rw [Finset.mem_Ico] at hN
  rw [Finset.mem_range]
  omega

noncomputable def recGridCS (A : ℝ) (B : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (A, A)
  | (n + 1) => let p := recGridCS A B n; (B n * p.2, p.2 + B n * p.2)

lemma recGridCS_snd_eq (A : ℝ) (B : ℕ → ℝ) :
    ∀ i, (recGridCS A B i).2 = ∑ k ∈ Finset.range (i + 1), (recGridCS A B k).1 := by
  intro i
  induction i with
  | zero => rw [Finset.sum_range_one]; rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    change (recGridCS A B n).2 + B n * (recGridCS A B n).2 =
      (recGridCS A B n).2 + (recGridCS A B (n + 1)).1
    rw [recGridCS]

lemma recGridCS_nonneg (A : ℝ) (B : ℕ → ℝ) (hA : 0 ≤ A) (hB : ∀ m, 0 ≤ B m) :
    ∀ i, 0 ≤ (recGridCS A B i).1 ∧ 0 ≤ (recGridCS A B i).2 := by
  intro i
  induction i with
  | zero => exact ⟨hA, hA⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩ <;>
      · show 0 ≤ _
        rw [recGridCS]
        first
        | exact mul_nonneg (hB n) ih.2
        | exact add_nonneg ih.2 (mul_nonneg (hB n) ih.2)

theorem antidiagonalTupleGrid_convolution_bound
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (a : ℕ → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (hbase : a 0 ≤ A)
    (hstep : ∀ m, a (m + 1) ≤
      B m * ∑ k ∈ Finset.range (m + 1), b ((m - k) + 1) * a k) :
    ∀ i, a i ≤ (recGridCS A B i).1 * antidiagonalTupleGrid b i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 =>
      rw [antidiagonalTupleGrid_zero, mul_one]
      change a 0 ≤ (recGridCS A B 0).1
      rw [recGridCS]; exact hbase
    | (m + 1) =>
      refine (hstep m).trans ?_
      have hkey : ∀ k ∈ Finset.range (m + 1),
          b ((m - k) + 1) * a k ≤
            (recGridCS A B k).1 * antidiagonalTupleGrid b (m + 1) := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hIH : a k ≤ (recGridCS A B k).1 * antidiagonalTupleGrid b k := ih k (by omega)
        have hCk_nn : 0 ≤ (recGridCS A B k).1 := (recGridCS_nonneg A B hA hB k).1
        calc b ((m - k) + 1) * a k
            ≤ b ((m - k) + 1) * ((recGridCS A B k).1 * antidiagonalTupleGrid b k) :=
              mul_le_mul_of_nonneg_left hIH (hb _)
          _ = (recGridCS A B k).1 * (b ((m - k) + 1) * antidiagonalTupleGrid b k) := by ring
          _ ≤ (recGridCS A B k).1 *
                antidiagonalTupleGrid b (k + ((m - k) + 1)) :=
              mul_le_mul_of_nonneg_left
                (single_factor_mul_antidiagonalTupleGrid_le b hb k ((m - k) + 1)
                  (by omega)) hCk_nn
          _ = (recGridCS A B k).1 * antidiagonalTupleGrid b (m + 1) := by
              rw [show k + ((m - k) + 1) = m + 1 from by omega]
      calc B m * ∑ k ∈ Finset.range (m + 1), b ((m - k) + 1) * a k
          ≤ B m * ∑ k ∈ Finset.range (m + 1),
              (recGridCS A B k).1 * antidiagonalTupleGrid b (m + 1) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hkey) (hB m)
        _ = B m * ((∑ k ∈ Finset.range (m + 1), (recGridCS A B k).1) *
              antidiagonalTupleGrid b (m + 1)) := by rw [← Finset.sum_mul]
        _ = (recGridCS A B (m + 1)).1 * antidiagonalTupleGrid b (m + 1) := by
            rw [← recGridCS_snd_eq A B m]
            show B m * ((recGridCS A B m).2 * antidiagonalTupleGrid b (m + 1)) = _
            rw [recGridCS]; ring

theorem antidiagonalTupleGrid_convolution_closure
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (a : ℕ → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (hbase : a 0 ≤ A)
    (hstep : ∀ m, a (m + 1) ≤
      B m * ∑ k ∈ Finset.range (m + 1), b ((m - k) + 1) * a k) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ i, a i ≤ C i * antidiagonalTupleGrid b i :=
  ⟨fun i => (recGridCS A B i).1, fun i => (recGridCS_nonneg A B hA hB i).1,
    antidiagonalTupleGrid_convolution_bound b hb a A hA B hB hbase hstep⟩

noncomputable def antidiagonalTupleGridCount (i : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)

lemma antidiagonalTupleGridCount_nonneg (i : ℕ) : 0 ≤ antidiagonalTupleGridCount i :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

lemma prodTerm_le_antidiagonalTupleGrid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (k n : ℕ) (hn : n < k + 1) (e : Fin n → ℕ)
    (he : e ∈ Finset.Nat.antidiagonalTuple n k) :
    (∏ m : Fin n, b (e m)) ≤ antidiagonalTupleGrid b k := by
  rw [antidiagonalTupleGrid]
  have h1 : (∏ m : Fin n, b (e m)) ≤
      ∑ e' ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e' m) :=
    Finset.single_le_sum (f := fun e' : Fin n → ℕ => ∏ m : Fin n, b (e' m))
      (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)) he
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n' : ℕ => ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k, ∏ m : Fin n', b (e' m))
    (fun n' _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)))
    (Finset.mem_range.mpr hn)

theorem antidiagonalTupleGrid_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j k : ℕ) :
    antidiagonalTupleGrid b j * antidiagonalTupleGrid b k ≤
      (antidiagonalTupleGridCount j * antidiagonalTupleGridCount k) *
        antidiagonalTupleGrid b (j + k) := by
  classical
  have hpair : ∀ n ∈ Finset.range (j + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n j,
      ∀ n' ∈ Finset.range (k + 1), ∀ e' ∈ Finset.Nat.antidiagonalTuple n' k,
      (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) ≤
        antidiagonalTupleGrid b (j + k) := by
    intro n hn e he n' hn' e' he'
    have happend : (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) =
        ∏ m : Fin (n + n'), b (Fin.append e e' m) := by
      rw [Fin.prod_univ_add]
      congr 1
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_left])
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_right])
    rw [happend]
    have hmem : Fin.append e e' ∈ Finset.Nat.antidiagonalTuple (n + n') (j + k) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at he he' ⊢
      rw [Fin.sum_univ_add]
      have h1 : (∑ m : Fin n, Fin.append e e' (Fin.castAdd n' m)) = j := by
        rw [← he]
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_left])
      have h2 : (∑ m : Fin n', Fin.append e e' (Fin.natAdd n m)) = k := by
        rw [← he']
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_right])
      rw [h1, h2]
    have hnn' : n + n' < j + k + 1 := by
      rw [Finset.mem_range] at hn hn'
      omega
    exact prodTerm_le_antidiagonalTupleGrid b hb (j + k) (n + n') hnn' _ hmem
  calc antidiagonalTupleGrid b j * antidiagonalTupleGrid b k
      = ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ((∏ m : Fin n, b (e m)) * antidiagonalTupleGrid b k) := by
        rw [antidiagonalTupleGrid, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])
    _ ≤ ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          (antidiagonalTupleGridCount k * antidiagonalTupleGrid b (j + k)) := by
        refine Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun e he => ?_))
        calc (∏ m : Fin n, b (e m)) * antidiagonalTupleGrid b k
            = ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                ((∏ m : Fin n, b (e m)) * ∏ m : Fin n', b (e' m)) := by
              rw [antidiagonalTupleGrid, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n' _ => by rw [Finset.mul_sum])
          _ ≤ ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                antidiagonalTupleGrid b (j + k) := by
              refine Finset.sum_le_sum (fun n' hn' => Finset.sum_le_sum (fun e' he' => ?_))
              exact hpair n hn e he n' hn' e' he'
          _ = antidiagonalTupleGridCount k * antidiagonalTupleGrid b (j + k) := by
              rw [antidiagonalTupleGridCount, Finset.sum_mul]
              exact Finset.sum_congr rfl (fun n' _ => by
                rw [Finset.sum_const, nsmul_eq_mul])
    _ = ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ) *
          (antidiagonalTupleGridCount k * antidiagonalTupleGrid b (j + k)) := by
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ = (antidiagonalTupleGridCount j * antidiagonalTupleGridCount k) *
          antidiagonalTupleGrid b (j + k) := by
        rw [show (antidiagonalTupleGridCount j * antidiagonalTupleGridCount k) *
            antidiagonalTupleGrid b (j + k) =
            antidiagonalTupleGridCount j *
              (antidiagonalTupleGridCount k * antidiagonalTupleGrid b (j + k)) from by
          ring]
        rw [show antidiagonalTupleGridCount j = ∑ n ∈ Finset.range (j + 1),
            ((Finset.Nat.antidiagonalTuple n j).card : ℝ) from rfl]
        rw [Finset.sum_mul]

noncomputable def antidiagonalTupleGridWindow (b : ℕ → ℝ) (w : ℕ) : ℝ :=
  ∑ k ∈ Finset.range w, antidiagonalTupleGrid b k

lemma antidiagonalTupleGridWindow_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (w : ℕ) :
    0 ≤ antidiagonalTupleGridWindow b w :=
  Finset.sum_nonneg (fun k _ => antidiagonalTupleGrid_nonneg b hb k)

lemma antidiagonalTupleGridWindow_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {w w' : ℕ}
    (h : w ≤ w') :
    antidiagonalTupleGridWindow b w ≤ antidiagonalTupleGridWindow b w' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun k _ _ => antidiagonalTupleGrid_nonneg b hb k)

lemma antidiagonalTupleGrid_le_window (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {k w : ℕ}
    (hk : k < w) :
    antidiagonalTupleGrid b k ≤ antidiagonalTupleGridWindow b w :=
  Finset.single_le_sum (fun k' _ => antidiagonalTupleGrid_nonneg b hb k')
    (Finset.mem_range.mpr hk)

lemma one_le_antidiagonalTupleGridWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {w : ℕ}
    (hw : 0 < w) : 1 ≤ antidiagonalTupleGridWindow b w := by
  rw [← antidiagonalTupleGrid_zero b]
  exact antidiagonalTupleGrid_le_window b hb hw

noncomputable def antidiagonalTupleGridWindowMulConst (a c : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (a + 1), ∑ k ∈ Finset.range (c + 1),
    antidiagonalTupleGridCount j * antidiagonalTupleGridCount k

lemma antidiagonalTupleGridWindowMulConst_nonneg (a c : ℕ) :
    0 ≤ antidiagonalTupleGridWindowMulConst a c :=
  Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
    mul_nonneg (antidiagonalTupleGridCount_nonneg j) (antidiagonalTupleGridCount_nonneg k)))

theorem antidiagonalTupleGridWindow_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (a c : ℕ) :
    antidiagonalTupleGridWindow b (a + 1) * antidiagonalTupleGridWindow b (c + 1) ≤
      antidiagonalTupleGridWindowMulConst a c * antidiagonalTupleGridWindow b (a + c + 1) := by
  calc antidiagonalTupleGridWindow b (a + 1) * antidiagonalTupleGridWindow b (c + 1)
      = ∑ j ∈ Finset.range (a + 1), ∑ k ∈ Finset.range (c + 1),
          antidiagonalTupleGrid b j * antidiagonalTupleGrid b k := by
        rw [antidiagonalTupleGridWindow, antidiagonalTupleGridWindow, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    _ ≤ ∑ j ∈ Finset.range (a + 1), ∑ k ∈ Finset.range (c + 1),
          (antidiagonalTupleGridCount j * antidiagonalTupleGridCount k) *
            antidiagonalTupleGridWindow b (a + c + 1) := by
        refine Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => ?_))
        refine le_trans (antidiagonalTupleGrid_mul_le b hb j k) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (antidiagonalTupleGridCount_nonneg j)
            (antidiagonalTupleGridCount_nonneg k))
        refine antidiagonalTupleGrid_le_window b hb ?_
        rw [Finset.mem_range] at hj hk
        omega
    _ = antidiagonalTupleGridWindowMulConst a c *
          antidiagonalTupleGridWindow b (a + c + 1) := by
        rw [antidiagonalTupleGridWindowMulConst, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_mul])

end Combinatorics
end DifferentialGeometry
