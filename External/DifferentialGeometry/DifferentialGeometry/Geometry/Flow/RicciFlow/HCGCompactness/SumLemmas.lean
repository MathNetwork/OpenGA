import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Lemma45Constants
import Mathlib.Tactic

set_option autoImplicit false








noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped BigOperators

theorem sum_range_le_sum_range
    {N : Nat -> Real}
    (hN : forall i : Nat, 0 <= N i)
    {k p : Nat} (hkp : k <= p) :
    Finset.sum (Finset.range (k + 1)) (fun i => N i) <=
    Finset.sum (Finset.range (p + 1)) (fun i => N i) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_range]
    omega
  · intro i _hi_big _hi_small
    exact hN i

theorem sum_shift_le_full
    {N : Nat -> Real}
    (hN : forall i : Nat, 0 <= N i)
    (p : Nat) :
    Finset.sum (Finset.range p) (fun k => N (k + 1)) <=
      Finset.sum (Finset.range (p + 1)) (fun i => N i) := by
  induction p with
  | zero =>
      simp [hN 0]
  | succ p ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right ih (N (p + 1))

theorem single_le_sum_range
    {N : Nat -> Real}
    (hN : forall i : Nat, 0 <= N i)
    {i k : Nat} (hik : i <= k) :
    N i <= Finset.sum (Finset.range (k + 1)) (fun j => N j) := by
  have hi_mem : i ∈ Finset.range (k + 1) := by
    rw [Finset.mem_range]
    omega
  exact Finset.single_le_sum (fun j _hj => hN j) hi_mem

theorem oneStep_partial_to_full
    {eps E G : Real} {N : Nat -> Real} {k p : Nat}
    (heps : 0 <= eps)
    (hE : 0 <= E)
    (hN : forall i : Nat, 0 <= N i)
    (hkp : k <= p)
    (h :
      G <= N (k + 1)
        + eps * E * Finset.sum (Finset.range (k + 1)) (fun i => N i)) :
    G <= N (k + 1)
      + eps * E * Finset.sum (Finset.range (p + 1)) (fun i => N i) := by
  have hsum :
      Finset.sum (Finset.range (k + 1)) (fun i => N i) <=
        Finset.sum (Finset.range (p + 1)) (fun i => N i) :=
    sum_range_le_sum_range hN hkp
  have hcoef : 0 <= eps * E := mul_nonneg heps hE
  have hmul :
      eps * E * Finset.sum (Finset.range (k + 1)) (fun i => N i) <=
        eps * E * Finset.sum (Finset.range (p + 1)) (fun i => N i) := by
    exact mul_le_mul_of_nonneg_left hsum hcoef
  linarith







theorem oneStep_from_leibniz
    {eps G : Real} {B A T N : Nat -> Real} {k s : Nat}
    (heps0 : 0 <= eps)
    (hB : forall i : Nat, 0 <= B i)
    (hT_nonneg : forall i : Nat, i <= k -> 0 <= T i)
    (hA : forall a : Nat, a <= k -> A a <= eps * B a)
    (hT : forall a : Nat, a <= k ->
      T (k - a) <= Finset.sum (Finset.range (k + 1)) (fun i => N i))
    (hG :
      G <= N (k + 1) +
        (s : Real) *
          Finset.sum (Finset.range (k + 1))
            (fun a => (Nat.choose k a : Real) * A a * T (k - a))) :
    G <= N (k + 1) +
      eps * oneStepConst B k s *
        Finset.sum (Finset.range (k + 1)) (fun i => N i) := by
  let S : Real := Finset.sum (Finset.range (k + 1)) (fun i => N i)
  have hterm (a : Nat) (ha_mem : a ∈ Finset.range (k + 1)) :
      (Nat.choose k a : Real) * A a * T (k - a) <=
        (Nat.choose k a : Real) * (eps * B a * S) := by
    have ha : a <= k := by
      rw [Finset.mem_range] at ha_mem
      omega
    have hchoose : 0 <= (Nat.choose k a : Real) := by
      positivity
    have hA_upper : 0 <= eps * B a := mul_nonneg heps0 (hB a)
    have hprod :
        A a * T (k - a) <= (eps * B a) * S := by
      exact mul_le_mul
        (hA a ha) (by simpa [S] using hT a ha)
        (hT_nonneg (k - a) (Nat.sub_le k a)) hA_upper
    calc
      (Nat.choose k a : Real) * A a * T (k - a)
          = (Nat.choose k a : Real) * (A a * T (k - a)) := by ring
      _ <= (Nat.choose k a : Real) * ((eps * B a) * S) := by
          exact mul_le_mul_of_nonneg_left hprod hchoose
      _ = (Nat.choose k a : Real) * (eps * B a * S) := by ring
  have hsum :
      Finset.sum (Finset.range (k + 1))
          (fun a => (Nat.choose k a : Real) * A a * T (k - a)) <=
        Finset.sum (Finset.range (k + 1))
          (fun a => (Nat.choose k a : Real) * (eps * B a * S)) := by
    exact Finset.sum_le_sum fun a ha => hterm a ha
  have hsum_factor :
      Finset.sum (Finset.range (k + 1))
          (fun a => (Nat.choose k a : Real) * (eps * B a * S)) =
        eps * S *
          Finset.sum (Finset.range (k + 1))
            (fun a => (Nat.choose k a : Real) * B a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  have hsum_scaled :
      (s : Real) *
          Finset.sum (Finset.range (k + 1))
            (fun a => (Nat.choose k a : Real) * A a * T (k - a)) <=
        eps * oneStepConst B k s * S := by
    have hs_nonneg : 0 <= (s : Real) := by positivity
    calc
      (s : Real) *
          Finset.sum (Finset.range (k + 1))
            (fun a => (Nat.choose k a : Real) * A a * T (k - a))
          <=
        (s : Real) *
          Finset.sum (Finset.range (k + 1))
            (fun a => (Nat.choose k a : Real) * (eps * B a * S)) := by
            exact mul_le_mul_of_nonneg_left hsum hs_nonneg
      _ = eps * oneStepConst B k s * S := by
            rw [hsum_factor]
            simp [oneStepConst, S]
            ring
  linarith






theorem oneStep_from_antidiagonal
    {eps G : Real} {B A T N : Nat -> Real} {k s : Nat}
    (heps0 : 0 <= eps)
    (hB : forall i : Nat, 0 <= B i)
    (hT_nonneg : forall i : Nat, i <= k -> 0 <= T i)
    (hA : forall a : Nat, a <= k -> A a <= eps * B a)
    (hT : forall b : Nat, b <= k ->
      T b <= Finset.sum (Finset.range (k + 1)) (fun i => N i))
    (hG :
      G <= N (k + 1) +
        (s : Real) *
          Finset.sum (Finset.antidiagonal k)
            (fun ab => (Nat.choose k ab.1 : Real) * A ab.1 * T ab.2)) :
    G <= N (k + 1) +
      eps * oneStepConst B k s *
        Finset.sum (Finset.range (k + 1)) (fun i => N i) := by
  have hsum :
      Finset.sum (Finset.antidiagonal k)
          (fun ab => (Nat.choose k ab.1 : Real) * A ab.1 * T ab.2) =
        Finset.sum (Finset.range (k + 1))
          (fun a => (Nat.choose k a : Real) * A a * T (k - a)) := by
    simpa [Nat.succ_eq_add_one] using
      (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b : Nat => (Nat.choose k a : Real) * A a * T b) k)
  have hG_range :
      G <= N (k + 1) +
        (s : Real) *
          Finset.sum (Finset.range (k + 1))
            (fun a => (Nat.choose k a : Real) * A a * T (k - a)) := by
    simpa [hsum] using hG
  exact oneStep_from_leibniz
    (eps := eps) (G := G) (B := B) (A := A) (T := T) (N := N)
    (k := k) (s := s) heps0 hB hT_nonneg hA
    (fun a ha => hT (k - a) (Nat.sub_le k a)) hG_range

private theorem sum_eps_E_mul
    {eps S : Real} {E : Nat -> Real} (p : Nat) :
    Finset.sum (Finset.range p) (fun k => eps * E k * S) =
      eps * S * Finset.sum (Finset.range p) (fun k => E k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring






theorem main_step_algebra
    {eps C A : Real} {E N G : Nat -> Real} {p : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hC : 0 <= C)
    (hE : forall k : Nat, 0 <= E k)
    (hN : forall i : Nat, 0 <= N i)
    (hA :
      A <= G p + eps * C * Finset.sum (Finset.range p) (fun k => G k))
    (hGp :
      G p <= N (p + 1)
        + eps * E p * Finset.sum (Finset.range (p + 1)) (fun i => N i))
    (hGk :
      forall k : Nat, k < p ->
        G k <= N (k + 1)
          + eps * E k * Finset.sum (Finset.range (p + 1)) (fun i => N i)) :
    A <=
      N (p + 1)
        + eps * (E p + C * (1 + Finset.sum (Finset.range p) (fun k => E k)))
          * Finset.sum (Finset.range (p + 1)) (fun i => N i) := by
  let S : Real := Finset.sum (Finset.range (p + 1)) (fun i => N i)
  let ESum : Real := Finset.sum (Finset.range p) (fun k => E k)
  have hS_nonneg : 0 <= S := by
    exact Finset.sum_nonneg fun i _hi => hN i
  have hESum_nonneg : 0 <= ESum := by
    exact Finset.sum_nonneg fun k _hk => hE k
  have hsumG0 :
      Finset.sum (Finset.range p) (fun k => G k) <=
        Finset.sum (Finset.range p) (fun k => N (k + 1) + eps * E k * S) := by
    exact Finset.sum_le_sum fun k hk => hGk k (by simpa [Finset.mem_range] using hk)
  have hsumG1 :
      Finset.sum (Finset.range p) (fun k => G k) <=
        Finset.sum (Finset.range p) (fun k => N (k + 1)) + eps * S * ESum := by
    calc
      Finset.sum (Finset.range p) (fun k => G k)
          <= Finset.sum (Finset.range p) (fun k => N (k + 1) + eps * E k * S) := hsumG0
      _ = Finset.sum (Finset.range p) (fun k => N (k + 1)) +
            Finset.sum (Finset.range p) (fun k => eps * E k * S) := by
            rw [Finset.sum_add_distrib]
      _ = Finset.sum (Finset.range p) (fun k => N (k + 1)) + eps * S * ESum := by
            rw [sum_eps_E_mul]
  have hshift :
      Finset.sum (Finset.range p) (fun k => N (k + 1)) <= S := by
    simpa [S] using sum_shift_le_full hN p
  have hsumG2 :
      Finset.sum (Finset.range p) (fun k => G k) <= S + eps * S * ESum := by
    linarith
  have hepsS :
      eps * S * ESum <= S * ESum := by
    have hSE : 0 <= S * ESum := mul_nonneg hS_nonneg hESum_nonneg
    have h := mul_le_mul_of_nonneg_right heps1 hSE
    nlinarith
  have hsumG3 :
      Finset.sum (Finset.range p) (fun k => G k) <= (1 + ESum) * S := by
    have htmp : S + eps * S * ESum <= S + S * ESum := by
      linarith
    have hrewrite : S + S * ESum = (1 + ESum) * S := by ring
    linarith
  have hcoef_nonneg : 0 <= eps * C := mul_nonneg heps0 hC
  have hmul_sum :
      eps * C * Finset.sum (Finset.range p) (fun k => G k) <=
        eps * C * ((1 + ESum) * S) := by
    exact mul_le_mul_of_nonneg_left hsumG3 hcoef_nonneg
  have hmain1 :
      A <= N (p + 1) + eps * E p * S +
        eps * C * ((1 + ESum) * S) := by
    linarith
  have hfinal_rewrite :
      N (p + 1) + eps * E p * S +
        eps * C * ((1 + ESum) * S) =
      N (p + 1) + eps * (E p + C * (1 + ESum)) * S := by
    ring
  simpa [S, ESum, hfinal_rewrite] using hmain1

theorem main_step_coeff_le_lemma45Const
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (p s : Nat) :
    oneStepConst B p s
      + lemma45Const B p (s + 1)
        * (1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k s))
      <= lemma45Const B (p + 1) s := by
  have hbase : 0 <= lemma45Const B p s :=
    lemma45Const_nonneg hB p s
  simp [lemma45Const]
  linarith







theorem main_step_to_lemma45Const
    {eps A : Real} {B N G : Nat -> Real} {p s : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (hN : forall i : Nat, 0 <= N i)
    (hA :
      A <= G p + eps * lemma45Const B p (s + 1) *
        Finset.sum (Finset.range p) (fun k => G k))
    (hGp :
      G p <= N (p + 1)
        + eps * oneStepConst B p s *
          Finset.sum (Finset.range (p + 1)) (fun i => N i))
    (hGk :
      forall k : Nat, k < p ->
        G k <= N (k + 1)
          + eps * oneStepConst B k s *
            Finset.sum (Finset.range (p + 1)) (fun i => N i)) :
    A <=
      N (p + 1)
        + eps * lemma45Const B (p + 1) s *
          Finset.sum (Finset.range (p + 1)) (fun i => N i) := by
  let S : Real := Finset.sum (Finset.range (p + 1)) (fun i => N i)
  let coeff : Real :=
    oneStepConst B p s
      + lemma45Const B p (s + 1)
        * (1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k s))
  have hmain :
      A <= N (p + 1) + eps * coeff * S := by
    simpa [S, coeff, add_comm, add_left_comm, add_assoc] using
      main_step_algebra
        (eps := eps) (C := lemma45Const B p (s + 1))
        (A := A) (E := fun k => oneStepConst B k s)
        (N := N) (G := G) (p := p)
        heps0 heps1 (lemma45Const_nonneg hB p (s + 1))
        (fun k => oneStepConst_nonneg hB k s) hN hA hGp hGk
  have hcoef : coeff <= lemma45Const B (p + 1) s := by
    simpa [coeff] using main_step_coeff_le_lemma45Const hB p s
  have hS_nonneg : 0 <= S := by
    exact Finset.sum_nonneg fun i _hi => hN i
  have hepsS_nonneg : 0 <= eps * S := mul_nonneg heps0 hS_nonneg
  have hmul :
      eps * coeff * S <= eps * lemma45Const B (p + 1) s * S := by
    calc
      eps * coeff * S = (eps * S) * coeff := by ring
      _ <= (eps * S) * lemma45Const B (p + 1) s :=
          mul_le_mul_of_nonneg_left hcoef hepsS_nonneg
      _ = eps * lemma45Const B (p + 1) s * S := by ring
  linarith



theorem main_step_to_lemma45Const_of_partials
    {eps A : Real} {B N G : Nat -> Real} {p s : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (hN : forall i : Nat, 0 <= N i)
    (hA :
      A <= G p + eps * lemma45Const B p (s + 1) *
        Finset.sum (Finset.range p) (fun k => G k))
    (hGp :
      G p <= N (p + 1)
        + eps * oneStepConst B p s *
          Finset.sum (Finset.range (p + 1)) (fun i => N i))
    (hGk :
      forall k : Nat, k < p ->
        G k <= N (k + 1)
          + eps * oneStepConst B k s *
            Finset.sum (Finset.range (k + 1)) (fun i => N i)) :
    A <=
      N (p + 1)
        + eps * lemma45Const B (p + 1) s *
          Finset.sum (Finset.range (p + 1)) (fun i => N i) := by
  refine main_step_to_lemma45Const
    (eps := eps) (A := A) (B := B) (N := N) (G := G)
    (p := p) (s := s) heps0 heps1 hB hN hA hGp ?_
  intro k hk
  exact oneStep_partial_to_full
    (eps := eps) (E := oneStepConst B k s) (G := G k) (N := N)
    heps0 (oneStepConst_nonneg hB k s) hN (Nat.le_of_lt hk)
    (hGk k hk)

end HCGCompactness
end DifferentialGeometry
