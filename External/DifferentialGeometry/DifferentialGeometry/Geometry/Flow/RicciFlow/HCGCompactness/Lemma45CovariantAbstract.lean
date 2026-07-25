import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SumLemmas
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference

set_option autoImplicit false































noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped BigOperators













theorem lemma45Scalar
    {eps : Real} {B N G D : Nat -> Real} {s : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (hN : forall i : Nat, 0 <= N i)
    (hLift : forall p : Nat,
      D (p + 1) <= G p + eps * lemma45Const B p (s + 1) *
        Finset.sum (Finset.range p) (fun k => G k))
    (hOne : forall k : Nat,
      G k <= N (k + 1) + eps * oneStepConst B k s *
        Finset.sum (Finset.range (k + 1)) (fun i => N i)) :
    forall p r : Nat, 0 < r -> r <= p ->
      D r <= N r + eps * lemma45Const B p s *
        Finset.sum (Finset.range r) (fun i => N i) := by
  intro p
  induction p with
  | zero =>
      intro r hr0 hrp
      omega
  | succ p ih =>
      intro r hr0 hrp
      by_cases hr_le_p : r <= p
      · have hih := ih r hr0 hr_le_p
        let S : Real := Finset.sum (Finset.range r) (fun i => N i)
        have hS_nonneg : 0 <= S := by
          exact Finset.sum_nonneg fun i _hi => hN i
        have hcoef :
            lemma45Const B p s <= lemma45Const B (p + 1) s :=
          lemma45Const_le_succ hB p s
        have hepsS_nonneg : 0 <= eps * S := mul_nonneg heps0 hS_nonneg
        have hmul :
            eps * lemma45Const B p s * S <=
              eps * lemma45Const B (p + 1) s * S := by
          calc
            eps * lemma45Const B p s * S = (eps * S) * lemma45Const B p s := by
              ring
            _ <= (eps * S) * lemma45Const B (p + 1) s :=
              mul_le_mul_of_nonneg_left hcoef hepsS_nonneg
            _ = eps * lemma45Const B (p + 1) s * S := by
              ring
        have hmono :
            N r + eps * lemma45Const B p s * S <=
              N r + eps * lemma45Const B (p + 1) s * S :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hmul (N r)
        exact hih.trans (by simpa [S] using hmono)
      · have hr_eq : r = p + 1 := by omega
        subst r
        exact main_step_to_lemma45Const_of_partials
          (eps := eps) (A := D (p + 1)) (B := B) (N := N) (G := G)
          (p := p) (s := s)
          heps0 heps1 hB hN (hLift p) (hOne p)
          (fun k _hk => hOne k)








theorem lemma45Anti
    {eps : Real} {B A N G D : Nat -> Real} {s : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (hN : forall i : Nat, 0 <= N i)
    (hA : forall a : Nat, A a <= eps * B a)
    (hLift : forall p : Nat,
      D (p + 1) <= G p + eps * lemma45Const B p (s + 1) *
        Finset.sum (Finset.range p) (fun k => G k))
    (hLeib : forall k : Nat,
      G k <= N (k + 1) +
        (s : Real) *
          Finset.sum (Finset.antidiagonal k)
            (fun ab => (Nat.choose k ab.1 : Real) * A ab.1 * N ab.2)) :
    forall p r : Nat, 0 < r -> r <= p ->
      D r <= N r + eps * lemma45Const B p s *
        Finset.sum (Finset.range r) (fun i => N i) := by
  refine lemma45Scalar
    (eps := eps) (B := B) (N := N) (G := G) (D := D) (s := s)
    heps0 heps1 hB hN hLift ?_
  intro k
  exact oneStep_from_antidiagonal
    (eps := eps) (G := G k) (B := B) (A := A) (T := N) (N := N)
    (k := k) (s := s) heps0 hB
    (fun i _hi => hN i)
    (fun a _ha => hA a)
    (fun b hb => single_le_sum_range hN hb)
    (hLeib k)





theorem lemma45ScalarBdd
    {eps : Real} {B N G D : Nat -> Real} {s P : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (hN : forall i : Nat, 0 <= N i)
    (hLift : forall p : Nat, p < P ->
      D (p + 1) <= G p + eps * lemma45Const B p (s + 1) *
        Finset.sum (Finset.range p) (fun k => G k))
    (hOne : forall k : Nat, k < P ->
      G k <= N (k + 1) + eps * oneStepConst B k s *
        Finset.sum (Finset.range (k + 1)) (fun i => N i)) :
    forall r : Nat, 0 < r -> r <= P ->
      D r <= N r + eps * lemma45Const B P s *
        Finset.sum (Finset.range r) (fun i => N i) := by
  revert hLift hOne
  induction P with
  | zero =>
      intro _ _ r hr0 hrP
      omega
  | succ P ih =>
      intro hLift hOne r hr0 hrP
      by_cases hr_le : r <= P
      · have hih := ih
          (fun p hp => hLift p (hp.trans (Nat.lt_succ_self P)))
          (fun k hk => hOne k (hk.trans (Nat.lt_succ_self P)))
          r hr0 hr_le
        have hS_nonneg : 0 <= Finset.sum (Finset.range r) (fun i => N i) :=
          Finset.sum_nonneg fun i _hi => hN i
        have hcoef : lemma45Const B P s <= lemma45Const B (P + 1) s :=
          lemma45Const_le_succ hB P s
        have hepsS : 0 <= eps * Finset.sum (Finset.range r) (fun i => N i) :=
          mul_nonneg heps0 hS_nonneg
        have hmul :
            eps * lemma45Const B P s *
              Finset.sum (Finset.range r) (fun i => N i) <=
            eps * lemma45Const B (P + 1) s *
              Finset.sum (Finset.range r) (fun i => N i) := by
          calc
            eps * lemma45Const B P s * Finset.sum (Finset.range r) (fun i => N i)
                = (eps * Finset.sum (Finset.range r) (fun i => N i)) *
                    lemma45Const B P s := by ring
            _ <= (eps * Finset.sum (Finset.range r) (fun i => N i)) *
                    lemma45Const B (P + 1) s :=
                  mul_le_mul_of_nonneg_left hcoef hepsS
            _ = eps * lemma45Const B (P + 1) s *
                    Finset.sum (Finset.range r) (fun i => N i) := by ring
        linarith
      · have hr_eq : r = P + 1 := by omega
        subst hr_eq
        exact main_step_to_lemma45Const_of_partials
          (eps := eps) (A := D (P + 1)) (B := B) (N := N) (G := G)
          (p := P) (s := s) heps0 heps1 hB hN
          (hLift P (Nat.lt_succ_self P))
          (hOne P (Nat.lt_succ_self P))
          (fun k hk => hOne k (hk.trans (Nat.lt_succ_self P)))












theorem lemma45Double
    {eps : Real} {B : Nat -> Real} {s : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (W : Nat -> Nat -> Real)
    (hW : forall i k : Nat, 0 <= W i k)
    (hOne : forall i k : Nat,
      W (i + 1) k <= W i (k + 1) + eps * oneStepConst B k (s + i) *
        Finset.sum (Finset.range (k + 1)) (fun j => W i j)) :
    forall p i r : Nat, 0 < r -> r <= p ->
      W (i + r) 0 <= W i r + eps * lemma45Const B p (s + i) *
        Finset.sum (Finset.range r) (fun j => W i j) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ihp =>
      intro i r hr0 hrp
      refine lemma45ScalarBdd (eps := eps) (B := B)
        (N := W i) (G := W (i + 1)) (D := fun a => W (i + a) 0)
        (s := s + i) (P := p) heps0 heps1 hB (hW i) ?_ ?_ r hr0 hrp
      · intro p' hp'
        rcases Nat.eq_zero_or_pos p' with rfl | hp'0
        · simp
        · have h := ihp p' hp' (i + 1) p' hp'0 (le_refl p')
          have hidx : i + (p' + 1) = (i + 1) + p' := by omega
          change W (i + (p' + 1)) 0 ≤ _
          rw [hidx]
          exact h
      · intro k _
        exact hOne i k






theorem lemma45DoubleBdd
    {eps : Real} {B : Nat -> Real} {s : Nat}
    (heps0 : 0 <= eps)
    (heps1 : eps <= 1)
    (hB : forall i : Nat, 0 <= B i)
    (P : Nat)
    (W : Nat -> Nat -> Real)
    (hW : forall i k : Nat, 0 <= W i k)
    (hOne : forall i k : Nat, i + k < P ->
      W (i + 1) k <= W i (k + 1) + eps * oneStepConst B k (s + i) *
        Finset.sum (Finset.range (k + 1)) (fun j => W i j)) :
    forall p i r : Nat, 0 < r -> r <= p -> i + p <= P ->
      W (i + r) 0 <= W i r + eps * lemma45Const B p (s + i) *
        Finset.sum (Finset.range r) (fun j => W i j) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ihp =>
      intro i r hr0 hrp hiP
      refine lemma45ScalarBdd (eps := eps) (B := B)
        (N := W i) (G := W (i + 1)) (D := fun a => W (i + a) 0)
        (s := s + i) (P := p) heps0 heps1 hB (hW i) ?_ ?_ r hr0 hrp
      · intro p' hp'
        rcases Nat.eq_zero_or_pos p' with rfl | hp'0
        · simp
        · have h := ihp p' hp' (i + 1) p' hp'0 (le_refl p') (by omega)
          have hidx : i + (p' + 1) = (i + 1) + p' := by omega
          change W (i + (p' + 1)) 0 ≤ _
          rw [hidx]
          exact h
      · intro k hk
        exact hOne i k (by omega)

end HCGCompactness
end DifferentialGeometry
