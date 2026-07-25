import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped BigOperators






noncomputable def oneStepConst (B : Nat -> Real) (k m : Nat) : Real :=
  (m : Real) *
    Finset.sum (Finset.range (k + 1))
      (fun a => (k.choose a : Real) * B a)





noncomputable def lemma45Const (B : Nat -> Real) : Nat -> Nat -> Real
  | 0, _m => 1
  | p + 1, m =>
      lemma45Const B p m
        + 1
        + oneStepConst B p m
        + lemma45Const B p (m + 1) *
          (1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m))

theorem oneStepConst_nonneg
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (k m : Nat) :
    0 <= oneStepConst B k m := by
  unfold oneStepConst
  refine mul_nonneg (by exact_mod_cast Nat.zero_le m) ?_
  refine Finset.sum_nonneg ?_
  intro a _ha
  exact mul_nonneg (by exact_mod_cast Nat.zero_le (k.choose a)) (hB a)

theorem lemma45Const_pos
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (p m : Nat) :
    0 < lemma45Const B p m := by
  induction p generalizing m with
  | zero =>
      simp [lemma45Const]
  | succ p ih =>
      have hprev_nonneg : 0 <= lemma45Const B p m := le_of_lt (ih m)
      have hstep_nonneg : 0 <= oneStepConst B p m :=
        oneStepConst_nonneg hB p m
      have hprev_succ_nonneg : 0 <= lemma45Const B p (m + 1) :=
        le_of_lt (ih (m + 1))
      have hsum_nonneg :
          0 <= Finset.sum (Finset.range p) (fun k => oneStepConst B k m) := by
        exact Finset.sum_nonneg fun k _hk => oneStepConst_nonneg hB k m
      have hfactor_nonneg :
          0 <= 1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m) := by
        linarith
      have hprod_nonneg :
          0 <= lemma45Const B p (m + 1) *
            (1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m)) :=
        mul_nonneg hprev_succ_nonneg hfactor_nonneg
      simp [lemma45Const]
      linarith

theorem lemma45Const_nonneg
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (p m : Nat) :
    0 <= lemma45Const B p m :=
  le_of_lt (lemma45Const_pos hB p m)

theorem lemma45Const_le_succ
    {B : Nat -> Real} (hB : forall i : Nat, 0 <= B i)
    (p m : Nat) :
    lemma45Const B p m <= lemma45Const B (p + 1) m := by
  have hstep_nonneg : 0 <= oneStepConst B p m :=
    oneStepConst_nonneg hB p m
  have hprev_succ_nonneg : 0 <= lemma45Const B p (m + 1) :=
    lemma45Const_nonneg hB p (m + 1)
  have hsum_nonneg :
      0 <= Finset.sum (Finset.range p) (fun k => oneStepConst B k m) := by
    exact Finset.sum_nonneg fun k _hk => oneStepConst_nonneg hB k m
  have hfactor_nonneg :
      0 <= 1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m) := by
    linarith
  have hprod_nonneg :
      0 <= lemma45Const B p (m + 1) *
        (1 + Finset.sum (Finset.range p) (fun k => oneStepConst B k m)) :=
    mul_nonneg hprev_succ_nonneg hfactor_nonneg
  simp [lemma45Const]
  linarith








noncomputable def compApproxConst (C : Nat -> Real) (p : Nat) : Real :=
  (2 : Real) ^ (p + 3) * (1 + (p : Real) * C p)

theorem compApproxConst_pos
    {C : Nat -> Real} (hC : forall i : Nat, 0 <= C i)
    (p : Nat) :
    0 < compApproxConst C p := by
  have hpow : 0 < (2 : Real) ^ (p + 3) := pow_pos (by norm_num) _
  have hp : 0 <= (p : Real) := by exact_mod_cast Nat.zero_le p
  have hfactor : 0 < 1 + (p : Real) * C p := by
    nlinarith [mul_nonneg hp (hC p)]
  exact mul_pos hpow hfactor

theorem compApproxConst_nonneg
    {C : Nat -> Real} (hC : forall i : Nat, 0 <= C i)
    (p : Nat) :
    0 <= compApproxConst C p :=
  le_of_lt (compApproxConst_pos hC p)

end HCGCompactness
end DifferentialGeometry
