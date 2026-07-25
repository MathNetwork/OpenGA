import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Algebra.Module.Equiv

set_option autoImplicit false








noncomputable section

open scoped BigOperators

namespace ContinuousLinearMap

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem invertible_of_id_sub [CompleteSpace E] {T : E →L[ℝ] E}
    (h : ‖ContinuousLinearMap.id ℝ E - T‖ < 1) : T.IsInvertible := by
  have hu : IsUnit T := by
    have h1 : IsUnit (1 - (1 - T)) := by
      have hlt : ‖(1 : E →L[ℝ] E) - T‖ < 1 := by simpa using h
      exact (Units.oneSub _ hlt).isUnit
    simpa using h1
  obtain ⟨u, hu⟩ := hu
  refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
  rw [← hu]
  ext v
  rfl



theorem sum_near_neg [Fintype ι]
    (μ : ι → ℝ) (A : ι → E →L[ℝ] E) (η : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1)
    (hA : ∀ i, ‖A i + ContinuousLinearMap.id ℝ E‖ ≤ η) :
    ‖(∑ i, μ i • A i) + ContinuousLinearMap.id ℝ E‖ ≤ η := by
  classical
  have hdecomp :
      (∑ i, μ i • A i) + ContinuousLinearMap.id ℝ E =
        ∑ i, μ i • (A i + ContinuousLinearMap.id ℝ E) := by
    symm
    simp only [smul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_smul, hsum, one_smul]
  rw [hdecomp]
  calc
    ‖∑ i, μ i • (A i + ContinuousLinearMap.id ℝ E)‖
        ≤ ∑ i, ‖μ i • (A i + ContinuousLinearMap.id ℝ E)‖ := norm_sum_le _ _
    _ = ∑ i, μ i * ‖A i + ContinuousLinearMap.id ℝ E‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
    _ ≤ ∑ i, μ i * η := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hA i) (hμ i)
    _ = η := by
      rw [← Finset.sum_mul, hsum, one_mul]



theorem sum_near_neg_inv [Fintype ι] [CompleteSpace E]
    (μ : ι → ℝ) (A : ι → E →L[ℝ] E) (η : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1)
    (hA : ∀ i, ‖A i + ContinuousLinearMap.id ℝ E‖ ≤ η) (hη : η < 1) :
    (∑ i, μ i • A i).IsInvertible := by
  let S : E →L[ℝ] E := ∑ i, μ i • A i
  have hS : ‖S + ContinuousLinearMap.id ℝ E‖ < 1 :=
    (sum_near_neg μ A η hμ hsum hA).trans_lt hη
  have hneg : (-S).IsInvertible := by
    apply invertible_of_id_sub
    simpa only [sub_neg_eq_add, add_comm] using hS
  rcases hneg with ⟨e, he⟩
  refine ⟨e.trans (ContinuousLinearEquiv.neg ℝ), ?_⟩
  ext x
  have he_apply : e x = -S x := by
    simpa only [neg_apply] using congrArg (fun f : E →L[ℝ] E => f x) he
  change -e x = (∑ i, μ i • A i) x
  rw [he_apply, neg_neg]

end ContinuousLinearMap
