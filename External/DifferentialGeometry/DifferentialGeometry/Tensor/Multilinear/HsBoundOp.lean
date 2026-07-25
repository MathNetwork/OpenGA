import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

open Finset
open scoped BigOperators RealInnerProductSpace

namespace ContinuousMultilinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem opNorm_sq_le_sum_sq_basisEval
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) :
    ‖A‖ ^ 2 ≤ ∑ idx : Fin j → ι, |A (fun k => b (idx k))| ^ 2 := by
  classical

  set S : ℝ := ∑ idx : Fin j → ι, |A (fun k => b (idx k))| ^ 2 with hS_def
  have hS_nonneg : 0 ≤ S := by
    refine Finset.sum_nonneg ?_
    intro idx _
    exact sq_nonneg _

  have hpoint : ∀ v : Fin j → E, ‖A v‖ ≤ Real.sqrt S * ∏ k, ‖v k‖ := by
    intro v

    have hv : ∀ k : Fin j, v k = ∑ i : ι, ⟪b i, v k⟫ • b i := by
      intro k
      exact (b.sum_repr' (v k)).symm

    have hAv : A v = ∑ idx : Fin j → ι,
        (∏ k : Fin j, ⟪b (idx k), v k⟫) • A (fun k => b (idx k)) := by
      have hexp : A v = A (fun k => ∑ i : ι, ⟪b i, v k⟫ • b i) := by
        refine congrArg A ?_
        funext k
        exact hv k

      have hstep1 : A (fun k => ∑ i : ι, ⟪b i, v k⟫ • b i)
          = ∑ idx : Fin j → ι, A (fun k => ⟪b (idx k), v k⟫ • b (idx k)) := by
        have := A.toMultilinearMap.map_sum
          (g := fun (k : Fin j) (i : ι) => ⟪b i, v k⟫ • b i)

        simpa using this
      have hstep2 : ∀ idx : Fin j → ι,
          A (fun k => ⟪b (idx k), v k⟫ • b (idx k))
            = (∏ k : Fin j, ⟪b (idx k), v k⟫) • A (fun k => b (idx k)) := by
        intro idx
        exact A.map_smul_univ
          (fun k : Fin j => ⟪b (idx k), v k⟫) (fun k : Fin j => b (idx k))
      rw [hexp, hstep1]
      exact Finset.sum_congr rfl fun idx _ => hstep2 idx

    have hAv_abs : ‖A v‖ = |A v| := Real.norm_eq_abs _

    have habs : |A v|
        = |∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))| := by
      have : A v = ∑ idx : Fin j → ι,
          (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k)) := by
        rw [hAv]
        refine Finset.sum_congr rfl ?_
        intro idx _
        rw [smul_eq_mul]
      rw [this]

    have hCS : (∑ idx : Fin j → ι,
        (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))) ^ 2
        ≤ (∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2) *
          (∑ idx : Fin j → ι, A (fun k => b (idx k)) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin j → ι))
        (fun idx => ∏ k : Fin j, ⟪b (idx k), v k⟫)
        (fun idx => A (fun k => b (idx k)))
    have hS_eq : S = ∑ idx : Fin j → ι, A (fun k => b (idx k)) ^ 2 := by
      rw [hS_def]
      refine Finset.sum_congr rfl ?_
      intro idx _
      rw [sq_abs]
    have hCS' : (∑ idx : Fin j → ι,
        (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))) ^ 2
        ≤ (∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2) * S := by
      rw [hS_eq]; exact hCS

    have hsumC_nonneg :
        0 ≤ ∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsqrt_le :
        Real.sqrt ((∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))) ^ 2)
          ≤ Real.sqrt
            ((∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2) * S) :=
      Real.sqrt_le_sqrt hCS'
    have heq1 :
        Real.sqrt ((∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))) ^ 2)
        = |∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))| := by
      rw [Real.sqrt_sq_eq_abs]
    have heq2 :
        Real.sqrt
          ((∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2) * S)
        = Real.sqrt
            (∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2)
          * Real.sqrt S :=
      Real.sqrt_mul hsumC_nonneg _
    rw [heq1, heq2] at hsqrt_le

    have hParseval :
        ∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2
          = ∏ k : Fin j, ‖v k‖ ^ 2 := by

      have hsq :
          ∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2
          = ∑ idx : Fin j → ι, ∏ k : Fin j, ⟪b (idx k), v k⟫ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro idx _
        rw [← Finset.prod_pow]

      have hprod_sum :
          ∑ idx : Fin j → ι, ∏ k : Fin j, ⟪b (idx k), v k⟫ ^ 2
          = ∏ k : Fin j, ∑ i : ι, ⟪b i, v k⟫ ^ 2 := by
        have h := (Finset.prod_univ_sum
          (κ := fun _ : Fin j => ι)
          (t := fun _ : Fin j => (Finset.univ : Finset ι))
          (f := fun k i => ⟪b i, v k⟫ ^ 2))

        have hpi : (Fintype.piFinset (fun _ : Fin j => (Finset.univ : Finset ι)))
                    = (Finset.univ : Finset (Fin j → ι)) := by
          ext idx; simp
        rw [h, hpi]

      have hslot : ∀ k : Fin j, ∑ i : ι, ⟪b i, v k⟫ ^ 2 = ‖v k‖ ^ 2 := by
        intro k
        exact b.sum_sq_inner_right (v k)
      rw [hsq, hprod_sum]
      refine Finset.prod_congr rfl ?_
      intro k _
      exact hslot k

    have hsqrt_prod :
        Real.sqrt (∏ k : Fin j, ‖v k‖ ^ 2) = ∏ k : Fin j, ‖v k‖ := by
      have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin j)), 0 ≤ ‖v k‖ ^ 2 :=
        fun k _ => sq_nonneg _
      rw [Real.sqrt_prod (Finset.univ : Finset (Fin j)) hnonneg]
      refine Finset.prod_congr rfl ?_
      intro k _
      rw [Real.sqrt_sq (norm_nonneg _)]

    calc ‖A v‖
        = |A v| := hAv_abs
      _ = |∑ idx : Fin j → ι,
            (∏ k : Fin j, ⟪b (idx k), v k⟫) * A (fun k => b (idx k))| := habs
      _ ≤ Real.sqrt
            (∑ idx : Fin j → ι, (∏ k : Fin j, ⟪b (idx k), v k⟫) ^ 2)
          * Real.sqrt S := hsqrt_le
      _ = Real.sqrt (∏ k : Fin j, ‖v k‖ ^ 2) * Real.sqrt S := by rw [hParseval]
      _ = (∏ k : Fin j, ‖v k‖) * Real.sqrt S := by rw [hsqrt_prod]
      _ = Real.sqrt S * ∏ k : Fin j, ‖v k‖ := by ring

  have hopNorm_le : ‖A‖ ≤ Real.sqrt S := by
    refine ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _) ?_
    intro v
    exact hpoint v

  have hopNorm_nonneg : 0 ≤ ‖A‖ := norm_nonneg _
  have hsq : ‖A‖ ^ 2 ≤ (Real.sqrt S) ^ 2 :=
    pow_le_pow_left₀ hopNorm_nonneg hopNorm_le 2
  have hsqrt_sq : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS_nonneg
  rw [hsqrt_sq] at hsq
  exact hsq

end ContinuousMultilinearMap

end
