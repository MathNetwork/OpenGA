import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem order_zero_sum_eq_eLpNorm
    (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    ∑ α : Fin 0 → Fin d,
        eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω) =
      eLpNorm u p (volume.restrict Ω) := by
  classical
  have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
    funext i; exact i.elim0
  haveI : Unique (Fin 0 → Fin d) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun α => (hUniq α).symm ▸ rfl }
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω))]
  simp [iterWeakPartial_zero]

theorem wkpNorm_split_order_zero
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    iteratedWeakSobolevNorm (d := d) k p u Ω =
      eLpNorm u p (volume.restrict Ω) +
        ∑ j ∈ Finset.range k,
          ∑ α : Fin (j + 1) → Fin d,
            eLpNorm (iterWeakPartial (d := d) p (j + 1) α u Ω)
              p (volume.restrict Ω) := by
  classical
  unfold iteratedWeakSobolevNorm
  rw [Finset.sum_range_succ']
  rw [order_zero_sum_eq_eLpNorm (d := d) p u Ω]
  rw [add_comm]

theorem wkpNorm_k_decomposition
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    iteratedWeakSobolevNorm (d := d) k p u Ω =
      eLpNorm u p (volume.restrict Ω) +
        ∑ j ∈ Finset.Icc 1 k,
          ∑ α : Fin j → Fin d,
            eLpNorm (iterWeakPartial (d := d) p j α u Ω)
              p (volume.restrict Ω) := by
  classical
  rw [wkpNorm_split_order_zero (d := d) k p u Ω]
  congr 1
  rw [Finset.sum_bij (i := fun (j : ℕ) (_ : j ∈ Finset.range k) => j + 1)]
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Icc]
    omega
  · intro j₁ _ j₂ _ h
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨j - 1, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  · intro j _
    rfl

theorem wkpNorm_k_two_decomposition
    (k : ℕ) (u : E → ℝ) (Ω : Set E) :
    iteratedWeakSobolevNorm (d := d) k 2 u Ω =
      eLpNorm u 2 (volume.restrict Ω) +
        ∑ j ∈ Finset.Icc 1 k,
          ∑ α : Fin j → Fin d,
            eLpNorm (iterWeakPartial (d := d) 2 j α u Ω)
              2 (volume.restrict Ω) :=
  wkpNorm_k_decomposition (d := d) k 2 u Ω

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
