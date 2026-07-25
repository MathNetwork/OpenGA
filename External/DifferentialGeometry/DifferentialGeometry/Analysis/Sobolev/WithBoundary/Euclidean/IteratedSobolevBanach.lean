import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevHalfSpace

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem MemWkpHalfSpace.exists_limit_of_wkpNormHalfSpace_cauchy
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    (k : ℕ) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : ℕ → E → ℝ}
    (hu_mem : ∀ n, MemWkpHalfSpace (d := d) k p (u n) Ω)
    (hu_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormHalfSpace (d := d) k p (fun x => u m x - u n x) Ω ≤
        ENNReal.ofReal ε) :
    ∃ u_lim : E → ℝ,
      MemWkpHalfSpace (d := d) k p u_lim Ω ∧
      Filter.Tendsto
        (fun n => wkpNormHalfSpace (d := d) k p (fun x => u n x - u_lim x) Ω)
        Filter.atTop (𝓝 0) := by
  have hΩ_open : IsOpen (interiorHalfSpace (d := d) Ω) :=
    interiorHalfSpace_isOpen hΩ
  have hu_mem' : ∀ n, MemWkp (d := d) k p (u n) (interiorHalfSpace Ω) := hu_mem
  have hu_cauchy' : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u m x - u n x)
        (interiorHalfSpace Ω) ≤ ENNReal.ofReal ε := hu_cauchy
  obtain ⟨u_lim, hu_lim_mem, h_tendsto⟩ :=
    MemWkp.exists_limit_of_wkpNorm_cauchy hΩ_open k p hp_one hp_top
      hu_mem' hu_cauchy'
  refine ⟨u_lim, hu_lim_mem, ?_⟩
  exact h_tendsto

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
