import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem chartTarget_iteratedFDeriv_two_eLpNorm_le_wkpNorm_two
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {u : EuclN → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_compact : HasCompactSupport u) (hu_supp : tsupport u ⊆ Ω) :
    eLpNorm (fun y : EuclN => ‖iteratedFDeriv ℝ 2 u y‖) 2
        (volume.restrict Ω) ≤
      iteratedWeakSobolevNorm (d := d) 2 2 u Ω := by
  classical
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
  have hu_smooth' : ContDiff ℝ (⊤ : ℕ∞) u := hu_smooth
  have h_sum_le :=
    eLpNorm_iteratedFDeriv_le_wkpNorm (d := d) hΩ_open
      (p := (2 : ℝ≥0∞)) hp_one (k := 2)
      hu_smooth' hu_compact hu_supp
  have h2_mem : (2 : ℕ) ∈ Finset.range (2 + 1) := by
    rw [Finset.mem_range]; omega
  have h_single :
      eLpNorm (fun y : EuclN => ‖iteratedFDeriv ℝ 2 u y‖) 2
          (volume.restrict Ω) ≤
        ∑ n ∈ Finset.range (2 + 1),
          eLpNorm (fun y : EuclN => ‖iteratedFDeriv ℝ n u y‖) 2
            (volume.restrict Ω) :=
    Finset.single_le_sum
      (f := fun n : ℕ =>
        eLpNorm (fun y : EuclN => ‖iteratedFDeriv ℝ n u y‖) 2
          (volume.restrict Ω))
      (fun _ _ => zero_le _) h2_mem
  exact h_single.trans h_sum_le

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
