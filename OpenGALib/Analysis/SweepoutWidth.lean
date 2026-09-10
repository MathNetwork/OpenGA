import OpenGALib.Analysis.AreaEnergy
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Width of a sweepout energy profile

The width of a parameterized family is defined using a supremum over all
parameter values. Attainment of that supremum is a separate compactness and
continuity result.
-/

noncomputable section

open Set

namespace OpenGA

variable {P : Type*} [Nonempty P]

/-- The width of a real-valued energy profile, defined as its supremum. -/
noncomputable def sweepoutWidth (energy : P → ℝ) : ℝ := ⨆ p, energy p

theorem energy_le_sweepoutWidth
    (energy : P → ℝ) (hbdd : BddAbove (Set.range energy)) (p : P) :
    energy p ≤ sweepoutWidth energy := by
  exact le_ciSup hbdd p

theorem finite_sample_width_le
    {ι : Type*} [Fintype ι] [Nonempty ι] (energy : P → ℝ)
    (hbdd : BddAbove (Set.range energy)) (sample : ι → P) :
    (⨆ i, energy (sample i)) ≤ sweepoutWidth energy := by
  apply ciSup_le
  intro i
  exact energy_le_sweepoutWidth energy hbdd (sample i)

end OpenGA
