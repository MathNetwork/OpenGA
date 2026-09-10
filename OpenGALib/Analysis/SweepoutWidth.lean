import OpenGALib.Analysis.WidthComparison
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

variable {P : Type*} [TopologicalSpace P]

/-- A finite-energy realization of a sweepout profile. The field `pair` is
intended to be obtained from the differential of each surface slice; that
geometric construction is deliberately left as a separate result. -/
structure SweepoutEnergyProfile (P : Type*) [TopologicalSpace P] where
  energy : P → ℝ
  pair : P → FiniteEnergyPair
  pair_energy : ∀ p, (pair p).energy = energy p
  continuous_energy : Continuous energy
  energy_bdd : BddAbove (Set.range energy)

/-- The width of a real-valued energy profile, defined as its supremum. -/
noncomputable def sweepoutWidth (energy : P → ℝ) : ℝ := ⨆ p, energy p

omit [TopologicalSpace P] in
theorem energy_le_sweepoutWidth
    (energy : P → ℝ) (hbdd : BddAbove (Set.range energy)) (p : P) :
    energy p ≤ sweepoutWidth energy := by
  exact le_ciSup hbdd p

theorem finite_sample_width_le
    {ι : Type*} [Fintype ι] [Nonempty ι] [Nonempty P] (energy : P → ℝ)
    (hbdd : BddAbove (Set.range energy)) (sample : ι → P) :
    (⨆ i, energy (sample i)) ≤ sweepoutWidth energy := by
  apply ciSup_le
  intro i
  exact energy_le_sweepoutWidth energy hbdd (sample i)

theorem profile_width_eq
    {P : Type*} [TopologicalSpace P] [Nonempty P]
    (profile : SweepoutEnergyProfile P) :
    sweepoutWidth profile.energy = ⨆ p, (profile.pair p).energy := by
  unfold sweepoutWidth
  congr 1
  funext p
  exact (profile.pair_energy p).symm

end OpenGA
