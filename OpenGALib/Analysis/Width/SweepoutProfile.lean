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
  pair_conformal : ∀ p, (pair p).IsConformal
  continuous_energy : Continuous energy
  energy_bdd : BddAbove (Set.range energy)

/-- The width of a real-valued energy profile, defined as its supremum. -/
noncomputable def sweepoutWidth (energy : P → ℝ) : ℝ := ⨆ p, energy p

omit [TopologicalSpace P] in
theorem energy_le_sweepoutWidth
    (energy : P → ℝ) (hbdd : BddAbove (Set.range energy)) (p : P) :
    energy p ≤ sweepoutWidth energy := by
  exact le_ciSup hbdd p

omit [TopologicalSpace P] in
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

theorem profile_pair_area_eq_energy
    {P : Type*} [TopologicalSpace P] [Nonempty P]
    (profile : SweepoutEnergyProfile P) (p : P) :
    (profile.pair p).area = profile.energy p := by
  have h := (integral_areaDensity_eq_energyDensity_iff
    (profile.pair p).first_measurable (profile.pair p).second_measurable
    (profile.pair p).energy_integrable).2 (profile.pair_conformal p)
  exact h.trans (profile.pair_energy p)

theorem profile_pair_area_le_width
    {P : Type*} [TopologicalSpace P] [Nonempty P]
    (profile : SweepoutEnergyProfile P) (p : P) :
    (profile.pair p).area ≤ sweepoutWidth profile.energy := by
  calc
    (profile.pair p).area ≤ (profile.pair p).energy :=
      integral_areaDensity_le_energyDensity
        (profile.pair p).first_measurable (profile.pair p).second_measurable
        (profile.pair p).energy_integrable
    _ = profile.energy p := profile.pair_energy p
    _ ≤ sweepoutWidth profile.energy :=
      energy_le_sweepoutWidth profile.energy profile.energy_bdd p

theorem exists_profile_maximizer
    {P : Type*} [TopologicalSpace P] [CompactSpace P] [Nonempty P]
    (profile : SweepoutEnergyProfile P) :
    ∃ p : P, profile.energy p = sweepoutWidth profile.energy := by
  obtain ⟨p, hp, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    profile.continuous_energy.continuousOn
  refine ⟨p, ?_⟩
  apply le_antisymm
  · exact energy_le_sweepoutWidth profile.energy profile.energy_bdd p
  · apply ciSup_le
    intro q
    exact (isMaxOn_iff.mp hmax) q (show q ∈ (Set.univ : Set P) from Set.mem_univ q)

end OpenGA
