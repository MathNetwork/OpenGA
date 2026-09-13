import Definitions.Def_OpenGA_WidthComparisonData
import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace OpenGA

/-- Analytic input before integrating the short-time area estimate. The same
time interval and sequence cutoff work for every slice. The derivative bound
allows slices below the initial supremum to use their initial area gap;
it does not demand negative area derivative from constant endpoint slices. -/
structure WidthAreaEvolutionData (width : ℝ → ℝ) (time scalar : ℝ) where
  realizer : FiniteEnergyPair
  realizer_conformal : realizer.IsConformal
  realized_energy : realizer.energy = width time
  competitor : ℕ → Icc (0 : ℝ) 1 → FiniteEnergyPair
  energy_cap : ℕ → ℝ
  energy_le_cap : ∀ j p, (competitor j p).energy ≤ energy_cap j
  cap_tendsto : Tendsto energy_cap atTop (𝓝 (width time))
  area : ℕ → Icc (0 : ℝ) 1 → ℝ → ℝ
  area_initial : ∀ j p, area j p time = (competitor j p).area
  uniform_evolution : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ start : ℕ,
    ∀ j ≥ start,
      (∀ s ∈ Ioo time (time + δ), width s ≤ ⨆ p, area j p s) ∧
      (∀ p, ContinuousOn (area j p) (Icc time (time + δ))) ∧
      (∀ p s, s ∈ Ioo time (time + δ) → DifferentiableAt ℝ (area j p) s) ∧
      (∀ p s, s ∈ Ioo time (time + δ) →
        deriv (area j p) s ≤ -(4 * Real.pi) - scalar / 2 * realizer.area + ε +
          ((⨆ q, (competitor j q).area) - (competitor j p).area) / δ)


end OpenGA
