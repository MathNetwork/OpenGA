import OpenGALib.Analysis.WidthComparison
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Width comparison from uniform area evolution

The area profiles below need not yet be geometric sweepouts. To apply this
result to Ricci flow one must construct admissible comparison families and
prove a common short-time derivative bound for all their slices. Pointwise
area variation for a single surface does not supply this uniformity.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace OpenGA

/-- Analytic input before integrating the short-time area estimate. The same
time interval and sequence cutoff work for every slice. -/
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
        deriv (area j p) s ≤ -(4 * Real.pi) - scalar / 2 * realizer.area + ε)

/-- Integrating the common derivative bound constructs the area-comparison
field; bounded initial energies justify the real supremum over slices. -/
noncomputable def WidthAreaEvolutionData.toComparison
    {width : ℝ → ℝ} {time scalar : ℝ}
    (D : WidthAreaEvolutionData width time scalar) : WidthComparisonData width time scalar where
  realizer := D.realizer
  realizer_conformal := D.realizer_conformal
  realized_energy := D.realized_energy
  competitor := D.competitor
  energy_cap := D.energy_cap
  energy_le_cap := D.energy_le_cap
  cap_tendsto := D.cap_tendsto
  area_comparison := by
    intro ε hε
    obtain ⟨δ, hδ, start, h⟩ := D.uniform_evolution ε hε
    refine ⟨δ, hδ, start, ?_⟩
    intro j hj s hs
    obtain ⟨hwidth, hcont, hdiff, hderiv⟩ := h j hj
    have hbdd : BddAbove (range (fun p => (D.competitor j p).area)) := by
      refine ⟨D.energy_cap j, ?_⟩
      rintro _ ⟨p, rfl⟩
      exact (integral_areaDensity_le_energyDensity
        (D.competitor j p).first_measurable (D.competitor j p).second_measurable
        (D.competitor j p).energy_integrable).trans (D.energy_le_cap j p)
    apply (hwidth s hs).trans
    apply ciSup_le
    intro p
    have hevol := (convex_Icc time (time + δ)).image_sub_le_mul_sub_of_deriv_le
      (hcont p)
      (fun x hx => (hdiff p x (by simpa only [interior_Icc] using hx)).differentiableWithinAt)
      (fun x hx => hderiv p x (by simpa only [interior_Icc] using hx))
      time ⟨le_rfl, by linarith⟩ s ⟨hs.1.le, hs.2.le⟩ hs.1.le
    rw [D.area_initial] at hevol
    have hsup := le_ciSup hbdd p
    nlinarith

theorem nonempty_widthComparisonData_of_areaEvolution
    {width : ℝ → ℝ} {time scalar : ℝ}
    (D : WidthAreaEvolutionData width time scalar) :
    Nonempty (WidthComparisonData width time scalar) := ⟨D.toComparison⟩

end OpenGA
