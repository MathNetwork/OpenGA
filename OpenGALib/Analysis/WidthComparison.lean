import OpenGALib.Analysis.AreaEnergy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Width variation from area-energy comparison data

This module isolates the analytic passage from comparison families to a
right-hand slope estimate. The input consists of finite-energy measurable
vector pairs, uniform energy caps tending to the width, an almost conformal
realizer, and a short-time area comparison. None of these data are a definition
of a surface differential, a sweepout, a harmonic map, or a Ricci flow.

The intended geometric inputs are described in Colding-Minicozzi,
*Width and Finite Extinction Time of Ricci Flow*, arXiv:0707.0108v1:
equation (1.4), the paragraph after Theorem 1.14, and the proof of Theorem 1.7,
equations (1.25)-(1.28) and footnote 6 (pp. 3, 6-8). The comparison hypothesis
below packages the uniform error estimates after shrinking the time interval;
constructing it from geometry is a separate open task.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology

namespace OpenGA

/-- **Math.** A measurable pair with finite Dirichlet energy. Its domain may
also be a disjoint union, as for a finite collection of sphere maps. -/
structure FiniteEnergyPair where
  domain : Type
  [measurableSpace : MeasurableSpace domain]
  target : Type
  [normedAddCommGroup : NormedAddCommGroup target]
  [innerProductSpace : InnerProductSpace ℝ target]
  measure : Measure domain
  first : domain → target
  second : domain → target
  first_measurable : AEStronglyMeasurable first measure
  second_measurable : AEStronglyMeasurable second measure
  energy_integrable : Integrable (fun x => energyDensity (first x) (second x)) measure

attribute [instance] FiniteEnergyPair.measurableSpace
  FiniteEnergyPair.normedAddCommGroup FiniteEnergyPair.innerProductSpace

/-- **Math.** Integrated area density of a finite-energy pair. -/
noncomputable def FiniteEnergyPair.area (p : FiniteEnergyPair) : ℝ :=
  ∫ x, areaDensity (p.first x) (p.second x) ∂p.measure

/-- **Math.** Integrated energy density of a finite-energy pair. -/
noncomputable def FiniteEnergyPair.energy (p : FiniteEnergyPair) : ℝ :=
  ∫ x, energyDensity (p.first x) (p.second x) ∂p.measure

/-- **Math.** Orthogonality and equal length almost everywhere; a condition
on the supplied fields, without asserting that they are a map differential. -/
def FiniteEnergyPair.IsConformal (p : FiniteEnergyPair) : Prop :=
  ∀ᵐ x ∂p.measure, ⟪p.first x, p.second x⟫_ℝ = 0 ∧ ‖p.first x‖ = ‖p.second x‖

/-- **Math.** Analytic comparison data at one time. Competitors are indexed by
a sequence and the unit interval. The realizer encodes the limiting harmonic
spheres only once the separate geometric construction has been supplied. -/
structure WidthComparisonData (width : ℝ → ℝ) (time scalar : ℝ) where
  realizer : FiniteEnergyPair
  realizer_conformal : realizer.IsConformal
  realized_energy : realizer.energy = width time
  competitor : ℕ → Icc (0 : ℝ) 1 → FiniteEnergyPair
  energy_cap : ℕ → ℝ
  energy_le_cap : ∀ j p, (competitor j p).energy ≤ energy_cap j
  cap_tendsto : Tendsto energy_cap atTop (𝓝 (width time))
  area_comparison : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ start : ℕ,
    ∀ j ≥ start, ∀ s ∈ Ioo time (time + δ),
      width s ≤ (⨆ p, (competitor j p).area) +
        (s - time) * (-(4 * Real.pi) - scalar / 2 * realizer.area + ε)

/-- **Math.** Finite-energy comparison families and a conformal realizer imply
the upper right slope estimate used in the extinction argument. -/
theorem eventually_width_slope_lt_of_comparison
    {width : ℝ → ℝ} {time scalar : ℝ}
    (data : WidthComparisonData width time scalar) (q : ℝ)
    (hq : -(4 * Real.pi) - scalar / 2 * width time < q) :
    ∀ᶠ s in 𝓝[>] time, slope width time s < q := by
  have hreal : data.realizer.area = width time := by
    have h := (integral_areaDensity_eq_energyDensity_iff
      data.realizer.first_measurable data.realizer.second_measurable
      data.realizer.energy_integrable).2 data.realizer_conformal
    exact h.trans data.realized_energy
  have hcap : ∀ j, (⨆ p, (data.competitor j p).area) ≤ data.energy_cap j := by
    intro j
    apply ciSup_le
    intro p
    exact (integral_areaDensity_le_energyDensity
      (data.competitor j p).first_measurable (data.competitor j p).second_measurable
      (data.competitor j p).energy_integrable).trans (data.energy_le_cap j p)
  let bound := -(4 * Real.pi) - scalar / 2 * width time
  let ε := (q - bound) / 4
  have hε : 0 < ε := by dsimp [ε, bound]; linarith
  obtain ⟨δ, hδ, start, hcomparison⟩ := data.area_comparison ε hε
  filter_upwards [Ioo_mem_nhdsGT (show time < time + δ by linarith)] with s hs
  have hstep : 0 < s - time := sub_pos.mpr hs.1
  have hevent : ∀ᶠ j in atTop, data.energy_cap j < width time + ε * (s - time) :=
    (tendsto_order.1 data.cap_tendsto).2 _ (by nlinarith)
  obtain ⟨j, hjcap, hjstart⟩ := (hevent.and (eventually_ge_atTop start)).exists
  have hcompare := hcomparison j hjstart s hs
  rw [hreal] at hcompare
  have hsup := hcap j
  have hquot : width s - width time < (s - time) * q := by
    have hgap : 0 < (s - time) * (q - bound - 2 * ε) :=
      mul_pos hstep (by dsimp [ε, bound]; linarith)
    dsimp [bound] at hgap
    nlinarith
  rw [slope_def_field]
  exact (div_lt_iff₀ hstep).2 (by nlinarith [hquot])

end OpenGA
