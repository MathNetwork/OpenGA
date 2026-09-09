import Definitions.Def_OpenGA_AreaEnergyDensities
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



end OpenGA
