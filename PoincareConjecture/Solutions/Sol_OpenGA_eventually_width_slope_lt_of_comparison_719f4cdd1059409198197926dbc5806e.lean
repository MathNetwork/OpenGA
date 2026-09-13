import Definitions.Def_OpenGA_WidthComparisonData
import Theorems.Thm_OpenGA_integral_areaDensity_le_energyDensity
import Theorems.Thm_OpenGA_integral_areaDensity_eq_energyDensity_iff

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open OpenGA

/-- **Math.** Finite-energy comparison families and a conformal realizer imply
the upper right slope estimate used in the extinction argument. -/
theorem solution
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
