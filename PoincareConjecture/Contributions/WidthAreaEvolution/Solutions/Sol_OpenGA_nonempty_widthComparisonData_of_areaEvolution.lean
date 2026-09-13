import Theorems.Thm_OpenGA_integral_areaDensity_le_energyDensity
import Definitions.Def_OpenGA_WidthAreaEvolutionData
set_option autoImplicit false
open Set Filter
open scoped Topology
open OpenGA

namespace OpenGA
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
    have hgap : 0 ≤ ((⨆ q, (D.competitor j q).area) -
        (D.competitor j p).area) / δ := div_nonneg (sub_nonneg.mpr hsup) hδ.le
    have hstep : s - time ≤ δ := by linarith [hs.2]
    have hbudget := mul_le_mul_of_nonneg_left hstep hgap
    have hcancel := div_mul_cancel₀
      ((⨆ q, (D.competitor j q).area) - (D.competitor j p).area) hδ.ne'
    nlinarith


end OpenGA
theorem solution {width : ℝ → ℝ} {time scalar : ℝ}
    (D : WidthAreaEvolutionData width time scalar) :
    Nonempty (WidthComparisonData width time scalar) := ⟨D.toComparison⟩
