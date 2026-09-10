import Definitions.Def_OpenGA_SurgeryAreaEvolutionData
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Area and energy densities

For the images `v`, `w` of an orthonormal tangent frame under a differential,
the area density is the square root of the Gram determinant and the energy
density is half the sum of the squared norms. The area is bounded by the
energy, with equality precisely for orthogonal vectors of equal norm.

The integral results assume measurable vector fields and integrable energy;
integrability of the area is a conclusion, not an additional assumption.
They apply on any measure space, including a restricted domain measure.
Identifying these fields with a Sobolev differential on a surface remains a
separate geometric interface. No global frame on the sphere is asserted.

Reference: Colding-Minicozzi, *Width and Finite Extinction Time of Ricci Flow*,
arXiv:0707.0108v1, equation (1.4) and the following equality discussion, p. 3.
https://arxiv.org/pdf/0707.0108v1#page=3
-/

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

namespace OpenGA

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma areaDensity_nonneg (v w : F) : 0 ≤ areaDensity v w :=
  Real.sqrt_nonneg _

omit [InnerProductSpace ℝ F] in
lemma energyDensity_nonneg (v w : F) : 0 ≤ energyDensity v w := by
  unfold energyDensity
  positivity

lemma areaDensity_sq (v w : F) :
    areaDensity v w ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 := by
  apply Real.sq_sqrt
  have h := real_inner_mul_inner_self_le v w
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith

/-- **Math.** The squared density gap separates the two conformality defects. -/
theorem energyDensity_sq_sub_areaDensity_sq (v w : F) :
    energyDensity v w ^ 2 - areaDensity v w ^ 2 =
      (‖v‖ ^ 2 - ‖w‖ ^ 2) ^ 2 / 4 + ⟪v, w⟫_ℝ ^ 2 := by
  rw [areaDensity_sq, energyDensity]
  ring

/-- **Math.** The two-dimensional area density is bounded by the energy density. -/
theorem areaDensity_le_energyDensity (v w : F) :
    areaDensity v w ≤ energyDensity v w := by
  have h := energyDensity_sq_sub_areaDensity_sq v w
  have he := energyDensity_nonneg v w
  nlinarith [sq_nonneg (‖v‖ ^ 2 - ‖w‖ ^ 2), sq_nonneg ⟪v, w⟫_ℝ]

/-- **Math.** Equality holds exactly for an orthogonal equal-length pair,
including the degenerate pair of zero vectors. -/
theorem areaDensity_eq_energyDensity_iff (v w : F) :
    areaDensity v w = energyDensity v w ↔ ⟪v, w⟫_ℝ = 0 ∧ ‖v‖ = ‖w‖ := by
  have h := energyDensity_sq_sub_areaDensity_sq v w
  constructor
  · intro heq
    rw [heq] at h
    have hi : ⟪v, w⟫_ℝ = 0 := by
      nlinarith [sq_nonneg (‖v‖ ^ 2 - ‖w‖ ^ 2), sq_nonneg ⟪v, w⟫_ℝ]
    have hn : ‖v‖ ^ 2 = ‖w‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v‖ ^ 2 - ‖w‖ ^ 2), sq_nonneg ⟪v, w⟫_ℝ]
    exact ⟨hi, by nlinarith [norm_nonneg v, norm_nonneg w]⟩
  · rintro ⟨hi, hn⟩
    rw [hi, hn] at h
    nlinarith [areaDensity_nonneg v w, energyDensity_nonneg v w]

lemma continuous_areaDensity : Continuous (fun p : F × F => areaDensity p.1 p.2) := by
  unfold areaDensity
  fun_prop

section Integral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v w : X → F}

/-- **Math.** Finite energy implies integrable area density. -/
theorem integrable_areaDensity (hv : AEStronglyMeasurable v μ)
    (hw : AEStronglyMeasurable w μ)
    (hE : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    Integrable (fun x => areaDensity (v x) (w x)) μ := by
  apply hE.mono_nonneg (continuous_areaDensity.comp_aestronglyMeasurable (hv.prodMk hw))
  · exact Filter.Eventually.of_forall fun x => areaDensity_nonneg (v x) (w x)
  · exact Filter.Eventually.of_forall fun x => areaDensity_le_energyDensity (v x) (w x)

/-- **Math.** Integrated area-energy inequality, with finite energy explicit. -/
theorem integral_areaDensity_le_energyDensity (hv : AEStronglyMeasurable v μ)
    (hw : AEStronglyMeasurable w μ)
    (hE : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    (∫ x, areaDensity (v x) (w x) ∂μ) ≤ ∫ x, energyDensity (v x) (w x) ∂μ :=
  integral_mono (integrable_areaDensity hv hw hE) hE
    (fun x => areaDensity_le_energyDensity (v x) (w x))

/-- **Math.** Equality of the integrals is equivalent to weak conformality
almost everywhere in the supplied orthonormal-frame representation. -/
theorem integral_areaDensity_eq_energyDensity_iff (hv : AEStronglyMeasurable v μ)
    (hw : AEStronglyMeasurable w μ)
    (hE : Integrable (fun x => energyDensity (v x) (w x)) μ) :
    (∫ x, areaDensity (v x) (w x) ∂μ) = (∫ x, energyDensity (v x) (w x) ∂μ) ↔
      ∀ᵐ x ∂μ, ⟪v x, w x⟫_ℝ = 0 ∧ ‖v x‖ = ‖w x‖ := by
  rw [integral_eq_iff_of_ae_le (integrable_areaDensity hv hw hE) hE
    (Filter.Eventually.of_forall fun x => areaDensity_le_energyDensity (v x) (w x))]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun x =>
    areaDensity_eq_energyDensity_iff (v x) (w x))

end Integral

end OpenGA

set_option autoImplicit false
open Set Filter
open scoped Topology

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

theorem nonempty_widthComparisonData_of_areaEvolution
    {width : ℝ → ℝ} {time scalar : ℝ}
    (D : WidthAreaEvolutionData width time scalar) :
    Nonempty (WidthComparisonData width time scalar) := ⟨D.toComparison⟩


noncomputable def SurgeryAreaEvolutionData.toMeasured {W T : ℝ}
    (D : SurgeryAreaEvolutionData W T) : MeasuredSurgeryComparisonData W T where
  volumeControl := D.volumeControl
  events_inside := D.events_inside
  finalTime_pos := D.finalTime_pos
  scalar := D.scalar
  width := D.width
  scalar_cont := D.scalar_cont
  width_cont := D.width_cont
  scalar_initial := D.scalar_initial
  width_initial := D.width_initial
  width_nonneg := D.width_nonneg
  scalar_slope := D.scalar_slope
  scalar_jump := D.scalar_jump
  width_jump := D.width_jump
  comparison := by
    intro a b hab t ht
    obtain ⟨A⟩ := D.area_evolution a b hab t ht
    exact nonempty_widthComparisonData_of_areaEvolution A

theorem nonempty_measuredSurgeryComparisonData_of_areaEvolution {W T : ℝ}
    (D : SurgeryAreaEvolutionData W T) : Nonempty (MeasuredSurgeryComparisonData W T) :=
  ⟨D.toMeasured⟩


end OpenGA
open Lean in
run_meta do
  for n in [``OpenGA.nonempty_widthComparisonData_of_areaEvolution,
      ``OpenGA.nonempty_measuredSurgeryComparisonData_of_areaEvolution] do
    let axioms ← collectAxioms n
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
    logInfo m!"{n}: standard axioms only"
