import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false








namespace DifferentialGeometry.Analysis.Integration

noncomputable section

open MeasureTheory Real Set

variable {α : Type*} [MeasurableSpace α]



theorem withDensity_prob
    (μ : Measure α) {ρ : α -> Real}
    (hρi : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    (hmass : (∫ x, ρ x ∂μ) = 1) :
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hρi hρ0, hmass]
  norm_num



theorem int_log_le_moment
    {ν : Measure α} [IsProbabilityMeasure ν]
    {X : α -> Real} {p : Real} (hp : 0 < p)
    (hX : ∀ᵐ x ∂ν, 0 < X x)
    (hlog : Integrable (fun x => Real.log (X x)) ν)
    (hmom : Integrable (fun x => X x ^ p) ν) :
    (∫ x, Real.log (X x) ∂ν) ≤
      Real.log (∫ x, X x ^ p ∂ν) / p := by
  let F : α -> Real := fun x => p * Real.log (X x)
  have hF : Integrable F ν := by
    simpa only [F] using hlog.const_mul p
  have hexp_eq :
      (Real.exp ∘ F) =ᵐ[ν] (fun x => X x ^ p) := by
    filter_upwards [hX] with x hx
    simp only [Function.comp_apply, F]
    rw [Real.rpow_def_of_pos hx p, mul_comm]
  have hexp : Integrable (Real.exp ∘ F) ν :=
    hmom.congr hexp_eq.symm
  have hJ :
      Real.exp (∫ x, F x ∂ν) ≤ ∫ x, Real.exp (F x) ∂ν := by
    simpa only [Function.comp_apply] using
      (convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
        (by simp) hF hexp)
  have hJ' :
      Real.exp (p * ∫ x, Real.log (X x) ∂ν) ≤
        ∫ x, X x ^ p ∂ν := by
    simpa only [F, integral_const_mul] using
      hJ.trans_eq (integral_congr_ae hexp_eq)
  have hmoment_pos : 0 < ∫ x, X x ^ p ∂ν :=
    lt_of_lt_of_le (Real.exp_pos _) hJ'
  have hlog_bound :
      p * (∫ x, Real.log (X x) ∂ν) ≤
        Real.log (∫ x, X x ^ p ∂ν) := by
    exact (Real.le_log_iff_exp_le hmoment_pos).2 hJ'
  rw [le_div_iff₀ hp]
  simpa only [mul_comm] using hlog_bound






theorem entropy_le_moment
    (μ : Measure α) {v : α → Real} {q : Real} (hq : 2 < q)
    (hvpos : ∀ᵐ x ∂μ, 0 < v x)
    (hv2 : Integrable (fun x => v x ^ 2) μ)
    (hmass : (∫ x, v x ^ 2 ∂μ) = 1)
    (hlog : Integrable (fun x => v x ^ 2 * Real.log (v x)) μ)
    (hmom : Integrable (fun x => v x ^ q) μ) :
    (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) ≤
      2 * (Real.log (∫ x, v x ^ q ∂μ) / (q - 2)) := by
  let ρ : α → ENNReal := fun x => ENNReal.ofReal (v x ^ 2)
  let ν : Measure α := μ.withDensity ρ
  have hρ : AEMeasurable ρ μ := by
    exact hv2.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hρtop : ∀ᵐ x ∂μ, ρ x < ⊤ := by
    filter_upwards with x
    simp only [ρ, ENNReal.ofReal_lt_top]
  have hsq0 : 0 ≤ᵐ[μ] fun x => v x ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg (v x)
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν, ρ]
    exact withDensity_prob μ hv2 hsq0 hmass
  have hvposν : ∀ᵐ x ∂ν, 0 < v x := by
    exact (withDensity_absolutelyContinuous μ ρ).ae_le hvpos
  have hlogν : Integrable (fun x => Real.log (v x)) ν := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [integrable_withDensity_iff_integrable_smul₀' hρ hρtop]
    refine hlog.congr ?_
    filter_upwards with x
    simp only [ρ, ENNReal.toReal_ofReal (sq_nonneg (v x)), smul_eq_mul]
  have hmomν : Integrable (fun x => v x ^ (q - 2)) ν := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [integrable_withDensity_iff_integrable_smul₀' hρ hρtop]
    refine hmom.congr ?_
    filter_upwards [hvpos] with x hx
    simp only [ρ, ENNReal.toReal_ofReal (sq_nonneg (v x)), smul_eq_mul]
    rw [← Real.rpow_natCast (v x) 2, ← Real.rpow_add hx]
    congr 1
    ring
  have hlog_eq :
      (∫ x, Real.log (v x) ∂ν) =
        ∫ x, v x ^ 2 * Real.log (v x) ∂μ := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hρ hρtop]
    apply integral_congr_ae
    filter_upwards with x
    simp only [ρ, ENNReal.toReal_ofReal (sq_nonneg (v x)), smul_eq_mul]
  have hmom_eq :
      (∫ x, v x ^ (q - 2) ∂ν) = ∫ x, v x ^ q ∂μ := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hρ hρtop]
    apply integral_congr_ae
    filter_upwards [hvpos] with x hx
    simp only [ρ, ENNReal.toReal_ofReal (sq_nonneg (v x)), smul_eq_mul]
    rw [← Real.rpow_natCast (v x) 2, ← Real.rpow_add hx]
    congr 1
    ring
  have hJ := int_log_le_moment (ν := ν) (X := v) (p := q - 2)
    (sub_pos.mpr hq) hvposν hlogν hmomν
  rw [hlog_eq, hmom_eq] at hJ
  calc
    (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) =
        2 * ∫ x, v x ^ 2 * Real.log (v x) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hvpos] with x hx
      rw [pow_two, Real.log_mul hx.ne' hx.ne']
      ring
    _ ≤ 2 * (Real.log (∫ x, v x ^ q ∂μ) / (q - 2)) :=
      mul_le_mul_of_nonneg_left hJ (by norm_num)

end

end DifferentialGeometry.Analysis.Integration
