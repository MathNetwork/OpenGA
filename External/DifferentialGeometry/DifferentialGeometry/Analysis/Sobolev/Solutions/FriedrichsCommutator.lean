import DifferentialGeometry.Analysis.Sobolev.Tools.Mollifier
import DifferentialGeometry.Analysis.Sobolev.Tools.Convolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise

namespace DifferentialGeometry.Analysis.Sobolev.FriedrichsCommutator

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def commutatorPointwise (a u φ : E → ℝ) (x : E) : ℝ :=
  a x * (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] φ) x -
    ((fun y => a y * u y) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] φ) x

omit [NeZero d] in

private lemma exists_sup_bound_nonneg
    {φ : E → ℝ} (hφ_cont : Continuous φ) (hφ_compact : HasCompactSupport φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |φ y| ≤ M := by
  rcases hφ_cont.bounded_above_of_compact_support hφ_compact with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, fun y => ?_⟩
  exact (hM y).trans (le_max_left _ _)

omit [NeZero d] in

private lemma memLp_smul_of_bound
    {a u : E → ℝ}
    (ha_meas : AEStronglyMeasurable a (volume : Measure E))
    {Λ : ℝ} (ha_bd : ∀ x, |a x| ≤ Λ)
    (hu : MemLp u 2 (volume : Measure E)) :
    MemLp (fun x => a x * u x) 2 (volume : Measure E) := by
  have hΛ_nn : 0 ≤ Λ := (abs_nonneg (a 0)).trans (ha_bd 0)
  refine MemLp.of_le (g := fun x => Λ * |u x|) ?_ ?_ ?_
  · have h_norm : MemLp (fun x => |u x|) 2 (volume : Measure E) := by
      have := hu.norm; simpa [Real.norm_eq_abs] using this
    have := h_norm.const_mul Λ
    simpa using this
  · exact ha_meas.mul hu.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have h_lhs : ‖a x * u x‖ = |a x| * |u x| := by
      rw [Real.norm_eq_abs, abs_mul]
    have h_rhs : ‖Λ * |u x|‖ = Λ * |u x| := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg hΛ_nn (abs_nonneg _))
    rw [h_lhs, h_rhs]
    exact mul_le_mul_of_nonneg_right (ha_bd x) (abs_nonneg _)

omit [NeZero d] in

private lemma measurePreserving_constSub' (x : E) :
    MeasurePreserving (fun t : E => x - t) volume volume := by
  have h_neg : MeasurePreserving (fun t : E => -t) volume volume :=
    Measure.measurePreserving_neg volume
  have h_addL : MeasurePreserving (fun t : E => x + t) volume volume :=
    measurePreserving_add_left volume x
  have heq : (fun t : E => x - t) = (fun t : E => x + (-t)) := by
    funext t; rw [sub_eq_add_neg]
  rw [heq]; exact h_addL.comp h_neg

omit [NeZero d] in

private lemma hasCompactSupport_translateSub
    {φ : E → ℝ} (hφ_compact : HasCompactSupport φ) (x : E) :
    HasCompactSupport (fun t : E => φ (x - t)) :=
  hφ_compact.comp_homeomorph (Homeomorph.subLeft x)

omit [NeZero d] in

private lemma integrable_conv_integrand
    {u φ : E → ℝ}
    (hu : MemLp u 2 (volume : Measure E))
    (hφ_cont : Continuous φ) (hφ_compact : HasCompactSupport φ) (x : E) :
    Integrable (fun t : E => u t * φ (x - t)) (volume : Measure E) := by
  classical
  rcases exists_sup_bound_nonneg hφ_cont hφ_compact with ⟨M, hM_nn, hM_bnd⟩
  have hφ_meas_sub : AEStronglyMeasurable (fun t : E => φ (x - t)) volume :=
    hφ_cont.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_constSub' x)
  have hum : AEStronglyMeasurable u volume := hu.aestronglyMeasurable
  have h_meas : AEStronglyMeasurable (fun t => u t * φ (x - t)) volume :=
    hum.mul hφ_meas_sub
  have hφ_compact_sub : HasCompactSupport (fun t : E => φ (x - t)) :=
    hasCompactSupport_translateSub hφ_compact x
  set K : Set E := tsupport (fun t : E => φ (x - t)) with hK_def
  have hK_compact : IsCompact K := hφ_compact_sub
  have hK_subset : tsupport (fun t : E => φ (x - t)) ⊆ K := subset_rfl
  have hu_loc : LocallyIntegrable u volume :=
    hu.locallyIntegrable (by norm_num)
  have hu_K : IntegrableOn u K volume := hu_loc.integrableOn_isCompact hK_compact
  have hbnd : ∀ t, ‖u t * φ (x - t)‖ ≤ M * (K.indicator (fun t => |u t|) t) := by
    intro t
    by_cases ht : t ∈ K
    · simp only [Real.norm_eq_abs, abs_mul]
      have h1 : |φ (x - t)| ≤ M := hM_bnd _
      have h2 : 0 ≤ |u t| := abs_nonneg _
      have hprod : |u t| * |φ (x - t)| ≤ |u t| * M :=
        mul_le_mul_of_nonneg_left h1 h2
      have h3 : |u t| * M = M * |u t| := by ring
      rw [h3] at hprod
      simp only [Set.indicator_of_mem ht]
      exact hprod
    · have hns : t ∉ Function.support (fun s : E => φ (x - s)) := by
        intro h
        exact ht (hK_subset (subset_tsupport _ h))
      simp only [Function.mem_support, ne_eq, Decidable.not_not] at hns
      have hzero : u t * φ (x - t) = 0 := by rw [hns]; ring
      rw [hzero]
      simp only [norm_zero, Set.indicator_of_notMem ht]
      exact mul_nonneg hM_nn (le_refl _)
  refine Integrable.mono' (g := fun t => M * (K.indicator (fun t => |u t|) t)) ?_ h_meas
    (Eventually.of_forall hbnd)
  have h_ind : Integrable (fun t => K.indicator (fun t => |u t|) t) volume := by
    rw [integrable_indicator_iff hK_compact.measurableSet]
    have huK_norm : IntegrableOn (fun t => ‖u t‖) K volume := hu_K.norm
    refine huK_norm.congr ?_
    refine Filter.EventuallyEq.symm ?_
    refine Filter.Eventually.of_forall ?_
    intro t; simp [Real.norm_eq_abs]
  exact h_ind.const_mul M

omit [NeZero d] in

private lemma conv_apply
    {u φ : E → ℝ} (x : E) :
    (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] φ) x =
      ∫ t, u t * φ (x - t) ∂(volume : Measure E) := by
  simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

omit [NeZero d] in

lemma commutatorPointwise_eq_integral
    {a u φ : E → ℝ} {Λ : ℝ}
    (ha_cont : Continuous a)
    (ha_bd : ∀ x, |a x| ≤ Λ)
    (hu : MemLp u 2 (volume : Measure E))
    (hφ_cont : Continuous φ) (hφ_compact : HasCompactSupport φ) (x : E) :
    commutatorPointwise a u φ x =
      ∫ t, φ (x - t) * (a x - a t) * u t ∂(volume : Measure E) := by
  classical
  have h_int_u : Integrable (fun t : E => u t * φ (x - t)) volume :=
    integrable_conv_integrand hu hφ_cont hφ_compact x
  have h_au_memLp : MemLp (fun t => a t * u t) 2 volume :=
    memLp_smul_of_bound ha_cont.aestronglyMeasurable ha_bd hu
  have h_int_au : Integrable (fun t : E => (a t * u t) * φ (x - t)) volume :=
    integrable_conv_integrand h_au_memLp hφ_cont hφ_compact x
  rw [commutatorPointwise]
  rw [conv_apply, conv_apply]
  rw [← integral_const_mul]
  have h_int1 : Integrable (fun t : E => a x * (u t * φ (x - t))) volume :=
    h_int_u.const_mul (a x)
  rw [← integral_sub h_int1 h_int_au]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring

omit [NeZero d] in

private lemma abs_commutator_integrand_le
    {a u φ : E → ℝ} {Λ ε : ℝ}
    (hΛ_nn : 0 ≤ Λ)
    (ha_lip : ∀ x y : E, |a x - a y| ≤ Λ * ‖x - y‖)
    (hφ_nn : ∀ y, 0 ≤ φ y)
    (hφ_supp : Function.support φ ⊆ Metric.closedBall (0 : E) ε)
    (x t : E) :
    |φ (x - t) * (a x - a t) * u t| ≤ φ (x - t) * (Λ * ε) * |u t| := by
  rcases eq_or_ne (φ (x - t)) 0 with hφzero | hφne
  · rw [hφzero]; simp
  · have hin : (x - t) ∈ Function.support φ := hφne
    have hcb : (x - t) ∈ Metric.closedBall (0 : E) ε := hφ_supp hin
    have hdist : ‖x - t‖ ≤ ε := by
      have := Metric.mem_closedBall.mp hcb
      simpa [dist_eq_norm] using this
    have hfun : 0 ≤ φ (x - t) := hφ_nn _
    have h_sub_bnd : |a x - a t| ≤ Λ * ε := by
      calc |a x - a t| ≤ Λ * ‖x - t‖ := ha_lip x t
        _ ≤ Λ * ε := mul_le_mul_of_nonneg_left hdist hΛ_nn
    have h1 : |φ (x - t) * (a x - a t) * u t| =
        φ (x - t) * |a x - a t| * |u t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfun]
    rw [h1]
    have hub : 0 ≤ φ (x - t) * |u t| :=
      mul_nonneg hfun (abs_nonneg _)
    have hub' : φ (x - t) * |a x - a t| * |u t|
              = (φ (x - t) * |u t|) * |a x - a t| := by ring
    have hub'' : φ (x - t) * (Λ * ε) * |u t|
              = (φ (x - t) * |u t|) * (Λ * ε) := by ring
    rw [hub', hub'']
    exact mul_le_mul_of_nonneg_left h_sub_bnd hub

omit [NeZero d] in

lemma abs_commutatorPointwise_le
    {a u φ : E → ℝ} {Λ ε : ℝ}
    (hΛ_nn : 0 ≤ Λ)
    (ha_cont : Continuous a)
    (ha_bd : ∀ x, |a x| ≤ Λ)
    (ha_lip : ∀ x y : E, |a x - a y| ≤ Λ * ‖x - y‖)
    (hu : MemLp u 2 (volume : Measure E))
    (hφ_cont : Continuous φ) (hφ_compact : HasCompactSupport φ)
    (hφ_nn : ∀ y, 0 ≤ φ y)
    (hφ_supp : Function.support φ ⊆ Metric.closedBall (0 : E) ε)
    (x : E) :
    |commutatorPointwise a u φ x| ≤
      (Λ * ε) * ∫ t, φ (x - t) * |u t| ∂(volume : Measure E) := by
  classical
  rw [commutatorPointwise_eq_integral ha_cont ha_bd hu hφ_cont hφ_compact]
  refine (abs_integral_le_integral_abs).trans ?_
  have h_abs_memLp : MemLp (fun t => |u t|) 2 volume := by
    have := hu.norm; simpa [Real.norm_eq_abs] using this
  have h_int_abs : Integrable (fun t : E => |u t| * φ (x - t)) volume :=
    integrable_conv_integrand h_abs_memLp hφ_cont hφ_compact x
  have h_rhs_int : Integrable (fun t : E => φ (x - t) * (Λ * ε) * |u t|) volume := by
    have heq : (fun t : E => φ (x - t) * (Λ * ε) * |u t|)
             = fun t : E => (Λ * ε) * (|u t| * φ (x - t)) := by
      funext t; ring
    rw [heq]; exact h_int_abs.const_mul _
  calc ∫ t, |φ (x - t) * (a x - a t) * u t| ∂(volume : Measure E)
      ≤ ∫ t, φ (x - t) * (Λ * ε) * |u t| ∂(volume : Measure E) := by
        refine integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) h_rhs_int ?_
        exact Eventually.of_forall fun t =>
          abs_commutator_integrand_le (u := u) hΛ_nn ha_lip hφ_nn hφ_supp x t
    _ = (Λ * ε) * ∫ t, φ (x - t) * |u t| ∂(volume : Measure E) := by
        rw [← integral_const_mul]
        congr 1; funext t; ring

omit [NeZero d] in

private lemma lintegral_constSub
    (x : E) (f : E → ℝ≥0∞) :
    ∫⁻ t, f (x - t) ∂(volume : Measure E) =
      ∫⁻ t, f t ∂(volume : Measure E) := by
  have hMP := measurePreserving_constSub' (d := d) x
  exact hMP.lintegral_comp_emb (Homeomorph.subLeft x).measurableEmbedding f

omit [NeZero d] in

private lemma enorm_commutatorPointwise_le_lintegral
    {a u φ : E → ℝ} {Λ ε : ℝ}
    (hΛ_nn : 0 ≤ Λ) (hε_nn : 0 ≤ ε)
    (ha_cont : Continuous a)
    (ha_bd : ∀ x, |a x| ≤ Λ)
    (ha_lip : ∀ x y : E, |a x - a y| ≤ Λ * ‖x - y‖)
    (hu : MemLp u 2 (volume : Measure E))
    (hφ_cont : Continuous φ) (hφ_compact : HasCompactSupport φ)
    (hφ_nn : ∀ y, 0 ≤ φ y)
    (hφ_supp : Function.support φ ⊆ Metric.closedBall (0 : E) ε)
    (x : E) :
    ‖commutatorPointwise a u φ x‖ₑ ≤
      ENNReal.ofReal (Λ * ε) *
        ∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ∂(volume : Measure E) := by
  classical
  have hΛε_nn : 0 ≤ Λ * ε := mul_nonneg hΛ_nn hε_nn
  have h1 : |commutatorPointwise a u φ x| ≤
      (Λ * ε) * ∫ t, φ (x - t) * |u t| ∂(volume : Measure E) :=
    abs_commutatorPointwise_le hΛ_nn ha_cont ha_bd ha_lip hu hφ_cont hφ_compact
      hφ_nn hφ_supp x
  have h_abs_memLp : MemLp (fun t => |u t|) 2 volume := by
    have := hu.norm; simpa [Real.norm_eq_abs] using this
  have h_int_abs : Integrable (fun t : E => |u t| * φ (x - t)) volume :=
    integrable_conv_integrand h_abs_memLp hφ_cont hφ_compact x
  have h_int_abs' : Integrable (fun t : E => φ (x - t) * |u t|) volume := by
    have heq : (fun t : E => φ (x - t) * |u t|)
             = fun t : E => |u t| * φ (x - t) := by funext t; ring
    rw [heq]; exact h_int_abs
  have h_int_nn : 0 ≤ᵐ[(volume : Measure E)] fun t : E => φ (x - t) * |u t| :=
    Eventually.of_forall fun t => mul_nonneg (hφ_nn _) (abs_nonneg _)
  have hen_lhs : ‖commutatorPointwise a u φ x‖ₑ
            = ENNReal.ofReal |commutatorPointwise a u φ x| :=
    Real.enorm_eq_ofReal_abs _
  rw [hen_lhs]
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ENNReal.ofReal_mul hΛε_nn]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  rw [show ENNReal.ofReal (∫ t, φ (x - t) * |u t| ∂(volume : Measure E))
        = ∫⁻ t, ENNReal.ofReal (φ (x - t) * |u t|) ∂(volume : Measure E) from
      ofReal_integral_eq_lintegral_ofReal h_int_abs' h_int_nn]
  refine lintegral_mono fun t => ?_
  rw [ENNReal.ofReal_mul (hφ_nn _)]
  exact le_of_eq (by rw [Real.enorm_eq_ofReal_abs])

omit [NeZero d] in

private lemma lintegral_phi_norm_u_sq_le
    {φ : E → ℝ}
    (hφ_meas : Measurable φ)
    (u : E → ℝ) (hu_meas : AEMeasurable u (volume : Measure E))
    (x : E) :
    (∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ
        ∂(volume : Measure E)) ^ (2 : ℝ) ≤
      (∫⁻ t, ENNReal.ofReal (φ (x - t)) ∂(volume : Measure E)) *
        (∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
            ∂(volume : Measure E)) := by
  classical
  set Φ : E → ℝ≥0∞ := fun t => ENNReal.ofReal (φ (x - t)) with hΦ_def
  have hΦ_meas : Measurable Φ := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact hφ_meas.comp (measurable_const.sub measurable_id)
  set f : E → ℝ≥0∞ := fun t => Φ t ^ ((1 : ℝ) / 2) with hf_def
  set g : E → ℝ≥0∞ := fun t => Φ t ^ ((1 : ℝ) / 2) * ‖u t‖ₑ with hg_def
  have hf_meas : AEMeasurable f volume :=
    (hΦ_meas.aemeasurable).pow_const ((1 : ℝ) / 2)
  have hg_meas : AEMeasurable g volume := by
    refine AEMeasurable.mul ?_ hu_meas.enorm
    exact (hΦ_meas.aemeasurable).pow_const ((1 : ℝ) / 2)
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hHolder :
      ∫⁻ t, (f * g) t ∂(volume : Measure E)
        ≤ (∫⁻ t, f t ^ (2 : ℝ) ∂(volume : Measure E)) ^ ((1 : ℝ) / 2)
            * (∫⁻ t, g t ^ (2 : ℝ) ∂(volume : Measure E)) ^ ((1 : ℝ) / 2) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq
      (μ := (volume : Measure E)) hpq hf_meas hg_meas
  have hfg : ∀ t, (f * g) t = Φ t * ‖u t‖ₑ := by
    intro t
    change Φ t ^ ((1 : ℝ) / 2) * (Φ t ^ ((1 : ℝ) / 2) * ‖u t‖ₑ) = Φ t * ‖u t‖ₑ
    rw [← mul_assoc]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    rw [show (1 : ℝ) / 2 + 1 / 2 = 1 from by norm_num, ENNReal.rpow_one]
  have hf_sq : ∀ t, f t ^ (2 : ℝ) = Φ t := by
    intro t
    change (Φ t ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = Φ t
    rw [← ENNReal.rpow_mul]
    rw [show ((1 : ℝ) / 2) * 2 = 1 from by norm_num, ENNReal.rpow_one]
  have hg_sq : ∀ t, g t ^ (2 : ℝ) = Φ t * ‖u t‖ₑ ^ (2 : ℝ) := by
    intro t
    change (Φ t ^ ((1 : ℝ) / 2) * ‖u t‖ₑ) ^ (2 : ℝ) = Φ t * ‖u t‖ₑ ^ (2 : ℝ)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [← ENNReal.rpow_mul]
    rw [show ((1 : ℝ) / 2) * 2 = 1 from by norm_num, ENNReal.rpow_one]
  have hLHS : ∫⁻ t, (f * g) t ∂(volume : Measure E)
            = ∫⁻ t, Φ t * ‖u t‖ₑ ∂(volume : Measure E) :=
    lintegral_congr fun t => hfg t
  have hRHS1 : ∫⁻ t, f t ^ (2 : ℝ) ∂(volume : Measure E)
             = ∫⁻ t, Φ t ∂(volume : Measure E) :=
    lintegral_congr fun t => hf_sq t
  have hRHS2 : ∫⁻ t, g t ^ (2 : ℝ) ∂(volume : Measure E)
             = ∫⁻ t, Φ t * ‖u t‖ₑ ^ (2 : ℝ) ∂(volume : Measure E) :=
    lintegral_congr fun t => hg_sq t
  rw [hLHS, hRHS1, hRHS2] at hHolder
  have hsq := ENNReal.rpow_le_rpow hHolder (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at hsq
  have hsimp : ∀ a : ℝ≥0∞, (a ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = a := fun a => by
    rw [← ENNReal.rpow_mul]; norm_num
  rw [hsimp, hsimp] at hsq
  exact hsq

omit [NeZero d] in

private lemma lintegral_ofReal_phi_lt_top
    {φ : E → ℝ} (hφ_cont : Continuous φ) (hφ_compact : HasCompactSupport φ) :
    ∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E) < ∞ := by
  have h_int : Integrable φ (volume : Measure E) :=
    hφ_cont.integrable_of_hasCompactSupport hφ_compact
  have h_norm : Integrable (fun y => ‖φ y‖) (volume : Measure E) := h_int.norm
  have h_finint : ∫⁻ y, ‖φ y‖ₑ ∂(volume : Measure E) < ∞ :=
    h_int.hasFiniteIntegral
  refine lt_of_le_of_lt ?_ h_finint
  refine lintegral_mono fun y => ?_
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

omit [NeZero d] in

private lemma aemeasurable_enorm_sq
    {u : E → ℝ} (hu : MemLp u 2 (volume : Measure E)) :
    AEMeasurable (fun t : E => ‖u t‖ₑ ^ (2 : ℝ)) (volume : Measure E) :=
  ((hu.aestronglyMeasurable.aemeasurable.enorm).pow_const _)

omit [NeZero d] in

private lemma eLpNorm_commutatorPointwise_sq_le_aux
    {a u φ : E → ℝ} {Λ ε : ℝ}
    (hΛ_nn : 0 ≤ Λ) (hε_nn : 0 ≤ ε)
    (ha_cont : Continuous a)
    (ha_bd : ∀ x, |a x| ≤ Λ)
    (ha_lip : ∀ x y : E, |a x - a y| ≤ Λ * ‖x - y‖)
    (hu : MemLp u 2 (volume : Measure E))
    (hφ_cont : Continuous φ) (hφ_compact : HasCompactSupport φ)
    (hφ_nn : ∀ y, 0 ≤ φ y)
    (hφ_supp : Function.support φ ⊆ Metric.closedBall (0 : E) ε) :
    eLpNorm (commutatorPointwise a u φ) 2 (volume : Measure E)
        ^ (2 : ℝ) ≤
      ENNReal.ofReal (Λ * ε) ^ (2 : ℝ) *
        (∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E)) ^ (2 : ℝ) *
        eLpNorm u 2 (volume : Measure E) ^ (2 : ℝ) := by
  classical
  have hφ_meas : Measurable φ := hφ_cont.measurable
  have hu_meas : AEMeasurable u (volume : Measure E) :=
    hu.aestronglyMeasurable.aemeasurable
  have h_eLpNorm_sq :
      eLpNorm (commutatorPointwise a u φ) 2 (volume : Measure E) ^ (2 : ℝ)
        = ∫⁻ x, ‖commutatorPointwise a u φ x‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure E) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure E))
      (f := commutatorPointwise a u φ)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    have h_2toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2toReal]
    rw [← ENNReal.rpow_mul]
    rw [show (1 : ℝ) / 2 * 2 = 1 from by norm_num, ENNReal.rpow_one]
  rw [h_eLpNorm_sq]
  have h_pt : ∀ x : E,
      ‖commutatorPointwise a u φ x‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (Λ * ε) ^ (2 : ℝ)
          * ((∫⁻ t, ENNReal.ofReal (φ (x - t)) ∂(volume : Measure E))
              * ∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
                ∂(volume : Measure E)) := by
    intro x
    have h1 := enorm_commutatorPointwise_le_lintegral
      hΛ_nn hε_nn ha_cont ha_bd ha_lip hu hφ_cont hφ_compact hφ_nn hφ_supp x
    have h_sq : ‖commutatorPointwise a u φ x‖ₑ ^ (2 : ℝ)
        ≤ (ENNReal.ofReal (Λ * ε)
            * ∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ
                ∂(volume : Measure E)) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 2)
    refine h_sq.trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    exact lintegral_phi_norm_u_sq_le hφ_meas u hu_meas x
  refine (lintegral_mono h_pt).trans ?_
  have hpow_finite : (ENNReal.ofReal (Λ * ε)) ^ (2 : ℝ) ≠ ∞ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
    exact ENNReal.ofReal_ne_top
  rw [lintegral_const_mul' _ _ hpow_finite]
  have hB : ∀ x : E,
      ∫⁻ t, ENNReal.ofReal (φ (x - t)) ∂(volume : Measure E) =
        ∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E) :=
    fun x => lintegral_constSub x (fun y => ENNReal.ofReal (φ y))
  have h_step1 :
      ∫⁻ x, (∫⁻ t, ENNReal.ofReal (φ (x - t)) ∂(volume : Measure E))
          * ∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
              ∂(volume : Measure E) ∂(volume : Measure E)
        = (∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E))
          * ∫⁻ x, ∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
              ∂(volume : Measure E) ∂(volume : Measure E) := by
    have h_phi_finite : (∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E)) ≠ ∞ :=
      (lintegral_ofReal_phi_lt_top hφ_cont hφ_compact).ne
    rw [← lintegral_const_mul' _ _ h_phi_finite]
    refine lintegral_congr fun x => ?_
    rw [hB x]
  rw [h_step1]
  rw [show ENNReal.ofReal (Λ * ε) ^ (2 : ℝ)
        * ((∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E))
            * ∫⁻ x, ∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
                ∂(volume : Measure E) ∂(volume : Measure E))
      = ENNReal.ofReal (Λ * ε) ^ (2 : ℝ)
          * (∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E))
          * ∫⁻ x, ∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
              ∂(volume : Measure E) ∂(volume : Measure E) from by ring]
  have h_tonelli :
      ∫⁻ x, ∫⁻ t, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure E) ∂(volume : Measure E) =
        ∫⁻ t, ∫⁻ x, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure E) ∂(volume : Measure E) := by
    refine lintegral_lintegral_swap ?_
    refine AEMeasurable.mul ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp (hφ_cont.measurable.comp
        (measurable_fst.sub measurable_snd))).aemeasurable
    · have := (hu_meas.enorm).pow_const (2 : ℝ)
      exact this.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd
          (μ := (volume : Measure E)) (ν := (volume : Measure E)))
  rw [h_tonelli]
  have h_inner : ∀ t : E,
      ∫⁻ x, ENNReal.ofReal (φ (x - t)) * ‖u t‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure E) =
        ‖u t‖ₑ ^ (2 : ℝ)
          * ∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E) := by
    intro t
    rw [lintegral_mul_const' _ _ (by
      refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
      exact ENNReal.coe_ne_top)]
    rw [mul_comm]
    congr 1
    have hMP : MeasurePreserving (fun x : E => x - t) volume volume := by
      have h_addR : MeasurePreserving (fun x : E => x + (-t)) volume volume :=
        measurePreserving_add_right volume (-t)
      have heq : (fun x : E => x - t) = (fun x : E => x + (-t)) := by
        funext x; rw [sub_eq_add_neg]
      rw [heq]; exact h_addR
    exact hMP.lintegral_comp_emb (Homeomorph.subRight t).measurableEmbedding
      (fun y : E => ENNReal.ofReal (φ y))
  conv_lhs => rw [lintegral_congr (fun t => h_inner t)]
  rw [lintegral_mul_const' _ _ (lintegral_ofReal_phi_lt_top hφ_cont hφ_compact).ne]
  have h_u_sq : ∫⁻ t, ‖u t‖ₑ ^ (2 : ℝ) ∂(volume : Measure E)
      = eLpNorm u 2 (volume : Measure E) ^ (2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure E)) (f := u)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    have h_2toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2toReal, ← ENNReal.rpow_mul]
    rw [show (1 : ℝ) / 2 * 2 = 1 from by norm_num, ENNReal.rpow_one]
  rw [h_u_sq]
  refine le_of_eq ?_
  set A : ℝ≥0∞ := ENNReal.ofReal (Λ * ε) ^ (2 : ℝ)
  set B : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E)
  set Eu : ℝ≥0∞ := eLpNorm u 2 (volume : Measure E) ^ (2 : ℝ)
  have hBsq : B ^ (2 : ℝ) = B * B := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, ENNReal.rpow_natCast,
      pow_two]
  rw [hBsq]
  rw [mul_assoc A B (Eu * B), ← mul_assoc B Eu B, mul_comm B Eu,
    mul_assoc Eu B B, mul_comm Eu (B * B), ← mul_assoc]

omit [NeZero d] in

theorem eLpNorm_commutatorPointwise_le
    {a u φ : E → ℝ} {Λ ε : ℝ}
    (hΛ_nn : 0 ≤ Λ) (hε_nn : 0 ≤ ε)
    (ha_cont : Continuous a)
    (ha_bd : ∀ x, |a x| ≤ Λ)
    (ha_lip : ∀ x y : E, |a x - a y| ≤ Λ * ‖x - y‖)
    (hu : MemLp u 2 (volume : Measure E))
    (hφ_cont : Continuous φ) (hφ_compact : HasCompactSupport φ)
    (hφ_nn : ∀ y, 0 ≤ φ y)
    (hφ_supp : Function.support φ ⊆ Metric.closedBall (0 : E) ε) :
    eLpNorm (commutatorPointwise a u φ) 2 (volume : Measure E) ≤
      ENNReal.ofReal (Λ * ε) *
        (∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E)) *
        eLpNorm u 2 (volume : Measure E) := by
  classical
  have h_sq := eLpNorm_commutatorPointwise_sq_le_aux
    hΛ_nn hε_nn ha_cont ha_bd ha_lip hu hφ_cont hφ_compact hφ_nn hφ_supp
  have h_root := ENNReal.rpow_le_rpow h_sq (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
  have hLHS : (eLpNorm (commutatorPointwise a u φ) 2 (volume : Measure E)
      ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = eLpNorm (commutatorPointwise a u φ) 2 (volume : Measure E) := by
    rw [← ENNReal.rpow_mul]
    rw [show (2 : ℝ) * ((1 : ℝ) / 2) = 1 from by norm_num, ENNReal.rpow_one]
  have hRHS :
      (ENNReal.ofReal (Λ * ε) ^ (2 : ℝ) *
        (∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E)) ^ (2 : ℝ) *
        eLpNorm u 2 (volume : Measure E) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        = ENNReal.ofReal (Λ * ε) *
          (∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure E)) *
          eLpNorm u 2 (volume : Measure E) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    have h_simp : ∀ a : ℝ≥0∞, (a ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = a := fun a => by
      rw [← ENNReal.rpow_mul]
      rw [show (2 : ℝ) * ((1 : ℝ) / 2) = 1 from by norm_num, ENNReal.rpow_one]
    rw [h_simp, h_simp, h_simp]
  rw [hLHS] at h_root
  rw [hRHS] at h_root
  exact h_root

omit [NeZero d] in
private lemma mollifierEps_props {ε : ℝ} (hε : 0 < ε) :
    Continuous (mollifierEps (d := d) hε)
      ∧ HasCompactSupport (mollifierEps (d := d) hε)
      ∧ (∀ y : E, 0 ≤ mollifierEps (d := d) hε y)
      ∧ Function.support (mollifierEps (d := d) hε) ⊆
          Metric.closedBall (0 : E) ε
      ∧ ∫⁻ y, ENNReal.ofReal (mollifierEps (d := d) hε y) ∂(volume : Measure E)
        = 1 := by
  refine ⟨mollifierEps_continuous hε, mollifierEps_compactSupport hε,
    mollifierEps_nonneg hε, ?_, ?_⟩
  · exact mollifierEps_support_subset_closedBall_eps hε
  · have h_int : ∫ y, mollifierEps (d := d) hε y ∂(volume : Measure E) = 1 :=
      mollifierEps_integral_eq_one hε
    have h_integrable : Integrable (mollifierEps (d := d) hε)
        (volume : Measure E) := mollifierEps_integrable hε
    have h_nn : 0 ≤ᵐ[(volume : Measure E)] mollifierEps (d := d) hε :=
      Eventually.of_forall (mollifierEps_nonneg hε)
    have := ofReal_integral_eq_lintegral_ofReal h_integrable h_nn
    rw [h_int] at this
    rw [← this]
    simp

omit [NeZero d] in
theorem friedrichsCommutator_tendsto_zero
    {a : E → ℝ} (ha_smooth : ContDiff ℝ ⊤ a)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (ha_bd : ∀ x : E, |a x| ≤ Λ)
    (h_grad_bd : ∀ x : E, ‖fderiv ℝ a x‖ ≤ Λ)
    {u : E → ℝ}
    (hu : MemLp u 2 (volume : Measure E)) :
    Filter.Tendsto
      (fun ε : ℝ => if h : 0 < ε then
        eLpNorm (commutatorPointwise a u (mollifierEps (d := d) h)) 2
          (volume : Measure E)
        else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  have ha_cont : Continuous a := ha_smooth.continuous
  have ha_diff : Differentiable ℝ a := ha_smooth.differentiable (by norm_cast)
  have h_grad_bd_nn : ∀ x : E, ‖fderiv ℝ a x‖₊ ≤ ⟨Λ, hΛ_nn⟩ := by
    intro x
    have := h_grad_bd x
    rwa [← NNReal.coe_le_coe, coe_nnnorm]
  have hLip : LipschitzWith ⟨Λ, hΛ_nn⟩ a :=
    lipschitzWith_of_nnnorm_fderiv_le ha_diff h_grad_bd_nn
  have ha_lip : ∀ x y : E, |a x - a y| ≤ Λ * ‖x - y‖ := by
    intro x y
    have h_dist := hLip.dist_le_mul x y
    rw [Real.dist_eq, dist_eq_norm] at h_dist
    exact h_dist
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη_pos
  set C : ℝ≥0∞ := eLpNorm u 2 (volume : Measure E) with hC_def
  have hC_top : C ≠ ∞ := hu.eLpNorm_lt_top.ne
  rcases eq_or_ne η ∞ with hη_top | hη_ne_top
  · rw [hη_top]
    refine Filter.Eventually.of_forall fun _ => ?_
    exact le_top
  set ηtop : ℝ := η.toReal with hηtop_def
  have hηtop_pos : 0 < ηtop := by
    rw [hηtop_def]
    exact ENNReal.toReal_pos hη_pos.ne' hη_ne_top
  set Ctop : ℝ := C.toReal with hCtop_def
  have hCtop_nn : 0 ≤ Ctop := ENNReal.toReal_nonneg
  set M : ℝ := (Λ + 1) * (Ctop + 1) with hM_def
  have hM_pos : 0 < M := by
    have h1 : 0 < Λ + 1 := by linarith
    have h2 : 0 < Ctop + 1 := by linarith
    exact mul_pos h1 h2
  set δ : ℝ := ηtop / M with hδ_def
  have hδ_pos : 0 < δ := div_pos hηtop_pos hM_pos
  have h_eventually : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      0 < ε ∧ ε < δ := by
    have h1 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := by
      filter_upwards [self_mem_nhdsWithin] with ε hε; exact hε
    have h2 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < δ :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ_pos)
    filter_upwards [h1, h2] with ε hε1 hε2
    exact ⟨hε1, hε2⟩
  filter_upwards [h_eventually] with ε hε
  obtain ⟨hε_pos, hε_lt⟩ := hε
  rw [dif_pos hε_pos]
  have h_prop := mollifierEps_props (d := d) hε_pos
  obtain ⟨h_cont, h_compact, h_nn, h_supp, h_intone⟩ := h_prop
  have h_bound :=
    eLpNorm_commutatorPointwise_le hΛ_nn hε_pos.le ha_cont ha_bd ha_lip hu
      h_cont h_compact h_nn h_supp
  rw [h_intone, mul_one] at h_bound
  refine h_bound.trans ?_
  have hC_eq_form : ENNReal.ofReal Ctop = eLpNorm u 2 (volume : Measure E) := by
    change ENNReal.ofReal (eLpNorm u 2 (volume : Measure E)).toReal
      = eLpNorm u 2 (volume : Measure E)
    exact ENNReal.ofReal_toReal hC_top
  have hΛε_nn : 0 ≤ Λ * ε := mul_nonneg hΛ_nn hε_pos.le
  rw [← hC_eq_form]
  rw [← ENNReal.ofReal_mul hΛε_nn]
  rw [← ENNReal.ofReal_toReal hη_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  have hCalc : Λ * ε * Ctop ≤ (Λ + 1) * ε * (Ctop + 1) := by
    have h1 : Λ ≤ Λ + 1 := by linarith
    have h2 : Ctop ≤ Ctop + 1 := by linarith
    have hε_nn : 0 ≤ ε := hε_pos.le
    have hCtop_p1_nn : 0 ≤ Ctop + 1 := by linarith
    have hΛp1_nn : 0 ≤ Λ + 1 := by linarith
    calc Λ * ε * Ctop
        = Λ * ε * Ctop := rfl
      _ ≤ (Λ + 1) * ε * Ctop := by
            have : Λ * ε ≤ (Λ + 1) * ε := mul_le_mul_of_nonneg_right h1 hε_nn
            exact mul_le_mul_of_nonneg_right this hCtop_nn
      _ ≤ (Λ + 1) * ε * (Ctop + 1) := by
            have h3 : 0 ≤ (Λ + 1) * ε := mul_nonneg hΛp1_nn hε_nn
            exact mul_le_mul_of_nonneg_left h2 h3
  refine hCalc.trans ?_
  change (Λ + 1) * ε * (Ctop + 1) ≤ ηtop
  have hM_pos' : 0 < (Λ + 1) * (Ctop + 1) := hM_pos
  have hε_lt_div : ε < ηtop / ((Λ + 1) * (Ctop + 1)) := hε_lt
  have h_factor_pos : 0 < (Λ + 1) * (Ctop + 1) := hM_pos'
  have hr : (Λ + 1) * ε * (Ctop + 1) = ε * ((Λ + 1) * (Ctop + 1)) := by ring
  rw [hr]
  have h_lt : ε * ((Λ + 1) * (Ctop + 1)) < (ηtop / ((Λ + 1) * (Ctop + 1)))
                * ((Λ + 1) * (Ctop + 1)) :=
    (mul_lt_mul_of_pos_right hε_lt_div h_factor_pos)
  refine le_of_lt (h_lt.trans_le ?_)
  rw [div_mul_cancel₀ _ (ne_of_gt h_factor_pos)]

end DifferentialGeometry.Analysis.Sobolev.FriedrichsCommutator
