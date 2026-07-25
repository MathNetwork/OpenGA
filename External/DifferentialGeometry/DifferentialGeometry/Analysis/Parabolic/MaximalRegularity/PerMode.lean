import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

def perModeConv (lam : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (-(lam * (t - s))) * f s

theorem perModeConv_def (lam : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    perModeConv lam f t = ∫ s in (0 : ℝ)..t, Real.exp (-(lam * (t - s))) * f s :=
  rfl

@[simp]
theorem perModeConv_zero_left (lam : ℝ) (f : ℝ → ℝ) :
    perModeConv lam f 0 = 0 := by
  simp [perModeConv]

private theorem kernel_factor (lam t s : ℝ) :
    Real.exp (-(lam * (t - s))) = Real.exp (-(lam * t)) * Real.exp (lam * s) := by
  rw [← Real.exp_add]
  ring_nf

section Continuity

variable {f : ℝ → ℝ}

theorem continuous_kernel_mul (lam t : ℝ) (hf : Continuous f) :
    Continuous (fun s => Real.exp (-(lam * (t - s))) * f s) := by
  fun_prop

theorem intervalIntegrable_kernel_mul (lam t : ℝ) (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fun s => Real.exp (-(lam * (t - s))) * f s) volume a b :=
  (continuous_kernel_mul lam t hf).intervalIntegrable a b

theorem continuous_perModeConv (lam : ℝ) (hf : Continuous f) :
    Continuous (perModeConv lam f) := by
  have hsplit : perModeConv lam f
      = fun t => Real.exp (-(lam * t)) *
          ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * f s := by
    funext t
    rw [perModeConv, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [kernel_factor, mul_assoc]
  rw [hsplit]
  have hg : Continuous (fun s => Real.exp (lam * s) * f s) := by fun_prop
  have hcont : Continuous (fun t => ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * f s) :=
    continuous_primitive (fun a b => (hg.intervalIntegrable a b)) 0
  fun_prop

theorem continuousOn_perModeConv (lam T : ℝ) (hf : Continuous f) :
    ContinuousOn (perModeConv lam f) (Set.Icc (0 : ℝ) T) :=
  (continuous_perModeConv lam hf).continuousOn

end Continuity

theorem kernelIntegral_space (lam t : ℝ) :
    ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s)))
      = 1 - Real.exp (-(lam * t)) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s => Real.exp (-(lam * (t - s))))
        (lam * Real.exp (-(lam * (t - s)))) s := by
    intro s _
    have hbase : HasDerivAt (fun s => -(lam * (t - s))) lam s := by
      have h1 : HasDerivAt (fun s : ℝ => t - s) (0 - 1) s :=
        (hasDerivAt_const s t).sub (hasDerivAt_id s)
      have h2 : HasDerivAt (fun s => -(lam * (t - s))) (-(lam * (0 - 1))) s :=
        (h1.const_mul lam).neg
      simpa using h2
    have hexp := hbase.exp
    simpa [mul_comm] using hexp
  have hint : IntervalIntegrable
      (fun s => lam * Real.exp (-(lam * (t - s)))) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

theorem kernelIntegral_time (lam s T : ℝ) :
    ∫ t in s..T, lam * Real.exp (-(lam * (t - s)))
      = 1 - Real.exp (-(lam * (T - s))) := by
  have hderiv : ∀ t ∈ Set.uIcc s T,
      HasDerivAt (fun t => -Real.exp (-(lam * (t - s))))
        (lam * Real.exp (-(lam * (t - s)))) t := by
    intro t _
    have hbase : HasDerivAt (fun t => -(lam * (t - s))) (-lam) t := by
      have h1 : HasDerivAt (fun t : ℝ => t - s) (1 - 0) t :=
        (hasDerivAt_id t).sub (hasDerivAt_const t s)
      have h2 : HasDerivAt (fun t => -(lam * (t - s))) (-(lam * (1 - 0))) t :=
        (h1.const_mul lam).neg
      simpa using h2
    have hexp := hbase.exp
    have hexp' : HasDerivAt (fun t => Real.exp (-(lam * (t - s))))
        (-(lam * Real.exp (-(lam * (t - s))))) t := by
      simpa [mul_comm, neg_mul] using hexp
    simpa using hexp'.neg
  have hint : IntervalIntegrable
      (fun t => lam * Real.exp (-(lam * (t - s)))) volume s T := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  ring

theorem kernelIntegral_space_le_one (lam t : ℝ) :
    ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) ≤ 1 := by
  rw [kernelIntegral_space]
  have : (0 : ℝ) ≤ Real.exp (-(lam * t)) := (Real.exp_pos _).le
  linarith

theorem kernelIntegral_space_nonneg {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    0 ≤ ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) := by
  rw [kernelIntegral_space]
  have h : Real.exp (-(lam * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  linarith

theorem kernelIntegral_time_le_one (lam s T : ℝ) :
    ∫ t in s..T, lam * Real.exp (-(lam * (t - s))) ≤ 1 := by
  rw [kernelIntegral_time]
  have : (0 : ℝ) ≤ Real.exp (-(lam * (T - s))) := (Real.exp_pos _).le
  linarith

theorem weighted_cauchy_schwarz {w g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hw : Continuous w) (hg : Continuous g) (hwpos : ∀ x ∈ Set.Icc a b, 0 ≤ w x) :
    (∫ x in a..b, w x * g x) ^ 2
      ≤ (∫ x in a..b, w x) * ∫ x in a..b, w x * g x ^ 2 := by
  set A : ℝ := ∫ x in a..b, w x * g x ^ 2 with hA
  set B : ℝ := ∫ x in a..b, w x * g x with hB
  set C : ℝ := ∫ x in a..b, w x with hC
  have hquad : ∀ c : ℝ, 0 ≤ C * (c * c) + (-(2 * B)) * c + A := by
    intro c
    have hintegrand : (fun x => w x * (g x - c) ^ 2)
        = fun x => w x * g x ^ 2 + (-(2 * c)) * (w x * g x) + (c * c) * w x := by
      funext x; ring
    have hexpand : (∫ x in a..b, w x * (g x - c) ^ 2)
        = A + (-(2 * c)) * B + (c * c) * C := by
      rw [hintegrand]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      · exact (hw.mul (hg.pow 2)).intervalIntegrable a b
      · exact ((continuous_const.mul (hw.mul hg))).intervalIntegrable a b
      · exact ((hw.mul (hg.pow 2)).add
          (continuous_const.mul (hw.mul hg))).intervalIntegrable a b
      · exact (continuous_const.mul hw).intervalIntegrable a b
    have hnonneg : 0 ≤ ∫ x in a..b, w x * (g x - c) ^ 2 := by
      refine intervalIntegral.integral_nonneg hab (fun x hx => ?_)
      exact mul_nonneg (hwpos x hx) (sq_nonneg _)
    rw [hexpand] at hnonneg
    nlinarith [hnonneg]
  have hdiscrim : discrim C (-(2 * B)) A ≤ 0 := discrim_le_zero hquad
  rw [discrim] at hdiscrim
  nlinarith [hdiscrim]

section Estimate

variable {f : ℝ → ℝ}

theorem perModeConv_sq_le_kernel_integral (lam : ℝ) (hlam : 0 ≤ lam)
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (lam * perModeConv lam f t) ^ 2
      ≤ ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) * f s ^ 2 := by
  set w : ℝ → ℝ := fun s => lam * Real.exp (-(lam * (t - s))) with hw_def
  have hw_cont : Continuous w := by fun_prop
  have hw_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) t, 0 ≤ w x := by
    intro x _
    exact mul_nonneg hlam (Real.exp_pos _).le
  have hlamphi : lam * perModeConv lam f t = ∫ s in (0 : ℝ)..t, w s * f s := by
    rw [perModeConv, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [hw_def]
    ring
  have hCS : (∫ s in (0 : ℝ)..t, w s * f s) ^ 2
      ≤ (∫ s in (0 : ℝ)..t, w s) * ∫ s in (0 : ℝ)..t, w s * f s ^ 2 :=
    weighted_cauchy_schwarz ht hw_cont hf hw_nonneg
  have hmass : (∫ s in (0 : ℝ)..t, w s) ≤ 1 := by
    simp only [hw_def]
    exact kernelIntegral_space_le_one lam t
  have hmass_nonneg : 0 ≤ ∫ s in (0 : ℝ)..t, w s := by
    simp only [hw_def]
    exact kernelIntegral_space_nonneg hlam ht
  have hwf2_nonneg : 0 ≤ ∫ s in (0 : ℝ)..t, w s * f s ^ 2 := by
    refine intervalIntegral.integral_nonneg ht (fun s hs => ?_)
    exact mul_nonneg (hw_nonneg s hs) (sq_nonneg _)
  calc (lam * perModeConv lam f t) ^ 2
      = (∫ s in (0 : ℝ)..t, w s * f s) ^ 2 := by rw [hlamphi]
    _ ≤ (∫ s in (0 : ℝ)..t, w s) * ∫ s in (0 : ℝ)..t, w s * f s ^ 2 := hCS
    _ ≤ 1 * ∫ s in (0 : ℝ)..t, w s * f s ^ 2 :=
        mul_le_mul_of_nonneg_right hmass hwf2_nonneg
    _ = ∫ s in (0 : ℝ)..t, w s * f s ^ 2 := one_mul _
    _ = ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) * f s ^ 2 := by
        simp only [hw_def]

private def schurIntegrand (lam : ℝ) (f : ℝ → ℝ) (t s : ℝ) : ℝ :=
  Set.indicator (Set.Iic t) (fun s => lam * Real.exp (-(lam * (t - s))) * f s ^ 2) s

private theorem schurIntegrand_of_le (lam : ℝ) (f : ℝ → ℝ) {t s : ℝ} (hst : s ≤ t) :
    schurIntegrand lam f t s = lam * Real.exp (-(lam * (t - s))) * f s ^ 2 := by
  rw [schurIntegrand, Set.indicator_of_mem (Set.mem_Iic.mpr hst)]

private theorem schurIntegrand_of_not_le (lam : ℝ) (f : ℝ → ℝ) {t s : ℝ}
    (hst : ¬ s ≤ t) : schurIntegrand lam f t s = 0 := by
  rw [schurIntegrand, Set.indicator_of_notMem (by simpa using hst)]

private theorem schurIntegrand_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (f : ℝ → ℝ)
    (t s : ℝ) : 0 ≤ schurIntegrand lam f t s := by
  rw [schurIntegrand]
  refine Set.indicator_nonneg (fun s _ => ?_) s
  exact mul_nonneg (mul_nonneg hlam (Real.exp_pos _).le) (sq_nonneg _)

private theorem setIntegral_schurIntegrand_space (lam : ℝ) (f : ℝ → ℝ)
    {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ s in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s
      = ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) * f s ^ 2 := by
  obtain ⟨ht0, htT⟩ := ht
  have hunfold : (fun s => schurIntegrand lam f t s)
      = Set.indicator (Set.Iic t)
          (fun s => lam * Real.exp (-(lam * (t - s))) * f s ^ 2) := by
    funext s; rw [schurIntegrand]
  rw [show (∫ s in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s)
        = ∫ s in Set.Icc (0 : ℝ) T,
            Set.indicator (Set.Iic t)
              (fun s => lam * Real.exp (-(lam * (t - s))) * f s ^ 2) s
      from by rw [hunfold]]
  rw [MeasureTheory.integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) T = Set.Icc (0 : ℝ) t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨hxt, hx0, _⟩; exact ⟨hx0, hxt⟩
    · rintro ⟨hx0, hxt⟩; exact ⟨hxt, hx0, le_trans hxt htT⟩
  rw [hset, intervalIntegral.integral_of_le ht0,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem setIntegral_schurIntegrand_time (lam : ℝ) (f : ℝ → ℝ)
    {T s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ∫ t in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s
      = f s ^ 2 * ∫ t in s..T, lam * Real.exp (-(lam * (t - s))) := by
  obtain ⟨hs0, hsT⟩ := hs
  have hcongr : ∀ t ∈ Set.Icc (0 : ℝ) T,
      schurIntegrand lam f t s
        = Set.indicator (Set.Ici s)
            (fun t => lam * Real.exp (-(lam * (t - s))) * f s ^ 2) t := by
    intro t _
    by_cases hst : s ≤ t
    · rw [schurIntegrand_of_le lam f hst, Set.indicator_of_mem (Set.mem_Ici.mpr hst)]
    · rw [schurIntegrand_of_not_le lam f hst,
        Set.indicator_of_notMem (by simpa using hst)]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hcongr,
    MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : Set.Ici s ∩ Set.Icc (0 : ℝ) T = Set.Icc s T := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨hsx, _, hxT⟩; exact ⟨hsx, hxT⟩
    · rintro ⟨hsx, hxT⟩; exact ⟨hsx, le_trans hs0 hsx, hxT⟩
  rw [hset, intervalIntegral.integral_of_le hsT,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
  ring

private theorem integrable_uncurry_schurIntegrand (lam : ℝ) (hlam : 0 ≤ lam)
    (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) :
    Integrable (Function.uncurry (schurIntegrand lam f))
      ((TimeSobolev.timeMeasure T).prod (TimeSobolev.timeMeasure T)) := by
  letI : MeasurableSpace ℝ := borel ℝ
  haveI : BorelSpace ℝ := ⟨rfl⟩
  rcases le_or_gt 0 T with hT | hT
  swap
  · have hzero : TimeSobolev.timeMeasure T = 0 :=
      TimeSobolev.timeMeasure_eq_zero_of_nonpos hT.le
    rw [hzero, Measure.zero_prod]
    exact integrable_zero_measure
  have hkernel_meas : Measurable
      (fun p : ℝ × ℝ => lam * Real.exp (-(lam * (p.1 - p.2))) * f p.2 ^ 2) := by
    apply Continuous.measurable
    fun_prop
  have htri_meas : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have huncurry_eq : Function.uncurry (schurIntegrand lam f)
      = Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1}
          (fun p => lam * Real.exp (-(lam * (p.1 - p.2))) * f p.2 ^ 2) := by
    funext p
    by_cases hp : p.2 ≤ p.1
    · rw [Function.uncurry_apply_pair, schurIntegrand_of_le lam f hp,
        Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 ≤ p.1} from hp)]
    · rw [Function.uncurry_apply_pair, schurIntegrand_of_not_le lam f hp,
        Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 ≤ p.1} from hp)]
  have hmeas : Measurable (Function.uncurry (schurIntegrand lam f)) := by
    rw [huncurry_eq]
    exact hkernel_meas.indicator htri_meas
  obtain ⟨t₀, _, ht₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) T)
      ⟨0, ⟨le_refl 0, hT⟩⟩ ((hf.pow 2).continuousOn.norm)
  set Cbound : ℝ := lam * (f t₀ ^ 2) with hCbound
  have hCbound_nonneg : 0 ≤ Cbound := by
    refine mul_nonneg hlam ?_
    positivity
  refine Integrable.of_mem_Icc 0 Cbound hmeas.aemeasurable ?_
  have hprod_restrict :
      (TimeSobolev.timeMeasure T).prod (TimeSobolev.timeMeasure T)
        = (volume.prod volume).restrict (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) T) := by
    rw [TimeSobolev.timeMeasure, Measure.prod_restrict]
  have hae_sq : ∀ᵐ p ∂((TimeSobolev.timeMeasure T).prod (TimeSobolev.timeMeasure T)),
      p ∈ Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) T := by
    rw [hprod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [hae_sq] with p hp
  obtain ⟨⟨hp10, hp1T⟩, ⟨hp20, hp2T⟩⟩ := hp
  refine ⟨schurIntegrand_nonneg hlam f p.1 p.2, ?_⟩
  by_cases hp : p.2 ≤ p.1
  · rw [Function.uncurry_apply_pair, schurIntegrand_of_le lam f hp]
    have hexp : Real.exp (-(lam * (p.1 - p.2))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ lam * (p.1 - p.2) := mul_nonneg hlam (by linarith)
      linarith
    have hf2 : f p.2 ^ 2 ≤ f t₀ ^ 2 := by
      have hmax := ht₀max (show p.2 ∈ Set.Icc (0 : ℝ) T from ⟨hp20, hp2T⟩)
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f p.2)),
        abs_of_nonneg (sq_nonneg (f t₀))] using hmax
    calc lam * Real.exp (-(lam * (p.1 - p.2))) * f p.2 ^ 2
        ≤ lam * 1 * f p.2 ^ 2 := by gcongr
      _ = lam * f p.2 ^ 2 := by ring
      _ ≤ lam * f t₀ ^ 2 := by gcongr
      _ = Cbound := hCbound.symm
  · rw [Function.uncurry_apply_pair, schurIntegrand_of_not_le lam f hp]
    exact hCbound_nonneg

theorem perModeConv_sq_integral_le (lam : ℝ) (hlam : 0 ≤ lam)
    (hf : Continuous f) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (lam * perModeConv lam f t) ^ 2
      ≤ ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  letI : MeasurableSpace ℝ := borel ℝ
  haveI : BorelSpace ℝ := ⟨rfl⟩
  have hstep1 : ∫ t in (0 : ℝ)..T, (lam * perModeConv lam f t) ^ 2
      ≤ ∫ t in (0 : ℝ)..T,
          ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) * f s ^ 2 := by
    refine intervalIntegral.integral_mono_on hT ?_ ?_ ?_
    · exact ((continuous_const.mul (continuous_perModeConv lam hf)).pow 2).intervalIntegrable 0 T
    · have heq : (fun t => ∫ s in (0 : ℝ)..t,
            lam * Real.exp (-(lam * (t - s))) * f s ^ 2)
          = fun t => Real.exp (-(lam * t)) *
              ∫ s in (0 : ℝ)..t, lam * Real.exp (lam * s) * f s ^ 2 := by
        funext t
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr (fun s _ => ?_)
        rw [kernel_factor]
        ring
      rw [heq]
      have hg : Continuous (fun s => lam * Real.exp (lam * s) * f s ^ 2) := by
        fun_prop
      have hcont : Continuous (fun t => ∫ s in (0 : ℝ)..t,
          lam * Real.exp (lam * s) * f s ^ 2) :=
        continuous_primitive (fun a b => hg.intervalIntegrable a b) 0
      have hpre : Continuous (fun t : ℝ => Real.exp (-(lam * t))) := by fun_prop
      exact (hpre.mul hcont).intervalIntegrable 0 T
    · intro t ht
      exact perModeConv_sq_le_kernel_integral lam hlam hf ht.1
  have hT_eq_inner : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) * f s ^ 2)
        = ∫ s in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s :=
    fun t ht => (setIntegral_schurIntegrand_space lam f ht).symm
  have hdouble_left : ∫ t in (0 : ℝ)..T,
        ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) * f s ^ 2
      = ∫ t in Set.Icc (0 : ℝ) T, ∫ s in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s := by
    rw [intervalIntegral.integral_of_le hT, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc hT_eq_inner
  have hfubini : ∫ t in Set.Icc (0 : ℝ) T,
        ∫ s in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s
      = ∫ s in Set.Icc (0 : ℝ) T,
          ∫ t in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s := by
    have hint := integrable_uncurry_schurIntegrand lam hlam f hf T
    have hswap := MeasureTheory.integral_integral_swap
      (μ := TimeSobolev.timeMeasure T) (ν := TimeSobolev.timeMeasure T)
      (f := schurIntegrand lam f) hint
    simpa only [TimeSobolev.timeMeasure] using hswap
  have hT_eq_outer : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ t in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s)
        = f s ^ 2 * (1 - Real.exp (-(lam * (T - s)))) := by
    intro s hs
    rw [setIntegral_schurIntegrand_time lam f hs, kernelIntegral_time]
  have hdouble_right : ∫ s in Set.Icc (0 : ℝ) T,
        ∫ t in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s
      = ∫ s in (0 : ℝ)..T, f s ^ 2 * (1 - Real.exp (-(lam * (T - s)))) := by
    rw [intervalIntegral.integral_of_le hT, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc hT_eq_outer
  have hfinal : ∫ s in (0 : ℝ)..T, f s ^ 2 * (1 - Real.exp (-(lam * (T - s))))
      ≤ ∫ s in (0 : ℝ)..T, f s ^ 2 := by
    refine intervalIntegral.integral_mono_on hT ?_ ?_ ?_
    · exact (Continuous.intervalIntegrable (by fun_prop) 0 T)
    · exact ((hf.pow 2)).intervalIntegrable 0 T
    · intro s _
      have hmass : (1 : ℝ) - Real.exp (-(lam * (T - s))) ≤ 1 := by
        have : (0 : ℝ) ≤ Real.exp (-(lam * (T - s))) := (Real.exp_pos _).le
        linarith
      calc f s ^ 2 * (1 - Real.exp (-(lam * (T - s))))
          ≤ f s ^ 2 * 1 := mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
        _ = f s ^ 2 := mul_one _
  calc ∫ t in (0 : ℝ)..T, (lam * perModeConv lam f t) ^ 2
      ≤ ∫ t in (0 : ℝ)..T,
          ∫ s in (0 : ℝ)..t, lam * Real.exp (-(lam * (t - s))) * f s ^ 2 := hstep1
    _ = ∫ t in Set.Icc (0 : ℝ) T,
          ∫ s in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s := hdouble_left
    _ = ∫ s in Set.Icc (0 : ℝ) T,
          ∫ t in Set.Icc (0 : ℝ) T, schurIntegrand lam f t s := hfubini
    _ = ∫ s in (0 : ℝ)..T, f s ^ 2 * (1 - Real.exp (-(lam * (T - s)))) := hdouble_right
    _ ≤ ∫ s in (0 : ℝ)..T, f s ^ 2 := hfinal

end Estimate

section Derivative

variable {f : ℝ → ℝ}

theorem perModeConv_hasDerivAt (lam : ℝ) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (perModeConv lam f)
      (f t - lam * perModeConv lam f t) t := by
  set ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * f s with hψ_def
  have hg : Continuous (fun s => Real.exp (lam * s) * f s) := by fun_prop
  have hsplit : perModeConv lam f = fun t => Real.exp (-(lam * t)) * ψ t := by
    funext t
    rw [perModeConv, hψ_def, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [kernel_factor, mul_assoc]
  have hψ_deriv : HasDerivAt ψ (Real.exp (lam * t) * f t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hpre_deriv : HasDerivAt (fun t => Real.exp (-(lam * t)))
      (-lam * Real.exp (-(lam * t))) t := by
    have hbase : HasDerivAt (fun t : ℝ => -(lam * t)) (-lam) t := by
      have h1 : HasDerivAt (fun t : ℝ => lam * t) lam t := by
        simpa using (hasDerivAt_id t).const_mul lam
      simpa using h1.neg
    have hexp := hbase.exp
    simpa [mul_comm] using hexp
  have hprod : HasDerivAt (fun t => Real.exp (-(lam * t)) * ψ t)
      (-lam * Real.exp (-(lam * t)) * ψ t
        + Real.exp (-(lam * t)) * (Real.exp (lam * t) * f t)) t :=
    hpre_deriv.mul hψ_deriv
  have hcancel : Real.exp (-(lam * t)) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hderiv_eq : -lam * Real.exp (-(lam * t)) * ψ t
        + Real.exp (-(lam * t)) * (Real.exp (lam * t) * f t)
      = f t - lam * (Real.exp (-(lam * t)) * ψ t) := by
    have hone : Real.exp (-(lam * t)) * (Real.exp (lam * t) * f t) = f t := by
      rw [← mul_assoc, hcancel, one_mul]
    rw [hone]; ring
  rw [hsplit]
  rw [hderiv_eq] at hprod
  exact hprod

theorem perModeConv_hasDerivWithinAt (lam : ℝ) (hf : Continuous f) (T t : ℝ) :
    HasDerivWithinAt (perModeConv lam f)
      (f t - lam * perModeConv lam f t) (Set.Icc (0 : ℝ) T) t :=
  (perModeConv_hasDerivAt lam hf t).hasDerivWithinAt

theorem continuous_perModeConv_deriv (lam : ℝ) (hf : Continuous f) :
    Continuous (fun t => f t - lam * perModeConv lam f t) :=
  hf.sub (continuous_const.mul (continuous_perModeConv lam hf))

theorem perModeConv_deriv_sq_integral_le (lam : ℝ) (hlam : 0 ≤ lam)
    (hf : Continuous f) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (f t - lam * perModeConv lam f t) ^ 2
      ≤ 4 * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  have hpoint : ∀ t : ℝ, (f t - lam * perModeConv lam f t) ^ 2
      ≤ 2 * f t ^ 2 + 2 * (lam * perModeConv lam f t) ^ 2 := by
    intro t
    nlinarith [sq_nonneg (f t + lam * perModeConv lam f t),
      sq_nonneg (f t - lam * perModeConv lam f t)]
  have hi_deriv : IntervalIntegrable
      (fun t => (f t - lam * perModeConv lam f t) ^ 2) volume 0 T :=
    ((continuous_perModeConv_deriv lam hf).pow 2).intervalIntegrable 0 T
  have hi_f2 : IntervalIntegrable (fun t => f t ^ 2) volume 0 T :=
    ((hf.pow 2)).intervalIntegrable 0 T
  have hi_lamphi2 : IntervalIntegrable
      (fun t => (lam * perModeConv lam f t) ^ 2) volume 0 T :=
    (((continuous_const.mul (continuous_perModeConv lam hf))).pow 2).intervalIntegrable 0 T
  have hmono : ∫ t in (0 : ℝ)..T, (f t - lam * perModeConv lam f t) ^ 2
      ≤ ∫ t in (0 : ℝ)..T,
          (2 * f t ^ 2 + 2 * (lam * perModeConv lam f t) ^ 2) := by
    refine intervalIntegral.integral_mono_on hT hi_deriv ?_ (fun t _ => hpoint t)
    exact (hi_f2.const_mul 2).add (hi_lamphi2.const_mul 2)
  have hsplit : ∫ t in (0 : ℝ)..T,
        (2 * f t ^ 2 + 2 * (lam * perModeConv lam f t) ^ 2)
      = 2 * (∫ t in (0 : ℝ)..T, f t ^ 2)
        + 2 * ∫ t in (0 : ℝ)..T, (lam * perModeConv lam f t) ^ 2 := by
    rw [intervalIntegral.integral_add (hi_f2.const_mul 2) (hi_lamphi2.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hreg : ∫ t in (0 : ℝ)..T, (lam * perModeConv lam f t) ^ 2
      ≤ ∫ t in (0 : ℝ)..T, f t ^ 2 :=
    perModeConv_sq_integral_le lam hlam hf hT
  have hf2_nonneg : 0 ≤ ∫ t in (0 : ℝ)..T, f t ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
  calc ∫ t in (0 : ℝ)..T, (f t - lam * perModeConv lam f t) ^ 2
      ≤ ∫ t in (0 : ℝ)..T,
          (2 * f t ^ 2 + 2 * (lam * perModeConv lam f t) ^ 2) := hmono
    _ = 2 * (∫ t in (0 : ℝ)..T, f t ^ 2)
          + 2 * ∫ t in (0 : ℝ)..T, (lam * perModeConv lam f t) ^ 2 := hsplit
    _ ≤ 2 * (∫ t in (0 : ℝ)..T, f t ^ 2)
          + 2 * ∫ t in (0 : ℝ)..T, f t ^ 2 := by gcongr
    _ = 4 * ∫ t in (0 : ℝ)..T, f t ^ 2 := by ring

end Derivative

section Smoothness

private theorem perModeConv_contDiff_natCast (lam : ℝ) :
    ∀ (k : ℕ) (f : ℝ → ℝ), ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (perModeConv lam f) := by
  intro k
  induction k with
  | zero =>
      intro f hf
      rw [Nat.cast_zero, contDiff_zero] at hf ⊢
      exact continuous_perModeConv lam hf
  | succ k ih =>
      intro f hf
      have hfcont : Continuous f := hf.continuous
      have hf_low : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) f :=
        hf.of_le (by rw [Nat.cast_succ]; exact le_self_add)
      have hphi_low : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (perModeConv lam f) :=
        ih f hf_low
      have hderiv_eq : deriv (perModeConv lam f)
          = fun t => f t - lam * perModeConv lam f t :=
        deriv_eq (fun t => perModeConv_hasDerivAt lam hfcont t)
      have hdiff : Differentiable ℝ (perModeConv lam f) :=
        fun t => (perModeConv_hasDerivAt lam hfcont t).differentiableAt
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨hdiff, fun hω => absurd hω (by simp), ?_⟩
      rw [hderiv_eq]
      exact hf_low.sub (contDiff_const.mul hphi_low)

theorem perModeConv_contDiff_of_contDiff (n : ℕ∞) (lam : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (perModeConv lam f) := by
  induction n using ENat.recTopCoe with
  | top =>
      rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ from rfl, contDiff_infty] at hf ⊢
      exact fun k => perModeConv_contDiff_natCast lam k f (hf k)
  | coe k => exact perModeConv_contDiff_natCast lam k f hf

theorem perModeConv_contDiff_top (lam : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (perModeConv lam f) :=
  perModeConv_contDiff_of_contDiff ⊤ lam f hf

end Smoothness

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
