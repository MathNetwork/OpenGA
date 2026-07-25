import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode
import Mathlib.MeasureTheory.Function.ContinuousMapDense

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

open TimeSobolev

section Integrability

variable {T : ℝ}

theorem integrableOn_bdd_mul_timeL2 {k : ℝ → ℝ} (hk : Continuous k)
    (f : timeL2 ℝ T) :
    IntegrableOn (fun s => k s * f s) (Set.Icc (0 : ℝ) T) volume := by
  rcases le_or_gt 0 T with hT | hT
  · obtain ⟨s₀, _, hs₀max⟩ :=
      isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) T)
        ⟨0, ⟨le_refl 0, hT⟩⟩ hk.norm.continuousOn
    have hfint : Integrable (fun s => f s) (timeMeasure T) := TimeSobolev.integrable f
    have hbound : ∀ᵐ s ∂(timeMeasure T), ‖k s‖ ≤ ‖k s₀‖ := by
      unfold timeMeasure
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
      exact hs₀max hs
    exact hfint.bdd_mul hk.aestronglyMeasurable hbound
  · rw [Icc_eq_empty (by linarith)]
    exact integrableOn_empty

theorem intervalIntegrable_exp_mul_timeL2 (lam : ℝ) (f : timeL2 ℝ T) (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => Real.exp (lam * s) * f s) volume 0 T := by
  refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hT]
  exact integrableOn_bdd_mul_timeL2 (by fun_prop) f

theorem intervalIntegrable_kernel_mul_timeL2 (lam t : ℝ) (f : timeL2 ℝ T)
    (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => Real.exp (-(lam * (t - s))) * f s) volume a b := by
  refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
  have hsub : Set.uIcc a b ⊆ Set.Icc (0 : ℝ) T := Set.uIcc_subset_Icc ha hb
  exact (integrableOn_bdd_mul_timeL2 (k := fun s => Real.exp (-(lam * (t - s))))
    (by fun_prop) f).mono_set hsub

theorem continuousOn_exp_primitive_timeL2 (lam : ℝ) (f : timeL2 ℝ T) (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * f s)
      (Set.Icc (0 : ℝ) T) := by
  have h := continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
    (f := fun s => Real.exp (lam * s) * f s) (μ := volume)
    (by rw [Set.uIcc_of_le hT]; exact integrableOn_bdd_mul_timeL2 (by fun_prop) f)
  rwa [Set.uIcc_of_le hT] at h

end Integrability

section Factoring

variable {T : ℝ}

theorem perModeConv_timeL2_factor (lam : ℝ) (f : timeL2 ℝ T) (t : ℝ) :
    perModeConv lam (fun s => f s) t
      = Real.exp (-(lam * t)) * ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * f s := by
  rw [perModeConv, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  rw [show Real.exp (-(lam * (t - s))) = Real.exp (-(lam * t)) * Real.exp (lam * s) from by
        rw [← Real.exp_add]; ring_nf, mul_assoc]

theorem continuousOn_perModeConv_timeL2 (lam : ℝ) (f : timeL2 ℝ T) (hT : 0 ≤ T) :
    ContinuousOn (perModeConv lam (fun s => f s)) (Set.Icc (0 : ℝ) T) := by
  have hfun : perModeConv lam (fun s => f s)
      = fun t => Real.exp (-(lam * t)) * ∫ s in (0 : ℝ)..t, Real.exp (lam * s) * f s := by
    funext t; exact perModeConv_timeL2_factor lam f t
  rw [hfun]
  exact (Continuous.continuousOn (by fun_prop)).mul
    (continuousOn_exp_primitive_timeL2 lam f hT)

end Factoring

section LiftedConv

variable {T : ℝ}

def perModeConvL2Fun (lam : ℝ) {T : ℝ} (hT : 0 ≤ T) (f : timeL2 ℝ T) :
    timeL2 ℝ T :=
  TimeSobolev.ofContinuousOn (continuousOn_perModeConv_timeL2 lam f hT)

theorem perModeConvL2Fun_coeFn (lam : ℝ) (hT : 0 ≤ T) (f : timeL2 ℝ T) :
    perModeConvL2Fun lam hT f =ᵐ[timeMeasure T] perModeConv lam (fun s => f s) :=
  TimeSobolev.coeFn_ofContinuousOn _

theorem perModeConv_timeL2_congr (lam : ℝ) {f₁ f₂ : ℝ → ℝ}
    (h : f₁ =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] f₂)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    perModeConv lam f₁ t = perModeConv lam f₂ t := by
  refine intervalIntegral.integral_congr_ae ?_
  have himp : ∀ᵐ x ∂volume, x ∈ Set.Icc (0 : ℝ) T → f₁ x = f₂ x :=
    (ae_restrict_iff' measurableSet_Icc).1 h
  filter_upwards [himp] with x hx
  intro hxI
  have hxIcc : x ∈ Set.Icc (0 : ℝ) T := by
    rw [Set.uIoc, min_eq_left ht.1, max_eq_right ht.1] at hxI
    exact ⟨le_of_lt hxI.1, le_trans hxI.2 ht.2⟩
  rw [hx hxIcc]

theorem perModeConvL2Fun_ofContinuousOn (lam : ℝ) (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) :
    perModeConvL2Fun lam hT (TimeSobolev.ofContinuousOn hf)
      =ᵐ[timeMeasure T] perModeConv lam f := by
  refine (perModeConvL2Fun_coeFn lam hT (TimeSobolev.ofContinuousOn hf)).trans ?_
  have hrep : ((TimeSobolev.ofContinuousOn hf : timeL2 ℝ T) : ℝ → ℝ)
      =ᵐ[timeMeasure T] f := TimeSobolev.coeFn_ofContinuousOn hf
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact perModeConv_timeL2_congr lam hrep ht

theorem perModeConvL2Fun_add (lam : ℝ) (hT : 0 ≤ T) (f₁ f₂ : timeL2 ℝ T) :
    perModeConvL2Fun lam hT (f₁ + f₂)
      = perModeConvL2Fun lam hT f₁ + perModeConvL2Fun lam hT f₂ := by
  refine Lp.ext ?_
  have h12 := perModeConvL2Fun_coeFn lam hT (f₁ + f₂)
  have h1 := perModeConvL2Fun_coeFn lam hT f₁
  have h2 := perModeConvL2Fun_coeFn lam hT f₂
  have hadd := Lp.coeFn_add (perModeConvL2Fun lam hT f₁) (perModeConvL2Fun lam hT f₂)
  have hfadd := Lp.coeFn_add f₁ f₂
  filter_upwards [h12, h1, h2, hadd, hfadd, ae_restrict_mem measurableSet_Icc]
    with t ht1 ht2 ht3 htadd htfadd htmem
  rw [ht1, htadd, Pi.add_apply, ht2, ht3]
  have hcongr : perModeConv lam (fun s => (f₁ + f₂) s) t
      = perModeConv lam (fun s => f₁ s + f₂ s) t :=
    perModeConv_timeL2_congr lam
      (h := by filter_upwards [hfadd] with r hr using hr) htmem
  rw [hcongr]
  unfold perModeConv
  rw [← intervalIntegral.integral_add
        (intervalIntegrable_kernel_mul_timeL2 lam t f₁ 0 t
          ⟨le_rfl, le_trans htmem.1 htmem.2⟩ htmem)
        (intervalIntegrable_kernel_mul_timeL2 lam t f₂ 0 t
          ⟨le_rfl, le_trans htmem.1 htmem.2⟩ htmem)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

theorem perModeConvL2Fun_smul (lam : ℝ) (hT : 0 ≤ T) (c : ℝ) (f : timeL2 ℝ T) :
    perModeConvL2Fun lam hT (c • f) = c • perModeConvL2Fun lam hT f := by
  refine Lp.ext ?_
  have hcf := perModeConvL2Fun_coeFn lam hT (c • f)
  have hf := perModeConvL2Fun_coeFn lam hT f
  have hsmul := Lp.coeFn_smul c (perModeConvL2Fun lam hT f)
  have hfsmul := Lp.coeFn_smul c f
  filter_upwards [hcf, hf, hsmul, hfsmul, ae_restrict_mem measurableSet_Icc]
    with t htcf htf htsmul htfsmul htmem
  rw [htcf, htsmul, Pi.smul_apply, htf, smul_eq_mul]
  have hcongr : perModeConv lam (fun s => (c • f) s) t
      = perModeConv lam (fun s => c * f s) t :=
    perModeConv_timeL2_congr lam
      (by filter_upwards [hfsmul] with r hr using by rw [hr]; rfl) htmem
  rw [hcongr]
  unfold perModeConv
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

theorem abs_perModeConv_timeL2_le (lam : ℝ) (hlam : 0 ≤ lam) (f : timeL2 ℝ T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    |perModeConv lam (fun s => f s) t| ≤ Real.sqrt T * ‖f‖ := by
  obtain ⟨ht0, htT⟩ := ht
  have hkernel_le : ∀ s ∈ Set.Ioc (0 : ℝ) t,
      ‖Real.exp (-(lam * (t - s))) * f s‖ ≤ ‖f s‖ := by
    intro s hs
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(lam * (t - s))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hs.1, hs.2])
    nlinarith [norm_nonneg (f s), hexp]
  have hint_kernel : IntegrableOn (fun s => Real.exp (-(lam * (t - s))) * f s)
      (Set.Ioc (0 : ℝ) t) volume := by
    have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT)
    exact (integrableOn_bdd_mul_timeL2 (k := fun s => Real.exp (-(lam * (t - s))))
      (by fun_prop) f).mono_set hsub
  have hint_f : IntegrableOn (fun s => f s) (Set.Ioc (0 : ℝ) t) volume :=
    (TimeSobolev.integrableOn f).mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  have hconv_le : |perModeConv lam (fun s => f s) t|
      ≤ ∫ s in Set.Ioc (0 : ℝ) t, ‖f s‖ := by
    rw [perModeConv, intervalIntegral.integral_of_le ht0, ← Real.norm_eq_abs]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on hint_kernel.norm hint_f.norm measurableSet_Ioc ?_
    intro s hs
    exact hkernel_le s hs
  have hmono : (∫ s in Set.Ioc (0 : ℝ) t, ‖f s‖)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, ‖f s‖ := by
    have hintT : IntegrableOn (fun s => ‖f s‖) (Set.Icc (0 : ℝ) T) volume :=
      (TimeSobolev.integrableOn f).norm
    refine setIntegral_mono_set hintT (Eventually.of_forall fun s => norm_nonneg _) ?_
    exact HasSubset.Subset.eventuallyLE
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  calc |perModeConv lam (fun s => f s) t|
      ≤ ∫ s in Set.Ioc (0 : ℝ) t, ‖f s‖ := hconv_le
    _ ≤ ∫ s in Set.Icc (0 : ℝ) T, ‖f s‖ := hmono
    _ ≤ Real.sqrt T * ‖f‖ := TimeSobolev.integral_norm_le f

theorem norm_perModeConvL2Fun_le (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) :
    ‖perModeConvL2Fun lam hT f‖ ≤ T * ‖f‖ := by
  have hbound : ‖perModeConvL2Fun lam hT f‖ ≤ Real.sqrt T * (Real.sqrt T * ‖f‖) := by
    rw [perModeConvL2Fun]
    refine TimeSobolev.norm_ofContinuousOn_le_of_bound _ (fun t ht => ?_)
    rw [Real.norm_eq_abs]
    exact abs_perModeConv_timeL2_le lam hlam f ht
  rwa [← mul_assoc, Real.mul_self_sqrt hT] at hbound

def perModeConvL2 (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ} (hT : 0 ≤ T) :
    timeL2 ℝ T →L[ℝ] timeL2 ℝ T :=
  LinearMap.mkContinuous
    { toFun := perModeConvL2Fun lam hT
      map_add' := perModeConvL2Fun_add lam hT
      map_smul' := fun c f => perModeConvL2Fun_smul lam hT c f }
    T
    (fun f => norm_perModeConvL2Fun_le lam hlam hT f)

@[simp] theorem perModeConvL2_apply (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) :
    perModeConvL2 lam hlam hT f = perModeConvL2Fun lam hT f := rfl

theorem perModeConvL2_coeFn (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T) (f : timeL2 ℝ T) :
    perModeConvL2 lam hlam hT f =ᵐ[timeMeasure T] perModeConv lam (fun s => f s) :=
  perModeConvL2Fun_coeFn lam hT f

end LiftedConv

section DensityExtension

variable {T : ℝ}

theorem norm_perModeConvL2_sq_eq (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) :
    ‖perModeConvL2 lam hlam hT f‖ ^ 2 =
      ∫ t in Set.Icc (0 : ℝ) T, (perModeConv lam (fun s => f s) t) ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [perModeConvL2_coeFn lam hlam hT f] with t ht
  rw [ht, Real.norm_eq_abs, sq_abs]

theorem perModeConv_boundedContinuous_eq (lam : ℝ)
    (F : BoundedContinuousFunction ℝ ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    perModeConv lam (fun s => (BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F) s) t
      = perModeConv lam F t := by
  refine perModeConv_timeL2_congr lam ?_ ht
  exact BoundedContinuousFunction.coeFn_toLp 2 (timeMeasure T) ℝ F

theorem norm_boundedContinuous_toLp_sq_eq (F : BoundedContinuousFunction ℝ ℝ) :
    ‖BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F‖ ^ 2 =
      ∫ t in Set.Icc (0 : ℝ) T, (F t) ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (timeMeasure T) ℝ F] with t ht
  rw [ht, Real.norm_eq_abs, sq_abs]

theorem timeL2_le_of_boundedContinuous {T : ℝ} {φ ψ : timeL2 ℝ T → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hbc : ∀ F : BoundedContinuousFunction ℝ ℝ,
      φ (BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F) ≤
        ψ (BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F))
    (f : timeL2 ℝ T) :
    φ f ≤ ψ f := by
  set C : Set (timeL2 ℝ T) := {g | φ g ≤ ψ g} with hC_def
  have hC_closed : IsClosed C := isClosed_le hφ hψ
  have hrange : Set.range (BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ) ⊆ C := by
    rintro g ⟨F, rfl⟩
    exact hbc F
  have hdense :
      Dense (Set.range (BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ)) :=
    BoundedContinuousFunction.toLp_denseRange ℝ (timeMeasure T) ℝ (by norm_num)
  have huniv : C = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hdense.closure_eq]
    exact (hC_closed.closure_subset_iff).mpr hrange
  have : f ∈ C := by rw [huniv]; exact Set.mem_univ f
  exact this

private theorem integral_zero_to_T_eq_Icc {T : ℝ} (hT : 0 ≤ T) (h : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..T, h t) = ∫ t in Set.Icc (0 : ℝ) T, h t := by
  rw [intervalIntegral.integral_of_le hT, ← MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem perModeConvL2_sq_le (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) :
    ‖(lam : ℝ) • perModeConvL2 lam hlam hT f‖ ≤ ‖f‖ := by
  refine timeL2_le_of_boundedContinuous
    (φ := fun f => ‖(lam : ℝ) • perModeConvL2 lam hlam hT f‖)
    (ψ := fun f => ‖f‖) (by fun_prop) (by fun_prop) (fun F => ?_) f
  set Ffun : timeL2 ℝ T := BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F
  have hsq : ‖(lam : ℝ) • perModeConvL2 lam hlam hT Ffun‖ ^ 2 ≤ ‖Ffun‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      norm_perModeConvL2_sq_eq lam hlam hT Ffun]
    have hcongr : ∫ t in Set.Icc (0 : ℝ) T,
          (perModeConv lam (fun s => Ffun s) t) ^ 2
        = ∫ t in Set.Icc (0 : ℝ) T, (perModeConv lam (fun s => F s) t) ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
      rw [perModeConv_boundedContinuous_eq lam F ht]
    rw [hcongr]
    have hbase := perModeConv_sq_integral_le lam hlam F.continuous hT
    have hlhs : ∫ t in (0 : ℝ)..T, (lam * perModeConv lam (fun s => F s) t) ^ 2
        = ∫ t in Set.Icc (0 : ℝ) T, (lam * perModeConv lam (fun s => F s) t) ^ 2 :=
      integral_zero_to_T_eq_Icc hT _
    have hrhs : (∫ t in (0 : ℝ)..T, (fun s => F s) t ^ 2)
        = ∫ t in Set.Icc (0 : ℝ) T, (F t) ^ 2 :=
      integral_zero_to_T_eq_Icc hT _
    rw [hlhs, hrhs] at hbase
    have hpull : lam ^ 2 * ∫ t in Set.Icc (0 : ℝ) T,
          (perModeConv lam (fun s => F s) t) ^ 2
        = ∫ t in Set.Icc (0 : ℝ) T, (lam * perModeConv lam (fun s => F s) t) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
      ring
    rw [hpull, norm_boundedContinuous_toLp_sq_eq F]
    exact hbase
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

def perModeConvDerivL2 (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ} (hT : 0 ≤ T) :
    timeL2 ℝ T →L[ℝ] timeL2 ℝ T :=
  ContinuousLinearMap.id ℝ (timeL2 ℝ T) - (lam : ℝ) • perModeConvL2 lam hlam hT

@[simp] theorem perModeConvDerivL2_apply (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) :
    perModeConvDerivL2 lam hlam hT f = f - (lam : ℝ) • perModeConvL2 lam hlam hT f := rfl

theorem perModeConvDerivL2_coeFn (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) :
    perModeConvDerivL2 lam hlam hT f =ᵐ[timeMeasure T]
      fun t => f t - lam * perModeConv lam (fun s => f s) t := by
  rw [perModeConvDerivL2_apply]
  have hsub := Lp.coeFn_sub f ((lam : ℝ) • perModeConvL2 lam hlam hT f)
  have hsmul := Lp.coeFn_smul (lam : ℝ) (perModeConvL2 lam hlam hT f)
  have hconv := perModeConvL2_coeFn lam hlam hT f
  filter_upwards [hsub, hsmul, hconv] with t ht1 ht2 ht3
  rw [ht1, Pi.sub_apply, ht2, Pi.smul_apply, ht3, smul_eq_mul]

theorem perModeConvDerivL2_sq_le (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) :
    ‖perModeConvDerivL2 lam hlam hT f‖ ≤ 2 * ‖f‖ := by
  refine timeL2_le_of_boundedContinuous
    (φ := fun f => ‖perModeConvDerivL2 lam hlam hT f‖)
    (ψ := fun f => 2 * ‖f‖) (by fun_prop) (by fun_prop) (fun F => ?_) f
  set Ffun : timeL2 ℝ T := BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F
  have hsq : ‖perModeConvDerivL2 lam hlam hT Ffun‖ ^ 2 ≤ (2 * ‖Ffun‖) ^ 2 := by
    have hnormsq : ‖perModeConvDerivL2 lam hlam hT Ffun‖ ^ 2
        = ∫ t in Set.Icc (0 : ℝ) T,
            (F t - lam * perModeConv lam (fun s => F s) t) ^ 2 := by
      rw [TimeSobolev.norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [perModeConvDerivL2_coeFn lam hlam hT Ffun,
        BoundedContinuousFunction.coeFn_toLp 2 (timeMeasure T) ℝ F,
        ae_restrict_mem measurableSet_Icc] with t ht htF htmem
      rw [ht, Real.norm_eq_abs, sq_abs, htF,
        perModeConv_boundedContinuous_eq lam F htmem]
    rw [hnormsq]
    have hbase := perModeConv_deriv_sq_integral_le lam hlam F.continuous hT
    have hlhs : ∫ t in (0 : ℝ)..T, (F t - lam * perModeConv lam (fun s => F s) t) ^ 2
        = ∫ t in Set.Icc (0 : ℝ) T,
            (F t - lam * perModeConv lam (fun s => F s) t) ^ 2 :=
      integral_zero_to_T_eq_Icc hT _
    have hrhs : (∫ t in (0 : ℝ)..T, F t ^ 2)
        = ∫ t in Set.Icc (0 : ℝ) T, F t ^ 2 :=
      integral_zero_to_T_eq_Icc hT _
    rw [hlhs, hrhs] at hbase
    calc ∫ t in Set.Icc (0 : ℝ) T,
          (F t - lam * perModeConv lam (fun s => F s) t) ^ 2
        ≤ 4 * ∫ t in Set.Icc (0 : ℝ) T, F t ^ 2 := hbase
      _ = (2 * ‖Ffun‖) ^ 2 := by
          rw [show (2 * ‖Ffun‖) ^ 2 = 4 * ‖Ffun‖ ^ 2 from by ring,
            norm_boundedContinuous_toLp_sq_eq F]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (by norm_num) (norm_nonneg _))] at h

end DensityExtension

section FTC

variable {T : ℝ}

open TimeSobolev.timeH1

theorem continuous_timeH1_mk_zero :
    Continuous (fun v : timeL2 ℝ T => TimeSobolev.timeH1.mk (0 : ℝ) v) := by
  have heq : (fun v : timeL2 ℝ T => TimeSobolev.timeH1.mk (0 : ℝ) v)
      = fun v => (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (timeL2 ℝ T)).symm
          (0, v) := by
    funext v; rfl
  rw [heq]
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (timeL2 ℝ T)).symm.continuous.comp
    (continuous_const.prodMk continuous_id)

theorem continuous_toFunL2_mk_zero_deriv (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T) :
    Continuous (fun f : timeL2 ℝ T => TimeSobolev.timeH1.toFunL2
      (TimeSobolev.timeH1.mk (0 : ℝ) (perModeConvDerivL2 lam hlam hT f))) := by
  have hcomp : (fun f : timeL2 ℝ T => TimeSobolev.timeH1.toFunL2
        (TimeSobolev.timeH1.mk (0 : ℝ) (perModeConvDerivL2 lam hlam hT f)))
      = (fun u => TimeSobolev.timeH1.toTimeL2 ℝ T u) ∘
          (fun v => TimeSobolev.timeH1.mk (0 : ℝ) v) ∘
          (fun f => perModeConvDerivL2 lam hlam hT f) := by
    funext f; rw [Function.comp_apply, Function.comp_apply,
      TimeSobolev.timeH1.toTimeL2_apply]
  rw [hcomp]
  exact (TimeSobolev.timeH1.toTimeL2 ℝ T).continuous.comp
    (continuous_timeH1_mk_zero.comp (perModeConvDerivL2 lam hlam hT).continuous)

theorem perModeConv_eq_integral_deriv (lam : ℝ) (F : BoundedContinuousFunction ℝ ℝ)
    (t : ℝ) :
    perModeConv lam (fun s => F s) t
      = ∫ s in (0 : ℝ)..t, (F s - lam * perModeConv lam (fun s => F s) s) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (perModeConv lam (fun s => F s))
        (F s - lam * perModeConv lam (fun s => F s) s) s :=
    fun s _ => perModeConv_hasDerivAt lam F.continuous s
  have hint : IntervalIntegrable
      (fun s => F s - lam * perModeConv lam (fun s => F s) s) volume 0 t :=
    (continuous_perModeConv_deriv lam F.continuous).intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    perModeConv_zero_left, sub_zero]

theorem perModeConvL2_eq_toFunL2_boundedContinuous (lam : ℝ) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (F : BoundedContinuousFunction ℝ ℝ) :
    perModeConvL2 lam hlam hT
        (BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F) =
      TimeSobolev.timeH1.toFunL2 (TimeSobolev.timeH1.mk (0 : ℝ)
        (perModeConvDerivL2 lam hlam hT
          (BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F))) := by
  set Ffun : timeL2 ℝ T := BoundedContinuousFunction.toLp 2 (timeMeasure T) ℝ F
  refine Lp.ext ?_
  have hlhs := perModeConvL2_coeFn lam hlam hT Ffun
  set v : timeL2 ℝ T := perModeConvDerivL2 lam hlam hT Ffun with hv_def
  have hrhs : ⇑(TimeSobolev.timeH1.toFunL2 (TimeSobolev.timeH1.mk (0 : ℝ) v))
      =ᵐ[timeMeasure T] (TimeSobolev.timeH1.mk (0 : ℝ) v).toFun :=
    TimeSobolev.coeFn_ofContinuousOn _
  have hvcoe := perModeConvDerivL2_coeFn lam hlam hT Ffun
  have hFcoe := BoundedContinuousFunction.coeFn_toLp 2 (timeMeasure T) ℝ F
  filter_upwards [hlhs, hrhs, ae_restrict_mem measurableSet_Icc]
    with t ht hrt htmem
  rw [ht, hrt, TimeSobolev.timeH1.toFun_apply, TimeSobolev.timeH1.init_mk, zero_add]
  have hintcongr : (∫ s in (0 : ℝ)..t, (TimeSobolev.timeH1.mk (0 : ℝ) v).deriv s)
      = ∫ s in (0 : ℝ)..t, (F s - lam * perModeConv lam (fun r => F r) s) := by
    rw [TimeSobolev.timeH1.deriv_mk]
    refine intervalIntegral.integral_congr_ae ?_
    have hae : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) T →
        (v s) = F s - lam * perModeConv lam (fun r => F r) s := by
      have h1 : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) T →
          (v s) = Ffun s - lam * perModeConv lam (fun r => Ffun r) s :=
        (ae_restrict_iff' measurableSet_Icc).1 hvcoe
      have h2 : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) T → Ffun s = F s :=
        (ae_restrict_iff' measurableSet_Icc).1 hFcoe
      filter_upwards [h1, h2] with s hs1 hs2 hsmem
      rw [hs1 hsmem, hs2 hsmem, perModeConv_boundedContinuous_eq lam F hsmem]
    filter_upwards [hae] with s hs hsI
    have hsmem : s ∈ Set.Icc (0 : ℝ) T := by
      rw [Set.uIoc, min_eq_left htmem.1, max_eq_right htmem.1] at hsI
      exact ⟨le_of_lt hsI.1, le_trans hsI.2 htmem.2⟩
    rw [hs hsmem]
  rw [hintcongr, ← perModeConv_eq_integral_deriv lam F t,
    perModeConv_boundedContinuous_eq lam F htmem]

theorem perModeConvL2_eq_toFunL2 (lam : ℝ) (hlam : 0 ≤ lam) (hT : 0 ≤ T)
    (f : timeL2 ℝ T) :
    perModeConvL2 lam hlam hT f =
      TimeSobolev.timeH1.toFunL2
        (TimeSobolev.timeH1.mk (0 : ℝ) (perModeConvDerivL2 lam hlam hT f)) := by
  have hkey : ‖perModeConvL2 lam hlam hT f -
      TimeSobolev.timeH1.toFunL2
        (TimeSobolev.timeH1.mk (0 : ℝ) (perModeConvDerivL2 lam hlam hT f))‖ ≤ 0 := by
    refine timeL2_le_of_boundedContinuous
      (φ := fun f => ‖perModeConvL2 lam hlam hT f -
        TimeSobolev.timeH1.toFunL2
          (TimeSobolev.timeH1.mk (0 : ℝ) (perModeConvDerivL2 lam hlam hT f))‖)
      (ψ := fun _ => 0)
      (((perModeConvL2 lam hlam hT).continuous.sub
        (continuous_toFunL2_mk_zero_deriv lam hlam hT)).norm)
      continuous_const (fun F => ?_) f
    simp only [perModeConvL2_eq_toFunL2_boundedContinuous lam hlam hT F, sub_self,
      norm_zero, le_refl]
  have hzero : ‖perModeConvL2 lam hlam hT f -
      TimeSobolev.timeH1.toFunL2
        (TimeSobolev.timeH1.mk (0 : ℝ) (perModeConvDerivL2 lam hlam hT f))‖ = 0 :=
    le_antisymm hkey (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end FTC

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
