import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

def timeMeasure (T : ℝ) : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) T)

instance instIsFiniteMeasureTimeMeasure (T : ℝ) : IsFiniteMeasure (timeMeasure T) := by
  unfold timeMeasure; infer_instance

theorem timeMeasure_univ (T : ℝ) :
    timeMeasure T Set.univ = ENNReal.ofReal T := by
  unfold timeMeasure
  rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]

theorem timeMeasure_eq_zero_of_nonpos {T : ℝ} (hT : T ≤ 0) :
    timeMeasure T = 0 := by
  refine Measure.measure_univ_eq_zero.1 ?_
  rw [timeMeasure_univ, ENNReal.ofReal_eq_zero]
  exact hT

theorem timeMeasure_real_univ {T : ℝ} (hT : 0 ≤ T) :
    (timeMeasure T).real Set.univ = T := by
  rw [measureReal_def, timeMeasure_univ, ENNReal.toReal_ofReal hT]

theorem timeMeasure_ne_zero {T : ℝ} (hT : 0 < T) :
    timeMeasure T ≠ 0 := by
  intro h
  have : timeMeasure T Set.univ = 0 := by rw [h]; rfl
  rw [timeMeasure_univ, ENNReal.ofReal_eq_zero] at this
  exact absurd this (not_le.2 hT)

theorem toReal_ofReal_rpow_half (T : ℝ) :
    (ENNReal.ofReal T ^ (1 / 2 : ℝ)).toReal = Real.sqrt T := by
  rcases le_or_gt 0 T with hT | hT
  · rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hT, ← Real.sqrt_eq_rpow]
  · rw [ENNReal.ofReal_eq_zero.2 hT.le, ENNReal.zero_rpow_of_pos (by norm_num),
      ENNReal.toReal_zero, Real.sqrt_eq_zero'.2 hT.le]

abbrev timeL2 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : Type _ :=
  MeasureTheory.Lp X 2 (timeMeasure T)

example : NormedAddCommGroup (timeL2 X T) := inferInstance
example : NormedSpace ℝ (timeL2 X T) := inferInstance
example : InnerProductSpace ℝ (timeL2 X T) := inferInstance
example : CompleteSpace (timeL2 X T) := inferInstance

theorem inner_def (f g : timeL2 X T) :
    (inner ℝ f g : ℝ) = ∫ t in Set.Icc (0 : ℝ) T, inner ℝ (f t) (g t) := by
  rw [L2.inner_def]; rfl

theorem memLp_iff {f : ℝ → X} :
    MemLp f 2 (timeMeasure T) ↔ ∃ F : timeL2 X T, F =ᵐ[timeMeasure T] f :=
  ⟨fun h => ⟨h.toLp f, h.coeFn_toLp⟩, fun ⟨F, hF⟩ => (Lp.memLp F).ae_eq hF⟩

theorem norm_sq_eq_integral (f : timeL2 X T) :
    ‖f‖ ^ 2 = ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_def]
  exact integral_congr_ae (Eventually.of_forall fun t => real_inner_self_eq_norm_sq _)

theorem norm_eq_sqrt_integral (f : timeL2 X T) :
    ‖f‖ = Real.sqrt (∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2) := by
  rw [← norm_sq_eq_integral, Real.sqrt_sq (norm_nonneg _)]

theorem integral_norm_sq_nonneg (f : timeL2 X T) :
    0 ≤ ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 := by
  rw [← norm_sq_eq_integral]; positivity

section ContinuousEmbedding

variable {f : ℝ → X}

omit [InnerProductSpace ℝ X] [CompleteSpace X] in

theorem memLp_of_continuousOn (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) :
    MemLp f 2 (timeMeasure T) := by
  have hmeas : AEStronglyMeasurable f (timeMeasure T) := by
    unfold timeMeasure
    exact hf.aestronglyMeasurable measurableSet_Icc
  rcases le_or_gt 0 T with hT | hT
  · obtain ⟨t₀, _, ht₀max⟩ :=
      isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) T) ⟨0, ⟨le_refl 0, hT⟩⟩ hf.norm
    refine MemLp.of_bound hmeas ‖f t₀‖ ?_
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ht₀max ht)
  · refine ⟨hmeas, ?_⟩
    rw [timeMeasure_eq_zero_of_nonpos hT.le, eLpNorm_measure_zero]
    exact ENNReal.zero_lt_top

def ofContinuousOn (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) : timeL2 X T :=
  (memLp_of_continuousOn hf).toLp f

theorem coeFn_ofContinuousOn (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) :
    ofContinuousOn hf =ᵐ[timeMeasure T] f :=
  (memLp_of_continuousOn hf).coeFn_toLp

theorem norm_ofContinuousOn_le_of_bound (hf : ContinuousOn f (Set.Icc (0 : ℝ) T))
    {C : ℝ} (hC : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ ≤ C) :
    ‖ofContinuousOn hf‖ ≤ Real.sqrt T * C := by
  have hbound : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ C := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hC)
  rw [ofContinuousOn, Lp.norm_toLp]
  have hle := eLpNorm_le_of_ae_bound (μ := timeMeasure T) (p := 2) hbound
  rcases le_or_gt 0 C with hC0 | hC0
  · refine le_trans (ENNReal.toReal_mono ?_ hle) ?_
    · exact ENNReal.mul_ne_top
        (by rw [timeMeasure_univ]
            exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness))
        ENNReal.ofReal_ne_top
    · rw [ENNReal.toReal_mul, timeMeasure_univ,
        show ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num,
        toReal_ofReal_rpow_half, ENNReal.toReal_ofReal hC0]
  · have hfzero : ∀ᵐ t ∂(timeMeasure T), f t = 0 := by
      filter_upwards [hbound] with t ht
      have : ‖f t‖ = 0 := le_antisymm (le_trans ht hC0.le) (norm_nonneg _)
      exact norm_eq_zero.1 this
    rw [eLpNorm_congr_ae hfzero, eLpNorm_zero', ENNReal.toReal_zero]
    have : 0 ≤ Real.sqrt T * C ∨ Real.sqrt T = 0 := by
      rcases le_or_gt 0 T with hT | hT
      · exact Or.inr (by rcases eq_or_lt_of_le hT with h | h
                         · rw [← h, Real.sqrt_zero]
                         · exact absurd (le_trans (norm_nonneg (f 0))
                             (hC 0 ⟨le_refl 0, hT⟩)) (not_le.2 hC0))
      · exact Or.inr (Real.sqrt_eq_zero'.2 hT.le)
    rcases this with h | h
    · exact h
    · rw [h, zero_mul]

end ContinuousEmbedding

section Const

def const (T : ℝ) (c : X) : timeL2 X T :=
  (memLp_const (μ := timeMeasure T) c).toLp _

theorem coeFn_const (c : X) :
    const T c =ᵐ[timeMeasure T] (fun _ => c) :=
  (memLp_const (μ := timeMeasure T) c).coeFn_toLp

theorem norm_const (T : ℝ) (c : X) :
    ‖const T c‖ = Real.sqrt T * ‖c‖ := by
  rw [const, Lp.norm_toLp]
  rcases le_or_gt 0 T with hT | hT
  · rcases eq_or_lt_of_le hT with hT0 | hTpos
    · rw [timeMeasure_eq_zero_of_nonpos (le_of_eq hT0.symm), eLpNorm_measure_zero,
        ENNReal.toReal_zero, ← hT0, Real.sqrt_zero, zero_mul]
    · rw [eLpNorm_const c (by norm_num) (timeMeasure_ne_zero hTpos), ENNReal.toReal_mul,
        show (1 / ENNReal.toReal 2) = (1 / 2 : ℝ) by norm_num, timeMeasure_univ,
        toReal_ofReal_rpow_half, toReal_enorm, mul_comm]
  · rw [timeMeasure_eq_zero_of_nonpos hT.le, eLpNorm_measure_zero, ENNReal.toReal_zero,
      Real.sqrt_eq_zero'.2 hT.le, zero_mul]

@[simp]
theorem const_zero (T : ℝ) : const T (0 : X) = 0 := by
  rw [← norm_eq_zero, norm_const, norm_zero, mul_zero]

end Const

section IntervalIntegral

theorem integrable (f : timeL2 X T) :
    Integrable (fun t => f t) (timeMeasure T) :=
  (Lp.memLp f).integrable (by norm_num)

theorem integrableOn (f : timeL2 X T) :
    IntegrableOn (fun t => f t) (Set.Icc (0 : ℝ) T) :=
  integrable f

theorem integral_norm_le (f : timeL2 X T) :
    ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ≤ Real.sqrt T * ‖f‖ := by
  have hf1 : MemLp (fun t => f t) 1 (timeMeasure T) :=
    (Lp.memLp f).mono_exponent (by norm_num)
  have hint : ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖
      = (eLpNorm (fun t => f t) 1 (timeMeasure T)).toReal := by
    rw [show (∫ t in Set.Icc (0 : ℝ) T, ‖f t‖) = ∫ t, ‖f t‖ ∂(timeMeasure T) from rfl,
      integral_norm_eq_lintegral_enorm hf1.1, eLpNorm_one_eq_lintegral_enorm]
  rw [hint, Lp.norm_def]
  have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := timeMeasure T) (p := 1) (q := 2) (by norm_num) (Lp.aestronglyMeasurable f)
  have hfin : eLpNorm (fun t => f t) 2 (timeMeasure T)
      * timeMeasure T Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    refine ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) ?_
    rw [timeMeasure_univ]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  refine le_trans (ENNReal.toReal_mono hfin hholder) ?_
  rw [ENNReal.toReal_mul, timeMeasure_univ,
    show (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num,
    toReal_ofReal_rpow_half, mul_comm]

def timeIntegralₗ (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : timeL2 X T →ₗ[ℝ] X where
  toFun f := ∫ t in Set.Icc (0 : ℝ) T, f t
  map_add' f g := by
    rw [← integral_add (integrableOn f) (integrableOn g)]
    refine integral_congr_ae ?_
    filter_upwards [(Lp.coeFn_add f g)] with t ht
    simp only [ht, Pi.add_apply]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [(Lp.coeFn_smul c f)] with t ht
    simp only [ht, Pi.smul_apply]

def timeIntegral (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : timeL2 X T →L[ℝ] X :=
  LinearMap.mkContinuous (timeIntegralₗ X T) (Real.sqrt T) (fun f => by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    exact integral_norm_le f)

@[simp]
theorem timeIntegral_apply (f : timeL2 X T) :
    timeIntegral X T f = ∫ t in Set.Icc (0 : ℝ) T, f t :=
  rfl

theorem norm_timeIntegral_le (f : timeL2 X T) :
    ‖∫ t in Set.Icc (0 : ℝ) T, f t‖ ≤ Real.sqrt T * ‖f‖ := by
  rw [← timeIntegral_apply]
  refine le_trans ((timeIntegral X T).le_opNorm f) ?_
  exact mul_le_mul_of_nonneg_right
    (LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg T) _) (norm_nonneg _)

theorem norm_timeIntegral_clm_le (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (T : ℝ) :
    ‖timeIntegral X T‖ ≤ Real.sqrt T :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg T) _

theorem timeIntegral_const {T : ℝ} (hT : 0 ≤ T) (c : X) :
    timeIntegral X T (const T c) = T • c := by
  rw [timeIntegral_apply,
    integral_congr_ae (g := fun _ => c)
      (by filter_upwards [coeFn_const (T := T) c] with t ht using ht),
    setIntegral_const, measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT]

end IntervalIntegral

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
