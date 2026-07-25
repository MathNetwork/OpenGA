import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Covering.OneDim


noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped ENNReal NNReal Topology InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

section VectorLebesgueDifferentiation

open IsUnifLocDoublingMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem average_Icc_eq {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) :
    (⨍ t in Icc a b, f t) = (b - a)⁻¹ • ∫ t in Icc a b, f t := by
  rw [setAverage_eq, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]

omit [CompleteSpace E] in
private theorem slope_integral_eq_average_right {f : ℝ → E}
    (hg : ∀ a b : ℝ, IntervalIntegrable f volume a b) (c x y : ℝ) (hxy : x ≤ y) :
    slope (fun u => ∫ t in c..u, f t) x y = ⨍ t in Icc x y, f t := by
  rw [average_Icc_eq hxy, slope_def_module, integral_interval_sub_left (hg c y) (hg c x),
    integral_of_le hxy, integral_Icc_eq_integral_Ioc]

omit [CompleteSpace E] in
private theorem slope_integral_eq_average_left {f : ℝ → E}
    (hg : ∀ a b : ℝ, IntervalIntegrable f volume a b) (c x y : ℝ) (hyx : y ≤ x) :
    slope (fun u => ∫ t in c..u, f t) x y = ⨍ t in Icc y x, f t := by
  rw [average_Icc_eq hyx, slope_def_module, integral_Icc_eq_integral_Ioc,
    ← integral_of_le hyx, ← integral_interval_sub_left (hg c x) (hg c y),
    ← neg_sub x y, inv_neg, neg_smul, ← smul_neg, neg_sub]

theorem locallyIntegrable_ae_hasDerivAt_integral
    {f : ℝ → E} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  have hg : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average hf
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  refine ⟨?_, ?_⟩
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp (Real.tendsto_Icc_vitaliFamily_left x))
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact slope_integral_eq_average_left hg c x y (le_of_lt hy)
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp (Real.tendsto_Icc_vitaliFamily_right x))
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact slope_integral_eq_average_right hg c x y (le_of_lt hy)

end VectorLebesgueDifferentiation

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

def timeH1 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : Type _ :=
  WithLp 2 (X × timeL2 X T)

namespace timeH1

instance : NormedAddCommGroup (timeH1 X T) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (X × timeL2 X T)))

instance : NormedSpace ℝ (timeH1 X T) :=
  inferInstanceAs (NormedSpace ℝ (WithLp 2 (X × timeL2 X T)))

instance : InnerProductSpace ℝ (timeH1 X T) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (X × timeL2 X T)))

instance : CompleteSpace (timeH1 X T) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (X × timeL2 X T)))

def mk (u₀ : X) (v : timeL2 X T) : timeH1 X T :=
  WithLp.toLp 2 (u₀, v)

def init (u : timeH1 X T) : X :=
  (WithLp.ofLp u).1

def deriv (u : timeH1 X T) : timeL2 X T :=
  (WithLp.ofLp u).2

@[simp]
theorem init_mk (u₀ : X) (v : timeL2 X T) : (mk u₀ v).init = u₀ := rfl

@[simp]
theorem deriv_mk (u₀ : X) (v : timeL2 X T) : (mk u₀ v).deriv = v := rfl

@[simp]
theorem mk_init_deriv (u : timeH1 X T) : mk u.init u.deriv = u := rfl

@[ext]
theorem ext {u w : timeH1 X T} (hinit : u.init = w.init) (hderiv : u.deriv = w.deriv) :
    u = w := by
  rw [← mk_init_deriv u, ← mk_init_deriv w, hinit, hderiv]

@[simp]
theorem init_add (u w : timeH1 X T) : (u + w).init = u.init + w.init := rfl

@[simp]
theorem deriv_add (u w : timeH1 X T) : (u + w).deriv = u.deriv + w.deriv := rfl

@[simp]
theorem init_smul (c : ℝ) (u : timeH1 X T) : (c • u).init = c • u.init := rfl

@[simp]
theorem deriv_smul (c : ℝ) (u : timeH1 X T) : (c • u).deriv = c • u.deriv := rfl

@[simp]
theorem init_zero : (0 : timeH1 X T).init = 0 := rfl

@[simp]
theorem deriv_zero : (0 : timeH1 X T).deriv = 0 := rfl

theorem inner_def (u w : timeH1 X T) :
    (inner ℝ u w : ℝ) = inner ℝ u.init w.init + inner ℝ u.deriv w.deriv :=
  rfl

theorem norm_sq_eq (u : timeH1 X T) :
    ‖u‖ ^ 2 = ‖u.init‖ ^ 2 + ‖u.deriv‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

theorem norm_init_le (u : timeH1 X T) : ‖u.init‖ ≤ ‖u‖ := by
  have h := norm_sq_eq u
  nlinarith [norm_nonneg u.init, norm_nonneg u.deriv, norm_nonneg u, sq_nonneg ‖u.deriv‖]

theorem norm_deriv_le (u : timeH1 X T) : ‖u.deriv‖ ≤ ‖u‖ := by
  have h := norm_sq_eq u
  nlinarith [norm_nonneg u.init, norm_nonneg u.deriv, norm_nonneg u, sq_nonneg ‖u.init‖]

def trace0 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : timeH1 X T →L[ℝ] X :=
  WithLp.fstL 2 ℝ X (timeL2 X T)

def timeDeriv (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : timeH1 X T →L[ℝ] timeL2 X T :=
  WithLp.sndL 2 ℝ X (timeL2 X T)

@[simp]
theorem trace0_apply (u : timeH1 X T) : trace0 X T u = u.init := rfl

@[simp]
theorem timeDeriv_apply (u : timeH1 X T) : timeDeriv X T u = u.deriv := rfl

@[simp]
theorem trace0_mk (u₀ : X) (v : timeL2 X T) : trace0 X T (mk u₀ v) = u₀ := rfl

@[simp]
theorem timeDeriv_mk (u₀ : X) (v : timeL2 X T) : timeDeriv X T (mk u₀ v) = v := rfl

def toFun (u : timeH1 X T) : ℝ → X :=
  fun t => u.init + ∫ s in (0 : ℝ)..t, u.deriv s

@[simp]
theorem toFun_apply (u : timeH1 X T) (t : ℝ) :
    u.toFun t = u.init + ∫ s in (0 : ℝ)..t, u.deriv s :=
  rfl

@[simp]
theorem toFun_zero (u : timeH1 X T) : u.toFun 0 = u.init := by
  simp [toFun]

theorem intervalIntegrable_deriv {a b : ℝ} (u : timeH1 X T)
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => u.deriv s) volume a b := by
  have hsub : uIcc a b ⊆ Icc (0 : ℝ) T :=
    uIcc_subset_Icc ha hb
  refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
  exact (TimeSobolev.integrableOn u.deriv).mono_set hsub

theorem continuousOn_toFun (u : timeH1 X T) :
    ContinuousOn u.toFun (Icc (0 : ℝ) T) := by
  rcases le_or_gt 0 T with hT | hT
  · have hcont : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, u.deriv s) (Icc (0 : ℝ) T) := by
      have h := continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
        (f := fun s => u.deriv s) (μ := volume)
        (by
          rw [uIcc_of_le hT]
          exact TimeSobolev.integrableOn u.deriv)
      rwa [uIcc_of_le hT] at h
    exact continuousOn_const.add hcont
  · rw [Icc_eq_empty (by linarith)]
    exact continuousOn_empty _

theorem continuousWithinAt_toFun (u : timeH1 X T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContinuousWithinAt u.toFun (Icc (0 : ℝ) T) t :=
  u.continuousOn_toFun t ht

theorem toFun_eq_trace0_add_integral (u : timeH1 X T) (t : ℝ) :
    u.toFun t = trace0 X T u + ∫ s in (0 : ℝ)..t, (timeDeriv X T u) s :=
  rfl

theorem toFun_sub_toFun (u : timeH1 X T) {t₀ t₁ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (ht₁ : t₁ ∈ Icc (0 : ℝ) T) :
    u.toFun t₁ - u.toFun t₀ = ∫ s in t₀..t₁, u.deriv s := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := by
    refine ⟨le_rfl, ?_⟩
    rcases ht₀ with ⟨h0t₀, ht₀T⟩
    linarith
  simp only [toFun_apply]
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (u.intervalIntegrable_deriv h0 ht₁) (u.intervalIntegrable_deriv h0 ht₀)

theorem hasDerivWithinAt_toFun_of_continuousOn (u : timeH1 X T) {g : ℝ → X}
    (hg : ContinuousOn g (Icc (0 : ℝ) T)) (hrep : u.deriv =ᵐ[timeMeasure T] g)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt u.toFun (g t) (Icc (0 : ℝ) T) t := by
  rcases le_or_gt 0 T with hT | hT
  · have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hgIcc : IntegrableOn g (Icc (0 : ℝ) T) volume :=
      (TimeSobolev.memLp_of_continuousOn hg).integrable (by norm_num)
    have hrepvol : (fun r => u.deriv r) =ᵐ[volume.restrict (Icc (0 : ℝ) T)] g := hrep
    have hae : ∀ s ∈ Icc (0 : ℝ) T, (∫ r in (0 : ℝ)..s, u.deriv r)
        = ∫ r in (0 : ℝ)..s, g r := by
      intro s hs
      refine intervalIntegral.integral_congr_ae ?_
      have hsub : Set.uIoc (0 : ℝ) s ⊆ Icc (0 : ℝ) T := by
        intro r hr
        rw [Set.uIoc, min_eq_left hs.1, max_eq_right hs.1] at hr
        exact ⟨le_of_lt hr.1, le_trans hr.2 hs.2⟩
      have hrestr : (fun r => u.deriv r) =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) s)] g :=
        hrepvol.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
      exact ae_imp_of_ae_restrict hrestr
    have hderiv : HasDerivWithinAt (fun s => ∫ r in (0 : ℝ)..s, g r) (g t)
        (Icc (0 : ℝ) T) t := by
      haveI hfact : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
      have hint : IntervalIntegrable g volume 0 t :=
        MeasureTheory.IntegrableOn.intervalIntegrable (by
          rw [uIcc_of_le ht.1]
          exact hgIcc.mono_set (Icc_subset_Icc le_rfl ht.2))
      have hmeas : StronglyMeasurableAtFilter g (𝓝[Icc (0 : ℝ) T] t) volume :=
        ⟨Icc (0 : ℝ) T, self_mem_nhdsWithin,
          (hg.aestronglyMeasurable measurableSet_Icc)⟩
      have hcont : ContinuousWithinAt g (Icc (0 : ℝ) T) t := hg t ht
      exact intervalIntegral.integral_hasDerivWithinAt_right hint hmeas hcont
    have hderiv' : HasDerivWithinAt (fun s => ∫ r in (0 : ℝ)..s, u.deriv r) (g t)
        (Icc (0 : ℝ) T) t :=
      hderiv.congr (fun s hs => hae s hs) (hae t ht)
    have := hderiv'.const_add u.init
    simpa only [toFun] using this
  · rw [Icc_eq_empty (by linarith)] at ht
    exact absurd ht (notMem_empty t)

theorem ae_hasDerivWithinAt_toFun (u : timeH1 X T) :
    ∀ᵐ t ∂(timeMeasure T), HasDerivWithinAt u.toFun (u.deriv t) (Icc (0 : ℝ) T) t := by
  rcases le_or_gt 0 T with hT | hT
  · have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hac : timeMeasure T ≪ volume :=
      Measure.absolutelyContinuous_of_le (Measure.restrict_le_self)
    set v : ℝ → X := fun s => if s ∈ Ioc (0 : ℝ) T then u.deriv s else 0 with hv_def
    have hvint : IntegrableOn v (Ioc (0 : ℝ) T) volume := by
      have hcongr : IntegrableOn (fun s => u.deriv s) (Ioc (0 : ℝ) T) volume :=
        (TimeSobolev.integrableOn u.deriv).mono_set Ioc_subset_Icc_self
      refine hcongr.congr_fun ?_ measurableSet_Ioc
      intro s hs
      simp only [hv_def, if_pos hs]
    have hvloc : LocallyIntegrable v volume := by
      refine Integrable.locallyIntegrable ?_
      refine (integrableOn_iff_integrable_of_support_subset (s := Ioc (0 : ℝ) T) ?_).1 hvint
      intro s hs
      by_contra hmem
      apply hs
      simp only [hv_def, if_neg hmem]
    have hLDT := locallyIntegrable_ae_hasDerivAt_integral hvloc
    have hLDT' : ∀ᵐ t ∂(timeMeasure T), ∀ c, HasDerivAt
        (fun x => ∫ r in c..x, v r) (v t) t := hac hLDT
    have hne0 : ∀ᵐ t ∂(timeMeasure T), t ≠ 0 :=
      hac (ae_iff.mpr (by simp))
    have hneT : ∀ᵐ t ∂(timeMeasure T), t ≠ T :=
      hac (ae_iff.mpr (by simp))
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hLDT', hne0, hneT, hmem] with t ht htne0 htneT htmem
    have htIoo : t ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_le_of_ne htmem.1 (Ne.symm htne0), lt_of_le_of_ne htmem.2 htneT⟩
    have hae : ∀ s ∈ Ioo (0 : ℝ) T,
        (∫ r in (0 : ℝ)..s, v r) = ∫ r in (0 : ℝ)..s, u.deriv r := by
      intro s hs
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with r hr
      rw [Set.uIoc, min_eq_left (le_of_lt hs.1), max_eq_right (le_of_lt hs.1)] at hr
      have hrIoc : r ∈ Ioc (0 : ℝ) T :=
        ⟨hr.1, le_trans hr.2 (le_of_lt hs.2)⟩
      simp only [hv_def, if_pos hrIoc]
    have htIoc : t ∈ Ioc (0 : ℝ) T := ⟨htIoo.1, le_of_lt htIoo.2⟩
    have hvt : v t = u.deriv t := by simp only [hv_def, if_pos htIoc]
    have hderiv_v : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, v r) (v t) t := ht 0
    have hderiv_u : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, u.deriv r)
        (u.deriv t) t := by
      have heq : (fun s => ∫ r in (0 : ℝ)..s, u.deriv r)
          =ᶠ[𝓝 t] fun s => ∫ r in (0 : ℝ)..s, v r := by
        filter_upwards [Ioo_mem_nhds htIoo.1 htIoo.2] with s hs using (hae s hs).symm
      exact hvt ▸ (hderiv_v.congr_of_eventuallyEq heq)
    exact (hderiv_u.const_add u.init).hasDerivWithinAt
  · have hbot : ae (timeMeasure T) = ⊥ :=
      MeasureTheory.ae_eq_bot.mpr (timeMeasure_eq_zero_of_nonpos (le_of_lt hT))
    rw [Filter.eventually_iff, hbot]
    exact Filter.mem_bot

theorem norm_toFun_le (u : timeH1 X T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ≤ ‖trace0 X T u‖ + Real.sqrt T * ‖timeDeriv X T u‖ := by
  rcases ht with ⟨ht0, htT⟩
  have hTnn : (0 : ℝ) ≤ T := le_trans ht0 htT
  have hint_eq : (∫ s in (0 : ℝ)..t, u.deriv s) = ∫ s in Ioc (0 : ℝ) t, u.deriv s :=
    intervalIntegral.integral_of_le ht0
  have hnorm_int : ‖∫ s in (0 : ℝ)..t, u.deriv s‖ ≤ ∫ s in Ioc (0 : ℝ) t, ‖u.deriv s‖ := by
    rw [hint_eq]
    exact norm_integral_le_integral_norm _
  have hmono : (∫ s in Ioc (0 : ℝ) t, ‖u.deriv s‖) ≤ ∫ s in Icc (0 : ℝ) T, ‖u.deriv s‖ := by
    have hintT : IntegrableOn (fun s => ‖u.deriv s‖) (Icc (0 : ℝ) T) volume :=
      (TimeSobolev.integrableOn u.deriv).norm
    refine setIntegral_mono_set hintT ?_ ?_
    · filter_upwards with s using norm_nonneg _
    · refine HasSubset.Subset.eventuallyLE ?_
      intro s hs
      exact ⟨le_of_lt hs.1, le_trans hs.2 htT⟩
  have hCS : (∫ s in Icc (0 : ℝ) T, ‖u.deriv s‖) ≤ Real.sqrt T * ‖u.deriv‖ :=
    TimeSobolev.integral_norm_le u.deriv
  calc ‖u.toFun t‖ = ‖u.init + ∫ s in (0 : ℝ)..t, u.deriv s‖ := rfl
    _ ≤ ‖u.init‖ + ‖∫ s in (0 : ℝ)..t, u.deriv s‖ := norm_add_le _ _
    _ ≤ ‖u.init‖ + ∫ s in Ioc (0 : ℝ) t, ‖u.deriv s‖ := by gcongr
    _ ≤ ‖u.init‖ + ∫ s in Icc (0 : ℝ) T, ‖u.deriv s‖ := by gcongr
    _ ≤ ‖u.init‖ + Real.sqrt T * ‖u.deriv‖ := by gcongr
    _ = ‖trace0 X T u‖ + Real.sqrt T * ‖timeDeriv X T u‖ := rfl

theorem norm_toFun_le_norm (u : timeH1 X T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.toFun t‖ ≤ (1 + Real.sqrt T) * ‖u‖ := by
  have hbase := u.norm_toFun_le ht
  have hinit : ‖trace0 X T u‖ ≤ ‖u‖ := by
    rw [trace0_apply]; exact u.norm_init_le
  have hderiv : ‖timeDeriv X T u‖ ≤ ‖u‖ := by
    rw [timeDeriv_apply]; exact u.norm_deriv_le
  have hsqrt : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg T
  calc ‖u.toFun t‖ ≤ ‖trace0 X T u‖ + Real.sqrt T * ‖timeDeriv X T u‖ := hbase
    _ ≤ ‖u‖ + Real.sqrt T * ‖u‖ := by
        refine add_le_add hinit ?_
        exact mul_le_mul_of_nonneg_left hderiv hsqrt
    _ = (1 + Real.sqrt T) * ‖u‖ := by ring

def toFunL2 (u : timeH1 X T) : timeL2 X T :=
  TimeSobolev.ofContinuousOn u.continuousOn_toFun

theorem norm_toFunL2_le (u : timeH1 X T) :
    ‖u.toFunL2‖ ≤ Real.sqrt T * ((1 + Real.sqrt T) * ‖u‖) := by
  rw [toFunL2]
  refine TimeSobolev.norm_ofContinuousOn_le_of_bound u.continuousOn_toFun ?_
  intro t ht
  exact u.norm_toFun_le_norm ht

theorem toFun_add (u w : timeH1 X T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (u + w).toFun t = u.toFun t + w.toFun t := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hsplit : ∫ s in (0 : ℝ)..t, ((u + w).deriv) s
      = (∫ s in (0 : ℝ)..t, u.deriv s) + ∫ s in (0 : ℝ)..t, w.deriv s := by
    have hcongr : ∫ s in (0 : ℝ)..t, ((u + w).deriv) s
        = ∫ s in (0 : ℝ)..t, (u.deriv s + w.deriv s) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hae : ⇑((u + w).deriv) =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
          (fun s => u.deriv s + w.deriv s) := by
        have hd : ((u + w).deriv : timeL2 X T) = u.deriv + w.deriv := deriv_add u w
        have := Lp.coeFn_add (u.deriv) (w.deriv)
        rw [hd]
        filter_upwards [this] with s hs using hs
      have hsub : Set.uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := by
        intro r hr
        rw [Set.uIoc, min_eq_left ht.1, max_eq_right ht.1] at hr
        exact ⟨le_of_lt hr.1, le_trans hr.2 ht.2⟩
      exact ae_imp_of_ae_restrict
        (hae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    rw [hcongr]
    exact intervalIntegral.integral_add
      (u.intervalIntegrable_deriv h0 ht) (w.intervalIntegrable_deriv h0 ht)
  simp only [toFun_apply, init_add, hsplit]
  abel

theorem toFun_smul (c : ℝ) (u : timeH1 X T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (c • u).toFun t = c • u.toFun t := by
  have hsmul : ∫ s in (0 : ℝ)..t, ((c • u).deriv) s
      = c • ∫ s in (0 : ℝ)..t, u.deriv s := by
    have hcongr : ∫ s in (0 : ℝ)..t, ((c • u).deriv) s
        = ∫ s in (0 : ℝ)..t, (c • u.deriv s) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hae : ⇑((c • u).deriv) =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
          (fun s => c • u.deriv s) := by
        have hd : ((c • u).deriv : timeL2 X T) = c • u.deriv := deriv_smul c u
        have := Lp.coeFn_smul c (u.deriv)
        rw [hd]
        filter_upwards [this] with s hs using hs
      have hsub : Set.uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := by
        intro r hr
        rw [Set.uIoc, min_eq_left ht.1, max_eq_right ht.1] at hr
        exact ⟨le_of_lt hr.1, le_trans hr.2 ht.2⟩
      exact ae_imp_of_ae_restrict
        (hae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    rw [hcongr, intervalIntegral.integral_smul]
  simp only [toFun_apply, init_smul, hsmul, smul_add]

def toTimeL2ₗ (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : timeH1 X T →ₗ[ℝ] timeL2 X T where
  toFun u := u.toFunL2
  map_add' u w := by
    refine Lp.ext ?_
    have huw : ⇑((u + w).toFunL2) =ᵐ[timeMeasure T] (u + w).toFun :=
      TimeSobolev.coeFn_ofContinuousOn (u + w).continuousOn_toFun
    have hu : ⇑(u.toFunL2) =ᵐ[timeMeasure T] u.toFun :=
      TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
    have hw : ⇑(w.toFunL2) =ᵐ[timeMeasure T] w.toFun :=
      TimeSobolev.coeFn_ofContinuousOn w.continuousOn_toFun
    have hadd := Lp.coeFn_add (u.toFunL2) (w.toFunL2)
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [huw, hu, hw, hadd, hmem] with t htuw htu htw htadd htmem
    rw [htuw, htadd, Pi.add_apply, htu, htw, toFun_add u w htmem]
  map_smul' c u := by
    refine Lp.ext ?_
    have hcu : ⇑((c • u).toFunL2) =ᵐ[timeMeasure T] (c • u).toFun :=
      TimeSobolev.coeFn_ofContinuousOn (c • u).continuousOn_toFun
    have hu : ⇑(u.toFunL2) =ᵐ[timeMeasure T] u.toFun :=
      TimeSobolev.coeFn_ofContinuousOn u.continuousOn_toFun
    have hsmul := Lp.coeFn_smul c (u.toFunL2)
    have hmem : ∀ᵐ t ∂(timeMeasure T), t ∈ Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hcu, hu, hsmul, hmem] with t htcu htu htsmul htmem
    rw [htcu, RingHom.id_apply, htsmul, Pi.smul_apply, htu, toFun_smul c u htmem]

def toTimeL2 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : timeH1 X T →L[ℝ] timeL2 X T :=
  LinearMap.mkContinuous (toTimeL2ₗ X T) (Real.sqrt T * (1 + Real.sqrt T)) (fun u => by
    have h := u.norm_toFunL2_le
    rwa [← mul_assoc] at h)

@[simp]
theorem toTimeL2_apply (u : timeH1 X T) : toTimeL2 X T u = u.toFunL2 := rfl

theorem norm_toTimeL2_le (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (T : ℝ) :
    ‖toTimeL2 X T‖ ≤ Real.sqrt T * (1 + Real.sqrt T) :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (Real.sqrt_nonneg T) (by positivity)) _

end timeH1

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
