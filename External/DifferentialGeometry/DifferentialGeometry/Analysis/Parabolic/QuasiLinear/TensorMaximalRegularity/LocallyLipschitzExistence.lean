import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzModulusOfContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionFieldLink
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceEnergy

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

def recentredCarrier (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeH1 (tensorHs (I := I) (M := M) g r s a) T :=
  TimeSobolev.timeH1.mk (0 : tensorHs (I := I) (M := M) g r s a)
    (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv

def recentredHiL2 (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T :=
  maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce -
    TimeSobolev.const T u₀

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem recentredCarrier_toFun_coeff (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ((recentredCarrier (I := I) (M := M) hT hT1 u₀ gforce).toFun t).coeff i =
      ∫ s in (0 : ℝ)..t,
        ((maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv s).coeff i := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  set lo := recentredCarrier (I := I) (M := M) hT hT1 u₀ gforce with hlo_def
  have hderiv : lo.deriv = (maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv := by
    rw [hlo_def, recentredCarrier, TimeSobolev.timeH1.deriv_mk]
  rw [← hderiv]
  have hcomm : ∫ s in (0 : ℝ)..t, (lo.deriv s).coeff i =
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
        (∫ s in (0 : ℝ)..t, lo.deriv s) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
      (lo.intervalIntegrable_deriv h0 ht)]
    rfl
  have hval : (lo.toFun t).coeff i =
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i) (lo.toFun t) := rfl
  rw [hval, TimeSobolev.timeH1.toFun_apply, map_add, hcomm]
  have hinit : lo.init = (0 : tensorHs (I := I) (M := M) g r s a) := by
    rw [hlo_def, recentredCarrier, TimeSobolev.timeH1.init_mk]
  rw [hinit, map_zero, zero_add]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem recentred_link (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ∀ᵐ t ∂(timeMeasure T),
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith)
          (recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce t) =
        (recentredCarrier (I := I) (M := M) hT hT1 u₀ gforce).toFun t := by
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
    MaximalRegularity.countable_tensorEigenIdx (I := I) (M := M)
      (g := g) (r := r) (s := s) h_compact
  have hper : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ∀ᵐ t ∂(timeMeasure T),
        (recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce t).coeff i =
          ((recentredCarrier (I := I) (M := M) hT hT1 u₀ gforce).toFun t).coeff i := by
    intro i
    have hsub := Lp.coeFn_sub
      (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce)
      (TimeSobolev.const T u₀)
    have hconst := TimeSobolev.coeFn_const (X := tensorHs (I := I) (M := M) g r s (a + 2))
      (T := T) u₀
    have hstruct := maxRegDuhamelSolField_coeff_ae (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 u₀ gforce i
    filter_upwards [hsub, hconst, hstruct,
      ae_restrict_mem (μ := volume) measurableSet_Icc] with t htsub htconst htstruct htmem
    have hlhs : (recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce t).coeff i =
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce t).coeff i -
          u₀.coeff i := by
      rw [recentredHiL2, htsub, Pi.sub_apply, htconst]
      simp only [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
    rw [hlhs, htstruct,
      recentredCarrier_toFun_coeff (I := I) (M := M) hT hT1 u₀ gforce i htmem]
    ring
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply]
  exact ht i

def maxRegRecentredCrossScaleField (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    CrossScaleField (I := I) (M := M) g r s a T where
  hiL2 := recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce
  lo := recentredCarrier (I := I) (M := M) hT hT1 u₀ gforce
  link := recentred_link (I := I) (M := M) (h_compact := h_compact) hT hT1 u₀ gforce

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem recentred_repr_zero (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (maxRegRecentredCrossScaleField (I := I) (M := M)
        (h_compact := h_compact) hT hT1 u₀ gforce).repr 0 =
      (0 : tensorHs (I := I) (M := M) g r s (a + 1)) := by
  set u := maxRegRecentredCrossScaleField (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce with hu_def
  refine tensorHs.ext ?_
  funext i
  rw [u.repr_coeff hT ⟨le_rfl, hT.le⟩ i, tensorHs.zero_coeff]
  change (u.lo.toFun 0).coeff i = 0
  rw [TimeSobolev.timeH1.toFun_zero]
  change (recentredCarrier (I := I) (M := M) hT hT1 u₀ gforce).init.coeff i = 0
  rw [recentredCarrier, TimeSobolev.timeH1.init_mk, tensorHs.zero_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem recentred_repr_eq_field_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ∀ᵐ t ∂(timeMeasure T),
      (maxRegRecentredCrossScaleField (I := I) (M := M)
          (h_compact := h_compact) hT hT1 u₀ gforce).repr t =
        maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce t -
          tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀ := by
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
    MaximalRegularity.countable_tensorEigenIdx (I := I) (M := M)
      (g := g) (r := r) (s := s) h_compact
  set u := maxRegRecentredCrossScaleField (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce with hu_def
  have hper : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ∀ᵐ t ∂(timeMeasure T),
        (u.repr t).coeff i =
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce t).coeff i -
            u₀.coeff i := by
    intro i
    have hHa1 := timeModeCoeff_coeFn (I := I) (M := M)
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) i
    have hHa1mode : timeModeCoeff (I := I) (M := M)
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) i =
          homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i +
            solModeCoeff (I := I) (M := M) (a := a) hT.le gforce i := by
      rw [maxRegDuhamelSolFieldHa1, timeModeCoeff_add (I := I) (M := M),
        maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M) (a := a)
          (T := T) hT.le u₀ i,
        maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
          (h_compact := h_compact) (a := a) hT hT1 gforce i]
    have haddcoe := Lp.coeFn_add
      (homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i)
      (solModeCoeff (I := I) (M := M) (a := a) hT.le gforce i)
    have hA := homModeCoeff_eq_init_add_integral (I := I) (M := M) (a := a) (T := T) u₀ i
    have hB := solModeCoeff_eq_integral (I := I) (M := M) (a := a) hT.le gforce i
    filter_upwards [hHa1, haddcoe, hA, hB,
      ae_restrict_mem (μ := volume) measurableSet_Icc] with t htHa1 htadd htA htB htmem
    have hfield : (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce t).coeff i =
        u₀.coeff i + (∫ s in (0 : ℝ)..t,
            (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s) +
          ∫ s in (0 : ℝ)..t, (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) s := by
      rw [← htHa1, hHa1mode, htadd, Pi.add_apply, htA, htB]
    have hrepr : (u.repr t).coeff i =
        ∫ s in (0 : ℝ)..t,
          ((maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv s).coeff i := by
      rw [u.repr_coeff hT htmem i]
      exact recentredCarrier_toFun_coeff (I := I) (M := M) hT hT1 u₀ gforce i htmem
    have hsplit_int : (∫ s in (0 : ℝ)..t,
          ((maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv s).coeff i) =
        (∫ s in (0 : ℝ)..t,
            (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s) +
          ∫ s in (0 : ℝ)..t, (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) s := by
      have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans htmem.1 htmem.2⟩
      have hint_hom : IntervalIntegrable
          (fun s => (homDerivModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) s)
          volume 0 t :=
        ((TimeSobolev.integrableOn _).mono_set (uIcc_subset_Icc h0 htmem)).intervalIntegrable
      have hint_duh : IntervalIntegrable
          (fun s => (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) s)
          volume 0 t :=
        ((TimeSobolev.integrableOn _).mono_set (uIcc_subset_Icc h0 htmem)).intervalIntegrable
      rw [← intervalIntegral.integral_add hint_hom hint_duh]
      refine intervalIntegral.integral_congr_ae ?_
      have hderiv_coe := maxRegDuhamelMap_deriv_coeff_ae (I := I) (M := M)
        (h_compact := h_compact) (a := a) hT hT1 u₀ gforce i
      have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
        (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0 htmem)
      have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_coe
      rw [ae_restrict_iff' measurableSet_uIoc] at hae
      filter_upwards [hae] with s hs hsmem
      rw [hs hsmem]
    rw [hrepr, hsplit_int, hfield]
    ring
  rw [← MeasureTheory.ae_all_iff] at hper
  filter_upwards [hper] with t ht
  refine tensorHs.ext ?_
  funext i
  have hti := ht i
  simp only [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff,
    tensorHsInclusion_coeff_apply]
  rw [← sub_eq_add_neg]
  exact hti

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_const_top
    (c : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M) (TimeSobolev.const T c) i =
      TimeSobolev.const T (c.coeff i) := by
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn (I := I) (M := M) (TimeSobolev.const T c) i
  have hconst := TimeSobolev.coeFn_const (X := tensorHs (I := I) (M := M) g r s (a + 2))
    (T := T) c
  have hrhs := TimeSobolev.coeFn_const (X := ℝ) (T := T) (c.coeff i)
  filter_upwards [hlhs, hconst, hrhs] with t htlhs htconst htrhs
  rw [htlhs, htconst, htrhs]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_timeModeCoeff_const_top_sq
    (c : tensorHs (I := I) (M := M) g r s (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) (hT : 0 ≤ T) :
    ‖timeModeCoeff (I := I) (M := M) (TimeSobolev.const T c) i‖ ^ 2 =
      T * (c.coeff i) ^ 2 := by
  rw [timeModeCoeff_const_top, TimeSobolev.norm_const, mul_pow, Real.sq_sqrt hT,
    Real.norm_eq_abs, sq_abs]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneousSolField_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (hT : 0 ≤ T) :
    ‖maxRegHomogeneousSolField (I := I) (M := M) a T u₀‖ ≤
      Real.sqrt T * ‖u₀‖ := by
  rw [show Real.sqrt T * ‖u₀‖ = 1 * ‖TimeSobolev.const T u₀‖ by
    rw [TimeSobolev.norm_const, one_mul]]
  refine norm_le_of_weighted_perMode_le (I := I) (M := M)
    (a := a + 2) (b := a + 2) (h_compact := h_compact) (C := 1) (by norm_num) _ _ (fun i => ?_)
  rw [maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT u₀ i,
    norm_timeModeCoeff_const_top_sq (I := I) (M := M) (a := a) u₀ i hT, one_pow, one_mul,
    mul_left_comm]
  exact weighted_homModeCoeff_le (I := I) (M := M) (a := a) (T := T) hT u₀ i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegHomogeneousDerivField_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2)) (hT : 0 ≤ T) :
    ‖maxRegHomogeneousDerivField (I := I) (M := M) a T u₀‖ ≤
      Real.sqrt T * ‖u₀‖ := by
  rw [show Real.sqrt T * ‖u₀‖ = 1 * ‖TimeSobolev.const T u₀‖ by
    rw [TimeSobolev.norm_const, one_mul]]
  refine norm_le_of_weighted_perMode_le (I := I) (M := M)
    (a := a + 2) (b := a) (h_compact := h_compact) (C := 1) (by norm_num) _ _ (fun i => ?_)
  rw [maxRegHomogeneousDerivField_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT u₀ i,
    norm_timeModeCoeff_const_top_sq (I := I) (M := M) (a := a) u₀ i hT, one_pow, one_mul,
    mul_left_comm]
  exact weighted_homDerivModeCoeff_le (I := I) (M := M) (a := a) (T := T) hT u₀ i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularitySolField_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (hT : 0 ≤ T) (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularitySolField (I := I) (M := M) a hT f‖ ≤ (1 + T) * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (I := I) (M := M)
    (a := a) (b := a + 2) (h_compact := h_compact) (C := 1 + T)
    (by linarith) _ f (fun i => ?_)
  rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT f i]
  exact weighted_solModeCoeff_le (I := I) (M := M) (a := a) hT f i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalRegularityDerivField_norm_le
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (hT : 0 ≤ T) (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maximalRegularityDerivField (I := I) (M := M) a hT f‖ ≤ 2 * ‖f‖ := by
  refine norm_le_of_weighted_perMode_le (I := I) (M := M)
    (a := a) (b := a) (h_compact := h_compact) (C := 2) (by norm_num) _ f (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT f i]
  exact weighted_derivModeCoeff_le (I := I) (M := M) (a := a) hT f i

theorem timeL2_norm_le_of_ae_bound
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f : timeL2 X T) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ s ∂(timeMeasure T), ‖f s‖ ≤ C) :
    ‖f‖ ≤ Real.sqrt T * C := by
  rw [show (‖f‖ : ℝ) = (eLpNorm f 2 (timeMeasure T)).toReal from rfl]
  have hle := eLpNorm_le_of_ae_bound (μ := timeMeasure T) (p := 2) hbound
  refine le_trans (ENNReal.toReal_mono ?_ hle) ?_
  · exact ENNReal.mul_ne_top
      (by rw [TimeSobolev.timeMeasure_univ]
          exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness))
      ENNReal.ofReal_ne_top
  · rw [ENNReal.toReal_mul, TimeSobolev.timeMeasure_univ,
      show ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num,
      TimeSobolev.toReal_ofReal_rpow_half, ENNReal.toReal_ofReal hC]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem truncatedNonlin_norm_le {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {u₀' : tensorHs (I := I) (M := M) g r s (a + 1)}
    (hN : LipschitzOnWith L_R N (Metric.closedBall u₀' R))
    (v : tensorHs (I := I) (M := M) g r s (a + 1)) :
    ‖truncatedNonlin (I := I) (M := M) N u₀' R v‖ ≤ ‖N u₀'‖ + (L_R : ℝ) * R := by
  have hρmem : recenteredBallRetraction u₀' R v ∈ Metric.closedBall u₀' R :=
    recenteredBallRetraction_mapsTo (X := _) hR u₀' (Set.mem_univ v)
  have hcentre : u₀' ∈ Metric.closedBall u₀' R := Metric.mem_closedBall_self hR
  have hdist : dist (recenteredBallRetraction u₀' R v) u₀' ≤ R := by
    rw [← Metric.mem_closedBall]; exact hρmem
  have hlip : ‖N (recenteredBallRetraction u₀' R v) - N u₀'‖ ≤ (L_R : ℝ) * R := by
    rw [← dist_eq_norm]
    refine le_trans (hN.dist_le_mul _ hρmem _ hcentre) ?_
    exact mul_le_mul_of_nonneg_left hdist L_R.coe_nonneg
  calc ‖truncatedNonlin (I := I) (M := M) N u₀' R v‖
      = ‖N (recenteredBallRetraction u₀' R v)‖ := rfl
    _ = ‖(N (recenteredBallRetraction u₀' R v) - N u₀') + N u₀'‖ := by rw [sub_add_cancel]
    _ ≤ ‖N (recenteredBallRetraction u₀' R v) - N u₀'‖ + ‖N u₀'‖ := norm_add_le _ _
    _ ≤ (L_R : ℝ) * R + ‖N u₀'‖ := by linarith [hlip]
    _ = ‖N u₀'‖ + (L_R : ℝ) * R := by ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_truncated_norm_le {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {u₀' : tensorHs (I := I) (M := M) g r s (a + 1)}
    (hN : LipschitzOnWith L_R N (Metric.closedBall u₀' R))
    (field : timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T) :
    ‖nemytskiiHa1 (I := I) (M := M)
        (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN) field‖ ≤
      Real.sqrt T * (‖N u₀'‖ + (L_R : ℝ) * R) := by
  have hCnn : 0 ≤ ‖N u₀'‖ + (L_R : ℝ) * R := by positivity
  refine timeL2_norm_le_of_ae_bound _ hCnn ?_
  have hcoe := nemytskiiHa1_coeFn (I := I) (M := M)
    (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN) field
  filter_upwards [hcoe] with t ht
  rw [ht]
  exact truncatedNonlin_norm_le (I := I) (M := M) hR hN (field t)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem recentred_repr_normSq_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖(maxRegRecentredCrossScaleField (I := I) (M := M)
        (h_compact := h_compact) hT hT1 u₀ gforce).repr t‖ ^ 2 ≤
      Real.sqrt T *
          ‖recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce‖ ^ 2 +
        (Real.sqrt T)⁻¹ *
          ‖(maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv‖ ^ 2 := by
  set u := maxRegRecentredCrossScaleField (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce with hu_def
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have henergy := u.normSq_repr_le_init_add_integral hT ht
  rw [recentred_repr_zero (I := I) (M := M) (h_compact := h_compact) hT hT1 u₀ gforce,
    norm_zero] at henergy
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at henergy
  refine le_trans henergy ?_
  have hhi_sq : IntegrableOn (fun s => ‖u.hiL2 s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
    have hLp : MemLp (fun s => u.hiL2 s) 2 (timeMeasure T) := Lp.memLp u.hiL2
    have hint := hLp.integrable_norm_rpow (by norm_num) (by norm_num)
    have hpow : (fun x => ‖u.hiL2 x‖ ^ (2 : ℝ≥0∞).toReal) = (fun x => ‖u.hiL2 x‖ ^ 2) := by
      funext x; rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
    rw [hpow] at hint; exact hint
  have hlo_sq : IntegrableOn (fun s => ‖u.lo.deriv s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
    have hLp : MemLp (fun s => u.lo.deriv s) 2 (timeMeasure T) := Lp.memLp u.lo.deriv
    have hint := hLp.integrable_norm_rpow (by norm_num) (by norm_num)
    have hpow : (fun x => ‖u.lo.deriv x‖ ^ (2 : ℝ≥0∞).toReal) = (fun x => ‖u.lo.deriv x‖ ^ 2) := by
      funext x; rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
    rw [hpow] at hint; exact hint
  have hstep1 : (∫ s in (0 : ℝ)..t, 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) ≤
      ∫ s in Set.Icc (0 : ℝ) T, 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖) := by
    rw [intervalIntegral.integral_of_le ht.1]
    refine setIntegral_mono_set (u.integrableOn_energyBound)
      (ae_of_all _ (fun s => by positivity)) ?_
    exact HasSubset.Subset.eventuallyLE (fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩)
  refine le_trans hstep1 ?_
  have hyoung : ∀ s, 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖) ≤
      Real.sqrt T * ‖u.hiL2 s‖ ^ 2 + (Real.sqrt T)⁻¹ * ‖u.lo.deriv s‖ ^ 2 := by
    intro s
    have hkey : 0 ≤ (Real.sqrt (Real.sqrt T) * ‖u.hiL2 s‖ -
        (Real.sqrt (Real.sqrt T))⁻¹ * ‖u.lo.deriv s‖) ^ 2 := sq_nonneg _
    have hssT_pos : 0 < Real.sqrt (Real.sqrt T) := Real.sqrt_pos.mpr hsqrtT_pos
    have hssT_sq : Real.sqrt (Real.sqrt T) ^ 2 = Real.sqrt T := Real.sq_sqrt hsqrtT_pos.le
    have hinv_sq : (Real.sqrt (Real.sqrt T))⁻¹ ^ 2 = (Real.sqrt T)⁻¹ := by
      rw [inv_pow, hssT_sq]
    have hmid : Real.sqrt (Real.sqrt T) * (Real.sqrt (Real.sqrt T))⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hssT_pos)
    nlinarith [hkey, hssT_sq, hinv_sq, hmid,
      mul_nonneg (norm_nonneg (u.hiL2 s)) (norm_nonneg (u.lo.deriv s))]
  have hbound_int : IntegrableOn
      (fun s => Real.sqrt T * ‖u.hiL2 s‖ ^ 2 + (Real.sqrt T)⁻¹ * ‖u.lo.deriv s‖ ^ 2)
      (Set.Icc (0 : ℝ) T) volume :=
    (hhi_sq.const_mul (Real.sqrt T)).add (hlo_sq.const_mul (Real.sqrt T)⁻¹)
  refine le_trans (setIntegral_mono (u.integrableOn_energyBound) hbound_int
    (fun s => hyoung s)) ?_
  rw [MeasureTheory.integral_add (hhi_sq.const_mul (Real.sqrt T))
      (hlo_sq.const_mul (Real.sqrt T)⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hhi_norm : ‖recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce‖ ^ 2 =
      ∫ s in Set.Icc (0 : ℝ) T, ‖u.hiL2 s‖ ^ 2 :=
    TimeSobolev.norm_sq_eq_integral _
  have hlo_norm : ‖(maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv‖ ^ 2 =
      ∫ s in Set.Icc (0 : ℝ) T, ‖u.lo.deriv s‖ ^ 2 :=
    TimeSobolev.norm_sq_eq_integral _
  rw [hhi_norm, hlo_norm]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem recentredHi_norm_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce‖ ≤
      2 * Real.sqrt T * ‖u₀‖ + (1 + T) * ‖gforce‖ := by
  rw [recentredHiL2, maxRegDuhamelSolField]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_add_le _ _) (le_refl _)) ?_
  have hhom := maxRegHomogeneousSolField_norm_le (I := I) (M := M)
    (h_compact := h_compact) u₀ hT.le
  have hduh := maximalRegularitySolField_norm_le (I := I) (M := M)
    (h_compact := h_compact) hT.le gforce
  have hconst : ‖TimeSobolev.const T u₀‖ = Real.sqrt T * ‖u₀‖ := TimeSobolev.norm_const T u₀
  rw [hconst]
  have : Real.sqrt T * ‖u₀‖ + (1 + T) * ‖gforce‖ + Real.sqrt T * ‖u₀‖ =
      2 * Real.sqrt T * ‖u₀‖ + (1 + T) * ‖gforce‖ := by ring
  linarith [hhom, hduh]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem recentredCarrier_deriv_norm_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖(maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv‖ ≤
      Real.sqrt T * ‖u₀‖ + 2 * ‖gforce‖ := by
  rw [maxRegDuhamelMap_deriv (I := I) (M := M) (a := a) (T := T) hT hT1 u₀ gforce]
  refine le_trans (norm_add_le _ _) ?_
  have hhom := maxRegHomogeneousDerivField_norm_le (I := I) (M := M)
    (h_compact := h_compact) u₀ hT.le
  have hduh := maximalRegularityDerivField_norm_le (I := I) (M := M)
    (h_compact := h_compact) hT.le gforce
  linarith [hhom, hduh]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem recentred_repr_normSq_le_of_smallForcing (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {C : ℝ} (hC : 0 ≤ C) (hgforce : ‖gforce‖ ≤ Real.sqrt T * C)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖(maxRegRecentredCrossScaleField (I := I) (M := M)
        (h_compact := h_compact) hT hT1 u₀ gforce).repr t‖ ^ 2 ≤
      Real.sqrt T * (4 * (‖u₀‖ + C) ^ 2 + (‖u₀‖ + 2 * C) ^ 2) := by
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsqrtT_le_one : Real.sqrt T ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hT1
  have henergy := recentred_repr_normSq_le (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce ht
  have hhi := recentredHi_norm_le (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce
  have hderiv := recentredCarrier_deriv_norm_le (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce
  have hhi' : ‖recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce‖ ≤
      2 * Real.sqrt T * (‖u₀‖ + C) := by
    refine le_trans hhi ?_
    have h1 : (1 + T) * ‖gforce‖ ≤ 2 * (Real.sqrt T * C) := by
      have : (1 + T) ≤ 2 := by linarith
      have hgn : 0 ≤ ‖gforce‖ := norm_nonneg _
      nlinarith [hgforce, hgn, mul_nonneg (Real.sqrt_nonneg T) hC]
    nlinarith [h1, Real.sqrt_nonneg T, norm_nonneg u₀, hC]
  have hderiv' : ‖(maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv‖ ≤
      Real.sqrt T * (‖u₀‖ + 2 * C) := by
    refine le_trans hderiv ?_
    nlinarith [hgforce, Real.sqrt_nonneg T, norm_nonneg u₀, hC]
  have hhi_sq : ‖recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce‖ ^ 2 ≤
      (2 * Real.sqrt T * (‖u₀‖ + C)) ^ 2 := by
    have hnn : 0 ≤ 2 * Real.sqrt T * (‖u₀‖ + C) := by positivity
    nlinarith [hhi', norm_nonneg (recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce), hnn]
  have hderiv_sq : ‖(maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv‖ ^ 2 ≤
      (Real.sqrt T * (‖u₀‖ + 2 * C)) ^ 2 := by
    have hnn : 0 ≤ Real.sqrt T * (‖u₀‖ + 2 * C) := by positivity
    nlinarith [hderiv', norm_nonneg ((maxRegDuhamelMap (I := I) (M := M)
      a hT hT1 u₀ gforce).deriv), hnn]
  refine le_trans henergy ?_
  have hssq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have hbound1 : Real.sqrt T *
        ‖recentredHiL2 (I := I) (M := M) hT hT1 u₀ gforce‖ ^ 2 ≤
      Real.sqrt T * (4 * T * (‖u₀‖ + C) ^ 2) := by
    refine mul_le_mul_of_nonneg_left (le_trans hhi_sq (le_of_eq ?_)) hsqrtT_pos.le
    rw [mul_pow, mul_pow, hssq]; ring
  have hbound2 : (Real.sqrt T)⁻¹ *
        ‖(maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv‖ ^ 2 ≤
      Real.sqrt T * (‖u₀‖ + 2 * C) ^ 2 := by
    have hstep : (Real.sqrt T)⁻¹ *
          ‖(maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce).deriv‖ ^ 2 ≤
        (Real.sqrt T)⁻¹ * (T * (‖u₀‖ + 2 * C) ^ 2) := by
      refine mul_le_mul_of_nonneg_left (le_trans hderiv_sq (le_of_eq ?_)) (by positivity)
      rw [mul_pow, hssq]
    refine le_trans hstep (le_of_eq ?_)
    have heq : (Real.sqrt T)⁻¹ * T = Real.sqrt T := by
      rw [mul_comm, ← div_eq_mul_inv, Real.div_sqrt]
    rw [← mul_assoc, heq]
  have hTle : Real.sqrt T * (4 * T * (‖u₀‖ + C) ^ 2) ≤
      Real.sqrt T * (4 * (‖u₀‖ + C) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hsqrtT_pos.le
    nlinarith [hT1, hT.le, sq_nonneg (‖u₀‖ + C)]
  nlinarith [hbound1, hbound2, hTle, hsqrtT_pos.le, sq_nonneg (‖u₀‖ + C),
    sq_nonneg (‖u₀‖ + 2 * C)]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelSolFieldHa1_stay (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hgforce : ‖gforce‖ ≤ Real.sqrt T * C)
    (hhoriz : Real.sqrt T * (4 * (‖u₀‖ + C) ^ 2 + (‖u₀‖ + 2 * C) ^ 2) ≤ R ^ 2) :
    ∀ᵐ t ∂(timeMeasure T),
      maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce t ∈
        Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show (a + 1) ≤ a + 2 by linarith) u₀) R := by
  have hReq := recentred_repr_eq_field_sub (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce
  filter_upwards [hReq, ae_restrict_mem (μ := volume) measurableSet_Icc] with t hteq htmem
  have hsup := recentred_repr_normSq_le_of_smallForcing (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce hC hgforce (t := t) htmem
  rw [Metric.mem_closedBall, dist_eq_norm, ← hteq]
  have hsq : ‖(maxRegRecentredCrossScaleField (I := I) (M := M)
      (h_compact := h_compact) hT hT1 u₀ gforce).repr t‖ ^ 2 ≤ R ^ 2 :=
    le_trans hsup hhoriz
  nlinarith [hsq, norm_nonneg ((maxRegRecentredCrossScaleField (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce).repr t), hR]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinear_strong_existence_locallyLipschitz_smallTime_stayDischarged_ofCompact
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 < R)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => N (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              a hT hT1 u₀ gforce t)) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR.le hN)
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) ∧
          ∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce t ∈
              Metric.closedBall
                (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                  (show (a + 1) ≤ a + 2 by linarith) u₀) R := by
  set u₀' := tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show (a + 1) ≤ a + 2 by linarith) u₀ with hu₀'
  set C : ℝ := ‖N u₀'‖ + (L_R : ℝ) * R with hC_def
  have hC_nn : 0 ≤ C := by positivity
  set K2 : ℝ := 4 * (‖u₀‖ + C) ^ 2 + (‖u₀‖ + 2 * C) ^ 2 with hK2_def
  have hK2_nn : 0 ≤ K2 := by positivity
  have hden_pos : 0 < K2 + 1 := by positivity
  obtain ⟨T_R, hT_R_pos, htrunc⟩ :=
    quasilinear_strong_existence_truncated_smallTime_ofCompact (I := I) (M := M)
      (h_compact := h_compact) (R := R) hR.le u₀ hN
  refine ⟨min T_R (min 1 ((R ^ 2 / (K2 + 1)) ^ 2)),
    lt_min hT_R_pos (lt_min one_pos (by positivity)), ?_⟩
  intro T hT hTT₀ hT1
  have hTTR : T ≤ T_R := le_trans hTT₀ (min_le_left _ _)
  have hThoriz : T ≤ (R ^ 2 / (K2 + 1)) ^ 2 :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨u, gforce, hu, hfix, htrace, hderiv⟩ := htrunc (T := T) hT hTTR hT1
  have hgforce_small : ‖gforce‖ ≤ Real.sqrt T * C := by
    rw [hfix]
    exact nemytskiiHa1_truncated_norm_le (I := I) (M := M) hR.le hN
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce)
  have hhoriz : Real.sqrt T * K2 ≤ R ^ 2 := by
    have hsqrtT_le : Real.sqrt T ≤ R ^ 2 / (K2 + 1) := by
      rw [show R ^ 2 / (K2 + 1) = Real.sqrt ((R ^ 2 / (K2 + 1)) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hThoriz
    calc Real.sqrt T * K2
        ≤ (R ^ 2 / (K2 + 1)) * K2 :=
          mul_le_mul_of_nonneg_right hsqrtT_le hK2_nn
      _ = R ^ 2 * (K2 / (K2 + 1)) := by rw [div_mul_eq_mul_div, mul_div_assoc]
      _ ≤ R ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one hden_pos]; linarith
      _ = R ^ 2 := mul_one _
  have hstay := maxRegDuhamelSolFieldHa1_stay (I := I) (M := M)
    (h_compact := h_compact) hT hT1 u₀ gforce hC_nn hR.le hgforce_small hhoriz
  refine ⟨u, gforce, hu, ?_, htrace, hderiv, hstay⟩
  conv_lhs => rw [hfix]
  exact nemytskiiHa1_truncated_eqOn_ball (I := I) (M := M) hR.le hN
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) hstay

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
