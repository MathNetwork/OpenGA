import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem homModeCoeff_zero (hT : 0 ≤ T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i = 0 := by
  have hsq := norm_homModeCoeff_sq_le (I := I) (M := M) (a := a) (T := T) hT
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i
  rw [tensorHs.zero_coeff] at hsq
  have hnorm : ‖homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i‖ = 0 := by
    nlinarith [norm_nonneg (homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i), hsq]
  exact norm_eq_zero.mp hnorm

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem homDerivModeCoeff_zero (hT : 0 ≤ T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homDerivModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i = 0 := by
  rw [homDerivModeCoeff_eq_smul (I := I) (M := M) (a := a) (T := T),
    homModeCoeff_zero (I := I) (M := M) (a := a) (T := T) hT i, smul_zero]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem maxRegDuhamelMap_zero_eq_recentredCarrier (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maxRegDuhamelMap (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce =
      recentredCarrier (I := I) (M := M) hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce := by
  refine TimeSobolev.timeH1.ext ?_ ?_
  · rw [maxRegDuhamelMap_init (I := I) (M := M) (a := a) (T := T) hT hT1, map_zero,
      recentredCarrier, TimeSobolev.timeH1.init_mk]
  · rw [recentredCarrier, TimeSobolev.timeH1.deriv_mk]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem carrier_coeff_ae_perModeConv (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun t => ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i)
        =ᵐ[timeMeasure T]
      fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  have hlam_nonneg : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
  have hcarr := maxRegDuhamelMap_zero_eq_recentredCarrier (I := I) (M := M)
    (a := a) (T := T) hT hT1 gforce
  have hsolint := solModeCoeff_eq_integral (I := I) (M := M) (a := a) hT.le gforce i
  have hconv := perModeConvL2_coeFn lam hlam_nonneg hT.le
    (timeModeCoeff (I := I) (M := M) gforce i)
  have hsoldef : solModeCoeff (I := I) (M := M) (a := a) hT.le gforce i =
      perModeConvL2 lam hlam_nonneg hT.le
        (timeModeCoeff (I := I) (M := M) gforce i) := rfl
  have hderiv := maxRegDuhamelMap_deriv_coeff_ae (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce i
  have hhd0 := homDerivModeCoeff_zero (I := I) (M := M) (a := a) (T := T) hT.le i
  have hhd0coe : ⇑(homDerivModeCoeff (I := I) (M := M) (a := a) (T := T)
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i) =ᵐ[timeMeasure T]
      fun _ => (0 : ℝ) := by
    rw [hhd0]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := timeMeasure T)] with τ hτ
    rw [hτ]; rfl
  filter_upwards [hsolint, hconv, ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t htsol htconv htmem
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans htmem.1 htmem.2⟩
  have hLHS : ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i =
      ∫ τ in (0 : ℝ)..t,
        ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).deriv τ).coeff i := by
    rw [hcarr]
    exact recentredCarrier_toFun_coeff (I := I) (M := M) hT hT1
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce i htmem'
  have hint_eq : (∫ τ in (0 : ℝ)..t,
        ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).deriv τ).coeff i) =
      ∫ τ in (0 : ℝ)..t, (derivModeCoeff (I := I) (M := M) (a := a) hT.le gforce i) τ := by
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0mem htmem')
    have haeD := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv
    have haeH := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hhd0coe
    rw [ae_restrict_iff' measurableSet_uIoc] at haeD haeH
    filter_upwards [haeD, haeH] with τ hτD hτH hτmem
    rw [hτD hτmem, hτH hτmem, zero_add]
  rw [hLHS, hint_eq, ← htsol, hsoldef, htconv]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem carrier_toFun_coeff_eq_perModeConv_IccExtend (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T))
    (hF_rep : ⇑gforce =ᵐ[timeMeasure T] F)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i)) t := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  set u := maxRegDuhamelMap (I := I) (M := M) a hT hT1
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce with hu_def
  set φi : ℝ → ℝ :=
    Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i) with hφi_def
  have hφi_cont : Continuous φi := by
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  have hφi_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T → φi x = (F x).coeff i := by
    intro x hx
    rw [hφi_def, Set.IccExtend_of_mem hT.le _ hx]
  have hLHS_cont : ContinuousOn (fun t => (u.toFun t).coeff i) (Set.Icc (0 : ℝ) T) := by
    have hcomp : ContinuousOn
        (fun t => (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
          (u.toFun t)) (Set.Icc (0 : ℝ) T) :=
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i).continuous.comp_continuousOn
        u.continuousOn_toFun
    simpa only [coeffCLM_apply] using hcomp
  have hRHS_cont : ContinuousOn (fun t => perModeConv lam φi t) (Set.Icc (0 : ℝ) T) :=
    (continuous_perModeConv lam hφi_cont).continuousOn
  have hae_base := carrier_coeff_ae_perModeConv (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce i
  have htmc := timeModeCoeff_coeFn (I := I) (M := M) gforce i
  have hae_forcing : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
      =ᵐ[timeMeasure T] fun s => (F s).coeff i := by
    filter_upwards [htmc, hF_rep] with s hs hsF
    rw [hs, hsF]
  have hconv_eq : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) T →
      perModeConv lam (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) x =
        perModeConv lam φi x := by
    intro x hx
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, le_trans hx.1 hx.2⟩
    simp only [perModeConv]
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0mem hx)
    have haeF := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hae_forcing
    rw [ae_restrict_iff' measurableSet_uIoc] at haeF
    filter_upwards [haeF] with s hsF hsmem
    have hsmem' : s ∈ Set.Icc (0 : ℝ) T := hsub hsmem
    rw [hsF hsmem, ← hφi_mem hsmem']
  have hae_full : (fun t => (u.toFun t).coeff i) =ᵐ[timeMeasure T]
      fun t => perModeConv lam φi t := by
    filter_upwards [hae_base, ae_restrict_mem (μ := volume) measurableSet_Icc]
      with x hx hxmem
    rw [hx]
    exact hconv_eq hxmem
  have hsub_clo : Set.Icc (0 : ℝ) T ⊆ closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hT)]
  have heqOn : Set.EqOn (fun t => (u.toFun t).coeff i)
      (fun t => perModeConv lam φi t) (Set.Icc (0 : ℝ) T) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae_full hLHS_cont hRHS_cont hsub_clo
  exact heqOn ht

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (hT : 0 < T) (hT1 : T ≤ 1)
    {d₂ : ℝ} (hd₂_pos : 0 < d₂) (hd₂_le : d₂ ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂))
    (hF_rep : ⇑gforce =ᵐ[volume.restrict (Set.Icc (0 : ℝ) d₂)] F)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) d₂) :
    ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i =
      perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (Set.IccExtend hd₂_pos.le (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F p.1).coeff i)) t := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam_def
  set u := maxRegDuhamelMap (I := I) (M := M) a hT hT1
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce with hu_def
  set φi : ℝ → ℝ :=
    Set.IccExtend hd₂_pos.le (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F p.1).coeff i) with hφi_def
  have hφi_cont : Continuous φi := by
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  have hφi_mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) d₂ → φi x = (F x).coeff i := by
    intro x hx
    rw [hφi_def, Set.IccExtend_of_mem hd₂_pos.le _ hx]
  have hLHS_cont : ContinuousOn (fun t => (u.toFun t).coeff i) (Set.Icc (0 : ℝ) d₂) := by
    have hcomp : ContinuousOn
        (fun t => (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
          (u.toFun t)) (Set.Icc (0 : ℝ) d₂) :=
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i).continuous.comp_continuousOn
        (u.continuousOn_toFun.mono (Set.Icc_subset_Icc le_rfl hd₂_le))
    simpa only [coeffCLM_apply] using hcomp
  have hRHS_cont : ContinuousOn (fun t => perModeConv lam φi t) (Set.Icc (0 : ℝ) d₂) :=
    (continuous_perModeConv lam hφi_cont).continuousOn
  have hae_base := carrier_coeff_ae_perModeConv (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce i
  have hae_base' := MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := volume)
    (Set.Icc_subset_Icc le_rfl hd₂_le) hae_base
  have htmc := timeModeCoeff_coeFn (I := I) (M := M) gforce i
  have htmc' := MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := volume)
    (Set.Icc_subset_Icc le_rfl hd₂_le) htmc
  have hae_forcing : (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) d₂)] fun s => (F s).coeff i := by
    filter_upwards [htmc', hF_rep] with s hs hsF
    rw [hs, hsF]
  have hconv_eq : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) d₂ →
      perModeConv lam (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) x =
        perModeConv lam φi x := by
    intro x hx
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) d₂ := ⟨le_rfl, le_trans hx.1 hx.2⟩
    simp only [perModeConv]
    refine intervalIntegral.integral_congr_ae ?_
    have hsub : Set.uIoc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) d₂ :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc h0mem hx)
    have haeF := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hae_forcing
    rw [ae_restrict_iff' measurableSet_uIoc] at haeF
    filter_upwards [haeF] with s hsF hsmem
    have hsmem' : s ∈ Set.Icc (0 : ℝ) d₂ := hsub hsmem
    rw [hsF hsmem, ← hφi_mem hsmem']
  have hae_full : (fun t => (u.toFun t).coeff i)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) d₂)] fun t => perModeConv lam φi t := by
    filter_upwards [hae_base', ae_restrict_mem (μ := volume) measurableSet_Icc]
      with x hx hxmem
    rw [hx]
    exact hconv_eq hxmem
  have hsub_clo : Set.Icc (0 : ℝ) d₂ ⊆ closure (interior (Set.Icc (0 : ℝ) d₂)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hd₂_pos)]
  have heqOn : Set.EqOn (fun t => (u.toFun t).coeff i)
      (fun t => perModeConv lam φi t) (Set.Icc (0 : ℝ) d₂) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae_full hLHS_cont hRHS_cont hsub_clo
  exact heqOn ht

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv_id_restrict (hT : 0 < T) (hT1 : T ≤ 1)
    (ha : 0 ≤ a) {d₂ : ℝ} (hd₂_pos : 0 < d₂) (hd₂_le : d₂ ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) d₂))
    (hF_rep : ⇑gforce =ᵐ[volume.restrict (Set.Icc (0 : ℝ) d₂)] F) :
    ∃ φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ,
      (∀ i, Continuous (φ i)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) d₂, ∀ i,
        tensorL2Coeff (I := I) (M := M) h_compact
            ((tensorHsToL2 (I := I) (M := M) h_compact ha)
              ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
                (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) := by
  refine ⟨fun i => Set.IccExtend hd₂_pos.le
      (fun p : ↑(Set.Icc (0 : ℝ) d₂) => (F p.1).coeff i), ?_, ?_⟩
  · intro i
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  · intro t ht i
    rw [tensorHsToL2_tensorL2Coeff ha]
    exact carrier_toFun_coeff_eq_perModeConv_IccExtend_restrict (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 hd₂_pos hd₂_le gforce hcoord hF_rep i ht

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_eq_perModeConv_forcing (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fun t => (maxRegDuhamelSolField (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce t).coeff i)
        =ᵐ[timeMeasure T]
      fun t => perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
        (fun s => (timeModeCoeff (I := I) (M := M) gforce i) s) t := by
  have hfield := maxRegDuhamelSolField_coeff_ae (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce i
  have hcarr := carrier_coeff_ae_perModeConv (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce i
  have hrec := maxRegDuhamelMap_zero_eq_recentredCarrier (I := I) (M := M)
    (a := a) (T := T) hT hT1 gforce
  filter_upwards [hfield, hcarr, ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t htfield htcarr htmem
  have htmem' : t ∈ Set.Icc (0 : ℝ) T := htmem
  have hcarr_int : ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t).coeff i =
      ∫ τ in (0 : ℝ)..t,
        ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).deriv τ).coeff i := by
    rw [hrec]
    exact recentredCarrier_toFun_coeff (I := I) (M := M) hT hT1
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce i htmem'
  have hzero : (0 : tensorHs (I := I) (M := M) g r s (a + 2)).coeff i = 0 := by
    rw [tensorHs.zero_coeff]
  rw [htfield, hzero, zero_add, ← hcarr_int, htcarr]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv (hT : 0 < T) (hT1 : T ≤ 1)
    (ha : 0 ≤ a)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T))
    (hF_rep : ⇑gforce =ᵐ[timeMeasure T] F)
    (hsum : ∀ c : ℝ, 0 ≤ c → Summable (forcingMass (I := I) (M := M) gforce c)) :
    ∃ φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ,
      (∀ i, Continuous (φ i)) ∧
      (∀ c : ℝ, 0 ≤ c → ∀ t ∈ Set.Icc (0 : ℝ) T,
        Summable (fun i => tensorSobolevWeight (I := I) (M := M) i c *
          ∫ s in (0 : ℝ)..t, (φ i s) ^ 2)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        tensorL2Coeff (I := I) (M := M) h_compact
            ((tensorHsToL2 (I := I) (M := M) h_compact ha)
              ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
                (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i)) t) := by
  refine ⟨fun i => Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i),
    ?_, ?_, ?_⟩
  · intro i
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  · intro c hc t ht
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hsum c hc)
    · refine mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i c) ?_
      refine intervalIntegral.integral_nonneg ht.1 ?_
      intro x _; positivity
    · set φi : ℝ → ℝ :=
        Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i) with hφi_def
      have hφi_cont : Continuous φi := by
        refine Continuous.Icc_extend' ?_
        exact (hcoord i).restrict
      have hforcing : forcingMass (I := I) (M := M) gforce c i =
          tensorSobolevWeight (I := I) (M := M) i c *
            ∫ τ in Set.Icc (0 : ℝ) T,
              ((timeModeCoeff (I := I) (M := M) gforce i) τ) ^ 2 := by
        rw [forcingMass, TimeSobolev.norm_sq_eq_integral]
        congr 1
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [] with τ
        rw [Real.norm_eq_abs, sq_abs]
      have htmc := timeModeCoeff_coeFn (I := I) (M := M) gforce i
      have hae_forcing : (fun τ => (timeModeCoeff (I := I) (M := M) gforce i) τ)
          =ᵐ[timeMeasure T] fun τ => φi τ := by
        filter_upwards [htmc, hF_rep, ae_restrict_mem (μ := volume) measurableSet_Icc]
          with τ hτ hτF hτmem
        rw [hτ, hτF, hφi_def, Set.IccExtend_of_mem hT.le _ hτmem]
      have hIcc_eq : (∫ τ in Set.Icc (0 : ℝ) T,
            ((timeModeCoeff (I := I) (M := M) gforce i) τ) ^ 2) =
          ∫ τ in Set.Icc (0 : ℝ) T, (φi τ) ^ 2 := by
        refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
        have hae' : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) T →
            (timeModeCoeff (I := I) (M := M) gforce i) τ = φi τ :=
          (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hae_forcing
        filter_upwards [hae'] with τ hτ hτmem
        rw [hτ hτmem]
      have htint : (∫ τ in (0 : ℝ)..t, (φi τ) ^ 2) ≤
          ∫ τ in Set.Icc (0 : ℝ) T, (φi τ) ^ 2 := by
        rw [intervalIntegral.integral_of_le ht.1,
          ← MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine MeasureTheory.setIntegral_mono_set (hφi_cont.pow 2).integrableOn_Icc ?_ ?_
        · filter_upwards with x; positivity
        · exact HasSubset.Subset.eventuallyLE (Set.Icc_subset_Icc le_rfl ht.2)
      rw [hforcing, hIcc_eq]
      exact mul_le_mul_of_nonneg_left htint (tensorSobolevWeight_nonneg (I := I) (M := M) i c)
  · intro t ht i
    rw [tensorHsToL2_tensorL2Coeff ha]
    exact carrier_toFun_coeff_eq_perModeConv_IccExtend (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce hcoord hF_rep i ht

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamel_toFun_tensorL2Coeff_eq_perModeConv_id (hT : 0 < T) (hT1 : T ≤ 1)
    (ha : 0 ≤ a)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {F : ℝ → tensorHs (I := I) (M := M) g r s a}
    (hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      ContinuousOn (fun t => (F t).coeff i) (Set.Icc (0 : ℝ) T))
    (hF_rep : ⇑gforce =ᵐ[timeMeasure T] F) :
    ∃ φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ,
      (∀ i, Continuous (φ i)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
        tensorL2Coeff (I := I) (M := M) h_compact
            ((tensorHsToL2 (I := I) (M := M) h_compact ha)
              ((maxRegDuhamelMap (I := I) (M := M) a hT hT1
                (0 : tensorHs (I := I) (M := M) g r s (a + 2)) gforce).toFun t)) i =
          perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) (φ i) t) := by
  refine ⟨fun i => Set.IccExtend hT.le (fun p : ↑(Set.Icc (0 : ℝ) T) => (F p.1).coeff i),
    ?_, ?_⟩
  · intro i
    refine Continuous.Icc_extend' ?_
    exact (hcoord i).restrict
  · intro t ht i
    rw [tensorHsToL2_tensorL2Coeff ha]
    exact carrier_toFun_coeff_eq_perModeConv_IccExtend (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce hcoord hF_rep i ht

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
