import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.ChartAlphaReprL2BoundOnPouTsupport
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrict


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma pouInter_isCompact (α β : M) :
    IsCompact
      (tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
       tsupport (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact.inter_right (isClosed_tsupport _)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma pouInter_subset_chartSourceα (α β : M) :
    (tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
     tsupport (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) ⊆
      (chartAt H α).source := by
  intro x hx
  exact (chartAtlasPOU_isSubordinate I M) α hx.1

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma pouInter_subset_chartSourceβ (α β : M) :
    (tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
     tsupport (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) ⊆
      (chartAt H β).source := by
  intro x hx
  exact (chartAtlasPOU_isSubordinate I M) β hx.2

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma ofReal_sq_eq_enorm_sq (r : ℝ) :
    ENNReal.ofReal (r ^ 2) = (‖r‖ₑ : ℝ≥0∞) ^ 2 := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

omit [BoundarylessManifold I M] in
theorem chart_α_pou_α_pou_β_raw_β_sq_le_chart_β_wkpNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
                (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx)
                (chartTargetEuclid (I := I) (M := M) β)) ^ 2 := by
  classical
  set K_M : Set M :=
    tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    with hKM_def
  have hKM_compact : IsCompact K_M := pouInter_isCompact (I := I) (M := M) α β
  have hKM_subset_α : K_M ⊆ (chartAt H α).source :=
    pouInter_subset_chartSourceα (I := I) (M := M) α β
  have hKM_subset_β : K_M ⊆ (chartAt H β).source :=
    pouInter_subset_chartSourceβ (I := I) (M := M) α β
  obtain ⟨Ω_αβ, Ω_βα, hΩαβ_open, _hΩβα_open, hΩαβ_subset_target,
      hΩβα_subset_target, hΩαβ_overlap, _hΩβα_overlap, h_image_subset, Φ,
      hΦ_eq, _hΦ_inv_eq⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      α β hKM_compact hKM_subset_α hKM_subset_β 0
  have h_image_subset' :
      ((toEuclidean : E ≃L[ℝ] EuclN) ∘ extChartAt I α) '' K_M ⊆ Ω_αβ :=
    h_image_subset
  set EuclTargetα : Set EuclN := chartTargetEuclid (I := I) (M := M) α
    with hEα_def
  set EuclTargetβ : Set EuclN := chartTargetEuclid (I := I) (M := M) β
    with hEβ_def
  have hΩαβ_meas : MeasurableSet Ω_αβ := hΩαβ_open.measurableSet
  have hEα_meas : MeasurableSet EuclTargetα :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have hjLB_pos : 0 < Φ.jacobian_lower_bound := Φ.jacobian_lower_bound_pos
  have hjLB_inv_pos : 0 < 1 / Φ.jacobian_lower_bound := by positivity
  set Kchg : ℝ := (1 / Φ.jacobian_lower_bound) ^ (1 / (2 : ℝ≥0∞).toReal)
    with hKchg_def
  have hKchg_nn : 0 ≤ Kchg := by
    rw [hKchg_def]
    exact Real.rpow_nonneg hjLB_inv_pos.le _
  refine ⟨Kchg ^ 2, sq_nonneg _, ?_⟩
  intro T
  set F : M → ℝ := fun x =>
    ((chartAtlasPOU I M α : M → ℝ) x) *
      (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx x) ^ 2
    with hF_def
  set Fe : EuclN → ℝ≥0∞ := fun y =>
    ENNReal.ofReal
      (F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
    with hFe_def
  have h_Fe_vanish_on_EuclTargetα_minus_Ωαβ :
      ∀ y ∈ EuclTargetα, y ∉ Ω_αβ → Fe y = 0 := by
    intro y hy_target hy_off
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have hsymm_target_α : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      have := hy_target
      rw [hEα_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at this
      exact this
    have hy_eq_φα_x : (toEuclidean (E := E)) (extChartAt I α x) = y := by
      rw [hx_def, (extChartAt I α).right_inv hsymm_target_α]
      exact (toEuclidean (E := E)).apply_symm_apply y
    have hx_notin_K : x ∉ K_M := by
      intro hxK
      have hy_in_image :
          y ∈ ((toEuclidean : E ≃L[ℝ] EuclN) ∘ extChartAt I α) '' K_M :=
        ⟨x, hxK, hy_eq_φα_x⟩
      exact hy_off (h_image_subset' hy_in_image)
    have h_cases :
        x ∉ tsupport (fun z : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) ∨
        x ∉ tsupport (fun z : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) := by
      by_contra h_both
      rw [not_or, not_not, not_not] at h_both
      exact hx_notin_K ⟨h_both.1, h_both.2⟩
    rcases h_cases with hxα | hxβ
    · have hPOUα_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 := by
        have hsupp_sub : Function.support
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
          tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          subset_tsupport _
        by_contra hne
        have hne' : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0 := hne
        have hin : x ∈ Function.support
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := hne'
        exact hxα (hsupp_sub hin)
      have hFx : F x = 0 := by
        simp [hF_def, hPOUα_zero]
      change ENNReal.ofReal (F x) = 0
      rw [hFx, ENNReal.ofReal_zero]
    · have hPOUβ_zero : (chartAtlasPOU I M β : M → ℝ) x = 0 := by
        have hsupp_sub : Function.support
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
          tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          subset_tsupport _
        by_contra hne
        have hne' : ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0 := hne
        have hin : x ∈ Function.support
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := hne'
        exact hxβ (hsupp_sub hin)
      have hcomp_zero :
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx x = 0 := by
        unfold tensorChartComponentPou
        rw [hPOUβ_zero, zero_mul]
      have hFx : F x = 0 := by
        simp [hF_def, hcomp_zero]
      change ENNReal.ofReal (F x) = 0
      rw [hFx, ENNReal.ofReal_zero]
  have h_LHS_eq_restrict_Ωαβ :
      ∫⁻ y in EuclTargetα, Fe y ∂(volume : Measure EuclN) =
        ∫⁻ y in Ω_αβ, Fe y ∂(volume : Measure EuclN) := by
    have h_ae_eq : Fe =ᵐ[(volume : Measure EuclN).restrict EuclTargetα]
        Ω_αβ.indicator Fe := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hEα_meas]
      refine Filter.Eventually.of_forall ?_
      intro y hy_target
      by_cases hy : y ∈ Ω_αβ
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy]
        exact h_Fe_vanish_on_EuclTargetα_minus_Ωαβ y hy_target hy
    rw [lintegral_congr_ae h_ae_eq, lintegral_indicator hΩαβ_meas]
    rw [Measure.restrict_restrict hΩαβ_meas,
      show Ω_αβ ∩ EuclTargetα = Ω_αβ from
        Set.inter_eq_left.mpr hΩαβ_subset_target]
  rw [h_LHS_eq_restrict_Ωαβ]
  have h_integrand_eq_on_Ωαβ : ∀ y ∈ Ω_αβ,
      Fe y =
        ENNReal.ofReal
          ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            (tensorChartComp (I := I) (M := M) g r s T β Idx Jdx (Φ.toFun y)) ^ 2) := by
    intro y hy
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) α β :=
      hΩαβ_overlap hy
    rcases hy_overlap with ⟨w, ⟨z, hz_in, hzw⟩, hwy⟩
    have hz_extchart : z ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hz_in.1
    have hy_eq2 : y = (toEuclidean (E := E)) (extChartAt I α z) := by
      rw [← hwy, ← hzw]
    have hz_eq_x : z = x := by
      have hx_def' : x = (extChartAt I α).symm ((toEuclidean (E := E)).symm y) := hx_def
      rw [hx_def', hy_eq2, (toEuclidean (E := E)).symm_apply_apply,
        (extChartAt I α).left_inv hz_extchart]
    have hx_source_α : x ∈ (chartAt H α).source := hz_eq_x ▸ hz_in.1
    have hx_source_β : x ∈ (chartAt H β).source := hz_eq_x ▸ hz_in.2
    have hy_eq_φα_x : (toEuclidean (E := E)) (extChartAt I α x) = y := by
      rw [← hz_eq_x, ← hy_eq2]
    have hΦy_eq : Φ.toFun y = chartTransitionEuclid (I := I) (M := M) α β y :=
      hΦ_eq y hy
    have h_trans_eq : chartTransitionEuclid (I := I) (M := M) α β y =
        (toEuclidean (E := E)) (extChartAt I β x) := by
      rw [← hy_eq_φα_x]
      exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α β hx_source_α
    have hΦy_eq2 : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I β x) := by
      rw [hΦy_eq, h_trans_eq]
    have hΦy_target_β : Φ.toFun y ∈ EuclTargetβ := by
      rw [hΦy_eq2, hEβ_def]
      refine ⟨extChartAt I β x, ?_, rfl⟩
      exact (extChartAt I β).map_source (by
        rw [extChartAt_source (I := I)]; exact hx_source_β)
    have h_comp_eq :
        tensorChartComp (I := I) (M := M) g r s T β Idx Jdx (Φ.toFun y) =
          tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx x := by
      rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s T β Idx Jdx hΦy_target_β]
      congr 1
      rw [hΦy_eq2, (toEuclidean (E := E)).symm_apply_apply]
      exact (extChartAt I β).left_inv (by
        rw [extChartAt_source (I := I)]; exact hx_source_β)
    change ENNReal.ofReal (F x) = _
    rw [hF_def, h_comp_eq]
  rw [setLIntegral_congr_fun hΩαβ_meas (fun y hy =>
    h_integrand_eq_on_Ωαβ y hy)]
  have hPOUα_le_one : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x ≤ 1 :=
    fun x => (chartAtlasPOU I M).le_one α x
  have hPOUα_nn : ∀ x : M, 0 ≤ (chartAtlasPOU I M α : M → ℝ) x :=
    fun x => (chartAtlasPOU I M).nonneg α x
  set g_β : EuclN → ℝ := tensorChartComp (I := I) (M := M) g r s T β Idx Jdx
    with hgβ_def
  have h_pou_bound :
      (∫⁻ y in Ω_αβ,
          ENNReal.ofReal
            ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              (g_β (Φ.toFun y)) ^ 2)
          ∂(volume : Measure EuclN)) ≤
        ∫⁻ y in Ω_αβ,
          ENNReal.ofReal ((g_β (Φ.toFun y)) ^ 2)
          ∂(volume : Measure EuclN) := by
    refine lintegral_mono_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    have hpouα_le : (chartAtlasPOU I M α : M → ℝ) x ≤ 1 := hPOUα_le_one x
    have hsq_nn : 0 ≤ (g_β (Φ.toFun y)) ^ 2 := sq_nonneg _
    refine ENNReal.ofReal_le_ofReal ?_
    calc (chartAtlasPOU I M α : M → ℝ) x * (g_β (Φ.toFun y)) ^ 2
        ≤ 1 * (g_β (Φ.toFun y)) ^ 2 :=
          mul_le_mul_of_nonneg_right hpouα_le hsq_nn
      _ = (g_β (Φ.toFun y)) ^ 2 := one_mul _
  have h_lintegral_eq_sq :
      (∫⁻ y in Ω_αβ,
          ENNReal.ofReal ((g_β (Φ.toFun y)) ^ 2)
          ∂(volume : Measure EuclN)) =
        (eLpNorm (fun y => g_β (Φ.toFun y)) 2
            ((volume : Measure EuclN).restrict Ω_αβ)) ^ 2 := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq]
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    exact ofReal_sq_eq_enorm_sq (g_β (Φ.toFun y))
  have h_p_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_p_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_chg :
      eLpNorm (fun y => g_β (Φ.toFun y)) 2
          ((volume : Measure EuclN).restrict Ω_αβ) ≤
        ENNReal.ofReal Kchg *
          eLpNorm g_β 2 ((volume : Measure EuclN).restrict Ω_βα) := by
    rw [hKchg_def]
    exact Φ.eLpNorm_comp_toFun_le_const h_p_one h_p_ne_top hΩαβ_open g_β
  have h_meas_mono : (volume : Measure EuclN).restrict Ω_βα ≤
      (volume : Measure EuclN).restrict EuclTargetβ :=
    Measure.restrict_mono hΩβα_subset_target le_rfl
  have h_eLpNorm_mono :
      eLpNorm g_β 2 ((volume : Measure EuclN).restrict Ω_βα) ≤
        eLpNorm g_β 2 ((volume : Measure EuclN).restrict EuclTargetβ) :=
    eLpNorm_mono_measure _ h_meas_mono
  have h_wkp : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2 g_β EuclTargetβ =
      eLpNorm g_β 2 ((volume : Measure EuclN).restrict EuclTargetβ) :=
    wkpNorm_zero (d := Module.finrank ℝ E) 2 g_β EuclTargetβ
  calc (∫⁻ y in Ω_αβ,
          ENNReal.ofReal
            ((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
              (g_β (Φ.toFun y)) ^ 2)
          ∂(volume : Measure EuclN))
      ≤ ∫⁻ y in Ω_αβ,
            ENNReal.ofReal ((g_β (Φ.toFun y)) ^ 2)
            ∂(volume : Measure EuclN) := h_pou_bound
    _ = (eLpNorm (fun y => g_β (Φ.toFun y)) 2
            ((volume : Measure EuclN).restrict Ω_αβ)) ^ 2 := h_lintegral_eq_sq
    _ ≤ (ENNReal.ofReal Kchg *
          eLpNorm g_β 2 ((volume : Measure EuclN).restrict Ω_βα)) ^ 2 := by
          gcongr
    _ = (ENNReal.ofReal Kchg) ^ 2 *
            (eLpNorm g_β 2 ((volume : Measure EuclN).restrict Ω_βα)) ^ 2 := by ring
    _ ≤ (ENNReal.ofReal Kchg) ^ 2 *
            (eLpNorm g_β 2 ((volume : Measure EuclN).restrict EuclTargetβ)) ^ 2 := by
          gcongr
    _ = (ENNReal.ofReal Kchg) ^ 2 *
            (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2 g_β EuclTargetβ) ^ 2 := by
          rw [h_wkp]
    _ = ENNReal.ofReal (Kchg ^ 2) *
            (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2 g_β EuclTargetβ) ^ 2 := by
          rw [← ENNReal.ofReal_pow hKchg_nn]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
