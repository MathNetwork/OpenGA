import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


noncomputable def smoothInclusionHsSuccLin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →ₗ[ℝ] SmoothCcTensorHs g r s k where
  toFun S := ⟨S.toCcTensor⟩
  map_add' S T := by
    change (⟨(S + T).toCcTensor⟩ : SmoothCcTensorHs g r s k) =
      (⟨S.toCcTensor⟩ : SmoothCcTensorHs g r s k) +
        (⟨T.toCcTensor⟩ : SmoothCcTensorHs g r s k)
    rw [SmoothCcTensorHs.toCcTensor_add]
    rfl
  map_smul' c S := by
    change (⟨(c • S).toCcTensor⟩ : SmoothCcTensorHs g r s k) =
      c • (⟨S.toCcTensor⟩ : SmoothCcTensorHs g r s k)
    rw [SmoothCcTensorHs.toCcTensor_smul]
    rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorPouSobolevNorm_inner_integral_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) < ⊤ := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2) with hf_def
  have hf_zero_off_K : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ K → f y = 0 := by
    intro y hy_target hy_off
    have hpush_zero :
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
          α (fun _ : M => (1 : ℝ)) y = 0 :=
      chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α (fun _ => 1) hy_target hy_off
    have hpush_unfold :
        chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
            α (fun _ : M => (1 : ℝ)) y =
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      simp [chartPushed]
    have hPOU_y : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      rw [← hpush_unfold]; exact hpush_zero
    change ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) * _) = 0
    rw [hPOU_y, zero_mul, ENNReal.ofReal_zero]
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hT_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hsplit :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      ∫⁻ y in K, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    rw [← MeasureTheory.lintegral_indicator hT_meas,
        ← MeasureTheory.lintegral_indicator hK_meas]
    refine MeasureTheory.lintegral_congr (fun y => ?_)
    by_cases hyK : y ∈ K
    · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hyK
      simp [Set.indicator_of_mem, hyK, hyT]
    · by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
      · have hf0 : f y = 0 := hf_zero_off_K y hyT hyK
        rw [Set.indicator_of_mem hyT, Set.indicator_of_notMem hyK, hf0]
      · simp [Set.indicator_of_notMem, hyK, hyT]
  rw [hsplit]
  have hK_vol : (volume :
      Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) K < ⊤ :=
    hK_compact.measure_lt_top
  refine MeasureTheory.setLIntegral_lt_top_of_le_nnreal hK_vol.ne ?_
  set ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun y =>
    ((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
      ‖iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2 with hψ_def
  have hψ_contOn :
      ContinuousOn ψ (chartTargetEuclid (I := I) (M := M) α) := by
    have hPOU_smooth :
        ContMDiff I (𝓘(ℝ, ℝ)) ∞
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have hPOU_pull_cont :
        ContinuousOn (fun y : EuclideanSpace ℝ
              (Fin (Module.finrank ℝ E)) =>
            (chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm y)))
          (chartTargetEuclid (I := I) (M := M) α) := by
      have hPOU_cont :
          Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
        hPOU_smooth.continuous
      have hSymmCont : ContinuousOn ((extChartAt I α).symm)
          (extChartAt I α).target :=
        continuousOn_extChartAt_symm α
      have h_toEucl_cont : Continuous
          ((toEuclidean (E := E)).symm : _ → _) :=
        (toEuclidean (E := E)).symm.continuous
      have h_inner : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine hSymmCont.comp h_toEucl_cont.continuousOn ?_
        intro y hy
        unfold chartTargetEuclid at hy
        obtain ⟨z, hz_tgt, hz_eq⟩ := hy
        rw [← hz_eq]
        change (toEuclidean (E := E)).symm
            ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
        rw [(toEuclidean (E := E)).symm_apply_apply]
        exact hz_tgt
      exact hPOU_cont.comp_continuousOn' h_inner
    have h_raw_smoothOn : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
        ((chartAt H α).source) :=
      tensorChartComponentRaw_contMDiffOn_chart_source
        (I := I) (M := M) g r s T α Idx Jdx
    have h_raw_pull_contDiffOn :
        ContDiffOn ℝ ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm)
          (extChartAt I α).target := by
      have h_extSymm : ContMDiffOn 𝓘(ℝ, E) I ∞
          ((extChartAt I α).symm : E → M) (extChartAt I α).target :=
        contMDiffOn_extChartAt_symm α
      have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm)
          (extChartAt I α).target := by
        refine h_raw_smoothOn.comp h_extSymm ?_
        intro y hy
        change (extChartAt I α).symm y ∈ (chartAt H α).source
        rw [← extChartAt_source (I := I)]
        exact (extChartAt I α).map_target hy
      exact h_comp_mdiff.contDiffOn
    have h_iter_contOn : ContinuousOn
        (iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm))
        (extChartAt I α).target := by
      have h_open : IsOpen (extChartAt I α).target :=
        isOpen_extChartAt_target α
      have h_cd_at : ∀ y ∈ (extChartAt I α).target,
          ContDiffAt ℝ ∞
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm) y :=
        fun y hy => h_raw_pull_contDiffOn.contDiffAt
          (h_open.mem_nhds hy)
      intro y hy
      have h_cd : ContDiffAt ℝ ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm) y := h_cd_at y hy
      have h_cont_iter : ContinuousAt
          (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm)) y := by
        exact h_cd.continuousAt_iteratedFDeriv (k := j) (by exact_mod_cast le_top)
      exact h_cont_iter.continuousWithinAt
    have h_iter_pull_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_toEucl_cont : Continuous
          ((toEuclidean (E := E)).symm : _ → _) :=
        (toEuclidean (E := E)).symm.continuous
      refine h_iter_contOn.comp h_toEucl_cont.continuousOn ?_
      intro y hy
      unfold chartTargetEuclid at hy
      obtain ⟨z, hz_tgt, hz_eq⟩ := hy
      rw [← hz_eq]
      change (toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
      rw [(toEuclidean (E := E)).symm_apply_apply]
      exact hz_tgt
    have h_norm_sq_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_norm : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ‖iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖)
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_iter_pull_contOn.norm
      exact h_norm.pow 2
    exact hPOU_pull_cont.mul h_norm_sq_contOn
  have hψ_contOn_K : ContinuousOn ψ K := hψ_contOn.mono hK_sub
  have hψ_bdd : ∃ M : ℝ, ∀ y ∈ K, ψ y ≤ M := by
    obtain ⟨M, hM⟩ := (hK_compact.image_of_continuousOn hψ_contOn_K).bddAbove
    refine ⟨M, fun y hy => ?_⟩
    exact hM ⟨y, hy, rfl⟩
  obtain ⟨B, hB⟩ := hψ_bdd
  refine ⟨B.toNNReal, fun y hy => ?_⟩
  rw [hf_def]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  change ψ y ≤ (B.toNNReal : ℝ≥0∞).toReal
  rw [ENNReal.coe_toReal, Real.coe_toNNReal']
  exact (hB y hy).trans (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorPouSobolevNorm_ne_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevNorm (I := I) (M := M) g k T ≠ ⊤ := by
  classical
  suffices h : tensorPouSobolevNorm (I := I) (M := M) g k T < ⊤ from h.ne
  rw [tensorPouSobolevNorm_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have htsum_eq :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm)
                      ((toEuclidean (E := E)).symm y)‖ ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E)))) := by
    refine tsum_eq_sum ?_
    intro α hα
    have hPOU_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    refine Finset.sum_eq_zero ?_
    intro IJ _
    refine Finset.sum_eq_zero ?_
    intro j _
    have h_integrand_zero :
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α
                      IJ.1 IJ.2
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) = 0 := by
      intro y _
      rw [hPOU_zero, zero_mul, ENNReal.ofReal_zero]
    rw [MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      h_integrand_zero]
    simp
  rw [htsum_eq]
  refine (ENNReal.sum_lt_top.mpr ?_).ne
  intro α _
  refine ENNReal.sum_lt_top.mpr ?_
  intro IJ _
  refine ENNReal.sum_lt_top.mpr ?_
  intro j _
  exact tensorPouSobolevNorm_inner_integral_lt_top
    (I := I) (M := M) g r s T α IJ.1 IJ.2 j

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_euclidPull_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_raw_smoothOn : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
      ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
  have h_raw_pull_contDiffOn :
      ContDiffOn ℝ ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
    have h_extSymm : ContMDiffOn 𝓘(ℝ, E) I ∞
        ((extChartAt I α).symm : E → M) (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm α
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
      refine h_raw_smoothOn.comp h_extSymm ?_
      intro y hy
      change (extChartAt I α).symm y ∈ (chartAt H α).source
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I α).map_target hy
    exact h_comp_mdiff.contDiffOn
  have h_toEucl_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have h_maps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨z, hz_tgt, hz_eq⟩
    have h_eq : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [h_eq]; exact hz_tgt
  exact h_raw_pull_contDiffOn.comp
    h_toEucl_symm_smooth.contDiffOn h_maps

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorPouSobolevHsNorm_inner_integral_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) < ⊤ := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) with hf_def
  have hf_zero_off_K : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ K → f y = 0 := by
    intro y hy_target hy_off
    have hpush_zero :
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
          α (fun _ : M => (1 : ℝ)) y = 0 :=
      chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α (fun _ => 1) hy_target hy_off
    have hpush_unfold :
        chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
            α (fun _ : M => (1 : ℝ)) y =
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      simp [chartPushed]
    have hPOU_y : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      rw [← hpush_unfold]; exact hpush_zero
    change ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) * _) = 0
    rw [hPOU_y, zero_mul, ENNReal.ofReal_zero]
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hT_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hsplit :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      ∫⁻ y in K, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    rw [← MeasureTheory.lintegral_indicator hT_meas,
        ← MeasureTheory.lintegral_indicator hK_meas]
    refine MeasureTheory.lintegral_congr (fun y => ?_)
    by_cases hyK : y ∈ K
    · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hyK
      simp [Set.indicator_of_mem, hyK, hyT]
    · by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
      · have hf0 : f y = 0 := hf_zero_off_K y hyT hyK
        rw [Set.indicator_of_mem hyT, Set.indicator_of_notMem hyK, hf0]
      · simp [Set.indicator_of_notMem, hyK, hyT]
  rw [hsplit]
  have hK_vol : (volume :
      Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) K < ⊤ :=
    hK_compact.measure_lt_top
  set ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun y =>
    ((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
      |(iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)
            y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 with hψ_def
  have hψ_contOn :
      ContinuousOn ψ (chartTargetEuclid (I := I) (M := M) α) := by
    have hPOU_smooth :
        ContMDiff I (𝓘(ℝ, ℝ)) ∞
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have hPOU_pull_cont :
        ContinuousOn (fun y : EuclideanSpace ℝ
              (Fin (Module.finrank ℝ E)) =>
            (chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm y)))
          (chartTargetEuclid (I := I) (M := M) α) := by
      have hPOU_cont :
          Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
        hPOU_smooth.continuous
      have hSymmCont : ContinuousOn ((extChartAt I α).symm)
          (extChartAt I α).target :=
        continuousOn_extChartAt_symm α
      have h_toEucl_cont : Continuous
          ((toEuclidean (E := E)).symm : _ → _) :=
        (toEuclidean (E := E)).symm.continuous
      have h_inner : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine hSymmCont.comp h_toEucl_cont.continuousOn ?_
        intro y hy
        unfold chartTargetEuclid at hy
        obtain ⟨z, hz_tgt, hz_eq⟩ := hy
        rw [← hz_eq]
        change (toEuclidean (E := E)).symm
            ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
        rw [(toEuclidean (E := E)).symm_apply_apply]
        exact hz_tgt
      exact hPOU_cont.comp_continuousOn' h_inner
    have h_iter_contOn : ContinuousOn
        (iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_cdOn :
          ContDiffOn ℝ ∞
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)
            (chartTargetEuclid (I := I) (M := M) α) :=
        tensorChartComponentRaw_euclidPull_contDiffOn
          (I := I) (M := M) g r s T α Idx Jdx
      intro y hy
      have h_cd : ContDiffAt ℝ ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm) y :=
        h_cdOn.contDiffAt (h_open.mem_nhds hy)
      have h_cont_iter : ContinuousAt
          (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)) y :=
        h_cd.continuousAt_iteratedFDeriv (k := j) (by exact_mod_cast le_top)
      exact h_cont_iter.continuousWithinAt
    have h_eval_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm)
              y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_apply : Continuous
          fun A : ContinuousMultilinearMap ℝ
              (fun _ : Fin j => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℝ =>
            A (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) :=
        continuous_eval_const _
      exact h_apply.comp_continuousOn h_iter_contOn
    have h_abs_sq_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_abs : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))|)
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_eval_contOn.abs
      exact h_abs.pow 2
    exact hPOU_pull_cont.mul h_abs_sq_contOn
  have hψ_contOn_K : ContinuousOn ψ K := hψ_contOn.mono hK_sub
  have hψ_bdd : ∃ M : ℝ, ∀ y ∈ K, ψ y ≤ M := by
    obtain ⟨M, hM⟩ := (hK_compact.image_of_continuousOn hψ_contOn_K).bddAbove
    refine ⟨M, fun y hy => ?_⟩
    exact hM ⟨y, hy, rfl⟩
  obtain ⟨B, hB⟩ := hψ_bdd
  refine MeasureTheory.setLIntegral_lt_top_of_le_nnreal hK_vol.ne ?_
  refine ⟨B.toNNReal, fun y hy => ?_⟩
  rw [hf_def]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  change ψ y ≤ (B.toNNReal : ℝ≥0∞).toReal
  rw [ENNReal.coe_toReal, Real.coe_toNNReal']
  exact (hB y hy).trans (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorPouSobolevHsNorm_ne_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k T ≠ ⊤ := by
  classical
  suffices h : tensorPouSobolevHsNorm (I := I) (M := M) g k T < ⊤ from h.ne
  rw [tensorPouSobolevHsNorm_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have htsum_eq :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E)))) := by
    refine tsum_eq_sum ?_
    intro α hα
    have hPOU_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    refine Finset.sum_eq_zero ?_
    intro IJ _
    refine Finset.sum_eq_zero ?_
    intro j _
    refine Finset.sum_eq_zero ?_
    intro basisIdx _
    have h_integrand_zero :
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) = 0 := by
      intro y _
      rw [hPOU_zero, zero_mul, ENNReal.ofReal_zero]
    rw [MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      h_integrand_zero]
    simp
  rw [htsum_eq]
  refine (ENNReal.sum_lt_top.mpr ?_).ne
  intro α _
  refine ENNReal.sum_lt_top.mpr ?_
  intro IJ _
  refine ENNReal.sum_lt_top.mpr ?_
  intro j _
  refine ENNReal.sum_lt_top.mpr ?_
  intro basisIdx _
  exact tensorPouSobolevHsNorm_inner_integral_lt_top
    (I := I) (M := M) g r s T α IJ.1 IJ.2 j basisIdx


omit [NeZero (Module.finrank ℝ E)] in
lemma smoothInclusionHsSuccLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (S : SmoothCcTensorHs g r s (k + 1)) :
    ‖smoothInclusionHsSuccLin (I := I) (M := M) g r s k S‖ ≤ 1 * ‖S‖ := by
  rw [one_mul]
  set T : SmoothCcTensor g r s := S.toCcTensor
  have h_inclusion :
      smoothInclusionHsSuccLin (I := I) (M := M) g r s k S =
        (⟨T⟩ : SmoothCcTensorHs g r s k) := rfl
  rw [h_inclusion]
  have h_lhs_coe :
      ‖(⟨T⟩ : SmoothCcTensorHs g r s k)‖ =
        ‖((⟨T⟩ : SmoothCcTensorHs g r s k) :
          UniformSpace.Completion (SmoothCcTensorHs g r s k))‖ :=
    (UniformSpace.Completion.norm_coe (⟨T⟩ : SmoothCcTensorHs g r s k)).symm
  have h_lhs_eq :
      ‖((⟨T⟩ : SmoothCcTensorHs g r s k) :
        UniformSpace.Completion (SmoothCcTensorHs g r s k))‖ =
      (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal := by
    change ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) k T‖ =
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal
    exact tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g k T
  have h_rhs_coe :
      ‖S‖ = ‖((⟨T⟩ : SmoothCcTensorHs g r s (k + 1)) :
        UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1)))‖ := by
    have hS : S = (⟨T⟩ : SmoothCcTensorHs g r s (k + 1)) := by
      cases S; rfl
    calc ‖S‖
        = ‖(⟨T⟩ : SmoothCcTensorHs g r s (k + 1))‖ := by rw [hS]
      _ = ‖((⟨T⟩ : SmoothCcTensorHs g r s (k + 1)) :
            UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1)))‖ :=
          (UniformSpace.Completion.norm_coe
            (⟨T⟩ : SmoothCcTensorHs g r s (k + 1))).symm
  have h_rhs_eq :
      ‖((⟨T⟩ : SmoothCcTensorHs g r s (k + 1)) :
        UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1)))‖ =
      (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
    change ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (k + 1) T‖ =
        (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal
    exact tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g (k + 1) T
  rw [h_lhs_coe, h_lhs_eq, h_rhs_coe, h_rhs_eq]
  exact ENNReal.toReal_mono
    (tensorPouSobolevHsNorm_ne_top (I := I) (M := M) g (k + 1) T)
    (tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g k T)


noncomputable def smoothInclusionHsSucc
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →L[ℝ] SmoothCcTensorHs g r s k :=
  (smoothInclusionHsSuccLin (I := I) (M := M) g r s k).mkContinuous 1
    (fun S => smoothInclusionHsSuccLin_norm_le (I := I) (M := M) g r s k S)


noncomputable def smoothInclusionHsSuccToHkCompl
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    SmoothCcTensorHs g r s (k + 1) →L[ℝ]
      TensorPouSobolevHilbert g r s k :=
  (UniformSpace.Completion.toComplL :
    SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k).comp
    (smoothInclusionHsSucc (I := I) (M := M) g r s k)


noncomputable def inclusionHk_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    TensorPouSobolevHilbert g r s (k + 1) →L[ℝ]
      TensorPouSobolevHilbert g r s k :=
  ContinuousLinearMap.extend
    (smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k)
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorHs g r s (k + 1) →L[ℝ]
        TensorPouSobolevHilbert g r s (k + 1))


omit [NeZero (Module.finrank ℝ E)] in
theorem inclusionHk_succ_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ‖inclusionHk_succ (I := I) (M := M) g r s k‖ ≤ 1 := by
  have h_dense :
      DenseRange
        (UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s (k + 1) →L[ℝ]
            TensorPouSobolevHilbert g r s (k + 1)) := by
    rw [show (UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s (k + 1) → TensorPouSobolevHilbert g r s (k + 1)) =
        ((↑) : SmoothCcTensorHs g r s (k + 1) →
          UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1))) from
        UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.denseRange_coe
  have h_to_hk_compl_norm :
      ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ ≤ 1 := by
    unfold smoothInclusionHsSuccToHkCompl
    have h_toCompl :
        ‖(UniformSpace.Completion.toComplL :
          SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
      rw [one_mul]
      change ‖((x : UniformSpace.Completion (SmoothCcTensorHs g r s k)))‖ ≤ ‖x‖
      rw [UniformSpace.Completion.norm_coe]
    have h_smooth_succ :
        ‖smoothInclusionHsSucc (I := I) (M := M) g r s k‖ ≤ 1 := by
      exact (smoothInclusionHsSuccLin (I := I) (M := M) g r s k).mkContinuous_norm_le
        zero_le_one
        (fun S => smoothInclusionHsSuccLin_norm_le (I := I) (M := M) g r s k S)
    calc ‖(UniformSpace.Completion.toComplL :
            SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k).comp
              (smoothInclusionHsSucc (I := I) (M := M) g r s k)‖
        ≤ ‖(UniformSpace.Completion.toComplL :
              SmoothCcTensorHs g r s k →L[ℝ] TensorPouSobolevHilbert g r s k)‖ *
          ‖smoothInclusionHsSucc (I := I) (M := M) g r s k‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul h_toCompl h_smooth_succ (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h_ext_bound' :
      ‖inclusionHk_succ (I := I) (M := M) g r s k‖ ≤
        ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro x
    refine UniformSpace.Completion.induction_on (p := fun x =>
        ‖inclusionHk_succ (I := I) (M := M) g r s k x‖ ≤
          ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ * ‖x‖) x
      ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro w
      have h_inc_eq :
          inclusionHk_succ (I := I) (M := M) g r s k
              ((w : UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1)))) =
            smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k w := by
        change inclusionHk_succ (I := I) (M := M) g r s k
            ((UniformSpace.Completion.toComplL :
              SmoothCcTensorHs g r s (k + 1) →L[ℝ]
                TensorPouSobolevHilbert g r s (k + 1)) w) =
          smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k w
        unfold inclusionHk_succ
        exact ContinuousLinearMap.extend_eq _
          (e := UniformSpace.Completion.toComplL)
          h_dense
          (by
            rw [show (UniformSpace.Completion.toComplL :
                  SmoothCcTensorHs g r s (k + 1) →
                    TensorPouSobolevHilbert g r s (k + 1)) =
                ((↑) : SmoothCcTensorHs g r s (k + 1) →
                  UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1))) from
                UniformSpace.Completion.coe_toComplL]
            exact UniformSpace.Completion.isUniformInducing_coe
              (SmoothCcTensorHs g r s (k + 1))) w
      rw [h_inc_eq]
      calc ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k w‖
          ≤ ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ * ‖w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖smoothInclusionHsSuccToHkCompl (I := I) (M := M) g r s k‖ *
            ‖((w : UniformSpace.Completion (SmoothCcTensorHs g r s (k + 1))))‖ := by
            rw [UniformSpace.Completion.norm_coe]
  linarith

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
