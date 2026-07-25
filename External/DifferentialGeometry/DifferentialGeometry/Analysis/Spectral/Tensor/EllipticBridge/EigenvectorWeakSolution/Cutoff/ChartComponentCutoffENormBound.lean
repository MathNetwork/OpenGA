import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def cutoffKernelEuclid (α : M) : Set EuclN :=
  (toEuclidean : E ≃L[ℝ] EuclN) '' (cutoffChartKernel (I := I) (M := M) α)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelEuclid_isCompact (α : M) :
    IsCompact (cutoffKernelEuclid (I := I) (M := M) α) :=
  (cutoffChartKernel_isCompact (I := I) (M := M) α).image
    (toEuclidean (E := E)).continuous

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelEuclid_measurableSet (α : M) :
    MeasurableSet (cutoffKernelEuclid (I := I) (M := M) α) :=
  (cutoffKernelEuclid_isCompact (I := I) (M := M) α).isClosed.measurableSet

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelEuclid_subset_chartTargetEuclid (α : M) :
    cutoffKernelEuclid (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, cutoffChartKernel_subset_target (I := I) (M := M) α hx, rfl⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_support_subset_cutoffKernelEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Function.support
        (cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2) ⊆
      cutoffKernelEuclid (I := I) (M := M) α := by
  classical
  intro y hy
  have hy_ne : cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 y ≠ 0 :=
    hy
  by_cases hy_in : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [cutoffComponentEuclid_apply_of_mem (I := I) (M := M)
      g r s S α P₀.1 P₀.2 hy_in] at hy_ne
    have hp_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        Function.support
          (cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2) :=
      hy_ne
    have hp_tsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        tsupport
          (cutoffComponentScalar (I := I) (M := M) g r s S α P₀.1 P₀.2) :=
      subset_tsupport _ hp_supp
    have hx_kernel :
        (extChartAt I α)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ∈
          cutoffChartKernel (I := I) (M := M) α :=
      cutoffComponentScalar_chartImage_subset_kernel
        (I := I) (M := M) g r s S α P₀.1 P₀.2
        ⟨_, hp_tsupp, rfl⟩
    have hy_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy_in
    rw [(extChartAt I α).right_inv hy_tgt] at hx_kernel
    refine ⟨(toEuclidean (E := E)).symm y, hx_kernel, ?_⟩
    exact (toEuclidean (E := E)).apply_symm_apply y
  · exact absurd
      (cutoffComponentEuclid_apply_of_notMem (I := I) (M := M)
        g r s S α P₀.1 P₀.2 hy_in)
      hy_ne


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma eLpNorm_chartPulledWeighted_restrict_le_of_support_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN}
    (densitySup : ℝ) (hdensitySup_pos : 0 < densitySup)
    (hdensitySup_bd : ∀ y ∈ K, densityOnEuclid (I := I) g α y ≤ densitySup)
    {f : EuclN → ℝ} (hf_supp : Function.support f ⊆ K) :
    eLpNorm f 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal (densitySup ^ (1 / (2 : ℝ))) *
        eLpNorm f 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set S : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hS_def
  have hS_open : IsOpen S :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have h_lint_le :
      ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)
          ∂((chartPulledWeightedMeasure (I := I) g α).restrict S) ≤
        ENNReal.ofReal densitySup *
          ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂((volume : Measure EuclN).restrict S) := by
    rw [show (chartPulledWeightedMeasure (I := I) g α).restrict S =
        ((volume : Measure EuclN).restrict S).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y)) by
      unfold chartPulledWeightedMeasure
      exact MeasureTheory.restrict_withDensity hS_meas _]
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀]
    rotate_left
    · have hdens_contOn : ContinuousOn (densityOnEuclid (I := I) g α) S :=
        densityOnEuclid_continuousOn (I := I) g α
      exact (hdens_contOn.aemeasurable hS_meas).ennreal_ofReal
    · exact Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
    rw [show ENNReal.ofReal densitySup *
          ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂((volume : Measure EuclN).restrict S) =
        ∫⁻ y, ENNReal.ofReal densitySup * ‖f y‖ₑ ^ (2 : ℝ)
          ∂((volume : Measure EuclN).restrict S) from
      (MeasureTheory.lintegral_const_mul' (r := ENNReal.ofReal densitySup) _
        ENNReal.ofReal_ne_top).symm]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [Pi.mul_apply]
    by_cases hfy : f y = 0
    · simp [hfy, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    · have hy_in : y ∈ K := hf_supp hfy
      have h_dens_le :
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) ≤
            ENNReal.ofReal densitySup :=
        ENNReal.ofReal_le_ofReal (hdensitySup_bd y hy_in)
      gcongr
  refine le_trans (ENNReal.rpow_le_rpow h_lint_le (by positivity)) ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / 2)]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_pos hdensitySup_pos]

private def chartL2RestrictLin (α : M) (s : Set EuclN) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) →ₗ[ℝ]
      Lp ℝ 2 ((chartL2Measure (I := I) (M := M) α).restrict s) where
  toFun lp :=
    ((Lp.memLp lp).restrict s).toLp (lp : EuclN → ℝ)
  map_add' lp₁ lp₂ := by
    rw [show (((Lp.memLp lp₁).restrict s).toLp ((lp₁ : EuclN → ℝ)) +
          ((Lp.memLp lp₂).restrict s).toLp ((lp₂ : EuclN → ℝ))) =
        (((Lp.memLp lp₁).restrict s).add ((Lp.memLp lp₂).restrict s)).toLp
          ((lp₁ : EuclN → ℝ) + (lp₂ : EuclN → ℝ)) from
      (MemLp.toLp_add _ _).symm]
    refine MemLp.toLp_congr _ _ ?_
    exact (Measure.restrict_le_self.absolutelyContinuous).ae_eq
      (Lp.coeFn_add lp₁ lp₂)
  map_smul' c lp := by
    simp only [RingHom.id_apply]
    rw [show (c • ((Lp.memLp lp).restrict s).toLp ((lp : EuclN → ℝ))) =
        (((Lp.memLp lp).restrict s).const_smul c).toLp
          (c • (lp : EuclN → ℝ)) from (MemLp.toLp_const_smul c _).symm]
    refine MemLp.toLp_congr _ _ ?_
    exact (Measure.restrict_le_self.absolutelyContinuous).ae_eq
      (Lp.coeFn_smul c lp)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartL2RestrictLin_norm_le (α : M) (s : Set EuclN)
    (lp : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    ‖chartL2RestrictLin (I := I) (M := M) α s lp‖ ≤ 1 * ‖lp‖ := by
  classical
  rw [one_mul]
  rw [chartL2RestrictLin, LinearMap.coe_mk, AddHom.coe_mk,
    Lp.norm_toLp, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top lp) ?_
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

private def chartL2RestrictCLM (α : M) (s : Set EuclN) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) →L[ℝ]
      Lp ℝ 2 ((chartL2Measure (I := I) (M := M) α).restrict s) :=
  (chartL2RestrictLin (I := I) (M := M) α s).mkContinuous 1
    (chartL2RestrictLin_norm_le (I := I) (M := M) α s)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma chartL2RestrictCLM_apply (α : M) (s : Set EuclN)
    (lp : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    chartL2RestrictCLM (I := I) (M := M) α s lp =
      ((Lp.memLp lp).restrict s).toLp (lp : EuclN → ℝ) := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartL2RestrictCLM_eq_zero_iff (α : M) (s : Set EuclN)
    (lp : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    chartL2RestrictCLM (I := I) (M := M) α s lp = 0 ↔
      (lp : EuclN → ℝ)
        =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict s] 0 := by
  rw [chartL2RestrictCLM_apply, Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    exact (MemLp.coeFn_toLp _).symm.trans h
  · intro h
    exact (MemLp.coeFn_toLp _).trans h

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartL2RestrictCLM_tensorL2ChartComponentCutoff_smooth_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    chartL2RestrictCLM (I := I) (M := M) α
        (cutoffKernelEuclid (I := I) (M := M) α)ᶜ
        (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀
          (SmoothCcTensor.toL2 (g := g) (r := r) (s := s) S))
      = 0 := by
  classical
  have hKcompl_meas : MeasurableSet (cutoffKernelEuclid (I := I) (M := M) α)ᶜ :=
    (cutoffKernelEuclid_measurableSet (I := I) (M := M) α).compl
  have h_ae :
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (S : TensorL2 r s g) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
        =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
          (cutoffKernelEuclid (I := I) (M := M) α)ᶜ] 0 := by
    refine (MeasureTheory.ae_restrict_iff' hKcompl_meas).mpr ?_
    have h_coeFn :=
      tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
        (I := I) (M := M) g r s S α P₀
    filter_upwards [h_coeFn] with y hy hy_off
    have hy_zero :
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (S : TensorL2 r s g) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [hy]
      by_contra hne
      exact hy_off
        (cutoffComponentEuclid_support_subset_cutoffKernelEuclid
          (I := I) (M := M) g r s S α P₀ hne)
    simpa using hy_zero
  rw [tensorL2ChartComponentCutoffCLM_apply, SmoothCcTensor.toL2_apply]
  exact (chartL2RestrictCLM_eq_zero_iff (I := I) (M := M) α
    (cutoffKernelEuclid (I := I) (M := M) α)ᶜ
    (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
      (S : TensorL2 r s g) α P₀)).mpr h_ae

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2ChartComponentCutoff_aeEq_zero_off_cutoffKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        (cutoffKernelEuclid (I := I) (M := M) α)ᶜ] 0 := by
  classical
  have h_zero :
      chartL2RestrictCLM (I := I) (M := M) α
          (cutoffKernelEuclid (I := I) (M := M) α)ᶜ
          (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀ u)
        = 0 := by
    refine DenseRange.induction_on
      (SmoothCcTensor.denseRange_toL2
        (g := g) (r := r) (s := s))
      u ?_ ?_
    · exact isClosed_eq
        ((chartL2RestrictCLM (I := I) (M := M) α
            (cutoffKernelEuclid (I := I) (M := M) α)ᶜ).continuous.comp
          (tensorL2ChartComponentCutoffCLM
            (I := I) (M := M) g r s α P₀).continuous)
        continuous_const
    · intro S
      exact chartL2RestrictCLM_tensorL2ChartComponentCutoff_smooth_eq_zero
        (I := I) (M := M) g r s S α P₀
  have h_eq := (chartL2RestrictCLM_eq_zero_iff (I := I) (M := M) α
    (cutoffKernelEuclid (I := I) (M := M) α)ᶜ
    (tensorL2ChartComponentCutoffCLM
      (I := I) (M := M) g r s α P₀ u)).mp h_zero
  rw [tensorL2ChartComponentCutoffCLM_apply] at h_eq
  exact h_eq

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_tensorL2ChartComponentCutoff_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (u : TensorL2 r s g) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * ENNReal.ofReal ‖u‖ := by
  classical
  set w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ with hw_def
  set f : EuclN → ℝ := (w : EuclN → ℝ) with hf_def
  set K : Set EuclN := cutoffKernelEuclid (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    cutoffKernelEuclid_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    cutoffKernelEuclid_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    cutoffKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨_c_min, c_max, _hc_min_pos, hc_le, h_dens_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  have hc_max_pos : 0 < c_max := lt_of_lt_of_le _hc_min_pos hc_le
  set Cop : ℝ := ‖tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀‖
    with hCop_def
  have hCop_nn : 0 ≤ Cop :=
    norm_nonneg (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀)
  refine ⟨c_max ^ (1 / (2 : ℝ)) * Cop,
    mul_nonneg (Real.rpow_nonneg hc_max_pos.le _) hCop_nn, ?_⟩
  set fK : EuclN → ℝ := K.indicator f with hfK_def
  have h_off : f =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict Kᶜ] 0 :=
    tensorL2ChartComponentCutoff_aeEq_zero_off_cutoffKernel
      (I := I) (M := M) g r s u α P₀
  have hf_aeEq_fK : f =ᵐ[chartL2Measure (I := I) (M := M) α] fK := by
    rw [hfK_def]
    have hKcompl_meas : MeasurableSet Kᶜ := hK_meas.compl
    have h_off' : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∈ Kᶜ → f y = 0 := by
      rw [← MeasureTheory.ae_restrict_iff' hKcompl_meas]
      filter_upwards [h_off] with y hy using hy
    filter_upwards [h_off'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy (by simpa using hyK)]
  have hfK_supp : Function.support fK ⊆ K := by
    rw [hfK_def]; exact Set.support_indicator_subset
  have h_wabs : (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) ≪
        chartL2Measure (I := I) (M := M) α := by
    have h_cl2 : chartL2Measure (I := I) (M := M) α =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) := rfl
    rw [h_cl2]
    have h_base : (chartPulledWeightedMeasure (I := I) g α) ≪
        (volume : Measure EuclN) := by
      unfold chartPulledWeightedMeasure
      exact MeasureTheory.withDensity_absolutelyContinuous _ _
    exact h_base.restrict (chartTargetEuclid (I := I) (M := M) α)
  have hf_aeEq_fK_w : f =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)] fK :=
    h_wabs.ae_eq hf_aeEq_fK
  have hf_aeEq_fK_v : f =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)] fK := hf_aeEq_fK
  have hf_eLpNorm_eq : eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) =
      ‖w‖ₑ := by
    rw [hf_def, Lp.enorm_def]
  have hw_op : ‖w‖ ≤ Cop * ‖u‖ := by
    rw [hw_def, hCop_def,
      ← tensorL2ChartComponentCutoffCLM_apply (I := I) (M := M) g r s α P₀ u]
    exact (tensorL2ChartComponentCutoffCLM
      (I := I) (M := M) g r s α P₀).le_opNorm u
  calc eLpNorm f 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
      = eLpNorm fK 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_congr_ae hf_aeEq_fK_w
    _ ≤ ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          eLpNorm fK 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_chartPulledWeighted_restrict_le_of_support_subset
          (I := I) (M := M) g α c_max hc_max_pos
          (fun y hy => (h_dens_bd y hy).2) hfK_supp
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
        rw [show chartL2Measure (I := I) (M := M) α =
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α) from rfl,
          eLpNorm_congr_ae hf_aeEq_fK_v.symm]
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) * ‖w‖ₑ := by
        rw [hf_eLpNorm_eq]
    _ ≤ ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          ENNReal.ofReal (Cop * ‖u‖) := by
        gcongr
        rw [← ofReal_norm_eq_enorm w]
        exact ENNReal.ofReal_le_ofReal hw_op
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ)) * Cop) * ENNReal.ofReal ‖u‖ := by
        rw [ENNReal.ofReal_mul hCop_nn,
          ENNReal.ofReal_mul (Real.rpow_nonneg hc_max_pos.le _), mul_assoc]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_tensorL2ChartComponentCutoff_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : TensorL2 r s g,
        eLpNorm ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C * ENNReal.ofReal ‖u‖ := by
  classical
  set K : Set EuclN := cutoffKernelEuclid (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    cutoffKernelEuclid_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    cutoffKernelEuclid_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    cutoffKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨_c_min, c_max, _hc_min_pos, hc_le, h_dens_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  have hc_max_pos : 0 < c_max := lt_of_lt_of_le _hc_min_pos hc_le
  set Cop : ℝ := ‖tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀‖
    with hCop_def
  have hCop_nn : 0 ≤ Cop :=
    norm_nonneg (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀)
  refine ⟨c_max ^ (1 / (2 : ℝ)) * Cop,
    mul_nonneg (Real.rpow_nonneg hc_max_pos.le _) hCop_nn, fun u => ?_⟩
  set w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ with hw_def
  set f : EuclN → ℝ := (w : EuclN → ℝ) with hf_def
  set fK : EuclN → ℝ := K.indicator f with hfK_def
  have h_off : f =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict Kᶜ] 0 :=
    tensorL2ChartComponentCutoff_aeEq_zero_off_cutoffKernel
      (I := I) (M := M) g r s u α P₀
  have hf_aeEq_fK : f =ᵐ[chartL2Measure (I := I) (M := M) α] fK := by
    rw [hfK_def]
    have hKcompl_meas : MeasurableSet Kᶜ := hK_meas.compl
    have h_off' : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∈ Kᶜ → f y = 0 := by
      rw [← MeasureTheory.ae_restrict_iff' hKcompl_meas]
      filter_upwards [h_off] with y hy using hy
    filter_upwards [h_off'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy (by simpa using hyK)]
  have hfK_supp : Function.support fK ⊆ K := by
    rw [hfK_def]; exact Set.support_indicator_subset
  have h_wabs : (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) ≪
        chartL2Measure (I := I) (M := M) α := by
    have h_cl2 : chartL2Measure (I := I) (M := M) α =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) := rfl
    rw [h_cl2]
    have h_base : (chartPulledWeightedMeasure (I := I) g α) ≪
        (volume : Measure EuclN) := by
      unfold chartPulledWeightedMeasure
      exact MeasureTheory.withDensity_absolutelyContinuous _ _
    exact h_base.restrict (chartTargetEuclid (I := I) (M := M) α)
  have hf_aeEq_fK_w : f =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)] fK :=
    h_wabs.ae_eq hf_aeEq_fK
  have hf_aeEq_fK_v : f =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)] fK := hf_aeEq_fK
  have hf_eLpNorm_eq : eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) =
      ‖w‖ₑ := by
    rw [hf_def, Lp.enorm_def]
  have hw_op : ‖w‖ ≤ Cop * ‖u‖ := by
    rw [hw_def, hCop_def,
      ← tensorL2ChartComponentCutoffCLM_apply (I := I) (M := M) g r s α P₀ u]
    exact (tensorL2ChartComponentCutoffCLM
      (I := I) (M := M) g r s α P₀).le_opNorm u
  calc eLpNorm f 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
      = eLpNorm fK 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_congr_ae hf_aeEq_fK_w
    _ ≤ ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          eLpNorm fK 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_chartPulledWeighted_restrict_le_of_support_subset
          (I := I) (M := M) g α c_max hc_max_pos
          (fun y hy => (h_dens_bd y hy).2) hfK_supp
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
        rw [show chartL2Measure (I := I) (M := M) α =
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α) from rfl,
          eLpNorm_congr_ae hf_aeEq_fK_v.symm]
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) * ‖w‖ₑ := by
        rw [hf_eLpNorm_eq]
    _ ≤ ENNReal.ofReal (c_max ^ (1 / (2 : ℝ))) *
          ENNReal.ofReal (Cop * ‖u‖) := by
        gcongr
        rw [← ofReal_norm_eq_enorm w]
        exact ENNReal.ofReal_le_ofReal hw_op
    _ = ENNReal.ofReal (c_max ^ (1 / (2 : ℝ)) * Cop) * ENNReal.ofReal ‖u‖ := by
        rw [ENNReal.ofReal_mul hCop_nn,
          ENNReal.ofReal_mul (Real.rpow_nonneg hc_max_pos.le _), mul_assoc]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
