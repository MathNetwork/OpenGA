import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedData
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.VariationalIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThree
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DerivedChartBilinearH1ComplDataCanonical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.FChartEffDef
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH1ComplData
open DifferentialGeometry.Analysis.Laplacian.FChartResidualMemW1p
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private abbrev K_α (α : M) : Set EuclN :=
  chartImagePOUTsupport (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma K_α_compact (α : M) : IsCompact (K_α (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma K_α_meas (α : M) : MeasurableSet (K_α (I := I) (M := M) α) :=
  (K_α_compact (I := I) (M := M) α).isClosed.measurableSet

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma K_α_subset_target (α : M) :
    K_α (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  chartImagePOUTsupport_subset_target (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTarget_diff_K_α_isOpen (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
  (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
    (K_α_compact (I := I) (M := M) α).isClosed

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartTarget_diff_K_α_subset_target (α : M) :
    chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := fun _ hy => hy.1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_ae_zero_on_open_of_ae_zero_on_open
    {Ω U : Set EuclN} (hΩ_open : IsOpen Ω) (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ω)
    {f w : EuclN → ℝ}
    (i : Fin (Module.finrank ℝ E))
    (hw_isWeak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i w f Ω)
    (hw_li : LocallyIntegrableOn w U (volume : Measure EuclN))
    (hf_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict U), f y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict U), w y = 0 := by
  classical
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hf_ae_zero_vol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → f y = 0 := by
    rw [← ae_restrict_iff' hU_meas]; exact hf_ae_zero
  have h_target : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → w y = 0 := by
    apply hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hw_li
    intro ψ hψ_smooth hψ_cs hψ_supp
    have hψ_supp_Ω : tsupport ψ ⊆ Ω := hψ_supp.trans hU_sub
    have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
    have h_weak := hw_isWeak ψ hψ_smooth hψ_cs hψ_supp_Ω
    have h_f_supp_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
        f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1) = 0 := by
      refine (ae_restrict_iff' hΩ_meas).mpr ?_
      filter_upwards [hf_ae_zero_vol] with y hy _hyΩ
      by_cases hy_U : y ∈ U
      · rw [hy hy_U]; ring
      · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
          (isClosed_tsupport _).isOpen_compl
        have h_y_not_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp h)
        have h_zero_nbhd : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds h_y_not_supp] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
          have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_nbhd
          rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
        rw [h_fderiv_zero]; simp
    have h_zero_lhs :
        ∫ y in Ω, f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1)
          ∂(volume : Measure EuclN) = 0 := by
      rw [MeasureTheory.integral_congr_ae h_f_supp_ae]; simp
    rw [h_zero_lhs] at h_weak
    have h_rhs_zero :
        ∫ y in Ω, w y * ψ y ∂(volume : Measure EuclN) = 0 := by linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • w x = 0 := fun x hx => by
      have hx_supp : x ∉ tsupport ψ := fun h => hx (hψ_supp_Ω h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_supp
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_rhs_zero
    intro x _hxΩ; simp [smul_eq_mul, mul_comm]
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target] with y hy hy_U
  exact hy hy_U

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma vol_restrict_complement_absCont_chartTarget (α : M) :
    (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) :=
  MeasureTheory.Measure.absolutelyContinuous_of_le
    (MeasureTheory.Measure.restrict_mono
      (chartTarget_diff_K_α_subset_target (I := I) (M := M) α) le_rfl)

private lemma base_u_chart_aeEq_chartPushed
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := by
  classical
  have h_chartTarget_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_v_abs_w :
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro A hA
    unfold chartPulledWeightedMeasure at hA
    rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable
          h_chartTarget_meas))] at hA
    rw [Measure.restrict_apply' h_chartTarget_meas]
    rw [Measure.restrict_apply' h_chartTarget_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  have h_coeFn := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
    (H1ComplToLp (I := I) (M := M) g u_h)
  exact h_v_abs_w.ae_le h_coeFn

private lemma base_u_chart_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart y = 0 := by
  classical
  have h_aeEq := base_u_chart_aeEq_chartPushed (I := I) (M := M) g α hu_h
  have h_abs := vol_restrict_complement_absCont_chartTarget
    (I := I) (M := M) (α := α)
  have h_aeEq_restrict := h_abs.ae_le h_aeEq
  have h_diff_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
  refine (ae_restrict_iff' h_diff_meas).mpr ?_
  filter_upwards [(ae_restrict_iff' h_diff_meas).mp h_aeEq_restrict] with y hy hy_diff
  rw [hy hy_diff]
  exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _
    hy_diff.1 hy_diff.2


omit [NeZero (Module.finrank ℝ E)] in
private lemma locallyIntegrableOn_of_memLp_two_global
    (α : M) {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))) :
    LocallyIntegrableOn f
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) := by
  classical
  intro x hx
  have hΩ_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hΩ_open x hx
  set B : Set EuclN := Metric.closedBall x (r / 2)
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset : B ⊆ chartTargetEuclid (I := I) (M := M) α \
      K_α (I := I) (M := M) α := by
    intro y hy; apply hr_subset
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
  have hB_subset_chart : B ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => (hB_subset hy).1
  have hB_meas : MeasurableSet B := hB_compact.isClosed.measurableSet
  have h_restrict_eq : ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)).restrict B =
      (volume : Measure EuclN).restrict B := by
    rw [Measure.restrict_restrict hB_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hB_subset_chart
  have h_memLp_B : MemLp f 2 ((volume : Measure EuclN).restrict B) := by
    rw [← h_restrict_eq]; exact hf.restrict B
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn f B (volume : Measure EuclN) :=
    h_memLp_B.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x
    (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall


omit [NeZero (Module.finrank ℝ E)] in
private lemma locallyIntegrableOn_of_locally_memLp_two
    (α : M) {f : EuclN → ℝ}
    (hf : ∀ K' : Set EuclN, IsCompact K' →
      K' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp f 2 ((volume : Measure EuclN).restrict K')) :
    LocallyIntegrableOn f
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) := by
  classical
  intro x hx
  have hΩ_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hΩ_open x hx
  set B : Set EuclN := Metric.closedBall x (r / 2)
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset : B ⊆ chartTargetEuclid (I := I) (M := M) α \
      K_α (I := I) (M := M) α := by
    intro y hy; apply hr_subset
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
  have hB_subset_chart : B ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => (hB_subset hy).1
  have h_memLp := hf B hB_compact hB_subset_chart
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn f B (volume : Measure EuclN) :=
    h_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x
    (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall


omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma memLp_top_of_continuousOn_on_compact
    (α : M) {f : EuclN → ℝ}
    (hf_contOn : ContinuousOn f (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp f ∞ ((volume : Measure EuclN).restrict K) := by
  classical
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_K : ContinuousOn f K := hf_contOn.mono hK_in
  have h_meas : AEStronglyMeasurable f ((volume : Measure EuclN).restrict K) :=
    h_K.aestronglyMeasurable hK_meas
  have h_bd : ∃ C : ℝ, ∀ y ∈ K, |f y| ≤ C := by
    by_cases h_empty : K = ∅
    · refine ⟨0, fun y hy => ?_⟩
      rw [h_empty] at hy; exact absurd hy (Set.notMem_empty y)
    have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    have h_abs : ContinuousOn (fun y => |f y|) K :=
      continuous_abs.comp_continuousOn h_K
    obtain ⟨y_max, _, h_max⟩ := hK_compact.exists_isMaxOn hK_ne h_abs
    exact ⟨|f y_max|, fun y hy => h_max hy⟩
  obtain ⟨C, hC_bd⟩ := h_bd
  have h_ae_bd : ∀ᵐ y ∂((volume : Measure EuclN).restrict K), |f y| ≤ C := by
    refine (ae_restrict_iff' hK_meas).mpr ?_
    exact Filter.Eventually.of_forall hC_bd
  refine ⟨h_meas, ?_⟩
  rw [eLpNorm_exponent_top]
  refine lt_of_le_of_lt ?_
    (show (ENNReal.ofReal (max C 0) : ℝ≥0∞) < ⊤ from ENNReal.ofReal_lt_top)
  refine eLpNormEssSup_le_of_ae_enorm_bound (C := ENNReal.ofReal (max C 0)) ?_
  refine h_ae_bd.mono (fun y hy => ?_)
  rw [Real.enorm_eq_ofReal_abs]
  apply ENNReal.ofReal_le_ofReal
  exact hy.trans (le_max_left _ _)

lemma base_weak_partial_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).weak_partial i y = 0 := by
  classical
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub : chartTargetEuclid (I := I) (M := M) α \
      K_α (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_isWeak := D.weak_partial_isWeakPartial i
  have hw_li : LocallyIntegrableOn (D.weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) :=
    locallyIntegrableOn_of_locally_memLp_two (α := α) (f := D.weak_partial i)
      (fun K' hK' hK'_in => D.weak_partial_locally_memLp i K' hK' hK'_in)
  have hf_ae := base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α hu_h
  exact weakPartial_ae_zero_on_open_of_ae_zero_on_open
    hΩ_open hU_open hU_sub (i := i) h_isWeak hw_li hf_ae

private lemma chartPushed_first_weak_partial_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) y = 0 := by
  classical
  have h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushed_memW1p_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h
  have h_isWeak :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      h_w1p i
  have h_pushed_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) y = 0 := by
    have h_diff_meas : MeasurableSet
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
      (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
    refine (ae_restrict_iff' h_diff_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _
      hy.1 hy.2
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_chosen_memLp :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_w1p i
  have hw_li := locallyIntegrableOn_of_memLp_two_global (α := α)
    h_chosen_memLp
  exact weakPartial_ae_zero_on_open_of_ae_zero_on_open
    hΩ_open hU_open hU_sub (i := i) h_isWeak hw_li h_pushed_zero

private lemma chosenSecondPartialChartPushedU_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y = 0 := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  set g_i : EuclN → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 i
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)
  have h_g_i_ae_zero :=
    chartPushed_first_weak_partial_ae_zero_off_K_α (I := I) (M := M)
      g α hu_h i
  have h_unfold : chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j g_i
        (chartTargetEuclid (I := I) (M := M) α) := rfl
  rw [h_unfold]
  have h_g_i_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 g_i
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_step := (laplacianDomainPow_two_chartPushed_memWkp_two_two
      (I := I) (M := M) g α hu_h).chosenWeakPartial_mem i
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
      at h_step
    exact h_step
  have h_isWeak :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      h_g_i_memW1p j
  have h_chosen_second_memLp :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_g_i_memW1p j
  have hw_li := locallyIntegrableOn_of_memLp_two_global (α := α)
    h_chosen_second_memLp
  exact weakPartial_ae_zero_on_open_of_ae_zero_on_open
    hΩ_open hU_open hU_sub (i := j) h_isWeak hw_li h_g_i_ae_zero

private lemma base_f_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart) 2
      ((volume : Measure EuclN).restrict K) := by
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  have h_weighted := D.f_chart_memLp_weighted
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_compact.isClosed.measurableSet hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : MemLp D.f_chart 2
      (ENNReal.ofReal c • ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

lemma base_f_chart_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart y = 0 := by
  classical
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  set U : Set EuclN := Ω \ K_α (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hK_meas : MeasurableSet (K_α (I := I) (M := M) α) :=
    K_α_meas (I := I) (M := M) α
  have h_fc_li : LocallyIntegrableOn D.f_chart U
      (volume : Measure EuclN) :=
    locallyIntegrableOn_of_locally_memLp_two (α := α) (f := D.f_chart)
      (fun K' hK' hK'_in => base_f_chart_locally_memLp (I := I) (M := M) g α
        hu_h hK' hK'_in)
  have h_density_contOn : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_continuousOn (I := I) g α
  have h_prod_locInt : LocallyIntegrableOn
      (fun y => densityOnEuclid (I := I) g α y * D.f_chart y) U
      (volume : Measure EuclN) := by
    intro x hx
    obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hU_open x hx
    set B : Set EuclN := Metric.closedBall x (r / 2)
    have hB_compact : IsCompact B := isCompact_closedBall _ _
    have hB_subset_U : B ⊆ U := by
      intro y hy; apply hr_subset
      rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
    have hB_subset_Ω : B ⊆ Ω := fun y hy => hU_sub (hB_subset_U hy)
    have h_fchart_K_memLp := base_f_chart_locally_memLp (I := I) (M := M) g α
      hu_h hB_compact hB_subset_Ω
    have hB_meas : MeasurableSet B := hB_compact.isClosed.measurableSet
    have h_density_memLp_top := memLp_top_of_continuousOn_on_compact
      (α := α) h_density_contOn hB_compact hB_subset_Ω
    have h_prod_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y *
        D.f_chart y) 2 ((volume : Measure EuclN).restrict B) :=
      MemLp.mul' (p := ∞) (q := 2) (r := 2) h_fchart_K_memLp h_density_memLp_top
    have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
    haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hB_finite
    have h_int : IntegrableOn (fun y => densityOnEuclid (I := I) g α y *
        D.f_chart y) B (volume : Measure EuclN) :=
      h_prod_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    refine ⟨B, ?_, h_int⟩
    refine Filter.mem_inf_of_left ?_
    apply Filter.mem_of_superset (Metric.ball_mem_nhds x
      (by linarith : 0 < r / 2))
    exact Metric.ball_subset_closedBall
  have h_zero_for_test : ∀ ψ : EuclN → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      ∫ y, ψ y • (densityOnEuclid (I := I) g α y * D.f_chart y)
        ∂(volume : Measure EuclN) = 0 := by
    intro ψ hψ_smooth hψ_cs hψ_supp_U
    have hψ_supp_chart : tsupport ψ ⊆ Ω := hψ_supp_U.trans hU_sub
    have h_var := D.variational_identity ψ hψ_smooth hψ_cs hψ_supp_chart
    change (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.f_chart y * ψ y
        ∂(volume : Measure EuclN) at h_var
    have h_principal_zero :
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) = 0 := by
      have h_integrand_ae_zero :
          (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =ᵐ[
            (volume : Measure EuclN).restrict Ω]
            (fun _ : EuclN => (0 : ℝ)) := by
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_wp_each : ∀ i : Fin (Module.finrank ℝ E),
            ∀ᵐ y ∂((volume : Measure EuclN).restrict U),
              D.weak_partial i y = 0 := fun i =>
          base_weak_partial_ae_zero_off_K_α (I := I) (M := M) g α hu_h i
        have h_wp_all_vol : ∀ᵐ y ∂(volume : Measure EuclN),
            ∀ i : Fin (Module.finrank ℝ E),
              y ∈ U → D.weak_partial i y = 0 := by
          rw [ae_all_iff]; intro i
          rw [← ae_restrict_iff' hU_meas]
          exact h_wp_each i
        filter_upwards [h_wp_all_vol] with y hy _hyΩ
        by_cases hy_U : y ∈ U
        · refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [hy i hy_U]; ring
        · have h_y_not_in_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp_U h)
          have h_compl_open : IsOpen (tsupport ψ)ᶜ :=
            (isClosed_tsupport _).isOpen_compl
          have h_zero_nbhd : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
            filter_upwards [h_compl_open.mem_nhds h_y_not_in_supp] with z hz
            exact image_eq_zero_of_notMem_tsupport hz
          have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
            have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_nbhd
            rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
          refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [h_fderiv_zero]; simp
      rw [MeasureTheory.integral_congr_ae h_integrand_ae_zero]; simp
    have h_mass_zero :
        ∫ y in Ω, densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
          ∂(volume : Measure EuclN) = 0 := by
      have h_integrand_ae_zero :
          (fun y : EuclN => densityOnEuclid (I := I) g α y * D.u_chart y * ψ y) =ᵐ[
            (volume : Measure EuclN).restrict Ω]
            (fun _ : EuclN => (0 : ℝ)) := by
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_uc_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict U),
            D.u_chart y = 0 :=
          base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α hu_h
        have h_uc_vol : ∀ᵐ y ∂(volume : Measure EuclN),
            y ∈ U → D.u_chart y = 0 := by
          rw [← ae_restrict_iff' hU_meas]; exact h_uc_ae
        filter_upwards [h_uc_vol] with y hy _hyΩ
        by_cases hy_U : y ∈ U
        · rw [hy hy_U]; ring
        · have h_y_not_in_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp_U h)
          have hψ_zero : ψ y = 0 := image_eq_zero_of_notMem_tsupport h_y_not_in_supp
          rw [hψ_zero]; ring
      rw [MeasureTheory.integral_congr_ae h_integrand_ae_zero]; simp
    rw [h_principal_zero, h_mass_zero, zero_add] at h_var
    have h_vanish_off_chart : ∀ x ∉ Ω,
        ψ x • (densityOnEuclid (I := I) g α x * D.f_chart x) = 0 := fun x hx => by
      have hx_not_supp : x ∉ tsupport ψ := fun h => hx (hψ_supp_chart h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_supp
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_chart]
    rw [show (fun x : EuclN => ψ x • (densityOnEuclid (I := I) g α x *
        D.f_chart x)) = (fun y : EuclN =>
        densityOnEuclid (I := I) g α y * D.f_chart y * ψ y) by
      funext y; simp [smul_eq_mul, mul_comm]]
    exact h_var.symm
  have h_cf_ae_zero : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U →
      densityOnEuclid (I := I) g α y * D.f_chart y = 0 :=
    hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero h_prod_locInt
      h_zero_for_test
  have h_target_ae : ∀ᵐ y ∂(volume : Measure EuclN),
      y ∈ U → D.f_chart y = 0 := by
    filter_upwards [h_cf_ae_zero] with y hy hy_U
    have h_cf := hy hy_U
    have h_density_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α (hU_sub hy_U)
    exact (mul_eq_zero.mp h_cf).resolve_left h_density_pos.ne'
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target_ae] with y hy hy_U
  exact hy hy_U

private lemma chosenFChartDeriv_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenFChartDeriv (I := I) (M := M) g α hu_h l y = 0 := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  have h_isWeak := chosenFChartDeriv_isWeakPartial (I := I) (M := M)
    g α hu_h l h_memW1p
  have h_global : MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    unfold chosenFChartDeriv
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_memW1p l
  have hw_li := locallyIntegrableOn_of_memLp_two_global (α := α) h_global
  have h_base_fc_ae := base_f_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  exact weakPartial_ae_zero_on_open_of_ae_zero_on_open
    hΩ_open hU_open hU_sub (i := l) h_isWeak hw_li h_base_fc_ae

private lemma fChartEffNumerator_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      diffChartForcingNumerator (I := I) (M := M) g α l hu_h y = 0 := by
  classical
  have h_fc_deriv := chosenFChartDeriv_ae_zero_off_K_α (I := I) (M := M) g α hu_h l
  have h_uc := base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  have h_fc := base_f_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  have h_wp_each : ∀ i : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)
          ).weak_partial i y = 0 := fun i =>
    base_weak_partial_ae_zero_off_K_α (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i
  have h_cspu_each : ∀ i j : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
        chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h i j y = 0 := fun i j =>
    chosenSecondPartialChartPushedU_ae_zero_off_K_α (I := I) (M := M)
      g α hu_h i j
  have h_wp_combine : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i : Fin (Module.finrank ℝ E),
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)
          ).weak_partial i y = 0 := by
    rw [ae_all_iff]; exact h_wp_each
  have h_cspu_combine : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i j : Fin (Module.finrank ℝ E),
        chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h i j y = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact h_cspu_each i j
  filter_upwards [h_fc_deriv, h_uc, h_fc, h_wp_combine, h_cspu_combine]
    with y hy_fcd hy_uc hy_fc hy_wp hy_cspu
  unfold diffChartForcingNumerator
  have h_sum_wp_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M)
                g 1 hu_h)).weak_partial i y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro j _
    rw [hy_wp i]; ring
  have h_sum_cspu_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i j y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro j _
    rw [hy_cspu i j]; ring
  rw [hy_fcd, hy_uc, hy_fc, h_sum_wp_zero, h_sum_cspu_zero]; ring

private lemma integral_fChartEffNumerator_eq_integral_density_fChartEff
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (ψ : EuclN → ℝ) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        diffChartForcingNumerator (I := I) (M := M) g α l hu_h y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          diffChartForcing (I := I) (M := M) g α l hu_h y * ψ y
        ∂(volume : Measure EuclN) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hU_meas : MeasurableSet (Ω \ K_α (I := I) (M := M) α) :=
    hΩ_meas.diff (K_α_meas (I := I) (M := M) α)
  have h_ae_eq : (fun y : EuclN =>
      diffChartForcingNumerator (I := I) (M := M) g α l hu_h y * ψ y) =ᵐ[
      (volume : Measure EuclN).restrict Ω]
      (fun y : EuclN => densityOnEuclid (I := I) g α y *
        diffChartForcing (I := I) (M := M) g α l hu_h y * ψ y) := by
    have h_numer_off := fChartEffNumerator_ae_zero_off_K_α
      (I := I) (M := M) g α l hu_h
    refine (ae_restrict_iff' hΩ_meas).mpr ?_
    have h_off_vol : ∀ᵐ y ∂(volume : Measure EuclN),
        y ∈ Ω \ K_α (I := I) (M := M) α →
        diffChartForcingNumerator (I := I) (M := M) g α l hu_h y = 0 := by
      rw [← ae_restrict_iff' hU_meas]; exact h_numer_off
    filter_upwards [h_off_vol] with y hy hy_Ω
    by_cases hy_K : y ∈ K_α (I := I) (M := M) α
    · have h_pt := density_mul_diffChartForcing_eq_indicator_numerator
        (I := I) (M := M) g α l hu_h y hy_Ω
      rw [Set.indicator_of_mem hy_K] at h_pt
      rw [h_pt]
    · have hy_diff : y ∈ Ω \ K_α (I := I) (M := M) α := ⟨hy_Ω, hy_K⟩
      rw [hy hy_diff]
      have h_pt := density_mul_diffChartForcing_eq_indicator_numerator
        (I := I) (M := M) g α l hu_h y hy_Ω
      rw [Set.indicator_of_notMem hy_K] at h_pt
      rw [h_pt]
  exact MeasureTheory.integral_congr_ae h_ae_eq

theorem derived_variational_identity_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i l y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial l y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        diffChartForcing (I := I) (M := M) g α l hu_h y * ψ y
      ∂(volume : Measure EuclN) := by
  classical
  have h_diff := differentiated_variational_identity_holds
    (I := I) (M := M) g α hu_h l hψ_smooth hψ_cs hψ_supp
  have h_cross := cross_derivative_term_ibp (I := I) (M := M) g α hu_h l
    hψ_smooth hψ_cs hψ_supp
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  set D_base := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
    g α (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h)
  set LHS_p : ℝ := ∫ y in Ω,
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
    ∂(volume : Measure EuclN)
  set LHS_m : ℝ := ∫ y in Ω,
    densityOnEuclid (I := I) g α y * D_base.weak_partial l y * ψ y
    ∂(volume : Measure EuclN)
  set T3 : ℝ := ∫ y in Ω,
    densityOnEuclid (I := I) g α y *
      chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y
    ∂(volume : Measure EuclN)
  set A1_cross : ℝ := ∫ y in Ω,
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          D_base.weak_partial i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
    ∂(volume : Measure EuclN)
  set A2_cross : ℝ := ∫ y in Ω,
    densityDerivOnEuclid (I := I) g α l y * D_base.u_chart y * ψ y
    ∂(volume : Measure EuclN)
  set B_cross : ℝ := ∫ y in Ω,
    densityDerivOnEuclid (I := I) g α l y * D_base.f_chart y * ψ y
    ∂(volume : Measure EuclN)
  set I_partials : ℝ := ∫ y in Ω,
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
          D_base.weak_partial i y * ψ y)
    ∂(volume : Measure EuclN)
  set I_cspu : ℝ := ∫ y in Ω,
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
    ∂(volume : Measure EuclN)
  have h_diff' : LHS_p + LHS_m = T3 - A1_cross - A2_cross + B_cross := h_diff
  have h_cross' : A1_cross = -(I_partials + I_cspu) := h_cross
  have h_combined : LHS_p + LHS_m = T3 + I_partials + I_cspu - A2_cross + B_cross := by
    rw [h_diff', h_cross']; ring
  have h_RHS_eq_num : T3 + I_partials + I_cspu - A2_cross + B_cross =
      ∫ y in Ω,
        diffChartForcingNumerator (I := I) (M := M) g α l hu_h y * ψ y
        ∂(volume : Measure EuclN) := by
    set K : Set EuclN := tsupport ψ
    have hψ_cont : Continuous ψ := hψ_smooth.continuous
    have hK_compact : IsCompact K := hψ_cs
    have hK_in : K ⊆ Ω := hψ_supp
    have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_sum_distrib_ψ : ∀ (F : Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → ℝ) (z : ℝ),
        (∑ i, ∑ j, F i j) * z = ∑ i, ∑ j, F i j * z := by
      intro F z
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
    have h_integrand_eq : (fun y : EuclN =>
        diffChartForcingNumerator (I := I) (M := M) g α l hu_h y * ψ y) =
        (fun y => densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y) +
        (fun y => (∑ i, ∑ j,
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                (EuclideanSpace.single j 1) *
              D_base.weak_partial i y * ψ y)) +
        (fun y => (∑ i, ∑ j,
              weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
              ψ y)) -
        (fun y => densityDerivOnEuclid (I := I) g α l y *
            D_base.u_chart y * ψ y) +
        (fun y => densityDerivOnEuclid (I := I) g α l y *
            D_base.f_chart y * ψ y) := by
      funext y
      unfold diffChartForcingNumerator
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [← h_sum_distrib_ψ (fun i j =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) * D_base.weak_partial i y) (ψ y),
        ← h_sum_distrib_ψ (fun i j =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenSecondPartialChartPushedU
            (I := I) (M := M) g α u_h i j y) (ψ y)]
      ring
    rw [h_integrand_eq]
    have hK_finite : (volume : Measure EuclN) K < ⊤ := hK_compact.measure_lt_top
    haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hK_finite
    have integrable_mul_compact_loc :
        ∀ {f : EuclN → ℝ}, (∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
            MemLp f 2 ((volume : Measure EuclN).restrict K')) →
          Integrable (fun y => f y * ψ y)
            ((volume : Measure EuclN).restrict Ω) := by
      intro f hf
      have h_f_K : MemLp f 2 ((volume : Measure EuclN).restrict K) :=
        hf K hK_compact hK_in
      have h_f_K_int : IntegrableOn f K (volume : Measure EuclN) :=
        h_f_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hψ_K_cont : ContinuousOn ψ K := hψ_cont.continuousOn
      have h_mul_K : IntegrableOn (fun y => f y * ψ y) K (volume : Measure EuclN) :=
        h_f_K_int.mul_continuousOn hψ_K_cont hK_compact
      have h_vanish_off_K : ∀ y, y ∉ K → f y * ψ y = 0 := by
        intro y hy
        have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [this]
      have h_eq_ind : (fun y => f y * ψ y) =
          K.indicator (fun y => f y * ψ y) := by
        funext y
        by_cases hy : y ∈ K
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy, h_vanish_off_K y hy]
      have h_ind_int : Integrable (K.indicator (fun y => f y * ψ y))
          (volume : Measure EuclN) :=
        (integrable_indicator_iff hK_meas).mpr h_mul_K
      have h_full : Integrable (fun y => f y * ψ y) (volume : Measure EuclN) := by
        rw [h_eq_ind]; exact h_ind_int
      exact h_full.restrict
    have h_memW1p :=
      base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
        (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
    have h_chosenFC_memLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
        MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l) 2
          ((volume : Measure EuclN).restrict K') := by
      intro K' hK' hK'_in
      have h_global : MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l) 2
          ((volume : Measure EuclN).restrict Ω) := by
        unfold chosenFChartDeriv
        exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
          h_memW1p l
      have hK'_meas : MeasurableSet K' := hK'.isClosed.measurableSet
      have h_restrict_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
          (volume : Measure EuclN).restrict K' := by
        rw [Measure.restrict_restrict hK'_meas]
        congr 1
        exact Set.inter_eq_self_of_subset_left hK'_in
      rw [← h_restrict_eq]; exact h_global.restrict K'
    have h_T3_int : Integrable (fun y => densityOnEuclid (I := I) g α y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := by
      apply integrable_mul_compact_loc
      intro K' hK' hK'_in
      have h_fc_K := h_chosenFC_memLp K' hK' hK'_in
      have h_density_memLp_top := memLp_top_of_continuousOn_on_compact
        (α := α) (densityOnEuclid_continuousOn (I := I) g α) hK' hK'_in
      exact MemLp.mul' (p := ∞) (q := 2) (r := 2) h_fc_K h_density_memLp_top
    have h_partials_int : Integrable (fun y => (∑ i, ∑ j,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
          D_base.weak_partial i y * ψ y))
        ((volume : Measure EuclN).restrict Ω) := by
      have h_pair_int : ∀ i j : Fin (Module.finrank ℝ E),
          Integrable (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid
            (I := I) g α i j l) y) (EuclideanSpace.single j 1) *
            D_base.weak_partial i y * ψ y)
          ((volume : Measure EuclN).restrict Ω) := by
        intro i j
        apply integrable_mul_compact_loc
        intro K' hK' hK'_in
        have h_wp_K := D_base.weak_partial_locally_memLp i K' hK' hK'_in
        have h_coef_contOn : ContinuousOn (fun y =>
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1)) Ω := by
          have h_diffOn := weightedInvGramDerivOnEuclid_contDiffOn
            (I := I) g α i j l
          have h_fderiv_diff :
              ContDiffOn ℝ (⊤ : ℕ∞)
                (fun y => fderiv ℝ
                  (weightedInvGramDerivOnEuclid (I := I) g α i j l) y) Ω :=
            ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ_open).1 h_diffOn).2
          have h_eval : ContDiff ℝ (⊤ : ℕ∞)
              (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
            (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
          exact (h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)).continuousOn
        have h_coef_memLp_top := memLp_top_of_continuousOn_on_compact
          (α := α) h_coef_contOn hK' hK'_in
        exact MemLp.mul' (p := ∞) (q := 2) (r := 2) h_wp_K h_coef_memLp_top
      have h_inner : ∀ i, Integrable (fun y => ∑ j, (fderiv ℝ
            (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            D_base.weak_partial i y * ψ y)
            ((volume : Measure EuclN).restrict Ω) :=
        fun i => integrable_finset_sum _ (fun j _ => h_pair_int i j)
      exact integrable_finset_sum _ (fun i _ => h_inner i)
    have h_cspu_int : Integrable (fun y => (∑ i, ∑ j,
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y))
        ((volume : Measure EuclN).restrict Ω) := by
      have h_pair_int : ∀ i j : Fin (Module.finrank ℝ E),
          Integrable (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
          ((volume : Measure EuclN).restrict Ω) := by
        intro i j
        apply integrable_mul_compact_loc
        intro K' hK' hK'_in
        have h_cspu_K := chosenSecondPartialChartPushedU_locally_memLp
          (I := I) (M := M) g α hu_h i j hK' hK'_in
        have h_coef_memLp_top := memLp_top_of_continuousOn_on_compact
          (α := α)
          (weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l)
          hK' hK'_in
        exact MemLp.mul' (p := ∞) (q := 2) (r := 2) h_cspu_K h_coef_memLp_top
      have h_inner : ∀ i, Integrable (fun y => ∑ j,
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
            ((volume : Measure EuclN).restrict Ω) :=
        fun i => integrable_finset_sum _ (fun j _ => h_pair_int i j)
      exact integrable_finset_sum _ (fun i _ => h_inner i)
    have h_A2_int : Integrable (fun y => densityDerivOnEuclid (I := I) g α l y *
        D_base.u_chart y * ψ y) ((volume : Measure EuclN).restrict Ω) := by
      apply integrable_mul_compact_loc
      intro K' hK' hK'_in
      have h_uc_K : MemLp D_base.u_chart 2
          ((volume : Measure EuclN).restrict K') := by
        have h_weighted := D_base.u_chart_memLp_weighted
        obtain ⟨c, _hc_pos, h_le⟩ :=
          volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
            (g := g) (α := α) hK' hK'.isClosed.measurableSet hK'_in
        have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
        have h_smul : MemLp D_base.u_chart 2
            (ENNReal.ofReal c • ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) :=
          h_weighted.smul_measure hc_ne_top
        exact h_smul.mono_measure h_le
      have h_coef_memLp_top := memLp_top_of_continuousOn_on_compact
        (α := α)
        (densityDerivOnEuclid_continuousOn (I := I) g α l) hK' hK'_in
      exact MemLp.mul' (p := ∞) (q := 2) (r := 2) h_uc_K h_coef_memLp_top
    have h_B_int : Integrable (fun y => densityDerivOnEuclid (I := I) g α l y *
        D_base.f_chart y * ψ y) ((volume : Measure EuclN).restrict Ω) := by
      apply integrable_mul_compact_loc
      intro K' hK' hK'_in
      have h_fc_K := base_f_chart_locally_memLp (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
        hK' hK'_in
      have h_coef_memLp_top := memLp_top_of_continuousOn_on_compact
        (α := α)
        (densityDerivOnEuclid_continuousOn (I := I) g α l) hK' hK'_in
      exact MemLp.mul' (p := ∞) (q := 2) (r := 2) h_fc_K h_coef_memLp_top
    have h_step1 : Integrable (fun y =>
        densityOnEuclid (I := I) g α y *
          chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y +
        ((∑ i, ∑ j,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            D_base.weak_partial i y * ψ y)))
        ((volume : Measure EuclN).restrict Ω) := h_T3_int.add h_partials_int
    have h_step2 : Integrable (fun y =>
        (densityOnEuclid (I := I) g α y *
          chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y +
        ∑ i, ∑ j,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            D_base.weak_partial i y * ψ y) +
        ((∑ i, ∑ j,
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
            ψ y)))
        ((volume : Measure EuclN).restrict Ω) := h_step1.add h_cspu_int
    have h_step3 : Integrable (fun y =>
        ((densityOnEuclid (I := I) g α y *
          chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y +
        ∑ i, ∑ j,
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            D_base.weak_partial i y * ψ y) +
        ∑ i, ∑ j,
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y *
            ψ y) -
        (densityDerivOnEuclid (I := I) g α l y *
          D_base.u_chart y * ψ y))
        ((volume : Measure EuclN).restrict Ω) := h_step2.sub h_A2_int
    have h_T3_pi : Integrable (fun y => densityOnEuclid (I := I) g α y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := h_T3_int
    have h_partials_pi : Integrable (fun y => ∑ i, ∑ j,
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
          D_base.weak_partial i y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := h_partials_int
    have h_cspu_pi : Integrable (fun y => ∑ i, ∑ j,
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := h_cspu_int
    have h_A2_pi : Integrable (fun y => densityDerivOnEuclid (I := I) g α l y *
        D_base.u_chart y * ψ y) ((volume : Measure EuclN).restrict Ω) := h_A2_int
    have h_B_pi : Integrable (fun y => densityDerivOnEuclid (I := I) g α l y *
        D_base.f_chart y * ψ y) ((volume : Measure EuclN).restrict Ω) := h_B_int
    rw [MeasureTheory.integral_add' (h_T3_pi.add h_partials_pi |>.add h_cspu_pi |>.sub h_A2_pi) h_B_pi]
    rw [MeasureTheory.integral_sub' (h_T3_pi.add h_partials_pi |>.add h_cspu_pi) h_A2_pi]
    rw [MeasureTheory.integral_add' (h_T3_pi.add h_partials_pi) h_cspu_pi]
    rw [MeasureTheory.integral_add' h_T3_pi h_partials_pi]
  rw [h_RHS_eq_num] at h_combined
  rw [h_combined]
  exact integral_fChartEffNumerator_eq_integral_density_fChartEff
    (I := I) (M := M) g α l hu_h ψ


noncomputable def derivedChartBilinearH1ComplDataUnconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ChartBilinearH1ComplData (I := I) (M := M) g α :=
  derivedChartBilinearH1ComplData (I := I) (M := M) g α l hu_h
    (fun _ψ hψ hψ_cs hψ_supp =>
      derived_variational_identity_holds (I := I) (M := M) g α l hu_h
        hψ hψ_cs hψ_supp)

lemma chosenSecondPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)),
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y = 0 :=
  chosenSecondPartialChartPushedU_ae_zero_off_K_α
    (I := I) (M := M) g α hu_h i j

end DerivedChartBilinearH1ComplDataCanonical
end Laplacian
end Analysis
end DifferentialGeometry

end
