import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.LeibnizCompensatedSource
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.VariationalLimit
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.VariationalLimitAnyTest
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
import DifferentialGeometry.Analysis.Elliptic.Operator.ChartMeasureEquiv
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPulledIntegralContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private def chartSrcPreimage (α : M) (θ : EuclN → ℝ) : Set M :=
  (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ''
    (tsupport θ)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartSrcPreimage_isCompact
    (α : M) {θ : EuclN → ℝ} (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    IsCompact (chartSrcPreimage (I := I) (M := M) α θ) := by
  classical
  unfold chartSrcPreimage
  exact (hθ_cs : IsCompact (tsupport θ)).image_of_continuousOn
    ((continuousOn_symm_toEuclideanSymm (I := I) (M := M) α).mono hθ_supp)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartSrcPreimage_subset_chartSource
    (α : M) {θ : EuclN → ℝ}
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    chartSrcPreimage (I := I) (M := M) α θ ⊆ (chartAt H α).source := by
  classical
  unfold chartSrcPreimage
  intro x hx
  rcases hx with ⟨y, hy_supp, hxy⟩
  rw [← hxy]
  exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α (hθ_supp hy_supp)

noncomputable def chartPulledIntegralWeight
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) : M → ℝ := by
  classical
  exact fun x : M =>
    if hx : x ∈ (chartAt H α).source then
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) / chartDensity g α x
    else 0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma chartPulledIntegralWeight_apply_of_mem
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x =
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) / chartDensity g α x := by
  classical
  unfold chartPulledIntegralWeight
  exact dif_pos hx

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartPulledIntegralWeight_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 := by
  classical
  unfold chartPulledIntegralWeight
  exact dif_neg hx

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartPulledIntegralWeight_apply_zero_off_preimage
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ} {x : M}
    (hx_src : x ∈ (chartAt H α).source)
    (hx_off : x ∉ chartSrcPreimage (I := I) (M := M) α θ) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 := by
  classical
  rw [chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx_src]
  have hTx_not_in : (toEuclidean (E := E)) ((extChartAt I α) x) ∉ tsupport θ := by
    intro h_in
    apply hx_off
    refine ⟨(toEuclidean (E := E)) ((extChartAt I α) x), h_in, ?_⟩
    change (extChartAt I α).symm
        ((toEuclidean (E := E)).symm ((toEuclidean (E := E))
          ((extChartAt I α) x))) = x
    have hsymm_inv : (toEuclidean (E := E)).symm ((toEuclidean (E := E))
        ((extChartAt I α) x)) = (extChartAt I α) x :=
      (toEuclidean (E := E)).symm_apply_apply _
    rw [hsymm_inv]
    have hxE : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hx_src
    exact (extChartAt I α).left_inv hxE
  have hθ_zero : θ ((toEuclidean (E := E)) ((extChartAt I α) x)) = 0 :=
    image_eq_zero_of_notMem_tsupport hTx_not_in
  rw [hθ_zero, zero_div]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartPulledIntegralWeight_support_subset
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) :
    Function.support (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      chartSrcPreimage (I := I) (M := M) α θ := by
  classical
  intro x hx
  rw [Function.mem_support] at hx
  by_cases hx_src : x ∈ (chartAt H α).source
  · by_contra hx_not
    have h_zero := chartPulledIntegralWeight_apply_zero_off_preimage
      (I := I) (M := M) g α (θ := θ) hx_src hx_not
    exact hx h_zero
  · have h_zero := chartPulledIntegralWeight_apply_of_notMem
      (I := I) (M := M) g α θ hx_src
    exact (hx h_zero).elim

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartPulledIntegralWeight_tsupport_subset
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      chartSrcPreimage (I := I) (M := M) α θ := by
  classical
  refine closure_minimal
    (chartPulledIntegralWeight_support_subset (I := I) (M := M) g α θ) ?_
  exact (chartSrcPreimage_isCompact (I := I) (M := M) α hθ_cs hθ_supp).isClosed

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPulledIntegralWeight_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    HasCompactSupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) :=
  HasCompactSupport.of_support_subset_isCompact
    (chartSrcPreimage_isCompact (I := I) (M := M) α hθ_cs hθ_supp)
    (chartPulledIntegralWeight_support_subset (I := I) (M := M) g α θ)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartPulledIntegralWeight_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      (chartAt H α).source :=
  (chartPulledIntegralWeight_tsupport_subset (I := I) (M := M) g α
      hθ_cs hθ_supp).trans
    (chartSrcPreimage_subset_chartSource (I := I) (M := M) α hθ_supp)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chart_map_continuousOn (α : M) :
    ContinuousOn (fun x : M => (toEuclidean (E := E)) ((extChartAt I α) x))
      (chartAt H α).source := by
  have h_ext : ContinuousOn (extChartAt I α) (chartAt H α).source := by
    have h_src : (chartAt H α).source = (extChartAt I α).source :=
      (DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M) α).symm
    rw [h_src]; exact continuousOn_extChartAt α
  exact (toEuclidean (E := E)).continuous.continuousOn.comp h_ext (Set.mapsTo_univ _ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartPulledIntegralWeight_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) :
    ContinuousOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
      (chartAt H α).source := by
  classical
  have h_eq : EqOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
      (fun x : M => θ ((toEuclidean (E := E)) ((extChartAt I α) x)) /
        chartDensity g α x)
      (chartAt H α).source := by
    intro x hx
    exact chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx
  refine ContinuousOn.congr ?_ h_eq
  have h_num_cont : ContinuousOn (fun x : M =>
      θ ((toEuclidean (E := E)) ((extChartAt I α) x))) (chartAt H α).source :=
    hθ_cont.continuousOn.comp (chart_map_continuousOn (I := I) (M := M) α)
      (Set.mapsTo_univ _ _)
  have h_dens_cont : ContinuousOn (chartDensity g α) (chartAt H α).source := by
    rw [show (chartAt H α).source =
        (trivializationAt E (TangentSpace I) α).baseSet from
      (DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
        (I := I) (M := M) α).symm]
    exact DifferentialGeometry.Integral.Measure.chartDensity_continuousOn
      (I := I) (M := M) g α
  have h_dens_ne_zero : ∀ x ∈ (chartAt H α).source, chartDensity g α x ≠ 0 := by
    intro x hx
    have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
        (I := I) (M := M)]
      exact hx
    exact (DifferentialGeometry.Integral.Measure.chartDensity_pos
      (I := I) g α hx_base).ne'
  exact h_num_cont.div h_dens_cont h_dens_ne_zero

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M] in
lemma chartPulledIntegralWeight_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
  classical
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx_in : x ∈ (chartAt H α).source
  · have h_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
    have h_contOn := chartPulledIntegralWeight_continuousOn_chartSource
      (I := I) (M := M) g α (θ := θ) hθ_cont
    exact h_contOn.continuousAt (h_open.mem_nhds hx_in)
  · have h_supp_sub : tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
        (chartAt H α).source :=
      chartPulledIntegralWeight_tsupport_subset_chartSource
        (I := I) (M := M) g α hθ_cs hθ_supp
    have hx_not_supp : x ∉ tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) :=
      fun h_in => hx_in (h_supp_sub h_in)
    have h_compl_open : IsOpen
        (tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_zero : EqOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
        (fun _ => (0 : ℝ))
        (tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ))ᶜ := by
      intro y hy
      have hy_off : y ∉ Function.support
          (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
        intro h_supp
        exact hy (subset_tsupport _ h_supp)
      exact Function.notMem_support.mp hy_off
    have h_ev : (chartPulledIntegralWeight (I := I) (M := M) g α θ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hx_not_supp] with y hy
      exact h_zero hy
    refine ContinuousAt.congr ?_ h_ev.symm
    exact continuousAt_const

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPulledIntegralWeight_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (chartPulledIntegralWeight (I := I) (M := M) g α θ) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (chartPulledIntegralWeight_continuous (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def chartPulledIntegralWeightLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (chartPulledIntegralWeight_memLp (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp).toLp _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M] in
private lemma weight_smul_continuous_aux
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : M → ℝ} (hv_cont : Continuous v) :
    Continuous (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
      v x) :=
  (chartPulledIntegralWeight_continuous (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp).mul hv_cont

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M] in
private lemma weight_smul_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : M → ℝ) :
    tsupport (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
      v x) ⊆ (chartAt H α).source := by
  classical
  have h_supp_sub : Function.support
      (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
        v x) ⊆
      Function.support (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra h_w
    apply hx
    have h_w_zero : chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 :=
      Function.notMem_support.mp h_w
    rw [h_w_zero, zero_mul]
  refine (closure_mono h_supp_sub).trans ?_
  exact chartPulledIntegralWeight_tsupport_subset_chartSource
    (I := I) (M := M) g α hθ_cs hθ_supp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma density_mul_weight_eq_theta
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartDensity g α x * chartPulledIntegralWeight (I := I) (M := M) g α θ x =
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  classical
  rw [chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx]
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) (M := M)]
    exact hx
  have h_dens_pos : 0 < chartDensity g α x :=
    DifferentialGeometry.Integral.Measure.chartDensity_pos (I := I) g α hx_base
  field_simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma integral_weight_smul_eq_chartPulled
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : M → ℝ} (hv_cont : Continuous v) :
    ∫ x, chartPulledIntegralWeight (I := I) (M := M) g α θ x * v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * θ y
        ∂(volume : Measure EuclN) := by
  classical
  set f : M → ℝ := fun x : M =>
    chartPulledIntegralWeight (I := I) (M := M) g α θ x * v x with hf_def
  have hf_cont : Continuous f :=
    weight_smul_continuous_aux (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp hv_cont
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    weight_smul_tsupport_subset_chartSource (I := I) (M := M) g α hθ_cs hθ_supp v
  have h_main := integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α (f := f) hf_cont hf_supp
  rw [h_main]
  rw [DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume]
  refine MeasureTheory.setIntegral_congr_fun
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet ?_
  intro y hy
  have hy_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have h_density_eq : densityOnEuclid (I := I) g α y =
      chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_inv1 : (extChartAt I α) ((extChartAt I α).symm
      ((toEuclidean (E := E)).symm y)) = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_target
  have h_inv2 : (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) = y :=
    (toEuclidean (E := E)).apply_symm_apply y
  have h_pw := density_mul_weight_eq_theta (I := I) (M := M) g α θ hy_src
  have h_pw' : chartDensity g α ((extChartAt I α).symm
      ((toEuclidean (E := E)).symm y)) *
      chartPulledIntegralWeight (I := I) (M := M) g α θ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = θ y := by
    rw [h_pw]
    rw [h_inv1, h_inv2]
  change densityOnEuclid (I := I) g α y *
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
    v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * θ y
  rw [h_density_eq]
  rw [hf_def]
  rw [show chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      (chartPulledIntegralWeight (I := I) (M := M) g α θ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      (chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        chartPulledIntegralWeight (I := I) (M := M) g α θ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) from by ring]
  rw [h_pw']
  ring

noncomputable def chartPulledIntegralCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
  (innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ)
    (chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPulledIntegralCLM_norm_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp‖ ≤ C := by
  refine ⟨‖chartPulledIntegralWeightLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp‖, norm_nonneg _, ?_⟩
  unfold chartPulledIntegralCLM
  exact le_of_eq (innerSL_apply_norm (𝕜 := ℝ)
    (chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp))

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPulledIntegralCLM_smoothToLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g v) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          θ y ∂(volume : Measure EuclN) := by
  classical
  unfold chartPulledIntegralCLM
  rw [innerSL_apply_apply]
  rw [L2.inner_def
    (chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp)
    (smoothToLp (I := I) (M := M) g v)]
  have hae_w : (chartPulledIntegralWeightLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      chartPulledIntegralWeight (I := I) (M := M) g α θ :=
    MemLp.coeFn_toLp (chartPulledIntegralWeight_memLp
      (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp)
  have hae_v : (smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_int_eq : ∫ a, @inner ℝ _ _
        ((chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_supp : Lp ℝ 2 _) a)
        ((smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ a, chartPulledIntegralWeight (I := I) (M := M) g α θ a * v.toFun a
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae_w, hae_v] with a hwa hva
    rw [hwa, hva]
    rw [show @inner ℝ _ _ (chartPulledIntegralWeight (I := I) (M := M) g α θ a)
          (v.toFun a) =
        v.toFun a * chartPulledIntegralWeight (I := I) (M := M) g α θ a from
      RCLike.inner_apply _ _]
    ring
  rw [h_int_eq]
  exact integral_weight_smul_eq_chartPulled (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp v.smooth.continuous

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPulledIntegralCLM_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp) :=
  (chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp).continuous

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPulledIntegralCLM_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {F : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {F_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto F atTop (𝓝 F_lim)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp (F n)) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp F_lim)) :=
  ((chartPulledIntegralCLM_continuous (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp).tendsto _).comp h_tendsto

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPulledIntegralCLM_tendsto_of_smoothToLp_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : ℕ → SmoothScalar g}
    {F_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n))
      atTop (𝓝 F_lim)) :
    Tendsto (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (v n).toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          θ y ∂(volume : Measure EuclN)) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp F_lim)) := by
  have h_smooth_formula : (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (v n).toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          θ y ∂(volume : Measure EuclN)) =
      (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_supp (smoothToLp (I := I) (M := M) g (v n))) := by
    funext n
    exact (chartPulledIntegralCLM_smoothToLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp (v n)).symm
  rw [h_smooth_formula]
  exact chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp h_tendsto

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    smoothToLp (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical =
      leibnizCompensatedSource (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v)
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_lhs_aeeq : (smoothToLp (I := I) (M := M) g
      (pouScalar (I := I) (M := M) α v).oneSubLapClassical : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp (pouScalar (I := I) (M := M) α v).oneSubLapClassical.memLp_two
  have h_rhs_aeeq : (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      ((leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          : Lp ℝ 2 _) : M → ℝ) :=
    pouScalar_oneSubLap_aeEq_fHLeibniz_smooth (I := I) (M := M) g α v
  exact h_lhs_aeeq.trans h_rhs_aeeq

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPulledIntegralCLM_pouScalar_oneSubLap_eq_fHLeibniz_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α v).oneSubLapClassical) =
      chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)) := by
  rw [smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz (I := I) (M := M) g α v]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : ℕ → SmoothScalar g}
    (h_fHLeibniz_tendsto :
      Tendsto (fun n => leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)))
        atTop (𝓝 (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h))) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical))
      atTop (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_supp
        (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h))) := by
  classical
  have h_eq_n : ∀ n,
      smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical =
      leibnizCompensatedSource (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g (v n))
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)) :=
    fun n => smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz
      (I := I) (M := M) g α (v n)
  have h_funeq : (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp
      (smoothToLp (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical)) =
    fun n => chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp
      (leibnizCompensatedSource (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g (v n))
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n))) := by
    funext n
    rw [h_eq_n n]
  rw [h_funeq]
  exact chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_supp h_fHLeibniz_tendsto

omit [NeZero (Module.finrank ℝ E)] in
theorem rhs_integral_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : ℕ → SmoothScalar g}
    (h_fHLeibniz_tendsto :
      Tendsto (fun n => leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)))
        atTop (𝓝 (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h))) :
    Tendsto (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN))
      atTop (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (θ := fun y => densityOnEuclid (I := I) g α y * ψ y)
        (by
          refine continuous_iff_continuousAt.mpr fun y => ?_
          by_cases hy : y ∈ tsupport ψ
          · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_supp hy
            have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
              Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
            have h_dens : ContinuousAt (densityOnEuclid (I := I) g α) y :=
              ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).continuousAt
                (hOpen.mem_nhds hy_T)
            exact h_dens.mul hψ.continuous.continuousAt
          · have h_compl_open : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
            have h_ev : (fun y => densityOnEuclid (I := I) g α y * ψ y) =ᶠ[𝓝 y]
                (fun _ => (0 : ℝ)) := by
              filter_upwards [h_compl_open.mem_nhds hy] with z hz
              have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
              rw [hψ_z, mul_zero]
            refine ContinuousAt.congr ?_ h_ev.symm
            exact continuousAt_const)
        (by
          refine HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => ?_)
          have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
          rw [hψ_y, mul_zero])
        (by
          refine subset_trans (closure_mono ?_) hψ_supp
          intro y hy
          rw [Function.mem_support] at hy
          by_contra hyψ
          apply hy
          have hψ_y : ψ y = 0 := Function.notMem_support.mp hyψ
          rw [hψ_y, mul_zero])
        (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h))) := by
  classical
  set θ : EuclN → ℝ := fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y with hθ_def
  have hθ_cont : Continuous θ := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    by_cases hy : y ∈ tsupport ψ
    · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_supp hy
      have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_dens : ContinuousAt (densityOnEuclid (I := I) g α) y :=
        ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).continuousAt
          (hOpen.mem_nhds hy_T)
      exact h_dens.mul hψ.continuous.continuousAt
    · have h_compl_open : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
      have h_ev : (fun y => densityOnEuclid (I := I) g α y * ψ y) =ᶠ[𝓝 y]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [h_compl_open.mem_nhds hy] with z hz
        have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
        rw [hψ_z, mul_zero]
      refine ContinuousAt.congr ?_ h_ev.symm
      exact continuousAt_const
  have hθ_cs : HasCompactSupport θ :=
    HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => by
      have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
      change densityOnEuclid (I := I) g α y * ψ y = 0
      rw [hψ_y, mul_zero])
  have hθ_supp : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    refine subset_trans (closure_mono ?_) hψ_supp
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    apply hy
    have hψ_y : ψ y = 0 := Function.notMem_support.mp hyψ
    change densityOnEuclid (I := I) g α y * ψ y = 0
    rw [hψ_y, mul_zero]
  have h_eq_smooth : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN) =
      chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
        (smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical) := by
    intro n
    rw [chartPulledIntegralCLM_smoothToLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_supp
      (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical]
    refine MeasureTheory.setIntegral_congr_fun
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet ?_
    intro y _hy
    change densityOnEuclid (I := I) g α y *
        ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        ψ y =
      ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        (densityOnEuclid (I := I) g α y * ψ y)
    ring
  rw [show (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN)) =
        (fun n => chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_supp
          (smoothToLp (I := I) (M := M) g
            (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical)) from
      funext h_eq_smooth]
  exact chartPulledIntegralCLM_RHS_tendsto_of_fHLeibniz_tendsto
    (I := I) (M := M) g α u_h hu_h hθ_cont hθ_cs hθ_supp h_fHLeibniz_tendsto

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain_variational_identity_general_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : ℕ → SmoothScalar g}
    (_h_v_tendsto :
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
        atTop (𝓝 u_h))
    (h_fHLeibniz_tendsto :
      Tendsto (fun n => leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)))
        atTop (𝓝 (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h))) :
    Tendsto (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN))
      atTop (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (θ := fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y)
        (by
          refine continuous_iff_continuousAt.mpr fun y => ?_
          by_cases hy : y ∈ tsupport ψ
          · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_supp hy
            have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
              Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
            have h_dens : ContinuousAt (densityOnEuclid (I := I) g α) y :=
              ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).continuousAt
                (hOpen.mem_nhds hy_T)
            exact h_dens.mul hψ.continuous.continuousAt
          · have h_compl_open : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
            have h_ev : (fun y => densityOnEuclid (I := I) g α y * ψ y) =ᶠ[𝓝 y]
                (fun _ => (0 : ℝ)) := by
              filter_upwards [h_compl_open.mem_nhds hy] with z hz
              have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
              rw [hψ_z, mul_zero]
            refine ContinuousAt.congr ?_ h_ev.symm
            exact continuousAt_const)
        (by
          refine HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => ?_)
          have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
          rw [hψ_y, mul_zero])
        (by
          refine subset_trans (closure_mono ?_) hψ_supp
          intro y hy
          rw [Function.mem_support] at hy
          by_contra hyψ
          apply hy
          have hψ_y : ψ y = 0 := Function.notMem_support.mp hyψ
          rw [hψ_y, mul_zero])
        (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h))) := by
  exact rhs_integral_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz
    (I := I) (M := M) g α u_h hu_h hψ hψ_cs hψ_supp h_fHLeibniz_tendsto

end ChartPulledIntegralContinuity
end Laplacian
end Analysis
end DifferentialGeometry

end
