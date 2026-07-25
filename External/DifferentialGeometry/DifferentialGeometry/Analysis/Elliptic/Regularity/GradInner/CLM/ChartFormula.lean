import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.Defs
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.Smooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.ChartData
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Geometry.Operator.Gradient
import Mathlib.MeasureTheory.Function.LpSpace.Basic


noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerCLMChartFormula

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearSmooth
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def partialDerivOnEuclid (α : M) (i : Fin (Module.finrank ℝ E)) (u : M → ℝ) :
    EuclN → ℝ := fun y =>
  partialDeriv (E := E) i (scalarOnE (I := I) α u) ((toEuclidean (E := E)).symm y)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
@[simp] lemma partialDerivOnEuclid_def (α : M) (i : Fin (Module.finrank ℝ E))
    (u : M → ℝ) (y : EuclN) :
    partialDerivOnEuclid (I := I) (M := M) α i u y =
      partialDeriv (E := E) i (scalarOnE (I := I) α u)
        ((toEuclidean (E := E)).symm y) := rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
theorem gradInner_eq_chart_formula
    (g : SmoothRiemannianMetric I M) (α : M)
    {ρα u : M → ℝ}
    (hρα : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρα) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    g.inner ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (gradFun (I := I) g ρα
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (gradFun (I := I) g u
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j u y := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have hx_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  have hx_chart_src : x ∈ (chartAt H α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_source
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_chart_src
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have h_φx : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_target
    rw [h_φx]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α h_target
  have h_step1 := gradInner_eq_invGramMatrix_partials_smooth
    (I := I) g α hρα hu hx_base hx_int
  have hφx_eq : extChartAt I α x = (toEuclidean (E := E)).symm y := by
    rw [hx_def]; exact (extChartAt I α).right_inv h_target
  have h_invGram : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α x i j =
        invGramOnEuclid (I := I) g α i j y := by
    intro i j
    unfold invGramOnEuclid; rfl
  have h_partial : ∀ k : Fin (Module.finrank ℝ E),
      ∀ u' : M → ℝ,
        partialDeriv (E := E) k (scalarOnE (I := I) α u') (extChartAt I α x) =
          partialDerivOnEuclid (I := I) (M := M) α k u' y := by
    intro k u'
    rw [hφx_eq]
    rfl
  rw [h_step1]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_partial i ρα, h_partial j u, h_invGram i j]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
theorem chartPushedRaw_gradInnerSmooth_pointwise
    (g : SmoothRiemannianMetric I M) (α : M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    g.inner ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (gradFun (I := I) g ρα
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (gradFun (I := I) g v.toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j v.toFun y :=
  gradInner_eq_chart_formula (I := I) (M := M) g α ρα.contMDiff v.smooth hy

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma partialDerivOnEuclid_contDiffOn (α : M) (i : Fin (Module.finrank ℝ E))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiffOn ℝ ∞ (partialDerivOnEuclid (I := I) (M := M) α i u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_scalar : ContDiffOn ℝ ∞ (scalarOnE (I := I) α u) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hu
  have h_open_target : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  have h_pd : ContDiffOn ℝ ∞
      (fun y : E => partialDeriv (E := E) i (scalarOnE (I := I) α u) y)
      (extChartAt I α).target := by
    unfold partialDeriv
    have h_fderiv_smooth :
        ContDiffOn ℝ ∞ (fun y : E => fderiv ℝ (scalarOnE (I := I) α u) y)
          (extChartAt I α).target := by
      have h_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞) from by
          simp]
      exact h_scalar.fderiv_of_isOpen h_open_target h_le
    exact h_fderiv_smooth.clm_apply contDiffOn_const
  have h_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm : EuclN → E) :=
    ContinuousLinearEquiv.contDiff _
  have h_maps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    exact toEuclidean_symm_mem_target (I := I) hy
  have h_comp : ContDiffOn ℝ ∞
      ((fun y : E => partialDeriv (E := E) i (scalarOnE (I := I) α u) y) ∘
        ((toEuclidean (E := E)).symm))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_pd.comp h_symm_smooth.contDiffOn h_maps
  exact h_comp

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma partialDerivOnEuclid_continuousOn (α : M) (i : Fin (Module.finrank ℝ E))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContinuousOn (partialDerivOnEuclid (I := I) (M := M) α i u)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (partialDerivOnEuclid_contDiffOn (I := I) (M := M) α i hu).continuousOn

def chartFormulaRhsSmooth (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) : EuclN → ℝ := fun y =>
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    invGramOnEuclid (I := I) g α i j y *
      partialDerivOnEuclid (I := I) (M := M) α i ρα y *
      partialDerivOnEuclid (I := I) (M := M) α j u y

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
@[simp] lemma chartFormulaRhsSmooth_def (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) (y : EuclN) :
    chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j u y := rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma chartFormulaRhsSmooth_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiffOn ℝ ∞ (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chartFormulaRhsSmooth
  refine ContDiffOn.sum (fun i _ => ?_)
  refine ContDiffOn.sum (fun j _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · refine ContDiffOn.mul ?_ ?_
    · exact invGramOnEuclid_contDiffOn (I := I) (M := M) g α i j
    · exact partialDerivOnEuclid_contDiffOn (I := I) (M := M) α i ρα.contMDiff
  · exact partialDerivOnEuclid_contDiffOn (I := I) (M := M) α j hu

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma chartFormulaRhsSmooth_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContinuousOn (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartFormulaRhsSmooth_contDiffOn (I := I) (M := M) g α ρα hu).continuousOn

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
theorem chartPushedRaw_gradInner_eq_rhs_pointwise
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) α
        (fun x : M => g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x)) y =
      chartFormulaRhsSmooth (I := I) (M := M) g α ρα v.toFun y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  unfold chartFormulaRhsSmooth
  exact chartPushedRaw_gradInnerSmooth_pointwise (I := I) (M := M) g α ρα v hy

noncomputable def chartFormulaRhsSmoothExt (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y
    else 0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma chartFormulaRhsSmoothExt_apply_of_mem (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα u y =
      chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y := by
  classical
  change (if y ∈ chartTargetEuclid (I := I) (M := M) α then
        chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y
      else 0) = _
  rw [if_pos hy]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma chartFormulaRhsSmoothExt_apply_of_notMem (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα u y = 0 := by
  classical
  change (if y ∈ chartTargetEuclid (I := I) (M := M) α then
        chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y
      else 0) = 0
  rw [if_neg hy]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma chartFormulaRhsSmoothExt_measurable
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    Measurable (chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα u) := by
  classical
  have h_meas_target : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_eq : chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα u =
      Set.indicator (chartTargetEuclid (I := I) (M := M) α)
        (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u) := by
    funext y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartFormulaRhsSmoothExt_apply_of_mem (I := I) (M := M) g α ρα u hy]
      rw [Set.indicator_of_mem hy]
    · rw [chartFormulaRhsSmoothExt_apply_of_notMem (I := I) (M := M) g α ρα u hy]
      rw [Set.indicator_of_notMem hy]
  rw [h_eq]
  have h_cont_on :
      ContinuousOn (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u)
        (chartTargetEuclid (I := I) (M := M) α) :=
    chartFormulaRhsSmooth_continuousOn (I := I) (M := M) g α ρα hu
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_piecewise_eq :
      Set.indicator (chartTargetEuclid (I := I) (M := M) α)
          (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u) =
        (chartTargetEuclid (I := I) (M := M) α).piecewise
          (chartFormulaRhsSmooth (I := I) (M := M) g α ρα u)
          (fun _ => (0 : ℝ)) := by
    funext y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy, Set.piecewise_eq_of_mem _ _ _ hy]
    · rw [Set.indicator_of_notMem hy, Set.piecewise_eq_of_notMem _ _ _ hy]
  rw [h_piecewise_eq]
  refine ContinuousOn.measurable_piecewise h_cont_on ?_ h_meas_target
  exact continuousOn_const

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedRawLpFromLp_gradInnerSmooth_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (gradInnerSmooth (I := I) (M := M) g ρα v) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα v.toFun := by
  classical
  have h_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (gradInnerSmooth (I := I) (M := M) g ρα v)
  have h_inner := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_inner_meas :
      Measurable ((gradInnerSmooth (I := I) (M := M) g ρα v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_pointwise_meas : Measurable (fun x : M =>
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)) :=
    (gradInnerSmooth_continuous (I := I) (M := M) g ρα v).measurable
  have h_chartPushedRaw_aeEq :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_inner_meas h_pointwise_meas h_inner
  have h_meas_target : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_weighted_restrict_ae_chartTarget :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
      y ∈ chartTargetEuclid (I := I) (M := M) α := by
    rw [ae_restrict_iff' h_meas_target]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [h_coeFn, h_chartPushedRaw_aeEq, h_weighted_restrict_ae_chartTarget]
    with y hy_coeFn hy_chartPushedRaw hy_target
  rw [hy_coeFn, hy_chartPushedRaw]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
  rw [chartFormulaRhsSmoothExt_apply_of_mem (I := I) (M := M) g α ρα v.toFun hy_target]
  unfold chartFormulaRhsSmooth
  exact chartPushedRaw_gradInnerSmooth_pointwise (I := I) (M := M) g α ρα v hy_target

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedRawLpFromLp_gradInnerCLM_smoothToH1Compl_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g v)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartFormulaRhsSmoothExt (I := I) (M := M) g α ρα v.toFun := by
  classical
  rw [gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα v]
  exact chartPushedRawLpFromLp_gradInnerSmooth_aeEq (I := I) (M := M) g α ρα v

end GradInnerCLMChartFormula
end Laplacian
end Analysis
end DifferentialGeometry

end
