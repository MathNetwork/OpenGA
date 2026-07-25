import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.ChartPartialUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartPartialUniformBoundElementaryScalarBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartPartialUniformBoundChartPushedRegularity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartPartialUniformBoundLeibnizTermFactorization
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.CutoffChartPartialUniformBoundPrincipalCovariantComponentBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def cutoffKernelM (α : M) : Set M :=
  tsupport (fun x : M => ((chartKernelCutoff (I := I) (M := M) α
    : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelM_isCompact (α : M) :
    IsCompact (cutoffKernelM (I := I) (M := M) α) :=
  chartKernelCutoff_hasCompactSupport (I := I) (M := M) α

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelM_isClosed (α : M) :
    IsClosed (cutoffKernelM (I := I) (M := M) α) :=
  isClosed_tsupport _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelM_subset_chart_source (α : M) :
    cutoffKernelM (I := I) (M := M) α ⊆ (chartAt H α).source := by
  refine Subset.trans ?_ (chartKernelCutoff_tsupport_subset_source
    (I := I) (M := M) α)
  exact subset_rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelM_subset_baseSet (α : M) :
    cutoffKernelM (I := I) (M := M) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
  exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hx

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRaw_cutoff_contDiff (α : M) :
    ContDiff ℝ ∞
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) :=
  DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M)
    (chartKernelCutoff_contMDiff (I := I) (M := M) α)
    (cutoffKernelM_subset_chart_source (I := I) (M := M) α)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_cutoffComponentEuclid_eq_leibniz
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) y =
      chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
          euclidPartial (E := E) k
            (chartPushedRaw (I := I) (M := M) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + euclidPartial (E := E) k
            (chartPushedRaw (I := I) (M := M) α
              (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y *
          chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y := by
  classical
  set χ : EuclN → ℝ :=
    chartPushedRaw (I := I) (M := M) α
      (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) with hχ_def
  set w : EuclN → ℝ :=
    chartPushedRaw (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) with hw_def
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_nhds : chartTargetEuclid (I := I) (M := M) α ∈ 𝓝 y :=
    hΩ_open.mem_nhds hy
  have h_eqf : cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx
      =ᶠ[𝓝 y] (fun z : EuclN => χ z * w z) := by
    filter_upwards [hΩ_nhds] with z hz
    rw [hχ_def, hw_def]
    exact cutoffComponentEuclid_eq_cutoff_mul_rawPushed
      (I := I) (M := M) g r s S α Idx Jdx hz
  have hχ_diff : DifferentiableAt ℝ χ y :=
    ((chartPushedRaw_cutoff_contDiff (I := I) (M := M) α).differentiable
      (by simp)).differentiableAt
  have hw_diffOn : DifferentiableOn ℝ w
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartPushedRaw_tensorChartComponentRaw_contDiffOn
      (I := I) (M := M) g r s S α Idx Jdx).differentiableOn (by simp)
  have hw_diff : DifferentiableAt ℝ w y :=
    (hw_diffOn y hy).differentiableAt hΩ_nhds
  have h_fderiv :
      fderiv ℝ (cutoffComponentEuclid (I := I) (M := M)
          g r s S α Idx Jdx) y =
        χ y • fderiv ℝ w y + w y • fderiv ℝ χ y := by
    rw [h_eqf.fderiv_eq]
    exact fderiv_mul hχ_diff hw_diff
  rw [euclidPartial_def, h_fderiv,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    euclidPartial_def, euclidPartial_def]
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_cutoffComponentEuclid_eq_three_terms
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) y =
      cutoffCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx y
        + cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y
        - cutoffLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y := by
  classical
  rw [euclidPartial_cutoffComponentEuclid_eq_leibniz
    (I := I) (M := M) g r s S α k Idx Jdx hy,
    euclidPartial_rawPushed_eq_covDerivComponent_sub'
      (I := I) (M := M) g r s S α k Idx Jdx hy]
  unfold cutoffCovDerivComponent cutoffLeibnizCrossTerm cutoffLowerOrderTerm
  ring

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRaw_cutoff_continuousOn (α : M) :
    ContinuousOn
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedRaw_cutoff_contDiff (I := I) (M := M) α).continuous.continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_chartPushedRaw_cutoff_continuousOn
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (euclidPartial_contDiff_of_contDiff' (E := E)
    (chartPushedRaw_cutoff_contDiff (I := I) (M := M) α) k).continuous.continuousOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma cutoffCovDerivComponent_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (cutoffCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set galt : EuclN → ℝ := fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
      (euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y)
    with hgalt_def
  have hgalt_cont : ContinuousOn galt
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartPushedRaw_cutoff_continuousOn (I := I) (M := M) α).mul
      ((euclidPartial_chartPushedRaw_rawComponent_continuousOn'
        (I := I) (M := M) g r s S α k Idx Jdx).add
      (covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α
        k Idx Jdx
        (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
          (I := I) (M := M) g r s S α Idx' Jdx')).continuousOn)
  refine hgalt_cont.congr (fun y hy => ?_)
  have h := euclidPartial_rawPushed_eq_covDerivComponent_sub'
    (I := I) (M := M) g r s S α k Idx Jdx hy
  unfold cutoffCovDerivComponent
  rw [hgalt_def, show
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α k)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) =
      euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y
      from by linarith [h]]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffLowerOrderTerm_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (cutoffLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold cutoffLowerOrderTerm
  exact (chartPushedRaw_cutoff_continuousOn (I := I) (M := M) α).mul
    (covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α
      k Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s S α Idx' Jdx')).continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffLeibnizCrossTerm_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold cutoffLeibnizCrossTerm
  exact (euclidPartial_chartPushedRaw_cutoff_continuousOn
      (I := I) (M := M) α k).mul
    (chartPushedRaw_rawComponent_continuousOn' (I := I) (M := M)
      g r s S α Idx Jdx)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma euclidPartial_chartPushedRaw_cutoff_tsupport_subset
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    tsupport
        (euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)))) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) := by
  classical
  have h1 : tsupport
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)))) ⊆
      tsupport (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) := by
    have h := tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)))
      (EuclideanSpace.single k (1 : ℝ))
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport _)) h
    intro y hy
    refine subset_tsupport _ ?_
    simpa [euclidPartial_def] using hy
  have h2 : tsupport (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) := by
    have hK_compact : IsCompact ((extChartAt I α) ''
        (cutoffKernelM (I := I) (M := M) α)) :=
      (cutoffKernelM_isCompact (I := I) (M := M) α).image_of_continuousOn
        ((continuousOn_extChartAt α).mono (by
          intro x hx
          rw [extChartAt_source]
          exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hx))
    have hKE_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α))) :=
      hK_compact.image (toEuclidean (E := E)).continuous
    refine closure_minimal ?_ hKE_compact.isClosed
    intro y hy
    rw [Function.mem_support] at hy
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      by_contra hy_off
      exact hy (chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy_off)
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    have hb_src : b ∈ (chartAt H α).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy_target
    have hb_cut : b ∈ cutoffKernelM (I := I) (M := M) α := by
      refine subset_tsupport _ ?_
      rw [Function.mem_support]
      intro hb_zero
      apply hy
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy_target]
      exact hb_zero
    have hb_ext : b ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hb_src
    have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have h_extChartAt_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
      rw [hb_def]
      exact (extChartAt I α).right_inv hy_symm
    refine ⟨extChartAt I α b, ⟨b, hb_cut, rfl⟩, ?_⟩
    rw [h_extChartAt_b]
    exact (toEuclidean (E := E)).apply_symm_apply y
  exact h1.trans h2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffLeibnizCrossTerm_eq_zero_off_cutoff_kernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∉ (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α))) :
    cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y = 0 := by
  classical
  unfold cutoffLeibnizCrossTerm
  have hχ_zero : euclidPartial (E := E) k
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y = 0 := by
    by_contra hne
    exact hy (euclidPartial_chartPushedRaw_cutoff_tsupport_subset
      (I := I) (M := M) α k (subset_tsupport _ (Function.mem_support.mpr hne)))
  rw [hχ_zero, zero_mul]

private def rawComponentCutoffM
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : M → ℝ :=
  (cutoffKernelM (I := I) (M := M) α).indicator
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma rawComponentCutoffM_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) ⊆
      cutoffKernelM (I := I) (M := M) α := by
  classical
  refine closure_minimal ?_ (cutoffKernelM_isClosed (I := I) (M := M) α)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_off
  exact hx (by rw [rawComponentCutoffM, Set.indicator_of_notMem hx_off])

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma rawComponentCutoffM_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  unfold rawComponentCutoffM
  rw [show (cutoffKernelM (I := I) (M := M) α).indicator
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) =
      (cutoffKernelM (I := I) (M := M) α).piecewise
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (fun _ : M => (0 : ℝ)) from by
    funext x
    by_cases hx : x ∈ cutoffKernelM (I := I) (M := M) α
    · simp [Set.indicator_of_mem hx, Set.piecewise_eq_of_mem _ _ _ hx]
    · simp [Set.indicator_of_notMem hx, Set.piecewise_eq_of_notMem _ _ _ hx]]
  have hraw_cont : ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (cutoffKernelM (I := I) (M := M) α) :=
    ((tensorChartComponentRaw_contMDiffOn_chart_source
        (I := I) (M := M) g r s S α Idx Jdx).continuousOn).mono
      (cutoffKernelM_subset_chart_source (I := I) (M := M) α)
  exact ContinuousOn.measurable_piecewise hraw_cont
    (continuousOn_const) (cutoffKernelM_isClosed (I := I) (M := M) α).measurableSet

omit [CompleteSpace E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_const_rawComponentCutoffM_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
        (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    sq_norm_le_const_mul_chartTensorInner_on_compact
      (I := I) (M := M) (E := E) g r s α
      (cutoffKernelM_isCompact (I := I) (M := M) α)
      (cutoffKernelM_subset_baseSet (I := I) (M := M) α)
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b
  have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  by_cases hb : b ∈ cutoffKernelM (I := I) (M := M) α
  · have hcut_eq : rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx b =
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
      rw [rawComponentCutoffM, Set.indicator_of_mem hb]
    rw [hcut_eq, tensorChartComponentRaw_def]
    set T : TensorRSModel r s ℝ E :=
      tensorTrivProj (I := I) (M := M) g r s S α b with hT_def
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      cutoffKernelM_subset_baseSet (I := I) (M := M) α hb
    have h_proj_le :
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx T‖ ≤
          C_proj * ‖T‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
          (norm_nonneg _))
    have h_proj_sq_le :
        (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2 ≤
          C_proj ^ 2 * ‖T‖ ^ 2 := by
      have h_abs : (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2 =
          ‖tensorChartComponentProjection (E := E) r s Idx Jdx T‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [h_abs]
      have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
      nlinarith [hsq, norm_nonneg (tensorChartComponentProjection (E := E)
        r s Idx Jdx T), norm_nonneg T, hC_proj_nn]
    have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by
      have h := h_norm b hb T
      rwa [hT_def, chartTensorInner_tensorTrivProj_eq_tensorInner
        (I := I) (M := M) g r s α S hb_base] at h
    calc (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2
        ≤ C_proj ^ 2 * ‖T‖ ^ 2 := h_proj_sq_le
      _ ≤ C_proj ^ 2 *
          (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
        mul_le_mul_of_nonneg_left h_triv_sq_le (sq_nonneg _)
      _ = C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  · have hcut_zero : rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx b
        = 0 := by
      rw [rawComponentCutoffM, Set.indicator_of_notMem hb]
    rw [hcut_zero]
    have h_rhs_nn : 0 ≤ C_proj ^ 2 * K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hK_nn) hQ_nn
    simpa using h_rhs_nn

omit [CompleteSpace E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_const_eLpNorm_rawComponentCutoffM_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    exists_const_rawComponentCutoffM_sq_le (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx
    with hf_def
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise (I := I) (M := M)
          g r s b (S.toFun b) (S.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt S Idx Jdx b)
  have h_inner_int := SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M) (g := g) (r := r) (s := s) S S
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  have h_sq :
      (eLpNorm f 2 μ) ^ 2 ≤
        ENNReal.ofReal (C *
          tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq' μ f]
    have h_lint_le :
        ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
          ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
            (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards with b using h_pt_enn b
    have h_lint_eq :
        ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ =
          ENNReal.ofReal (∫ b, C * tensorInnerPointwise
            (I := I) (M := M) g r s b (S.toFun b) (S.toFun b) ∂μ) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        h_C_smul_int h_C_smul_nn).symm
    have h_int_const_mul :
        ∫ b, C * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) ∂μ =
          C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
      unfold tensorL2Inner
      rw [integral_const_mul]
    rw [h_lint_eq, h_int_const_mul] at h_lint_le
    exact h_lint_le
  have h_inner_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    refine integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have h_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
        (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 := by
    unfold tensorL2Norm
    rw [sq, Real.mul_self_sqrt h_inner_nn]
  set Stotal : ℝ := C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun
    with hStotal_def
  have hStotal_nn : 0 ≤ Stotal := mul_nonneg hC_nn h_inner_nn
  have h_eLp_le : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt Stotal) := by
    have h_pow := le_sqrt_of_sq_le' h_sq
    rw [sqrt_ofReal_eq_ofReal_sqrt' hStotal_nn] at h_pow
    exact h_pow
  have h_sqrt_factor : Real.sqrt Stotal = Real.sqrt C * ‖S‖ := by
    rw [hStotal_def, h_norm_sq, Real.sqrt_mul hC_nn,
      show (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 =
        tensorL2Norm (I := I) (M := M) g r s S.toFun *
          tensorL2Norm (I := I) (M := M) g r s S.toFun from by ring,
      Real.sqrt_mul_self
        (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun),
      SmoothCcTensor.norm_def (I := I) (M := M)]
  rw [h_sqrt_factor, ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLp_le
  exact h_eLp_le

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_const_euclidPartial_chartPushedRaw_cutoff_le
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧
      ∀ y : EuclN,
        ‖euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y‖
            ≤ Cχ := by
  classical
  set χ : EuclN → ℝ :=
    euclidPartial (E := E) k
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) with hχ_def
  have hχ_cont : Continuous χ := by
    rw [hχ_def]
    exact (euclidPartial_contDiff_of_contDiff' (E := E)
      (chartPushedRaw_cutoff_contDiff (I := I) (M := M) α) k).continuous
  have hχ_cpt : HasCompactSupport χ := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α))) ?_ ?_
    · exact ((cutoffKernelM_isCompact (I := I) (M := M) α).image_of_continuousOn
        ((continuousOn_extChartAt α).mono (by
          intro x hx
          rw [extChartAt_source]
          exact cutoffKernelM_subset_chart_source (I := I) (M := M)
            α hx))).image (toEuclidean (E := E)).continuous
    · refine subset_trans ?_
        (euclidPartial_chartPushedRaw_cutoff_tsupport_subset
          (I := I) (M := M) α k)
      exact subset_tsupport _
  by_cases hK_ne : (tsupport χ).Nonempty
  · obtain ⟨x₀, _, hx₀_max⟩ :=
      hχ_cpt.exists_isMaxOn hK_ne (hχ_cont.norm.continuousOn)
    refine ⟨max ‖χ x₀‖ 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy : y ∈ tsupport χ
    · exact (hx₀_max hy).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact le_max_right _ _
  · refine ⟨0, le_refl 0, fun y => ?_⟩
    have hy : y ∉ tsupport χ := fun hy => hK_ne ⟨y, hy⟩
    rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffLeibnizCrossTerm_le_const_mul_chartPushedRaw_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {Cχ : ℝ} (hCχ_nn : 0 ≤ Cχ)
    (hCχ : ∀ y : EuclN,
      ‖euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y‖ ≤ Cχ)
    (y : EuclN) :
    ‖cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y‖ ≤
      Cχ * ‖chartPushedRaw (I := I) (M := M) α
        (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) y‖ := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    by_cases hb : b ∈ cutoffKernelM (I := I) (M := M) α
    · have h_cut_eval : chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) y =
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) hy,
          rawComponentCutoffM, Set.indicator_of_mem hb]
      have h_raw_eval : chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y =
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy]
      unfold cutoffLeibnizCrossTerm
      rw [h_cut_eval, h_raw_eval, norm_mul]
      exact mul_le_mul_of_nonneg_right (hCχ y) (norm_nonneg _)
    · have h_cross_zero : cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α
          k Idx Jdx y = 0 := by
        refine cutoffLeibnizCrossTerm_eq_zero_off_cutoff_kernel
          (I := I) (M := M) g r s S α k Idx Jdx ?_
        rintro ⟨z, ⟨b', hb'_cut, hb'_eq⟩, hz_eq⟩
        apply hb
        have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
          rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
          exact hy
        have hb'_src : b' ∈ (extChartAt I α).source := by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hb'_cut
        have h_symm_y : (toEuclidean (E := E)).symm y = z := by
          rw [← hz_eq]
          exact (toEuclidean (E := E)).symm_apply_apply z
        have hb_eq_b' : b = b' := by
          rw [hb_def, h_symm_y, ← hb'_eq, (extChartAt I α).left_inv hb'_src]
        rw [hb_eq_b']
        exact hb'_cut
      rw [h_cross_zero, norm_zero]
      exact mul_nonneg hCχ_nn (norm_nonneg _)
  · have h_cross_zero : cutoffLeibnizCrossTerm (I := I) (M := M) g r s S α
        k Idx Jdx y = 0 := by
      unfold cutoffLeibnizCrossTerm
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy,
        mul_zero]
    have h_cut_zero : chartPushedRaw (I := I) (M := M) α
        (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (rawComponentCutoffM (I := I) (M := M) g r s S α Idx Jdx) hy
    rw [h_cross_zero, norm_zero, h_cut_zero, norm_zero, mul_zero]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_const_eLpNorm_cutoffLeibnizCrossTerm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      eLpNorm
          (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
            k Idx Jdx) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨Cχ, hCχ_nn, hCχ⟩ :=
    exists_const_euclidPartial_chartPushedRaw_cutoff_le (I := I) (M := M) α k
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  obtain ⟨C_bridge, hC_bridge_pos, hC_bridge⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α (cutoffKernelM_isCompact (I := I) (M := M) α)
      (cutoffKernelM_subset_chart_source (I := I) (M := M) α) hp_one hp_top
  obtain ⟨C_cut, hC_cut_nn, hC_cut⟩ :=
    exists_const_eLpNorm_rawComponentCutoffM_le (I := I) (M := M) g r s α
  refine ⟨Cχ * (C_bridge * C_cut),
    mul_nonneg hCχ_nn (mul_nonneg hC_bridge_pos.le hC_cut_nn), ?_⟩
  intro S Idx Jdx
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  set normCut : EuclN → ℝ := fun y : EuclN =>
    ‖chartPushedRaw (I := I) (M := M) α
      (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) y‖
    with hnormCut_def
  have h_ptwise : ∀ y : EuclN,
      ‖cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx y‖ ≤
        (Cχ • normCut) y := by
    intro y
    rw [Pi.smul_apply, smul_eq_mul, hnormCut_def]
    exact cutoffLeibnizCrossTerm_le_const_mul_chartPushedRaw_cutoff
      (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx hCχ_nn hCχ y
  have h_mono :
      eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        eLpNorm (Cχ • normCut) 2 μ :=
    eLpNorm_mono_real h_ptwise
  have h_smul :
      eLpNorm (Cχ • normCut) 2 μ =
        ‖Cχ‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ := by
    rw [eLpNorm_const_smul Cχ normCut 2 μ, hnormCut_def, eLpNorm_norm]
  have hCχ_enorm : ‖Cχ‖ₑ = ENNReal.ofReal Cχ := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hCχ_nn]
  have h_bridge :
      eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ ≤
        ENNReal.ofReal C_bridge *
          eLpNorm (rawComponentCutoffM (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx)
            2 (riemannianMeasure (I := I) g (chartAtlasPOU I M)) :=
    hC_bridge
      (rawComponentCutoffM_measurable (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx)
      (rawComponentCutoffM_tsupport_subset (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx)
  have h_meas_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure (I := I) (M := M) g := rfl
  rw [h_meas_eq] at h_bridge
  have h_cut_h1 :
      eLpNorm (rawComponentCutoffM (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_cut * (‖S‖₊ : ℝ≥0∞) := by
    have hb := hC_cut S.toCcTensor Idx Jdx
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (zero_le _))
    rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from by
      rw [show ((‖S‖₊ : ℝ≥0∞)) = ‖S‖ₑ from (enorm_eq_nnnorm S).symm,
        ← ofReal_norm_eq_enorm S]]
    exact ENNReal.ofReal_le_ofReal
      (SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S)
  calc eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ
      ≤ eLpNorm (Cχ • normCut) 2 μ := h_mono
    _ = ‖Cχ‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ := h_smul
    _ = ENNReal.ofReal Cχ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoffM (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ := by rw [hCχ_enorm]
    _ ≤ ENNReal.ofReal Cχ *
          (ENNReal.ofReal C_bridge *
            eLpNorm (rawComponentCutoffM (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) 2
              (riemannianVolumeMeasure (I := I) (M := M) g)) :=
        mul_le_mul_of_nonneg_left h_bridge (by positivity)
    _ ≤ ENNReal.ofReal Cχ *
          (ENNReal.ofReal C_bridge *
            (ENNReal.ofReal C_cut * (‖S‖₊ : ℝ≥0∞))) := by gcongr
    _ = ENNReal.ofReal (Cχ * (C_bridge * C_cut)) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hCχ_nn, ENNReal.ofReal_mul hC_bridge_pos.le]
        ring

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffCovNormSumFun_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tsupport (cutoffCovNormSumFun (I := I) (M := M) g r s S α) ⊆
      cutoffKernelM (I := I) (M := M) α := by
  classical
  have hfun_eq : cutoffCovNormSumFun (I := I) (M := M) g r s S α =
      fun b : M =>
        ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b •
          Real.sqrt
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) := by
    funext b
    rw [cutoffCovNormSumFun]
    rfl
  rw [hfun_eq]
  exact tsupport_smul_subset_left
    (f := fun b : M => ((chartKernelCutoff (I := I) (M := M) α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
    (g := fun b : M =>
      Real.sqrt
        (∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))‖ ^ 2))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_const_eLpNorm_cutoffCovDerivComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E))
      (m : Fin (Module.finrank ℝ E)),
      eLpNorm
        (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          m Idx Jdx)
        2 ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  set Kα : Set M := cutoffKernelM (I := I) (M := M) α with hKα_def
  have hKα_compact : IsCompact Kα := cutoffKernelM_isCompact (I := I) (M := M) α
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    cutoffKernelM_subset_chart_source (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C_bridge, hC_bridge_pos, hC_bridge⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  obtain ⟨C_cov, hC_cov_nn, hC_cov⟩ :=
    exists_eLpNorm_chartWeight_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
      (fun x : M => ((chartKernelCutoff (I := I) (M := M) α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      (fun x => (chartKernelCutoff_mem_Icc (I := I) (M := M) α x).1)
      (fun x => (chartKernelCutoff_mem_Icc (I := I) (M := M) α x).2)
      hKα_compact
      (cutoffKernelM_subset_baseSet (I := I) (M := M) α)
      (subset_rfl)
  refine ⟨C_proj * (C_bridge * C_cov),
    mul_nonneg hC_proj_nn (mul_nonneg hC_bridge_pos.le hC_cov_nn), ?_⟩
  intro S Idx Jdx m
  set v : M → ℝ := cutoffCovNormSumFun (I := I) (M := M) g r s S.toCcTensor α
    with hv_def
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have h_ptwise : ∀ y : EuclN,
      ‖cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          m Idx Jdx y‖ ≤
        (C_proj • chartPushedRaw (I := I) (M := M) α v) y := by
    intro y
    rw [hv_def, hC_proj_def]
    exact cutoffCovDerivComponent_le_chartPushedRaw (I := I) (M := M)
      g r s S.toCcTensor α m Idx Jdx y
  have h_mono :
      eLpNorm (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          m Idx Jdx) 2 μ ≤
        eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ :=
    eLpNorm_mono_real h_ptwise
  have h_smul :
      eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ =
        ‖C_proj‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ :=
    eLpNorm_const_smul C_proj (chartPushedRaw (I := I) (M := M) α v) 2 μ
  have hC_proj_enorm : ‖C_proj‖ₑ = ENNReal.ofReal C_proj := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC_proj_nn]
  have hv_meas : Measurable v :=
    cutoffCovNormSumFun_measurable (I := I) (M := M) g r s S.toCcTensor α
  have hv_supp : tsupport v ⊆ Kα :=
    cutoffCovNormSumFun_tsupport_subset (I := I) (M := M) g r s S.toCcTensor α
  have h_bridge :
      eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ ≤
        ENNReal.ofReal C_bridge *
          eLpNorm v 2
            (riemannianMeasure (I := I) g (chartAtlasPOU I M)) :=
    hC_bridge hv_meas hv_supp
  have h_meas_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure (I := I) (M := M) g := rfl
  rw [h_meas_eq] at h_bridge
  have hv_eq : v = fun b : M =>
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s
                    S.toCcTensor b
                    (chartBasisVecFiber (I := I) α i b)))‖ ^ 2) := by
    rw [hv_def]
    funext b
    rw [cutoffCovNormSumFun]
  have h_cov :
      eLpNorm v 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞) := by
    rw [hv_eq]
    exact hC_cov S
  calc eLpNorm (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          m Idx Jdx) 2 μ
      ≤ eLpNorm (C_proj • chartPushedRaw (I := I) (M := M) α v) 2 μ := h_mono
    _ = ‖C_proj‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ :=
        h_smul
    _ = ENNReal.ofReal C_proj *
          eLpNorm (chartPushedRaw (I := I) (M := M) α v) 2 μ := by
        rw [hC_proj_enorm]
    _ ≤ ENNReal.ofReal C_proj *
          (ENNReal.ofReal C_bridge *
            eLpNorm v 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
        exact mul_le_mul_of_nonneg_left h_bridge (by positivity)
    _ ≤ ENNReal.ofReal C_proj *
          (ENNReal.ofReal C_bridge *
            (ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞))) := by
        gcongr
    _ = ENNReal.ofReal (C_proj * (C_bridge * C_cov)) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hC_proj_nn,
          ENNReal.ofReal_mul hC_bridge_pos.le]
        ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma mem_cutoffKernelM_image_of_cutoffComponentEuclid_ne_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hne : cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y ≠ 0) :
    y ∈ chartTargetEuclid (I := I) (M := M) α ∧
      y ∈ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) := by
  classical
  have hy : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    by_contra hy
    exact hne (cutoffComponentEuclid_apply_of_notMem
      (I := I) (M := M) g r s S α Idx Jdx hy)
  refine ⟨hy, ?_⟩
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hval : cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y =
      cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx b :=
    cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy
  rw [hval] at hne
  have hχ_ne : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)
      : M → ℝ) b ≠ 0 := by
    intro hχ_zero
    apply hne
    unfold cutoffComponentScalar
    rw [hχ_zero, zero_mul]
  have hb_cut : b ∈ cutoffKernelM (I := I) (M := M) α :=
    subset_tsupport _ (Function.mem_support.mpr hχ_ne)
  have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hb_cut
  have h_extChartAt_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]
    exact (extChartAt I α).right_inv hy_symm
  refine ⟨extChartAt I α b, ⟨b, hb_cut, rfl⟩, ?_⟩
  rw [h_extChartAt_b]
  exact (toEuclidean (E := E)).apply_symm_apply y

omit [CompleteSpace E] in
private theorem exists_const_covDerivLowerOrderCoeff_bdd_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
        (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
        {y : EuclN},
        y ∈ chartTargetEuclid (I := I) (M := M) α →
        y ∈ (toEuclidean (E := E)) ''
          ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) →
        |covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
          Jdx Jdx' y| ≤ C := by
  classical
  have hKE_compact : IsCompact ((extChartAt I α) ''
      (cutoffKernelM (I := I) (M := M) α)) :=
    (cutoffKernelM_isCompact (I := I) (M := M) α).image_of_continuousOn
      ((continuousOn_extChartAt α).mono (by
        intro x hx
        rw [extChartAt_source]
        exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hx))
  have hKE_sub_interior : (extChartAt I α) ''
      (cutoffKernelM (I := I) (M := M) α) ⊆
      interior ((extChartAt I α).target : Set E) := by
    have h_open : IsOpen ((extChartAt I α).target : Set E) :=
      isOpen_extChartAt_target (I := I) α
    rw [h_open.interior_eq]
    rintro y ⟨x, hx, rfl⟩
    have hx_src : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hx
    exact (extChartAt I α).map_source hx_src
  obtain ⟨Cχ, hCχ_nn, hCχ⟩ :=
    chartChristoffel_bdd_on_compact (I := I) (M := M) g α
      hKE_compact hKE_sub_interior
  refine ⟨(r + s) * Cχ, by positivity, ?_⟩
  intro m Idx Idx' Jdx Jdx' y hy hb
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have himg : extChartAt I α b ∈ (extChartAt I α) ''
      (cutoffKernelM (I := I) (M := M) α) := by
    obtain ⟨z, ⟨b', hb'_cut, hb'_eq⟩, hz_eq⟩ := hb
    have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have hb'_src : b' ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact cutoffKernelM_subset_chart_source (I := I) (M := M) α hb'_cut
    have h_symm_y : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]
      exact (toEuclidean (E := E)).symm_apply_apply z
    have hb_eq_b' : b = b' := by
      rw [hb_def, h_symm_y, ← hb'_eq, (extChartAt I α).left_inv hb'_src]
    rw [hb_eq_b']
    exact ⟨b', hb'_cut, rfl⟩
  have hinput : ∀ k : Fin r,
      |inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y| ≤ Cχ := by
    intro k
    rw [inputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g r α m k
      Idx Idx' hy,
      chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
        (I := I) (M := M) g α hb_base m (Idx k) (Idx' k),
      abs_mul]
    calc |chartChristoffel (I := I) g α (Idx' k) m (Idx k)
              (extChartAt I α b)| *
            |∏ i ∈ Finset.univ.erase k,
              (if Idx' i = Idx i then (1 : ℝ) else 0)|
        ≤ Cχ * 1 := by
          refine mul_le_mul (hCχ _ himg _ _ _)
            (abs_prod_kronecker_le_one' _ _) (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  have houtput : ∀ l : Fin s,
      |outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y| ≤ Cχ := by
    intro l
    rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g s α m l
      Jdx Jdx' hy,
      chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel
        (I := I) (M := M) g α hb_base m (Jdx' l) (Jdx l),
      abs_mul]
    calc |chartChristoffel (I := I) g α (Jdx l) m (Jdx' l)
              (extChartAt I α b)| *
            |∏ j ∈ Finset.univ.erase l,
              (if Jdx j = Jdx' j then (1 : ℝ) else 0)|
        ≤ Cχ * 1 := by
          refine mul_le_mul (hCχ _ himg _ _ _)
            (abs_prod_kronecker_le_one' _ _) (abs_nonneg _) hCχ_nn
      _ = Cχ := mul_one _
  have hsum_input :
      |∑ k : Fin r,
          inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y *
            (if Jdx' = Jdx then (1 : ℝ) else 0)| ≤ r * Cχ := by
    have h := abs_sum_coeff_kronecker_le' (Finset.univ : Finset (Fin r))
      (fun k => inputSlotCoeff (I := I) (M := M) g r α m k Idx Idx' y)
      (fun _ => Jdx' = Jdx) hCχ_nn (fun k _ => hinput k)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hsum_output :
      |∑ l : Fin s,
          outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y *
            (if Idx' = Idx then (1 : ℝ) else 0)| ≤ s * Cχ := by
    have h := abs_sum_coeff_kronecker_le' (Finset.univ : Finset (Fin s))
      (fun l => outputSlotCoeff (I := I) (M := M) g s α m l Jdx Jdx' y)
      (fun _ => Idx' = Idx) hCχ_nn (fun l _ => houtput l)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  rw [covDerivLowerOrderCoeff_def]
  have habs_sub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
      _ ≤ |a| + |-b| := abs_add_le a (-b)
      _ = |a| + |b| := by rw [abs_neg]
  refine (habs_sub _ _).trans ?_
  have := add_le_add hsum_input hsum_output
  rw [add_mul]
  linarith

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_coeff_mul_cutoffComponent_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    {Ccoeff : ℝ} (hCcoeff_nn : 0 ≤ Ccoeff)
    (hCcoeff : ∀ {y : EuclN},
      y ∈ chartTargetEuclid (I := I) (M := M) α →
      y ∈ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (cutoffKernelM (I := I) (M := M) α)) →
      |covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
        Jdx Jdx' y| ≤ Ccoeff) :
    eLpNorm
        (fun y : EuclN =>
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
              Jdx Jdx' y *
            cutoffComponentEuclid (I := I) (M := M) g r s S α Idx' Jdx' y) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal Ccoeff *
        eLpNorm (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx' Jdx') 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
  set comp : EuclN → ℝ :=
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx' Jdx' with hcomp_def
  have hpt : ∀ y : EuclN,
      ‖covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
            Jdx Jdx' y * comp y‖ ≤
        ‖(Ccoeff : ℝ) • comp y‖ := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, smul_eq_mul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg hCcoeff_nn]
    by_cases hcz : comp y = 0
    · rw [hcz, abs_zero, mul_zero, mul_zero]
    · obtain ⟨hy, hb⟩ :=
        mem_cutoffKernelM_image_of_cutoffComponentEuclid_ne_zero
          (I := I) (M := M) g r s S α Idx' Jdx' (by rw [← hcomp_def]; exact hcz)
      exact mul_le_mul_of_nonneg_right (hCcoeff hy hb) (abs_nonneg _)
  calc eLpNorm
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
                Jdx Jdx' y * comp y) 2 μ
      ≤ eLpNorm ((Ccoeff : ℝ) • comp) 2 μ := eLpNorm_mono hpt
    _ = ‖(Ccoeff : ℝ)‖ₑ * eLpNorm comp 2 μ :=
        eLpNorm_const_smul (Ccoeff : ℝ) comp 2 _
    _ = ENNReal.ofReal Ccoeff * eLpNorm comp 2 μ := by
        rw [Real.enorm_eq_ofReal hCcoeff_nn]

omit [CompleteSpace E] in
private theorem exists_const_sum_eLpNorm_cutoffLowerOrderTerm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ m : Fin (Module.finrank ℝ E),
        eLpNorm
          (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
            m Idx Jdx) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨Ccoeff, hCcoeff_nn, hCcoeff⟩ :=
    exists_const_covDerivLowerOrderCoeff_bdd_cutoff (I := I) (M := M) g r s α
  obtain ⟨Ccomp, hCcomp_nn, hCcomp⟩ :=
    cutoffComponentEuclid_eLpNorm_le_uniform (I := I) (M := M) g r s α
  set n : ℕ := Module.finrank ℝ E with hn_def
  set Npair : ℕ := Fintype.card ((Fin r → Fin n) × (Fin s → Fin n))
    with hNpair_def
  refine ⟨n * (Npair * (Ccoeff * Ccomp)), by positivity, ?_⟩
  intro S Idx Jdx
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have hμ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have hdir : ∀ m : Fin n,
      eLpNorm
          (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
            m Idx Jdx) 2 μ ≤
        ENNReal.ofReal (Npair * (Ccoeff * Ccomp)) * (‖S‖₊ : ℝ≥0∞) := by
    intro m
    have hae :
        (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
            m Idx Jdx)
          =ᵐ[μ]
        ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y) := by
      rw [hμ_def]
      refine (ae_restrict_iff' hμ_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Finset.sum_apply]
      exact cutoffLowerOrderTerm_eq_linearCombination
        (I := I) (M := M) g r s S.toCcTensor α m Idx Jdx hy
    rw [eLpNorm_congr_ae hae]
    have hmeas : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        AEStronglyMeasurable
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y) μ := by
      intro p
      rw [hμ_def]
      have hcont_on : ContinuousOn
          (fun y : EuclN =>
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                Jdx p.2 y *
              cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                p.1 p.2 y)
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine ContinuousOn.mul ?_ ?_
        · exact (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
            g r s α m Idx p.1 Jdx p.2).continuousOn
        · exact (cutoffComponentEuclid_continuous (I := I) (M := M)
            g r s S.toCcTensor α p.1 p.2).continuousOn
      exact hcont_on.aestronglyMeasurable hμ_meas
    have hcomp_h1 : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        eLpNorm (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α p.1 p.2) 2 μ ≤
          ENNReal.ofReal Ccomp * (‖S‖₊ : ℝ≥0∞) := by
      intro p
      rw [hμ_def]
      have hb := hCcomp S.toCcTensor p.1 p.2
      rw [chartL2Measure] at hb
      refine hb.trans (mul_le_mul_of_nonneg_left ?_ (zero_le _))
      rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from by
        rw [show ((‖S‖₊ : ℝ≥0∞)) = ‖S‖ₑ from (enorm_eq_nnnorm S).symm,
          ← ofReal_norm_eq_enorm S]]
      exact ENNReal.ofReal_le_ofReal
        (SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S)
    have hsummand : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        eLpNorm
            (fun y : EuclN =>
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                  Jdx p.2 y *
                cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                  p.1 p.2 y) 2 μ ≤
          ENNReal.ofReal (Ccoeff * Ccomp) * (‖S‖₊ : ℝ≥0∞) := by
      intro p
      have h1 :
          eLpNorm
              (fun y : EuclN =>
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1
                    Jdx p.2 y *
                  cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α
                    p.1 p.2 y) 2 μ ≤
            ENNReal.ofReal Ccoeff *
              eLpNorm (cutoffComponentEuclid (I := I) (M := M)
                g r s S.toCcTensor α p.1 p.2) 2 μ := by
        rw [hμ_def]
        exact eLpNorm_coeff_mul_cutoffComponent_le (I := I) (M := M) g r s
          S.toCcTensor α m Idx p.1 Jdx p.2 hCcoeff_nn
          (fun {y} hy hb => hCcoeff m Idx p.1 Jdx p.2 hy hb)
      refine (h1.trans
        (mul_le_mul_of_nonneg_left (hcomp_h1 p) (zero_le _))).trans_eq ?_
      rw [ENNReal.ofReal_mul hCcoeff_nn, mul_assoc]
    refine (eLpNorm_sum_le (fun p _ => hmeas p) (by norm_num)).trans ?_
    refine (Finset.sum_le_sum (fun p _ => hsummand p)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, ← hNpair_def, nsmul_eq_mul]
    rw [show ((Npair : ℝ≥0∞)) = ENNReal.ofReal (Npair : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  refine (Finset.sum_le_sum (fun m _ => hdir m)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) from by
    rw [ENNReal.ofReal_natCast]]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

omit [CompleteSpace E] in
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_cutoffComponentEuclid_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ k : Fin (Module.finrank ℝ E),
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C_cov, hC_cov_nn, hC_cov⟩ :=
    exists_const_eLpNorm_cutoffCovDerivComponent_le_uniform
      (I := I) (M := M) g r s α
  obtain ⟨C_low, hC_low_nn, hC_low⟩ :=
    exists_const_sum_eLpNorm_cutoffLowerOrderTerm_le_uniform
      (I := I) (M := M) g r s α
  set n : ℕ := Module.finrank ℝ E with hn_def
  have h_cross_const : ∀ k : Fin n,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
              k Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := fun k =>
    exists_const_eLpNorm_cutoffLeibnizCrossTerm_le_uniform
      (I := I) (M := M) g r s α k
  set C_cross : ℝ := ∑ k : Fin n, (h_cross_const k).choose with hC_cross_def
  have hC_cross_nn : 0 ≤ C_cross :=
    Finset.sum_nonneg (fun k _ => (h_cross_const k).choose_spec.1)
  refine ⟨(n : ℝ) * C_cov + C_low + C_cross,
    by positivity, ?_⟩
  intro S Idx Jdx
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  have hμ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have hdir : ∀ k : Fin n,
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) 2 μ ≤
        eLpNorm
            (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
              k Idx Jdx) 2 μ
          + eLpNorm
              (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
                k Idx Jdx) 2 μ
          + eLpNorm
              (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                k Idx Jdx) 2 μ := by
    intro k
    have h_step1 := chosenWeakPartial'_cutoffComponentEuclid_ae_eq_euclidPartial
      (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
    rw [hμ_def, eLpNorm_congr_ae h_step1]
    set tCov : EuclN → ℝ :=
      cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htCov_def
    set tCross : EuclN → ℝ :=
      cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htCross_def
    set tLow : EuclN → ℝ :=
      cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htLow_def
    have h_three :
        euclidPartial (E := E) k
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx)
          =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)]
        (fun y : EuclN => tCov y + tCross y - tLow y) := by
      refine (ae_restrict_iff' hμ_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [htCov_def, htCross_def, htLow_def]
      exact euclidPartial_cutoffComponentEuclid_eq_three_terms
        (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx hy
    rw [eLpNorm_congr_ae h_three]
    have h_cov_meas : AEStronglyMeasurable tCov
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (cutoffCovDerivComponent_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    have h_cross_meas : AEStronglyMeasurable tCross
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (cutoffLeibnizCrossTerm_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    have h_low_meas : AEStronglyMeasurable tLow
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (cutoffLowerOrderTerm_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    exact eLpNorm_add_add_sub_le h_cov_meas h_cross_meas h_low_meas
  refine (Finset.sum_le_sum (fun k _ => hdir k)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h_cov_sum :
      ∑ k : Fin n,
        eLpNorm (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal ((n : ℝ) * C_cov) * (‖S‖₊ : ℝ≥0∞) := by
    have h_each : ∀ k : Fin n,
        eLpNorm (cutoffCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
          ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞) := fun k => hC_cov S Idx Jdx k
    refine (Finset.sum_le_sum (fun k _ => h_each k)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have h_low_sum :
      ∑ k : Fin n,
        eLpNorm (cutoffLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal C_low * (‖S‖₊ : ℝ≥0∞) := hC_low S Idx Jdx
  have h_cross_sum :
      ∑ k : Fin n,
        eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal C_cross * (‖S‖₊ : ℝ≥0∞) := by
    have h_each : ∀ k : Fin n,
        eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
          ENNReal.ofReal ((h_cross_const k).choose) * (‖S‖₊ : ℝ≥0∞) := by
      intro k
      exact (h_cross_const k).choose_spec.2 S Idx Jdx
    refine (Finset.sum_le_sum (fun k _ => h_each k)).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    rw [hC_cross_def]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => (h_cross_const k).choose_spec.1)]
  calc (∑ k : Fin n,
            eLpNorm (cutoffCovDerivComponent (I := I) (M := M)
              g r s S.toCcTensor α k Idx Jdx) 2 μ
          + ∑ k : Fin n,
            eLpNorm (cutoffLeibnizCrossTerm (I := I) (M := M)
              g r s S.toCcTensor α k Idx Jdx) 2 μ)
        + ∑ k : Fin n,
            eLpNorm (cutoffLowerOrderTerm (I := I) (M := M)
              g r s S.toCcTensor α k Idx Jdx) 2 μ
      ≤ (ENNReal.ofReal ((n : ℝ) * C_cov) * (‖S‖₊ : ℝ≥0∞)
            + ENNReal.ofReal C_cross * (‖S‖₊ : ℝ≥0∞))
          + ENNReal.ofReal C_low * (‖S‖₊ : ℝ≥0∞) := by
        gcongr
    _ = ENNReal.ofReal ((n : ℝ) * C_cov + C_low + C_cross) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (by positivity) hC_cross_nn,
          ENNReal.ofReal_add (by positivity) hC_low_nn]
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
