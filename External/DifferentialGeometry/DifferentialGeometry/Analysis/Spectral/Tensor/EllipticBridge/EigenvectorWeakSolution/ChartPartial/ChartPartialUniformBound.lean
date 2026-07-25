import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartPartialLowerOrderBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.ChartPartialCovariantBound
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound


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

private lemma eLpNorm_add_add_sub_le
    {β : Type*} [MeasurableSpace β] {ν : Measure β} {a b c : β → ℝ}
    (ha : AEStronglyMeasurable a ν) (hb : AEStronglyMeasurable b ν)
    (hc : AEStronglyMeasurable c ν) :
    eLpNorm (fun y => a y + b y - c y) 2 ν ≤
      eLpNorm a 2 ν + eLpNorm b 2 ν + eLpNorm c 2 ν := by
  have h_ab : eLpNorm (fun y => a y + b y) 2 ν ≤
      eLpNorm a 2 ν + eLpNorm b 2 ν :=
    eLpNorm_add_le ha hb (by norm_num)
  have h_full : eLpNorm (fun y => (a y + b y) - c y) 2 ν ≤
      eLpNorm (fun y => a y + b y) 2 ν + eLpNorm c 2 ν :=
    eLpNorm_sub_le (ha.add hb) hc (by norm_num)
  exact h_full.trans (by gcongr)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_contDiff_of_contDiff
    {u : EuclN → ℝ} (hu : ContDiff ℝ ∞ u) (k : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k u) := by
  have hfd : ContDiff ℝ ∞ (fun z => fderiv ℝ u z) :=
    hu.fderiv_right (m := (∞ : WithTop ℕ∞))
      (by rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl])
  have hcomp : euclidPartial (E := E) k u =
      (fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single k 1)) ∘
        (fun z => fderiv ℝ u z) := by
    funext z; rw [euclidPartial_def]; rfl
  rw [hcomp]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single k 1)).contDiff.comp hfd

private def pouKernelM (α : M) : Set M :=
  tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouKernelM_isClosed (α : M) :
    IsClosed (pouKernelM (I := I) (M := M) α) :=
  isClosed_tsupport _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouKernelM_subset_chart_source (α : M) :
    pouKernelM (I := I) (M := M) α ⊆ (chartAt H α).source :=
  DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouKernelM_isCompact (α : M) :
    IsCompact (pouKernelM (I := I) (M := M) α) :=
  (pouKernelM_isClosed (I := I) (M := M) α).isCompact

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartAtlasPOU_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
  (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRaw_pou_contDiff (α : M) :
    ContDiff ℝ ∞
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) :=
  DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M)
    (chartAtlasPOU_contMDiff (I := I) (M := M) α)
    (pouKernelM_subset_chart_source (I := I) (M := M) α)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorChartComponent_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  rw [tensorChartComponent_def]
  refine DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M) ?_ ?_
  · exact tensorChartComponentPou_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  · exact tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S α Idx Jdx

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponent_hasCompactSupport'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [tensorChartComponent_def]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponent_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rw [tensorChartComponent_def]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenWeakPartial'_tensorChartComponent_ae_eq_euclidPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorChartComponent_contDiff (I := I) (M := M) g r s S α Idx Jdx
  have hu_cpt : HasCompactSupport u :=
    tensorChartComponent_hasCompactSupport' (I := I) (M := M) g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    tensorChartComponent_tsupport_subset (I := I) (M := M) g r s S α Idx Jdx
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2 u (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hΩ_open hu_smooth hu_cpt hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial_smooth_ae_eq
      (d := Module.finrank ℝ E) hp_one hΩ_open hu_smooth hu_W1p k
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [euclidPartial_def]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponent_eq_pou_mul_rawPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y =
      chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
        chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y := by
  classical
  rw [tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy]
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_tensorChartComponent_eq_leibniz
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y =
      chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
          euclidPartial (E := E) k
            (chartPushedRaw (I := I) (M := M) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + euclidPartial (E := E) k
            (chartPushedRaw (I := I) (M := M) α
              (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) y *
          chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y := by
  classical
  set ρ : EuclN → ℝ :=
    chartPushedRaw (I := I) (M := M) α
      (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) with hρ_def
  set w : EuclN → ℝ :=
    chartPushedRaw (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) with hw_def
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_nhds : chartTargetEuclid (I := I) (M := M) α ∈ 𝓝 y :=
    hΩ_open.mem_nhds hy
  have h_eqf : tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx
      =ᶠ[𝓝 y] (fun z : EuclN => ρ z * w z) := by
    filter_upwards [hΩ_nhds] with z hz
    rw [hρ_def, hw_def]
    exact tensorChartComponent_eq_pou_mul_rawPushed
      (I := I) (M := M) g r s S α Idx Jdx hz
  have hρ_diff : DifferentiableAt ℝ ρ y :=
    ((chartPushedRaw_pou_contDiff (I := I) (M := M) α).differentiable
      (by simp)).differentiableAt
  have hw_diffOn : DifferentiableOn ℝ w
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartPushedRaw_tensorChartComponentRaw_contDiffOn
      (I := I) (M := M) g r s S α Idx Jdx).differentiableOn (by simp)
  have hw_diff : DifferentiableAt ℝ w y :=
    (hw_diffOn y hy).differentiableAt hΩ_nhds
  have h_fderiv :
      fderiv ℝ (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y =
        ρ y • fderiv ℝ w y + w y • fderiv ℝ ρ y := by
    rw [h_eqf.fderiv_eq]
    exact fderiv_mul hρ_diff hw_diff
  rw [euclidPartial_def, h_fderiv,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    euclidPartial_def, euclidPartial_def]
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartial_rawPushed_eq_covDerivComponent_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y =
      tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
              (chartBasisVecFiber (I := I) α k)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
        - covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y := by
  have h := covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s S α k Idx Jdx hy
  linarith [h]

private def leibnizCrossTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) y *
      chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y

private def pouCovDerivComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
            (chartBasisVecFiber (I := I) α k)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))

private def pouLowerOrderTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
      covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_tensorChartComponent_eq_three_terms
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y =
      pouCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx y
        + leibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y
        - pouLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y := by
  classical
  rw [euclidPartial_tensorChartComponent_eq_leibniz
    (I := I) (M := M) g r s S α k Idx Jdx hy,
    euclidPartial_rawPushed_eq_covDerivComponent_sub
      (I := I) (M := M) g r s S α k Idx Jdx hy]
  unfold pouCovDerivComponent leibnizCrossTerm pouLowerOrderTerm
  ring

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRaw_pou_continuousOn (α : M) :
    ContinuousOn
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedRaw_pou_contDiff (I := I) (M := M) α).continuous.continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_chartPushedRaw_pou_continuousOn
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (euclidPartial_contDiff_of_contDiff (E := E)
    (chartPushedRaw_pou_contDiff (I := I) (M := M) α) k).continuous.continuousOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_rawComponent_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedRaw_tensorChartComponentRaw_contDiffOn
    (I := I) (M := M) g r s S α Idx Jdx).continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartial_chartPushedRaw_rawComponent_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (euclidPartial_chartPushedRaw_contDiffOn
    (I := I) (M := M) g r s S α k Idx Jdx).continuousOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma pouCovDerivComponent_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (pouCovDerivComponent (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set galt : EuclN → ℝ := fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) y *
      (euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y
        + covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y)
    with hgalt_def
  have hgalt_cont : ContinuousOn galt
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartPushedRaw_pou_continuousOn (I := I) (M := M) α).mul
      ((euclidPartial_chartPushedRaw_rawComponent_continuousOn
        (I := I) (M := M) g r s S α k Idx Jdx).add
      (covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α
        k Idx Jdx
        (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
          (I := I) (M := M) g r s S α Idx' Jdx')).continuousOn)
  refine hgalt_cont.congr (fun y hy => ?_)
  have h := euclidPartial_rawPushed_eq_covDerivComponent_sub
    (I := I) (M := M) g r s S α k Idx Jdx hy
  unfold pouCovDerivComponent
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
private lemma pouLowerOrderTerm_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (pouLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold pouLowerOrderTerm
  exact (chartPushedRaw_pou_continuousOn (I := I) (M := M) α).mul
    (covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g r s S α
      k Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s S α Idx' Jdx')).continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma leibnizCrossTerm_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (leibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold leibnizCrossTerm
  exact (euclidPartial_chartPushedRaw_pou_continuousOn (I := I) (M := M) α k).mul
    (chartPushedRaw_rawComponent_continuousOn (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma euclidPartial_chartPushedRaw_pou_tsupport_subset
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    tsupport
        (euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)))) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (pouKernelM (I := I) (M := M) α)) := by
  classical
  have h1 : tsupport
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)))) ⊆
      tsupport (chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) := by
    have h := tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)))
      (EuclideanSpace.single k (1 : ℝ))
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport _)) h
    intro y hy
    refine subset_tsupport _ ?_
    simpa [euclidPartial_def] using hy
  have h2 : tsupport (chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (pouKernelM (I := I) (M := M) α)) := by
    have hK_compact : IsCompact ((extChartAt I α) ''
        (pouKernelM (I := I) (M := M) α)) :=
      chartImage_pouTsupport_isCompact (I := I) (M := M) α
    have hKE_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (pouKernelM (I := I) (M := M) α))) :=
      hK_compact.image (toEuclidean (E := E)).continuous
    refine closure_minimal ?_ hKE_compact.isClosed
    intro y hy
    rw [Function.mem_support] at hy
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      by_contra hy_off
      exact hy (chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) hy_off)
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    have hb_src : b ∈ (chartAt H α).source :=
      symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy_target
    have hb_pou : b ∈ pouKernelM (I := I) (M := M) α := by
      refine subset_tsupport _ ?_
      rw [Function.mem_support]
      intro hb_zero
      apply hy
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) hy_target]
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
    refine ⟨extChartAt I α b, ⟨b, hb_pou, rfl⟩, ?_⟩
    rw [h_extChartAt_b]
    exact (toEuclidean (E := E)).apply_symm_apply y
  exact h1.trans h2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma leibnizCrossTerm_eq_zero_off_pou_kernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∉ (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (pouKernelM (I := I) (M := M) α))) :
    leibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y = 0 := by
  classical
  unfold leibnizCrossTerm
  have hχ_zero : euclidPartial (E := E) k
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) y = 0 := by
    by_contra hne
    exact hy (euclidPartial_chartPushedRaw_pou_tsupport_subset (I := I) (M := M) α k
      (subset_tsupport _ (Function.mem_support.mpr hne)))
  rw [hχ_zero, zero_mul]

private def rawComponentCutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : M → ℝ :=
  (pouKernelM (I := I) (M := M) α).indicator
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma rawComponentCutoff_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx) ⊆
      pouKernelM (I := I) (M := M) α := by
  classical
  refine closure_minimal ?_ (pouKernelM_isClosed (I := I) (M := M) α)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_off
  exact hx (by rw [rawComponentCutoff, Set.indicator_of_notMem hx_off])

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma rawComponentCutoff_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  unfold rawComponentCutoff
  rw [show (pouKernelM (I := I) (M := M) α).indicator
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) =
      (pouKernelM (I := I) (M := M) α).piecewise
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (fun _ : M => (0 : ℝ)) from by
    funext x
    by_cases hx : x ∈ pouKernelM (I := I) (M := M) α
    · simp [Set.indicator_of_mem hx, Set.piecewise_eq_of_mem _ _ _ hx]
    · simp [Set.indicator_of_notMem hx, Set.piecewise_eq_of_notMem _ _ _ hx]]
  have hraw_cont : ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (pouKernelM (I := I) (M := M) α) :=
    ((tensorChartComponentRaw_contMDiffOn_chart_source
        (I := I) (M := M) g r s S α Idx Jdx).continuousOn).mono
      (pouKernelM_subset_chart_source (I := I) (M := M) α)
  exact ContinuousOn.measurable_piecewise hraw_cont
    (continuousOn_const) (pouKernelM_isClosed (I := I) (M := M) α).measurableSet

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_const_rawComponentCutoff_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
        (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    tensorTrivProj_norm_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b
  have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  by_cases hb : b ∈ pouKernelM (I := I) (M := M) α
  · have hcut_eq : rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx b =
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
      rw [rawComponentCutoff, Set.indicator_of_mem hb]
    rw [hcut_eq, tensorChartComponentRaw_def]
    set T : TensorRSModel r s ℝ E :=
      tensorTrivProj (I := I) (M := M) g r s S α b with hT_def
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
          (S.toFun b) (S.toFun b) := h_norm S b hb
    calc (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2
        ≤ C_proj ^ 2 * ‖T‖ ^ 2 := h_proj_sq_le
      _ ≤ C_proj ^ 2 *
          (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
        mul_le_mul_of_nonneg_left h_triv_sq_le (sq_nonneg _)
      _ = C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  · have hcut_zero : rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx b
        = 0 := by
      rw [rawComponentCutoff, Set.indicator_of_notMem hb]
    rw [hcut_zero]
    have h_rhs_nn : 0 ≤ C_proj ^ 2 * K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hK_nn) hQ_nn
    simpa using h_rhs_nn

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) :
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

private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

private lemma sqrt_ofReal_eq_ofReal_sqrt {a : ℝ} (ha : 0 ≤ a) :
    (ENNReal.ofReal a) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt a) := by
  rw [show a = Real.sqrt a * Real.sqrt a from (Real.mul_self_sqrt ha).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt a)) * (ENNReal.ofReal (Real.sqrt a)) =
      (ENNReal.ofReal (Real.sqrt a)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_const_eLpNorm_rawComponentCutoff_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    exists_const_rawComponentCutoff_sq_le (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx
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
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
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
    have h_pow := le_sqrt_of_sq_le h_sq
    rw [sqrt_ofReal_eq_ofReal_sqrt hStotal_nn] at h_pow
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
private lemma exists_const_euclidPartial_chartPushedRaw_pou_le
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧
      ∀ y : EuclN,
        ‖euclidPartial (E := E) k
          (chartPushedRaw (I := I) (M := M) α
            (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) y‖ ≤ Cχ := by
  classical
  set χ : EuclN → ℝ :=
    euclidPartial (E := E) k
      (chartPushedRaw (I := I) (M := M) α
        (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) with hχ_def
  have hχ_cont : Continuous χ := by
    rw [hχ_def]
    exact (euclidPartial_contDiff_of_contDiff (E := E)
      (chartPushedRaw_pou_contDiff (I := I) (M := M) α) k).continuous
  have hχ_cpt : HasCompactSupport χ := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (pouKernelM (I := I) (M := M) α))) ?_ ?_
    · exact (chartImage_pouTsupport_isCompact (I := I) (M := M) α).image
        (toEuclidean (E := E)).continuous
    · refine subset_trans ?_
        (euclidPartial_chartPushedRaw_pou_tsupport_subset (I := I) (M := M) α k)
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
private lemma leibnizCrossTerm_le_const_mul_chartPushedRaw_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {Cχ : ℝ} (hCχ_nn : 0 ≤ Cχ)
    (hCχ : ∀ y : EuclN,
      ‖euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯))) y‖ ≤ Cχ)
    (y : EuclN) :
    ‖leibnizCrossTerm (I := I) (M := M) g r s S α k Idx Jdx y‖ ≤
      Cχ * ‖chartPushedRaw (I := I) (M := M) α
        (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx) y‖ := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
      with hb_def
    by_cases hb : b ∈ pouKernelM (I := I) (M := M) α
    · have h_cut_eval : chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx) y =
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx) hy,
          rawComponentCutoff, Set.indicator_of_mem hb]
      have h_raw_eval : chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y =
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy]
      unfold leibnizCrossTerm
      rw [h_cut_eval, h_raw_eval, norm_mul]
      exact mul_le_mul_of_nonneg_right (hCχ y) (norm_nonneg _)
    · have h_cross_zero : leibnizCrossTerm (I := I) (M := M) g r s S α
          k Idx Jdx y = 0 := by
        refine leibnizCrossTerm_eq_zero_off_pou_kernel
          (I := I) (M := M) g r s S α k Idx Jdx ?_
        rintro ⟨z, ⟨b', hb'_pou, hb'_eq⟩, hz_eq⟩
        apply hb
        have hy_symm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
          rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
          exact hy
        have hb'_src : b' ∈ (extChartAt I α).source := by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact pouKernelM_subset_chart_source (I := I) (M := M) α hb'_pou
        have h_symm_y : (toEuclidean (E := E)).symm y = z := by
          rw [← hz_eq]
          exact (toEuclidean (E := E)).symm_apply_apply z
        have hb_eq_b' : b = b' := by
          rw [hb_def, h_symm_y, ← hb'_eq, (extChartAt I α).left_inv hb'_src]
        rw [hb_eq_b']
        exact hb'_pou
      rw [h_cross_zero, norm_zero]
      exact mul_nonneg hCχ_nn (norm_nonneg _)
  · have h_cross_zero : leibnizCrossTerm (I := I) (M := M) g r s S α
        k Idx Jdx y = 0 := by
      unfold leibnizCrossTerm
      rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy,
        mul_zero]
    have h_cut_zero : chartPushedRaw (I := I) (M := M) α
        (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx) y = 0 :=
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α
        (rawComponentCutoff (I := I) (M := M) g r s S α Idx Jdx) hy
    rw [h_cross_zero, norm_zero, h_cut_zero, norm_zero, mul_zero]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_const_eLpNorm_leibnizCrossTerm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      eLpNorm
          (leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨Cχ, hCχ_nn, hCχ⟩ :=
    exists_const_euclidPartial_chartPushedRaw_pou_le (I := I) (M := M) α k
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  obtain ⟨C_bridge, hC_bridge_pos, hC_bridge⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α (pouKernelM_isCompact (I := I) (M := M) α)
      (pouKernelM_subset_chart_source (I := I) (M := M) α) hp_one hp_top
  obtain ⟨C_cut, hC_cut_nn, hC_cut⟩ :=
    exists_const_eLpNorm_rawComponentCutoff_le (I := I) (M := M) g r s α
  refine ⟨Cχ * (C_bridge * C_cut),
    mul_nonneg hCχ_nn (mul_nonneg hC_bridge_pos.le hC_cut_nn), ?_⟩
  intro S Idx Jdx
  set μ : Measure EuclN :=
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)
    with hμ_def
  set normCut : EuclN → ℝ := fun y : EuclN =>
    ‖chartPushedRaw (I := I) (M := M) α
      (rawComponentCutoff (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) y‖
    with hnormCut_def
  have h_ptwise : ∀ y : EuclN,
      ‖leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx y‖ ≤
        (Cχ • normCut) y := by
    intro y
    rw [Pi.smul_apply, smul_eq_mul, hnormCut_def]
    exact leibnizCrossTerm_le_const_mul_chartPushedRaw_cutoff
      (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx hCχ_nn hCχ y
  have h_mono :
      eLpNorm (leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        eLpNorm (Cχ • normCut) 2 μ :=
    eLpNorm_mono_real h_ptwise
  have h_smul :
      eLpNorm (Cχ • normCut) 2 μ =
        ‖Cχ‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoff (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)) 2 μ := by
    rw [eLpNorm_const_smul Cχ normCut 2 μ, hnormCut_def, eLpNorm_norm]
  have hCχ_enorm : ‖Cχ‖ₑ = ENNReal.ofReal Cχ := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hCχ_nn]
  have h_bridge :
      eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoff (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)) 2 μ ≤
        ENNReal.ofReal C_bridge *
          eLpNorm (rawComponentCutoff (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
            2 (riemannianMeasure (I := I) g (chartAtlasPOU I M)) :=
    hC_bridge
      (rawComponentCutoff_measurable (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (rawComponentCutoff_tsupport_subset (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx)
  have h_meas_eq :
      riemannianMeasure (I := I) g (chartAtlasPOU I M) =
        riemannianVolumeMeasure (I := I) (M := M) g := rfl
  rw [h_meas_eq] at h_bridge
  have h_cut_h1 :
      eLpNorm (rawComponentCutoff (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_cut * (‖S‖₊ : ℝ≥0∞) := by
    have hb := hC_cut S.toCcTensor Idx Jdx
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (zero_le _))
    rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from by
      rw [show ((‖S‖₊ : ℝ≥0∞)) = ‖S‖ₑ from (enorm_eq_nnnorm S).symm,
        ← ofReal_norm_eq_enorm S]]
    exact ENNReal.ofReal_le_ofReal
      (SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S)
  calc eLpNorm (leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ
      ≤ eLpNorm (Cχ • normCut) 2 μ := h_mono
    _ = ‖Cχ‖ₑ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoff (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ := h_smul
    _ = ENNReal.ofReal Cχ * eLpNorm (chartPushedRaw (I := I) (M := M) α
          (rawComponentCutoff (I := I) (M := M) g r s S.toCcTensor α
            Idx Jdx)) 2 μ := by rw [hCχ_enorm]
    _ ≤ ENNReal.ofReal Cχ *
          (ENNReal.ofReal C_bridge *
            eLpNorm (rawComponentCutoff (I := I) (M := M) g r s S.toCcTensor α
              Idx Jdx) 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :=
        mul_le_mul_of_nonneg_left h_bridge (by positivity)
    _ ≤ ENNReal.ofReal Cχ *
          (ENNReal.ofReal C_bridge *
            (ENNReal.ofReal C_cut * (‖S‖₊ : ℝ≥0∞))) := by gcongr
    _ = ENNReal.ofReal (Cχ * (C_bridge * C_cut)) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hCχ_nn, ENNReal.ofReal_mul hC_bridge_pos.le]
        ring

omit [CompleteSpace E] in
theorem exists_const_sum_eLpNorm_chosenWeakPartial'_tensorChartComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      ∑ k : Fin (Module.finrank ℝ E),
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 k
            (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C_cov, hC_cov_nn, hC_cov⟩ :=
    exists_const_sum_eLpNorm_pou_covDerivComponent_le_uniform
      (I := I) (M := M) g r s α
  obtain ⟨C_low, hC_low_nn, hC_low⟩ :=
    exists_const_sum_eLpNorm_pou_covDerivLowerOrderTerm_le_uniform
      (I := I) (M := M) g r s α
  set n : ℕ := Module.finrank ℝ E with hn_def
  have h_cross_const : ∀ k : Fin n,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := fun k =>
    exists_const_eLpNorm_leibnizCrossTerm_le_uniform (I := I) (M := M) g r s α k
  set C_cross : ℝ := ∑ k : Fin n, (h_cross_const k).choose with hC_cross_def
  have hC_cross_nn : 0 ≤ C_cross :=
    Finset.sum_nonneg (fun k _ => (h_cross_const k).choose_spec.1)
  refine ⟨C_cov + C_low + C_cross,
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
          (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) 2 μ ≤
        eLpNorm
            (pouCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
              k Idx Jdx) 2 μ
          + eLpNorm
              (leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
                k Idx Jdx) 2 μ
          + eLpNorm
              (pouLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
                k Idx Jdx) 2 μ := by
    intro k
    have h_step1 := chosenWeakPartial'_tensorChartComponent_ae_eq_euclidPartial
      (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
    rw [hμ_def, eLpNorm_congr_ae h_step1]
    set tCov : EuclN → ℝ :=
      pouCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htCov_def
    set tCross : EuclN → ℝ :=
      leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htCross_def
    set tLow : EuclN → ℝ :=
      pouLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx
      with htLow_def
    have h_three :
        euclidPartial (E := E) k
            (tensorChartComponent (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
          =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)]
        (fun y : EuclN => tCov y + tCross y - tLow y) := by
      refine (ae_restrict_iff' hμ_meas).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [htCov_def, htCross_def, htLow_def]
      exact euclidPartial_tensorChartComponent_eq_three_terms
        (I := I) (M := M) g r s S.toCcTensor α k Idx Jdx hy
    rw [eLpNorm_congr_ae h_three]
    have h_cov_meas : AEStronglyMeasurable tCov
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (pouCovDerivComponent_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    have h_cross_meas : AEStronglyMeasurable tCross
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (leibnizCrossTerm_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    have h_low_meas : AEStronglyMeasurable tLow
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      (pouLowerOrderTerm_continuousOn (I := I) (M := M) g r s S.toCcTensor α
        k Idx Jdx).aestronglyMeasurable hμ_meas
    exact eLpNorm_add_add_sub_le h_cov_meas h_cross_meas h_low_meas
  refine (Finset.sum_le_sum (fun k _ => hdir k)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h_cov_sum :
      ∑ k : Fin n,
        eLpNorm (pouCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞) := by
    have h := hC_cov S Idx Jdx
    refine le_of_eq_of_le ?_ h
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rfl
  have h_low_sum :
      ∑ k : Fin n,
        eLpNorm (pouLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal C_low * (‖S‖₊ : ℝ≥0∞) := by
    have h := hC_low S Idx Jdx
    refine le_of_eq_of_le ?_ h
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rfl
  have h_cross_sum :
      ∑ k : Fin n,
        eLpNorm (leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
          k Idx Jdx) 2 μ ≤
        ENNReal.ofReal C_cross * (‖S‖₊ : ℝ≥0∞) := by
    have h_each : ∀ k : Fin n,
        eLpNorm (leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
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
            eLpNorm (pouCovDerivComponent (I := I) (M := M) g r s S.toCcTensor α
              k Idx Jdx) 2 μ
          + ∑ k : Fin n,
            eLpNorm (leibnizCrossTerm (I := I) (M := M) g r s S.toCcTensor α
              k Idx Jdx) 2 μ)
        + ∑ k : Fin n,
            eLpNorm (pouLowerOrderTerm (I := I) (M := M) g r s S.toCcTensor α
              k Idx Jdx) 2 μ
      ≤ (ENNReal.ofReal C_cov * (‖S‖₊ : ℝ≥0∞)
            + ENNReal.ofReal C_cross * (‖S‖₊ : ℝ≥0∞))
          + ENNReal.ofReal C_low * (‖S‖₊ : ℝ≥0∞) := by
        gcongr
    _ = ENNReal.ofReal (C_cov + C_low + C_cross) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (by positivity) hC_cross_nn,
          ENNReal.ofReal_add hC_cov_nn hC_low_nn]
        ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
