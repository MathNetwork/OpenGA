import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.CovApplyFrameToCoordExpansion
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set MeasureTheory Filter Topology Function NormedSpace
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem chartFrameNormGlobalSmoothCoordMatrix_pullback_contDiffOn_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_chart :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) I ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) (M := M) α
  have h_coord : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartFrameNormGlobalSmoothCoordMatrix_contMDiffOn (I := I) (M := M) g α i k
  have h_maps :
      MapsTo (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α)
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have h_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        (chartAt H α).source :=
      DifferentialGeometry.Analysis.Sobolev.Chart.symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
    change (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source
    exact h_src
  have h_comp :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 𝓘(ℝ, ℝ) ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_coord.comp h_chart h_maps
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

private noncomputable def coordMatrixOnEuclid
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

private lemma coordMatrixOnEuclid_def
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    coordMatrixOnEuclid (I := I) (M := M) g α i k y =
      chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

private lemma coordMatrixOnEuclid_contDiffOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (coordMatrixOnEuclid (I := I) (M := M) g α i k)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartFrameNormGlobalSmoothCoordMatrix_pullback_contDiffOn_chartTarget
    (I := I) (M := M) g α i k

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma extDerivFun_apply_scalar
    (f : M → ℝ) {x : M} (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk]
  rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma partialDeriv_scalarOnE_eq_euclidPartial_pulled
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (α : M) (m : Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    partialDeriv (E := E) m (scalarOnE (I := I) α f)
        (extChartAt I α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      euclidPartial (E := E) m (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  rw [euclidPartial_def]
  have hpushed_eq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f =ᶠ[𝓝 y]
        ((scalarOnE (I := I) α f) ∘ (toEuclidean (E := E)).symm) := by
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hy_sob : y ∈ (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := hy
    filter_upwards [hopen.mem_nhds hy] with z hz
    have hz_sob : z ∈ (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := hz
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α f hz_sob]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq hpushed_eq]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := scalarOnE (I := I) α f) (x := y)]
  rw [ContinuousLinearMap.comp_apply]
  rw [show (toEuclidean (E := E)).symm.toContinuousLinearMap
      (EuclideanSpace.single m (1 : ℝ)) = (chartModelBasis E) m from by
    rw [chartModelBasis_apply]; rfl]
  rw [partialDeriv]
  rw [show (toEuclidean (E := E)).symm y = extChartAt I α b from hphi_b.symm]

omit [NeZero (Module.finrank ℝ E)] in
private lemma extDerivFun_chartBasisVecFiber_eq_euclidPartial_of_mdiff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (α : M) (m : Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    extDerivFun (I := I) f
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartBasisVecFiber (I := I) α m
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      euclidPartial (E := E) m (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have hb_chart : b ∈ (chartAt H α).source :=
    DifferentialGeometry.Analysis.Sobolev.Chart.symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  rw [extDerivFun_apply_scalar (I := I) f (x := b)
    (chartBasisVecFiber (I := I) α m b)]
  rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (I := I) α hf hb_chart hb_int m]
  exact partialDeriv_scalarOnE_eq_euclidPartial_pulled
    (I := I) (M := M) f α m hy

private lemma extDerivFun_pull_eq_euclidPartial_on_target
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k l : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        extDerivFun
          (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartBasisVecFiber (I := I) α l
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
      (euclidPartial (E := E) l
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    DifferentialGeometry.Analysis.Sobolev.Chart.symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change b ∈ (chartAt H α).source
    exact hb_chart
  have h_base_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have h_coord_on :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun b : M =>
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartFrameNormGlobalSmoothCoordMatrix_contMDiffOn (I := I) (M := M) g α i k
  have h_coord_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b) b :=
    (h_coord_on b hb_base).contMDiffAt (h_base_open.mem_nhds hb_base)
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M =>
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b) b :=
    h_coord_at.mdifferentiableAt (by simp)
  exact extDerivFun_chartBasisVecFiber_eq_euclidPartial_of_mdiff
    (I := I) (M := M)
    (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k) α l hy hf_mdiff

private lemma coordMatrixOnEuclid_eventuallyEq_chartPushedRaw
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (coordMatrixOnEuclid (I := I) (M := M) g α i k)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k))
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [coordMatrixOnEuclid_def]
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k) hy]

private lemma euclidPartial_chartPushedRaw_coordMatrix_contDiffOn
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) l
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
      (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k) with hu_def
  set v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    coordMatrixOnEuclid (I := I) (M := M) g α i k with hv_def
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_eq : Set.EqOn u v (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy
    exact (coordMatrixOnEuclid_eventuallyEq_chartPushedRaw
      (I := I) (M := M) g α i k hy).symm
  have hv_smooth : ContDiffOn ℝ ∞ v (chartTargetEuclid (I := I) (M := M) α) :=
    coordMatrixOnEuclid_contDiffOn (I := I) (M := M) g α i k
  have hu_smooth : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α) :=
    hv_smooth.congr (fun z hz => h_eq hz)
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu_smooth
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
          L (EuclideanSpace.single l 1)) ∘ (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

theorem chartFrameNormGlobalSmoothCoordMatrix_dirDeriv_pullback_contDiffOn_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        extDerivFun
          (chartFrameNormGlobalSmoothCoordMatrix (I := I) g α i k)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartBasisVecFiber (I := I) α l
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine (euclidPartial_chartPushedRaw_coordMatrix_contDiffOn
    (I := I) (M := M) g α i k l).congr ?_
  intro y hy
  exact extDerivFun_pull_eq_euclidPartial_on_target
    (I := I) (M := M) g α i k l hy

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
