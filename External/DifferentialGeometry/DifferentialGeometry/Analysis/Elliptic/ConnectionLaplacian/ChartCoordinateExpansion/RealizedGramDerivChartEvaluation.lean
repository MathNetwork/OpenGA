import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilin_chartBasis_eq_tensorChartComponent
    (g₀ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    smoothCcTensorBilinForm (I := I) g₀ W x (chartModelBasis E a) (chartModelBasis E b) =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 W x ![] ![a, b] x := by
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ W x
    (chartModelBasis E a) (chartModelBasis E b)]
  exact unitModel_basisChart_eq_tensorChartComponent (I := I) (M := M) g₀ W x a b

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cometricFinBasisTrace_eq_chartInvGram_bilin
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k₁ : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k₁)))
          ((Module.finBasis ℝ E) k₁)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l •
          F (chartModelBasis E l) (chartModelBasis E k₁) := by
  classical
  set L₁ : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (cometricLmodel (I := I) g₁ x).comp
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)) with hL₁
  set F' : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := F.comp L₁ with hF'
  have hFapp : ∀ (φ : E →L[ℝ] ℝ) (v : E),
      F' φ v = F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) v := by
    intro φ v
    rfl
  have htrace := (cDualBasis_trace_basis_indep (E := E) (chartModelBasis E) F').symm
  rw [show (∑ k₁ : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k₁)))
          ((Module.finBasis ℝ E) k₁)) =
      ∑ k₁ : Fin (Module.finrank ℝ E),
        F' ((Module.finBasis ℝ E).cDualBasis k₁) ((Module.finBasis ℝ E) k₁) from
    Finset.sum_congr rfl (fun k₁ _ => (hFapp _ _).symm)]
  rw [htrace]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [hFapp ((chartModelBasis E).cDualBasis k₁) (chartModelBasis E k₁)]
  rw [cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum (I := I) g₁ x k₁]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply]

def quadrilinearMapSlotBilinearAt
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (i j : Fin 4) (hij : i ≠ j) (base : Fin 4 → E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f (Function.update (Function.update base i c) j v)
          map_add' := fun v1 v2 => by
            rw [f.map_update_add (Function.update base i c) j v1 v2]
          map_smul' := fun r v => by
            rw [f.map_update_smul (Function.update base i c) j r v]; rfl }
      map_add' := fun c1 c2 => by
        ext v
        change f (Function.update (Function.update base i (c1 + c2)) j v) =
          f (Function.update (Function.update base i c1) j v) +
          f (Function.update (Function.update base i c2) j v)
        rw [Function.update_comm hij c1 v base, Function.update_comm hij c2 v base,
          Function.update_comm hij (c1 + c2) v base]
        rw [f.map_update_add (Function.update base j v) i c1 c2]
      map_smul' := fun r c => by
        ext v
        change f (Function.update (Function.update base i (r • c)) j v) =
          r • f (Function.update (Function.update base i c) j v)
        rw [Function.update_comm hij c v base, Function.update_comm hij (r • c) v base]
        rw [f.map_update_smul (Function.update base j v) i r c] }

omit [NeZero (Module.finrank ℝ E)] in
lemma unitModel4SlotBilin_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (i j : Fin 4) (hij : i ≠ j) (base : Fin 4 → E) (c v : E) :
    quadrilinearMapSlotBilinearAt (E := E) f i j hij base c v =
      f (Function.update (Function.update base i c) j v) := rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma partialDeriv_scalarOnE_eq_euclidPartial_local
    (f : M → ℝ) (α : M) (m : Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    partialDeriv (E := E) m (scalarOnE (I := I) α f)
        (extChartAt I α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      euclidPartial (E := E) m
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
      (I := I) hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  rw [euclidPartial_def]
  have hpushed_eq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f =ᶠ[𝓝 y]
        ((scalarOnE (I := I) α f) ∘ (toEuclidean (E := E)).symm) := by
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
        (I := I) (M := M) α
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α f hz]
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (m₁ m₂ : Fin (Module.finrank ℝ E)) (a b : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) m₂
        (fun y' => euclidPartial (E := E) m₁
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b]))
          y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      partialDeriv (E := E) m₂
        (partialDeriv (E := E) m₁
          (scalarOnE (I := I) x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b])))
        (extChartAt I x x) := by
  classical
  set f : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] with hf_def
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) x
  have hYmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  set gm : M → ℝ := fun p =>
    partialDeriv (E := E) m₁ (scalarOnE (I := I) x f) (extChartAt I x p) with hgm_def
  have hinner_eqOn : Set.EqOn
      (fun y' => euclidPartial (E := E) m₁ (chartPushedRaw I x f) y')
      (chartPushedRaw I x gm)
      (chartTargetEuclid (I := I) (M := M) x) := by
    intro y' hy'
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) x gm hy']
    change euclidPartial (E := E) m₁ (chartPushedRaw I x f) y' =
      partialDeriv (E := E) m₁ (scalarOnE (I := I) x f)
        (extChartAt I x ((extChartAt I x).symm ((toEuclidean (E := E)).symm y')))
    rw [partialDeriv_scalarOnE_eq_euclidPartial_local f x m₁ hy']
  have hinner_ev :
      (fun y' => euclidPartial (E := E) m₁ (chartPushedRaw I x f) y') =ᶠ[𝓝
        ((toEuclidean (E := E)) (extChartAt I x x))]
      (chartPushedRaw I x gm) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hYmem) hinner_eqOn
  rw [show euclidPartial (E := E) m₂
        (fun y' => euclidPartial (E := E) m₁ (chartPushedRaw I x f) y')
        ((toEuclidean (E := E)) (extChartAt I x x)) =
      euclidPartial (E := E) m₂ (chartPushedRaw I x gm)
        ((toEuclidean (E := E)) (extChartAt I x x)) from by
    rw [euclidPartial_def, euclidPartial_def, hinner_ev.fderiv_eq] ]
  rw [← partialDeriv_scalarOnE_eq_euclidPartial_local gm x m₂ hYmem]
  have hscalarOnE_gm : scalarOnE (I := I) x gm =ᶠ[𝓝 (extChartAt I x x)]
      partialDeriv (E := E) m₁ (scalarOnE (I := I) x f) := by
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x htarget
    filter_upwards [isOpen_interior.mem_nhds hint] with z hz
    have hzt : z ∈ (extChartAt I x).target := interior_subset hz
    change partialDeriv (E := E) m₁ (scalarOnE (I := I) x f)
        (extChartAt I x ((extChartAt I x).symm z)) =
      partialDeriv (E := E) m₁ (scalarOnE (I := I) x f) z
    rw [(extChartAt I x).right_inv hzt]
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  rw [hround]
  rw [partialDeriv, partialDeriv]
  rw [Filter.EventuallyEq.fderiv_eq hscalarOnE_gm]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
lemma realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b : Fin (Module.finrank ℝ E)) :
    realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b =ᶠ[𝓝 (extChartAt I x x)]
      (fun y => (1 / 2 : ℝ) *
        (scalarOnE (I := I) x
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b]) y +
          scalarOnE (I := I) x
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a]) y)) := by
  classical
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hx_src
  have htarget_open : IsOpen ((extChartAt I x).target : Set E) :=
    isOpen_extChartAt_target (I := I) x
  filter_upwards [htarget_open.mem_nhds htarget] with y hy_tgt
  have hp : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hy_tgt
  rw [realizedGramDeriv]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent_two_witness
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b y hp]
  rw [scalarOnE_def, scalarOnE_def]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma scalarOnE_contDiffOn_tensorChartComponentRaw
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (scalarOnE (I := I) x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] Jdx))
      (extChartAt I x).target := by
  classical
  set f : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] Jdx with hf_def
  have hpush : ContDiffOn ℝ ∞ (chartPushedRaw I x f)
      (chartTargetEuclid (I := I) (M := M) x) :=
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g₀ 0 2 S x ![] Jdx
  have hcomp : ContDiffOn ℝ ∞ ((chartPushedRaw I x f) ∘ (toEuclidean (E := E)))
      (extChartAt I x).target := by
    refine hpush.comp (toEuclidean (E := E)).contDiff.contDiffOn ?_
    intro z hz
    refine ⟨z, hz, rfl⟩
  refine hcomp.congr (fun z hz => ?_)
  have hzeucl : (toEuclidean (E := E)) z ∈ chartTargetEuclid (I := I) (M := M) x := ⟨z, hz, rfl⟩
  rw [Function.comp_apply,
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) x f hzeucl]
  rw [(toEuclidean (E := E)).symm_apply_apply]
  rw [scalarOnE_def]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma partialDeriv_scalarOnE_tensorChartComponentRaw_differentiableAt
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (m : Fin (Module.finrank ℝ E)) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) m
        (scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] Jdx)))
      (extChartAt I x x) := by
  classical
  set u : E → ℝ := scalarOnE (I := I) x
    (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] Jdx) with hu_def
  have hcd : ContDiffOn ℝ ∞ u (extChartAt I x).target :=
    scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ S x Jdx
  have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x
      ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
  have hcd_int : ContDiffOn ℝ ∞ u (interior (extChartAt I x).target) := hcd.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (interior (extChartAt I x).target) :=
    hcd_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hpd : ContDiffOn ℝ ∞ (partialDeriv (E := E) m u) (interior (extChartAt I x).target) := by
    unfold partialDeriv
    exact hfderiv.clm_apply contDiffOn_const
  exact (hpd.contDiffAt (isOpen_interior.mem_nhds hint)).differentiableAt (by simp)

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
lemma partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m₁ m₂ a b : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m₂
        (partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) =
      (1 / 2 : ℝ) * euclidPartial (E := E) m₂
          (fun y' => euclidPartial (E := E) m₁
            (chartPushedRaw I x
              (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b])) y')
          (toEuclidean (E := E) (extChartAt I x x)) +
        (1 / 2 : ℝ) * euclidPartial (E := E) m₂
          (fun y' => euclidPartial (E := E) m₁
            (chartPushedRaw I x
              (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a])) y')
          (toEuclidean (E := E) (extChartAt I x x)) := by
  classical
  rw [euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE (I := I) g₀ (T - T') x m₁ m₂ a b]
  rw [euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE (I := I) g₀ (T - T') x m₁ m₂ b a]
  set fab : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b]
    with hfab_def
  set fba : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a]
    with hfba_def
  set Pab : E → ℝ := partialDeriv (E := E) m₁ (scalarOnE (I := I) x fab) with hPab_def
  set Pba : E → ℝ := partialDeriv (E := E) m₁ (scalarOnE (I := I) x fba) with hPba_def
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x a b
  have hev1 : partialDeriv (E := E) m₁
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) =ᶠ[𝓝 (extChartAt I x x)]
      (fun y => (1 / 2 : ℝ) * (Pab y + Pba y)) := by
    have hdab : ∀ᶠ y in 𝓝 (extChartAt I x x),
        DifferentiableAt ℝ (scalarOnE (I := I) x fab) y := by
      have hcd : ContDiffOn ℝ ∞ (scalarOnE (I := I) x fab) (extChartAt I x).target :=
        scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ (T - T') x ![a, b]
      have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
        extChartAt_target_subset_interior_of_boundaryless (I := I) x
          ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
      filter_upwards [isOpen_interior.mem_nhds hint] with z hz
      exact ((hcd.mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    have hdba : ∀ᶠ y in 𝓝 (extChartAt I x x),
        DifferentiableAt ℝ (scalarOnE (I := I) x fba) y := by
      have hcd : ContDiffOn ℝ ∞ (scalarOnE (I := I) x fba) (extChartAt I x).target :=
        scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ (T - T') x ![b, a]
      have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
        extChartAt_target_subset_interior_of_boundaryless (I := I) x
          ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
      filter_upwards [isOpen_interior.mem_nhds hint] with z hz
      exact ((hcd.mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    have hpd_ev : partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) =ᶠ[𝓝 (extChartAt I x x)]
        partialDeriv (E := E) m₁
          (fun y => (1 / 2 : ℝ) * (scalarOnE (I := I) x fab y + scalarOnE (I := I) x fba y)) := by
      filter_upwards [hev.eventuallyEq_nhds] with z hz
      unfold partialDeriv
      rw [hz.fderiv_eq]
    filter_upwards [hpd_ev, hdab, hdba] with z hz hdz_ab hdz_ba
    rw [hz]
    rw [partialDeriv_const_mul (1 / 2 : ℝ)
        (fun y => scalarOnE (I := I) x fab y + scalarOnE (I := I) x fba y)
        (hdz_ab.add hdz_ba)]
    rw [partialDeriv_add (scalarOnE (I := I) x fab) (scalarOnE (I := I) x fba) hdz_ab hdz_ba]
  have hfinal : partialDeriv (E := E) m₂
        (partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) =
      partialDeriv (E := E) m₂ (fun y => (1 / 2 : ℝ) * (Pab y + Pba y)) (extChartAt I x x) := by
    change fderiv ℝ
        (partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) ((chartModelBasis E) m₂) =
      fderiv ℝ (fun y => (1 / 2 : ℝ) * (Pab y + Pba y)) (extChartAt I x x) ((chartModelBasis E) m₂)
    rw [hev1.fderiv_eq]
  rw [hfinal]
  have hPab_diff : DifferentiableAt ℝ Pab (extChartAt I x x) :=
    partialDeriv_scalarOnE_tensorChartComponentRaw_differentiableAt (I := I) (M := M) g₀
      (T - T') x m₁ ![a, b]
  have hPba_diff : DifferentiableAt ℝ Pba (extChartAt I x x) :=
    partialDeriv_scalarOnE_tensorChartComponentRaw_differentiableAt (I := I) (M := M) g₀
      (T - T') x m₁ ![b, a]
  rw [partialDeriv_const_mul (1 / 2 : ℝ) (fun y => Pab y + Pba y)
      (hPab_diff.add hPba_diff)]
  rw [partialDeriv_add Pab Pba hPab_diff hPba_diff]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) a
        (fun y' => euclidPartial (E := E) b
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d]))
          y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      euclidPartial (E := E) b
        (fun y' => euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d]))
          y')
        (toEuclidean (E := E) (extChartAt I x x)) := by
  classical
  set u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d])
    with hu_def
  set Y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (E := E) (extChartAt I x x) with hY_def
  have hmem : Y ∈ chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) x
  have hcd : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) x) :=
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g₀ 0 2 S x ![] ![c, d]
  have hcdAt : ContDiffAt ℝ ∞ u Y :=
    hcd.contDiffAt (hopen.mem_nhds hmem)
  have hsymm2 : IsSymmSndFDerivAt ℝ u Y := by
    refine ContDiffAt.isSymmSndFDerivAt hcdAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hg_diff : DifferentiableAt ℝ (fderiv ℝ u) Y := by
    have hcd_int : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) x) := hcd
    have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (chartTargetEuclid (I := I) (M := M) x) :=
      hcd_int.fderiv_of_isOpen hopen (by rw [ENat.coe_top_add_one])
    exact (hfderiv.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
  have hkey : ∀ r t : Fin (Module.finrank ℝ E),
      euclidPartial (E := E) r
          (fun y' => euclidPartial (E := E) t u y') Y =
        (fderiv ℝ (fderiv ℝ u) Y (EuclideanSpace.single r 1))
          (EuclideanSpace.single t 1) := by
    intro r t
    rw [euclidPartial_def]
    set L : (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single t 1) with hL
    have hcomp_eq : (fun z => euclidPartial (E := E) t u z) =
        L ∘ (fderiv ℝ u) := by
      funext z; rw [euclidPartial_def]; rfl
    rw [hcomp_eq, fderiv_comp Y L.differentiableAt hg_diff, L.fderiv]
    rfl
  rw [hkey a b, hkey b a]
  exact (hsymm2 _ _).symm

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
lemma partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m a b : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
        (extChartAt I x x) =
      (1 / 2 : ℝ) * euclidPartial (E := E) m
          (chartPushedRaw I x
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b]))
          (toEuclidean (E := E) (extChartAt I x x)) +
        (1 / 2 : ℝ) * euclidPartial (E := E) m
          (chartPushedRaw I x
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a]))
          (toEuclidean (E := E) (extChartAt I x x)) := by
  classical
  set fab : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b]
    with hfab_def
  set fba : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a]
    with hfba_def
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x a b
  have hdab : DifferentiableAt ℝ (scalarOnE (I := I) x fab) (extChartAt I x x) := by
    have hcd : ContDiffOn ℝ ∞ (scalarOnE (I := I) x fab) (extChartAt I x).target :=
      scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ (T - T') x ![a, b]
    have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x
        ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
    exact ((hcd.mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hint)).differentiableAt (by simp)
  have hdba : DifferentiableAt ℝ (scalarOnE (I := I) x fba) (extChartAt I x x) := by
    have hcd : ContDiffOn ℝ ∞ (scalarOnE (I := I) x fba) (extChartAt I x).target :=
      scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ (T - T') x ![b, a]
    have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x
        ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
    exact ((hcd.mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hint)).differentiableAt (by simp)
  have hpd_eq : partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
        (extChartAt I x x) =
      partialDeriv (E := E) m
        (fun y => (1 / 2 : ℝ) * (scalarOnE (I := I) x fab y + scalarOnE (I := I) x fba y))
        (extChartAt I x x) := by
    unfold partialDeriv
    rw [hev.fderiv_eq]
  rw [hpd_eq]
  rw [partialDeriv_const_mul (1 / 2 : ℝ)
      (fun y => scalarOnE (I := I) x fab y + scalarOnE (I := I) x fba y)
      (hdab.add hdba)]
  rw [partialDeriv_add (scalarOnE (I := I) x fab) (scalarOnE (I := I) x fba) hdab hdba]
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  have hYmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hPab : partialDeriv (E := E) m (scalarOnE (I := I) x fab) (extChartAt I x x) =
      euclidPartial (E := E) m (chartPushedRaw I x fab)
        (toEuclidean (E := E) (extChartAt I x x)) := by
    have h := partialDeriv_scalarOnE_eq_euclidPartial_local fab x m hYmem
    rw [hround] at h
    exact h
  have hPba : partialDeriv (E := E) m (scalarOnE (I := I) x fba) (extChartAt I x x) =
      euclidPartial (E := E) m (chartPushedRaw I x fba)
        (toEuclidean (E := E) (extChartAt I x x)) := by
    have h := partialDeriv_scalarOnE_eq_euclidPartial_local fba x m hYmem
    rw [hround] at h
    exact h
  rw [hPab, hPba]
  ring

private lemma sum_pi_fin_succ' {n : ℕ} {β : Type*} [AddCommMonoid β]
    {N : ℕ} (g : (Fin (N + 1) → Fin n) → β) :
    (∑ p : Fin (N + 1) → Fin n, g p)
      = ∑ a : Fin n, ∑ q : Fin N → Fin n, g (Fin.cons a q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin n)).sum_comp g]
  rw [Fintype.sum_prod_type]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covDerivLowerOrderTerm02_center_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (m p q : Fin (Module.finrank ℝ E)) :
    covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S x m ![] ![p, q]
        (toEuclidean (E := E) (extChartAt I x x)) =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m p r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![r, q] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m q r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![p, r] x) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hmemsrc
  rw [covDerivLowerOrderTerm_def]
  rw [hround]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    ⟨⟨![]⟩, fun f => by funext j; exact absurd j.2 (by simp)⟩
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![] : Fin 0 → Fin (Module.finrank ℝ E))]
  · simp only [covDerivLowerOrderCoeff_def]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, if_true, mul_one, zero_sub]
    have hout : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        (∑ l : Fin 2, outputSlotCoeff (I := I) (M := M) g₀ 2 x m l ![p, q] J'
            (toEuclidean (E := E) (extChartAt I x x))) =
          chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0) := by
      intro J'
      rw [Fin.sum_univ_two]
      rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 0 ![p, q] J' hcenter,
        outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 1 ![p, q] J' hcenter]
      rw [hround]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 0) p,
        chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 1) q]
      have herase0 : (Finset.univ.erase (0 : Fin 2)) = {(1 : Fin 2)} := by decide
      have herase1 : (Finset.univ.erase (1 : Fin 2)) = {(0 : Fin 2)} := by decide
      rw [herase0, herase1]
      simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_congr rfl (fun J' _ => by rw [hout J'] :
      ∀ J' ∈ Finset.univ,
        (-∑ x_2, outputSlotCoeff (I := I) (M := M) g₀ 2 x m x_2 ![p, q] J'
            (toEuclidean (E := E) (extChartAt I x x))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x)]
    rw [← (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.sum_comp
      (fun J' : Fin 2 → Fin (Module.finrank ℝ E) =>
        (-(chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x)]
    rw [Fintype.sum_prod_type]
    simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsplit : ∀ a : Fin (Module.finrank ℝ E),
        (∑ b : Fin (Module.finrank ℝ E),
          -((chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                  (if q = b then (1 : ℝ) else 0)) +
              chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                (if p = a then (1 : ℝ) else 0)) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) =
          (-(chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, q] x)) +
          (if p = a then (1 : ℝ) else 0) *
            (-∑ b : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) := by
      intro a
      rw [show (∑ b : Fin (Module.finrank ℝ E),
            -((chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                    (if q = b then (1 : ℝ) else 0)) +
                chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                  (if p = a then (1 : ℝ) else 0)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) =
          (∑ b : Fin (Module.finrank ℝ E),
            -(chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                (if q = b then (1 : ℝ) else 0)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) +
          (∑ b : Fin (Module.finrank ℝ E),
            (if p = a then (1 : ℝ) else 0) *
              -(chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_); ring]
      congr 1
      · rw [Finset.sum_eq_single q]
        · rw [if_pos rfl]; ring
        · intro b _ hbq; rw [if_neg (fun h => hbq h.symm)]; ring
        · intro h; exact absurd (Finset.mem_univ q) h
      · rw [← Finset.mul_sum, Finset.sum_neg_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [chartChristoffel_symm (I := I) g₀ x p m a (extChartAt I x x)]
    · rw [Finset.sum_eq_single p]
      · rw [if_pos rfl, one_mul]
        congr 1
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [chartChristoffel_symm (I := I) g₀ x q m b (extChartAt I x x)]
      · intro a _ hap; rw [if_neg (fun h => hap h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ p) h
  · intro b _ hb
    exact absurd (Subsingleton.elim b ![]) hb
  · intro h; exact absurd (Finset.mem_univ _) h

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covDerivLowerOrderTerm03_center_hout
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m b c d : Fin (Module.finrank ℝ E))
    (J' : Fin 3 → Fin (Module.finrank ℝ E)) :
    (∑ l : Fin 3, outputSlotCoeff (I := I) (M := M) g₀ 3 x m l ![b, c, d] J'
        (toEuclidean (E := E) (extChartAt I x x))) =
      chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
          ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
      chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
          ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
      chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
          ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hmemsrc
  rw [Fin.sum_univ_three]
  rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 0 ![b, c, d] J' hcenter,
    outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 1 ![b, c, d] J' hcenter,
    outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 2 ![b, c, d] J' hcenter]
  rw [hround]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 0) b,
    chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 1) c,
    chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 2) d]
  have herase0 : (Finset.univ.erase (0 : Fin 3)) = {(1 : Fin 3), (2 : Fin 3)} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 3)) = {(0 : Fin 3), (2 : Fin 3)} := by decide
  have herase2 : (Finset.univ.erase (2 : Fin 3)) = {(0 : Fin 3), (1 : Fin 3)} := by decide
  rw [herase0, herase1, herase2]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [chartChristoffel_symm (I := I) g₀ x b m (J' 0) (extChartAt I x x),
    chartChristoffel_symm (I := I) g₀ x c m (J' 1) (extChartAt I x x),
    chartChristoffel_symm (I := I) g₀ x d m (J' 2) (extChartAt I x x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma sum_fin3_collapse_gen
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ) :
    (∑ J' : Fin 3 → Fin (Module.finrank ℝ E), F (J' 0) (J' 1) (J' 2)) =
      ∑ a0 : Fin (Module.finrank ℝ E), ∑ a1 : Fin (Module.finrank ℝ E),
        ∑ a2 : Fin (Module.finrank ℝ E), F a0 a1 a2 := by
  classical
  rw [sum_pi_fin_succ']
  refine Finset.sum_congr rfl (fun a0 _ => ?_)
  rw [sum_pi_fin_succ']
  refine Finset.sum_congr rfl (fun a1 _ => ?_)
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (Module.finrank ℝ E))) _ _ (fun q => ?_)
  simp only [Equiv.funUnique_apply, Fin.cons_zero,
    show ((1 : Fin 3) = (Fin.succ 0)) from rfl,
    show ((2 : Fin 3) = (Fin.succ 1)) from rfl,
    show ((1 : Fin 2) = (Fin.succ 0)) from rfl, Fin.cons_succ]
  rw [show (default : Fin 1) = (0 : Fin 1) from rfl]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covDerivLowerOrderTerm03_center_eq
    (g₀ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 3) (x : M)
    (m b c d : Fin (Module.finrank ℝ E)) :
    covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3 W x m ![] ![b, c, d]
        (toEuclidean (E := E) (extChartAt I x x)) =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m b r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![r, c, d] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m c r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![b, r, d] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m d r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![b, c, r] x) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [covDerivLowerOrderTerm_def]
  rw [hround]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    ⟨⟨![]⟩, fun f => by funext j; exact absurd j.2 (by simp)⟩
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![] : Fin 0 → Fin (Module.finrank ℝ E))]
  · simp only [covDerivLowerOrderCoeff_def]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, if_true, mul_one, zero_sub]
    rw [Finset.sum_congr rfl (fun J' _ => by
        rw [covDerivLowerOrderTerm03_center_hout (I := I) (M := M) g₀ x m b c d J'] :
      ∀ J' ∈ Finset.univ,
        (-∑ x_2, outputSlotCoeff (I := I) (M := M) g₀ 3 x m x_2 ![b, c, d] J'
            (toEuclidean (E := E) (extChartAt I x x))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
              ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x)]
    rw [Finset.sum_congr rfl (fun J' _ =>
      show (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
              ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0))) +
        (-(chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0))) +
        (-(chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))
        from by
          rw [show (![J' 0, J' 1, J' 2] : Fin 3 → Fin (Module.finrank ℝ E)) = J' from by
            funext j; fin_cases j <;> rfl]
          ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m b a0 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if c = a1 then (1 : ℝ) else 0) * (if d = a2 then (1 : ℝ) else 0))),
      sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m c a1 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if b = a0 then (1 : ℝ) else 0) * (if d = a2 then (1 : ℝ) else 0))),
      sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m d a2 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if b = a0 then (1 : ℝ) else 0) * (if c = a1 then (1 : ℝ) else 0)))]
    congr 1
    · congr 1
      · rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun a0 _ => ?_)
        rw [Finset.sum_eq_single c]
        · rw [Finset.sum_eq_single d]
          · rw [if_pos rfl, if_pos rfl]; ring
          · intro a2 _ ha2; rw [if_neg (show ¬ d = a2 from fun h => ha2 h.symm), mul_zero]; ring
          · intro h; exact absurd (Finset.mem_univ d) h
        · intro a1 _ ha1
          refine Finset.sum_eq_zero (fun a2 _ => ?_)
          rw [if_neg (show ¬ c = a1 from fun h => ha1 h.symm), zero_mul]; ring
        · intro h; exact absurd (Finset.mem_univ c) h
      · rw [← Finset.sum_neg_distrib]
        rw [Finset.sum_eq_single b]
        · refine Finset.sum_congr rfl (fun a1 _ => ?_)
          rw [Finset.sum_eq_single d]
          · rw [if_pos rfl, if_pos rfl]; ring
          · intro a2 _ ha2; rw [if_neg (show ¬ d = a2 from fun h => ha2 h.symm), mul_zero]; ring
          · intro h; exact absurd (Finset.mem_univ d) h
        · intro a0 _ ha0
          refine Finset.sum_eq_zero (fun a1 _ => ?_)
          refine Finset.sum_eq_zero (fun a2 _ => ?_)
          rw [if_neg (show ¬ b = a0 from fun h => ha0 h.symm), zero_mul]; ring
        · intro h; exact absurd (Finset.mem_univ b) h
    · rw [← Finset.sum_neg_distrib]
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single c]
        · refine Finset.sum_congr rfl (fun a2 _ => ?_)
          rw [if_pos rfl, if_pos rfl]; ring
        · intro a1 _ ha1
          refine Finset.sum_eq_zero (fun a2 _ => ?_)
          rw [if_neg (show ¬ c = a1 from fun h => ha1 h.symm), mul_zero]; ring
        · intro h; exact absurd (Finset.mem_univ c) h
      · intro a0 _ ha0
        refine Finset.sum_eq_zero (fun a1 _ => ?_)
        refine Finset.sum_eq_zero (fun a2 _ => ?_)
        rw [if_neg (show ¬ b = a0 from fun h => ha0 h.symm), zero_mul]; ring
      · intro h; exact absurd (Finset.mem_univ b) h
  · intro b' _ hb'
    exact absurd (Subsingleton.elim b' ![]) hb'
  · intro h; exact absurd (Finset.mem_univ _) h

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_covDerivLowerOrderTerm02_center_eq_sum
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) a
        (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d] y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      ∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) × (Fin 2 → Fin (Module.finrank ℝ E)),
        (secondCovDerivLO_valueCoeff (I := I) (M := M) g₀ 0 2 x b a ![] p.1 ![c, d] p.2
              (toEuclidean (E := E) (extChartAt I x x)) *
            rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h p.1 p.2
              (toEuclidean (E := E) (extChartAt I x x)) +
          secondCovDerivLO_gradCoeff (I := I) (M := M) g₀ 0 2 x b ![] p.1 ![c, d] p.2
              (toEuclidean (E := E) (extChartAt I x x)) *
            euclidPartial (E := E) a
              (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h p.1 p.2)
              (toEuclidean (E := E) (extChartAt I x x))) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have heq : Set.EqOn
      (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d] y')
      (fun y' => ∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E)),
          lowerOrderSummand (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p y')
      (chartTargetEuclid (I := I) (M := M) x) := by
    intro y _
    exact covDerivLowerOrderTerm_eq_sum_lowerOrderSummand
      (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] y
  rw [euclidPartial_def,
    Filter.EventuallyEq.fderiv_eq (heq.eventuallyEq_of_mem (hopen.mem_nhds hcenter)),
    ← euclidPartial_def]
  have hsummand_diff : ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
        (Fin 2 → Fin (Module.finrank ℝ E)),
      DifferentiableAt ℝ (lowerOrderSummand (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p)
        (toEuclidean (E := E) (extChartAt I x x)) := by
    intro p
    exact ((lowerOrderSummand_contDiffOn (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p).differentiableOn
      (by norm_cast)).differentiableAt (hopen.mem_nhds hcenter)
  rw [euclidPartial_finsetSum a Finset.univ (fun p _ => hsummand_diff p)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact euclidPartial_lowerOrderSummand_apply (I := I) (M := M) g₀ 0 2 x h b a ![] ![c, d] p hcenter

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
