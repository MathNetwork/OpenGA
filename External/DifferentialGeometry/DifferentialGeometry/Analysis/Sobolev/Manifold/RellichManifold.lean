import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.External.DeGiorgi.SobolevSpace
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import Mathlib.Analysis.InnerProductSpace.EuclideanDist


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [IsManifold I ∞ M] in
lemma chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α u y =
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y := by
  classical
  unfold chartPushed
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) hy]

omit [IsManifold I ∞ M] in
lemma chartPushedRaw_pou_mul_eq_zero_off_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y = 0 :=
  chartPushedRaw_apply_of_notMem (I := I) (M := M) α
    (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) hy

omit [IsManifold I ∞ M] in
lemma chartPushed_eq_chartPushedRaw_pou_ae
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α u
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) := by
  filter_upwards [self_mem_ae_restrict
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)] with y hy
  exact chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (I := I) (M := M) ρ α u hy

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

omit [I.Boundaryless] in
private lemma extChartAt_image_tsupport_pou_compact
    (α : M) :
    IsCompact ((extChartAt I α) ''
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        : M → ℝ))) ∧
    (extChartAt I α) ''
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        : M → ℝ)) ⊆
      (extChartAt I α).target := by
  have hsubord :
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).IsSubordinate
        (fun α : M => (chartAt H α).source) :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate (I := I) (M := M)
  have hsupp_sub : tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source := hsubord α
  exact image_extChartAt_tsupport_compact_subset_target
    (I := I) (M := M)
    (u := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (α := α) hsupp_sub

omit [I.Boundaryless] in
private lemma toEuclidean_image_tsupport_pou_compact_subset_target
    (α : M) :
    IsCompact (toEuclidean ''
        ((extChartAt I α) ''
          (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)))) ∧
      toEuclidean ''
        ((extChartAt I α) ''
          (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ))) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
  obtain ⟨hcomp, hsub⟩ :=
    extChartAt_image_tsupport_pou_compact (I := I) (M := M) α
  refine ⟨hcomp.image (toEuclidean (E := E)).continuous, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z, hsub hz, rfl⟩

private noncomputable def chartCompact (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  toEuclidean ''
    ((extChartAt I α) ''
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

omit [I.Boundaryless] in
private lemma chartCompact_isCompact (α : M) :
    IsCompact (chartCompact (I := I) (M := M) α) :=
  (toEuclidean_image_tsupport_pou_compact_subset_target (I := I) (M := M) α).1

omit [I.Boundaryless] in
private lemma chartCompact_subset_chartTargetEuclid (α : M) :
    chartCompact (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  (toEuclidean_image_tsupport_pou_compact_subset_target (I := I) (M := M) α).2

private noncomputable def chartThickeningRadius (α : M) : ℝ :=
  ((chartCompact_isCompact (I := I) (M := M) α).exists_thickening_subset_open
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartCompact_subset_chartTargetEuclid (I := I) (M := M) α)).choose

private lemma chartThickeningRadius_pos (α : M) :
    0 < chartThickeningRadius (I := I) (M := M) α :=
  ((chartCompact_isCompact (I := I) (M := M) α).exists_thickening_subset_open
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartCompact_subset_chartTargetEuclid (I := I) (M := M) α)).choose_spec.1

private lemma chartThickeningRadius_subset (α : M) :
    Metric.thickening (chartThickeningRadius (I := I) (M := M) α)
        (chartCompact (I := I) (M := M) α) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  ((chartCompact_isCompact (I := I) (M := M) α).exists_thickening_subset_open
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartCompact_subset_chartTargetEuclid (I := I) (M := M) α)).choose_spec.2

private noncomputable def chartNbhd (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  Metric.thickening (chartThickeningRadius (I := I) (M := M) α)
    (chartCompact (I := I) (M := M) α)

private lemma chartNbhd_isOpen (α : M) :
    IsOpen (chartNbhd (I := I) (M := M) α) :=
  Metric.isOpen_thickening

private lemma chartNbhd_isBounded (α : M) :
    Bornology.IsBounded (chartNbhd (I := I) (M := M) α) :=
  (chartCompact_isCompact (I := I) (M := M) α).isBounded.thickening

private lemma chartNbhd_subset_chartTargetEuclid (α : M) :
    chartNbhd (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  chartThickeningRadius_subset (I := I) (M := M) α

private lemma chartCompact_subset_chartNbhd (α : M) :
    chartCompact (I := I) (M := M) α ⊆ chartNbhd (I := I) (M := M) α :=
  Metric.self_subset_thickening
    (chartThickeningRadius_pos (I := I) (M := M) α)
    (chartCompact (I := I) (M := M) α)

omit [CompactSpace M] [I.Boundaryless] in
lemma chartPushedRaw_pou_mul_eq_zero_off_chartCompact
    (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartCompact (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · have hsmul :
        tsupport (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
          tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) =
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x • u x) := by
        funext x; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
    have h_supp_sub :
        tsupport (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
          (chartAt H α).source := by
      have hsubord :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).IsSubordinate
            (fun α : M => (chartAt H α).source) :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate (I := I) (M := M)
      exact hsmul.trans (hsubord α)
    apply chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M)
      (u := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x)
      (α := α) hy_target
    intro hcontra
    apply hy
    obtain ⟨z, hz_chart_image, hzy⟩ := hcontra
    obtain ⟨x, hx_supp, hxz⟩ := hz_chart_image
    refine ⟨z, ⟨x, ?_, hxz⟩, hzy⟩
    have h_t_sub : tsupport (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) y * u y) ⊆ tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          : M → ℝ) := by
      have h_eq : (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y) =
          (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) y • u y) := by
        funext y; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun y : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
    exact h_t_sub hx_supp
  · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy_target

lemma chartPushedRaw_pou_mul_tsupport_subset_chartNbhd
    (α : M) (u : M → ℝ) :
    tsupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      chartNbhd (I := I) (M := M) α := by
  have h_supp_sub_compact :
      Function.support (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
        chartCompact (I := I) (M := M) α := by
    intro y hy
    by_contra hcontra
    apply hy
    exact chartPushedRaw_pou_mul_eq_zero_off_chartCompact (I := I) (M := M) α u hcontra
  have h_compact_closed : IsClosed (chartCompact (I := I) (M := M) α) :=
    (chartCompact_isCompact (I := I) (M := M) α).isClosed
  have h_tsupp_sub_compact :
      tsupport (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
        chartCompact (I := I) (M := M) α := by
    rw [tsupport]
    exact h_compact_closed.closure_subset_iff.mpr h_supp_sub_compact
  exact h_tsupp_sub_compact.trans (chartCompact_subset_chartNbhd (I := I) (M := M) α)

omit [I.Boundaryless] in
lemma chartPushedRaw_pou_mul_hasCompactSupport
    (α : M) (u : M → ℝ) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) := by
  have h_tsupp_sub :
      tsupport (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
        chartCompact (I := I) (M := M) α := by
    intro y hy
    by_contra hcontra
    have h_supp_sub_compact :
        Function.support (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
          chartCompact (I := I) (M := M) α := by
      intro z hz
      by_contra hcontraZ
      apply hz
      exact chartPushedRaw_pou_mul_eq_zero_off_chartCompact (I := I) (M := M) α u hcontraZ
    have h_compact_closed : IsClosed (chartCompact (I := I) (M := M) α) :=
      (chartCompact_isCompact (I := I) (M := M) α).isClosed
    have htsupp_sub :
        tsupport (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
          chartCompact (I := I) (M := M) α := by
      rw [tsupport]
      exact h_compact_closed.closure_subset_iff.mpr h_supp_sub_compact
    exact hcontra (htsupp_sub hy)
  exact (chartCompact_isCompact (I := I) (M := M) α).of_isClosed_subset
    isClosed_closure h_tsupp_sub

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] in

omit [IsManifold I ∞ M] in
lemma chartPushedRaw_sub
    (α : M) (u v : M → ℝ) :
    chartPushedRaw (I := I) (M := M) α (fun x => u x - v x) =
      fun y => chartPushedRaw (I := I) (M := M) α u y -
        chartPushedRaw (I := I) (M := M) α v y := by
  classical
  funext y
  unfold chartPushedRaw
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · simp [hy]
  · simp [hy]

omit [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] in

omit [IsManifold I ∞ M] [T2Space M] in
lemma chartPushedRaw_pullbackToM_apply
    (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartPushedRaw (I := I) (M := M) α
        (pullbackToM (M := M) I α w) y =
      (chartTargetEuclid (I := I) (M := M) α).indicator w y := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rw [Set.indicator_of_mem hy]
    rw [pullbackToM_apply_of_mem (M := M) (I := I) α w
      (symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy)]
    obtain ⟨z, hz_target, hzy⟩ := hy
    have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    have hy_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [hy_symm, hz_eq, ← hzy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    rw [Set.indicator_of_notMem hy]

omit [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] in
omit [IsManifold I ∞ M] [T2Space M] in
lemma chartPushedRaw_pullbackToM_eq_indicator
    (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    chartPushedRaw (I := I) (M := M) α (pullbackToM (M := M) I α w) =
      (chartTargetEuclid (I := I) (M := M) α).indicator w := by
  funext y
  exact chartPushedRaw_pullbackToM_apply (I := I) (M := M) α w y

omit [I.Boundaryless] in
lemma pullbackToM_tsupport_subset_of_supp_in_chartCompact
    (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (hw_supp : tsupport w ⊆ chartCompact (I := I) (M := M) α) :
    tsupport (pullbackToM (M := M) I α w) ⊆ (chartAt H α).source := by
  classical
  set P : Set M :=
    (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
      (extChartAt I α).symm ((toEuclidean : E ≃L[ℝ] _).symm y)) ''
        chartCompact (I := I) (M := M) α
  have hP_compact : IsCompact P := by
    apply (chartCompact_isCompact (I := I) (M := M) α).image_of_continuousOn
    have hcompact_sub_target := chartCompact_subset_chartTargetEuclid (I := I) (M := M) α
    exact (continuousOn_symm_toEuclideanSymm (I := I) (M := M) α).mono hcompact_sub_target
  have hP_subset_source : P ⊆ (chartAt H α).source := by
    rintro x ⟨y, hy_compact, rfl⟩
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α :=
      chartCompact_subset_chartTargetEuclid (I := I) (M := M) α hy_compact
    exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy_target
  have h_supp_sub : Function.support (pullbackToM (M := M) I α w) ⊆ P := by
    intro x hx
    by_cases hxsource : x ∈ (chartAt H α).source
    · have hpb : pullbackToM (M := M) I α w x =
          w (toEuclidean (extChartAt I α x)) :=
        pullbackToM_apply_of_mem (M := M) (I := I) α w hxsource
      have hwy_ne : w (toEuclidean (extChartAt I α x)) ≠ 0 := by
        intro h
        apply hx
        rw [hpb, h]
      have hy_chartCompact :
          (toEuclidean : E ≃L[ℝ] _) (extChartAt I α x) ∈
            chartCompact (I := I) (M := M) α := by
        apply hw_supp
        exact subset_tsupport _ (Function.mem_support.mpr hwy_ne)
      refine ⟨(toEuclidean : E ≃L[ℝ] _) (extChartAt I α x), hy_chartCompact, ?_⟩
      change (extChartAt I α).symm
        ((toEuclidean : E ≃L[ℝ] _).symm
          ((toEuclidean : E ≃L[ℝ] _) (extChartAt I α x))) = x
      have h_t_inv : (toEuclidean : E ≃L[ℝ] _).symm
          ((toEuclidean : E ≃L[ℝ] _) (extChartAt I α x)) = extChartAt I α x := by
        simp
      rw [h_t_inv]
      have hsource :
          x ∈ (extChartAt I α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hxsource
      exact (extChartAt I α).left_inv hsource
    · exfalso
      apply hx
      exact pullbackToM_apply_of_notMem (M := M) (I := I) α w hxsource
  have h_P_closed : IsClosed P := hP_compact.isClosed
  have h_tsupp_sub_P : tsupport (pullbackToM (M := M) I α w) ⊆ P := by
    rw [tsupport]
    exact h_P_closed.closure_subset_iff.mpr h_supp_sub
  exact h_tsupp_sub_P.trans hP_subset_source

omit [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] in
lemma pullbackToM_eq_zero_off_chart_source
    (α : M) (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    pullbackToM (M := M) I α w x = 0 :=
  pullbackToM_apply_of_notMem (M := M) (I := I) α w hx

omit [CompactSpace M] in
lemma memW1p_chartPushedRaw_pou_mul_of_memWkpChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 p u)
    (α : M) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_ae := chartPushed_eq_chartPushedRaw_pou_ae
    (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
  have h_chart_pushed : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := hu α
  have h_chart_pushed_w1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp
      h_chart_pushed
  have hopen := chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (d := Module.finrank ℝ E) (p := p) hopen h_ae).mp h_chart_pushed_w1p

lemma memW1p_chartPushedRaw_pou_mul_chartNbhd
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 p u)
    (α : M) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartNbhd (I := I) (M := M) α) := by
  classical
  have h_target := memW1p_chartPushedRaw_pou_mul_of_memWkpChart
    (I := I) (M := M) g hu α
  set hwT : DeGiorgi.MemW1pWitness (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) :=
    DeGiorgi.MemW1p.someWitness h_target with hwT_def
  have hwN : DeGiorgi.MemW1pWitness (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartNbhd (I := I) (M := M) α) :=
    hwT.restrict (chartNbhd_isOpen (I := I) (M := M) α)
      (chartNbhd_subset_chartTargetEuclid (I := I) (M := M) α)
  exact hwN.memW1p

lemma memW01p_chartPushedRaw_pou_mul_chartNbhd
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u)
    (α : M) :
    DeGiorgi.MemW01p (d := Module.finrank ℝ E) (ENNReal.ofReal p)
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartNbhd (I := I) (M := M) α) := by
  classical
  have h_w1p := memW1p_chartPushedRaw_pou_mul_chartNbhd (I := I) (M := M) g hu α
  have h_supp := chartPushedRaw_pou_mul_tsupport_subset_chartNbhd (I := I) (M := M) α u
  have h_compact := chartPushedRaw_pou_mul_hasCompactSupport (I := I) (M := M) α u
  exact DeGiorgi.memW01p_of_memW1p_of_tsupport_subset
    (chartNbhd_isOpen (I := I) (M := M) α) hp_one h_w1p h_compact h_supp

omit [CompactSpace M] [I.Boundaryless] in
lemma eLpNorm_chartPushedRaw_pou_mul_eq_chartPushed
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    (u : M → ℝ) (α : M) :
    eLpNorm (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  let _ := g
  refine eLpNorm_congr_ae ?_
  exact (chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u).symm

lemma eLpNorm_chartPushedRaw_pou_mul_chartNbhd_le
    {p : ℝ≥0∞} (u : M → ℝ) (α : M) :
    eLpNorm (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNbhd (I := I) (M := M) α)) ≤
      eLpNorm (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  refine eLpNorm_mono_measure _ ?_
  exact MeasureTheory.Measure.restrict_mono_set _
    (chartNbhd_subset_chartTargetEuclid (I := I) (M := M) α)

lemma rellich_witness_weakGrad_isWeakPartial
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    let h_mem := memW01p_chartPushedRaw_pou_mul_chartNbhd
      (I := I) (M := M) g hp_one hu α
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (fun x => (Classical.choose h_mem.2).weakGrad x i)
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartNbhd (I := I) (M := M) α) := by
  intro h_mem
  exact (Classical.choose h_mem.2).isWeakGrad i

lemma rellich_witness_weakGrad_memLp
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    let h_mem := memW01p_chartPushedRaw_pou_mul_chartNbhd
      (I := I) (M := M) g hp_one hu α
    MemLp (fun x => (Classical.choose h_mem.2).weakGrad x i) (ENNReal.ofReal p)
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartNbhd (I := I) (M := M) α)) := by
  intro h_mem
  exact (Classical.choose h_mem.2).weakGrad_component_memLp i

lemma rellich_witness_weakGrad_ae_eq_chosenWeakPartial'
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    let h_mem := memW01p_chartPushedRaw_pou_mul_chartNbhd
      (I := I) (M := M) g hp_one hu α
    (fun x => (Classical.choose h_mem.2).weakGrad x i) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNbhd (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro h_mem
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
      ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hChart_w1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) (ENNReal.ofReal p)
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h := hu α
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp h
  have hChart_w1p_chosenWeakPartial :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hChart_w1p i
  have hChart_w1p_chosenWeakPartial_chartNbhd :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartNbhd (I := I) (M := M) α) :=
    DeGiorgi.HasWeakPartialDeriv.restrict (chartNbhd_isOpen (I := I) (M := M) α)
      (chartNbhd_subset_chartTargetEuclid (I := I) (M := M) α)
      hChart_w1p_chosenWeakPartial
  have h_ae_chartNbhd :
      chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
        =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNbhd (I := I) (M := M) α)]
        chartPushedRaw (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) := by
    have h_full := chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
    have h_restrict : (volume :
        Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartNbhd (I := I) (M := M) α) ≤
      (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartTargetEuclid (I := I) (M := M) α) :=
      MeasureTheory.Measure.restrict_mono_set _
        (chartNbhd_subset_chartTargetEuclid (I := I) (M := M) α)
    exact h_full.filter_mono (MeasureTheory.ae_mono h_restrict)
  have hChart_w1p_chosenWeakPartial_raw :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α))
        (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartNbhd (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae
      (chartNbhd_isOpen (I := I) (M := M) α) i h_ae_chartNbhd
      hChart_w1p_chosenWeakPartial_chartNbhd
  have hWit_isWeak := (Classical.choose h_mem.2).isWeakGrad i
  have hWit_loc :=
    ((Classical.choose h_mem.2).weakGrad_component_memLp i).locallyIntegrable hp_le
  have hChosen_memLp :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hChart_w1p i
  have hChosen_memLp_chartNbhd :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNbhd (I := I) (M := M) α)) :=
    hChosen_memLp.mono_measure
      (MeasureTheory.Measure.restrict_mono_set _
        (chartNbhd_subset_chartTargetEuclid (I := I) (M := M) α))
  have hChosen_loc := hChosen_memLp_chartNbhd.locallyIntegrable hp_le
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq
    (chartNbhd_isOpen (I := I) (M := M) α) hWit_isWeak
    hChart_w1p_chosenWeakPartial_raw hWit_loc hChosen_loc

omit [CompactSpace M] in
lemma eLpNorm_chartPushed_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    (u : M → ℝ) (α : M) :
    eLpNorm (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  have hbound1 :
      eLpNorm (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) p
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := by
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    rw [Finset.sum_range_succ]
    refine le_trans ?_ le_self_add
    rw [Finset.sum_range_one]
    have hUniq : ∀ α : Fin 0 → Fin (Module.finrank ℝ E), α = (fun i : Fin 0 => i.elim0) :=
      fun α => by funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique
      (f := fun α' : Fin 0 → Fin (Module.finrank ℝ E) =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) p 0 α'
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)) p
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)))]
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  exact hbound1.trans (ENNReal.le_tsum α)

lemma eLpNorm_rellich_witness_weakGrad_le_wkpNormChart
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u)
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    let h_mem := memW01p_chartPushedRaw_pou_mul_chartNbhd
      (I := I) (M := M) g hp_one hu α
    eLpNorm (fun x => (Classical.choose h_mem.2).weakGrad x i) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNbhd (I := I) (M := M) α)) ≤
      wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u := by
  classical
  intro h_mem
  have h_ae := rellich_witness_weakGrad_ae_eq_chosenWeakPartial'
    (I := I) (M := M) g hp_one hu α i
  rw [eLpNorm_congr_ae h_ae]
  have h_subset_le :
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartNbhd (I := I) (M := M) α)) ≤
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
    eLpNorm_mono_measure _
      (MeasureTheory.Measure.restrict_mono_set _
        (chartNbhd_subset_chartTargetEuclid (I := I) (M := M) α))
  refine h_subset_le.trans ?_
  have h_in_wkpNorm :
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := by
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    refine le_trans ?_ le_add_self
    set f : (Fin 1 → Fin (Module.finrank ℝ E)) → ℝ≥0∞ := fun α' =>
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) (ENNReal.ofReal p) 1 α'
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) with hf_def
    set α_i : Fin 1 → Fin (Module.finrank ℝ E) := fun _ => i with hα_i_def
    have h_iter_eq :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) (ENNReal.ofReal p) 1 α_i
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := by
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
    have hf_α_i :
        f α_i =
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
      change eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) (ENNReal.ofReal p) 1 α_i
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) = _
      rw [h_iter_eq]
    rw [← hf_α_i]
    exact Finset.single_le_sum (f := f)
      (fun α' _ => zero_le _) (Finset.mem_univ α_i)
  exact h_in_wkpNorm.trans (ENNReal.le_tsum α)

private lemma exists_chart_rellich_subseq_aux
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : ℕ → M → ℝ}
    (hu_mem : ∀ n, MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) (u n))
    {R : ℝ}
    (hu_bdd : ∀ n, wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) (u n) ≤
      ENNReal.ofReal R)
    (α : M) (ψ : ℕ → ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ w_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
        MemLp w_α (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNbhd (I := I) (M := M) α)) ∧
        Filter.Tendsto
          (fun k => eLpNorm
              (fun y => chartPushedRaw (I := I) (M := M) α
                (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (ψ (σ k)) x) y - w_α y)
              (ENNReal.ofReal p)
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartNbhd (I := I) (M := M) α)))
          Filter.atTop (𝓝 0) := by
  classical
  set v : ℕ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun n =>
    chartPushedRaw (I := I) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u (ψ n) x) with hv_def
  have hv_mem : ∀ n, DeGiorgi.MemW01p (d := Module.finrank ℝ E) (ENNReal.ofReal p)
      (v n) (chartNbhd (I := I) (M := M) α) := by
    intro n
    exact memW01p_chartPushedRaw_pou_mul_chartNbhd
      (I := I) (M := M) g hp_one (hu_mem (ψ n)) α
  have hv_bdd_fun : ∀ n, eLpNorm (v n) (ENNReal.ofReal p)
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartNbhd (I := I) (M := M) α)) ≤ ENNReal.ofReal R := by
    intro n
    have h_step1 : eLpNorm (v n) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNbhd (I := I) (M := M) α)) ≤
        eLpNorm (v n) (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      rw [hv_def]
      exact eLpNorm_chartPushedRaw_pou_mul_chartNbhd_le
        (I := I) (M := M) (u := u (ψ n)) α
    have h_step2 : eLpNorm (v n) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
        eLpNorm (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α (u (ψ n)))
          (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      rw [hv_def]
      exact eLpNorm_chartPushedRaw_pou_mul_eq_chartPushed
        (I := I) (M := M) g (u (ψ n)) α
    rw [h_step2] at h_step1
    refine h_step1.trans ?_
    exact (eLpNorm_chartPushed_le_wkpNormChart (I := I) (M := M) g (u (ψ n)) α).trans
      (hu_bdd (ψ n))
  have hv_bdd_grad : ∀ n,
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm (fun x => (Classical.choose (hv_mem n).2).weakGrad x i)
          (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartNbhd (I := I) (M := M) α)) ≤ ENNReal.ofReal R := by
    intro n
    refine le_trans ?_ (hu_bdd (ψ n))
    have h_term_bound : ∀ i : Fin (Module.finrank ℝ E),
        eLpNorm (fun x => (Classical.choose (hv_mem n).2).weakGrad x i)
            (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNbhd (I := I) (M := M) α)) ≤
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
      intro i
      have h_ae := rellich_witness_weakGrad_ae_eq_chosenWeakPartial'
        (I := I) (M := M) g hp_one (hu_mem (ψ n)) α i
      rw [eLpNorm_congr_ae h_ae]
      exact eLpNorm_mono_measure _
        (MeasureTheory.Measure.restrict_mono_set _
          (chartNbhd_subset_chartTargetEuclid (I := I) (M := M) α))
    refine le_trans (Finset.sum_le_sum (fun i _ => h_term_bound i)) ?_
    have h_grad_sum_le_wkpNorm :
        ∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α (u (ψ n)))
            (chartTargetEuclid (I := I) (M := M) α) := by
      unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      refine le_trans ?_ le_add_self
      let hEquiv : (Fin 1 → Fin (Module.finrank ℝ E)) ≃ Fin (Module.finrank ℝ E) := {
        toFun := fun f => f 0
        invFun := fun i _ => i
        left_inv := by
          intro f
          funext k
          fin_cases k
          rfl
        right_inv := fun i => rfl }
      have hEquiv_app : ∀ f : Fin 1 → Fin (Module.finrank ℝ E), hEquiv f = f 0 := fun _ => rfl
      have h_sum_eq :
          ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) (ENNReal.ofReal p) 1 α'
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α (u (ψ n)))
                (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
              ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) =
          ∑ i : Fin (Module.finrank ℝ E),
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α (u (ψ n)))
                (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
              ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
        apply Finset.sum_bijective hEquiv (Equiv.bijective hEquiv)
        · intro a; simp
        · intro α' _
          have h_iter :
              DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) (ENNReal.ofReal p) 1 α'
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α (u (ψ n)))
                (chartTargetEuclid (I := I) (M := M) α) =
              DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) (ENNReal.ofReal p) (α' 0)
                (chartPushed (I := I) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α (u (ψ n)))
                (chartTargetEuclid (I := I) (M := M) α) := by
            rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
            rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
          rw [h_iter, hEquiv_app α']
      rw [← h_sum_eq]
    refine h_grad_sum_le_wkpNorm.trans ?_
    exact ENNReal.le_tsum α
  have h_nbhd_open := chartNbhd_isOpen (I := I) (M := M) α
  have h_nbhd_bdd := chartNbhd_isBounded (I := I) (M := M) α
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
      ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hp_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rcases DifferentialGeometry.Analysis.Sobolev.rellich_kondrachov_W01p_seq
    (d := Module.finrank ℝ E) h_nbhd_open h_nbhd_bdd hp_le hp_top hv_mem
    hv_bdd_fun hv_bdd_grad with ⟨σ, hσ_mono, w_α, hw_α_memLp, h_tendsto⟩
  exact ⟨σ, hσ_mono, w_α, hw_α_memLp, h_tendsto⟩

omit [I.Boundaryless] in
lemma pullbackToM_chartCompact_indicator_tsupport_subset_chart_source
    (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    tsupport (pullbackToM (M := M) I α
        ((chartCompact (I := I) (M := M) α).indicator w)) ⊆
      (chartAt H α).source := by
  classical
  have h_supp_indic : Function.support
      ((chartCompact (I := I) (M := M) α).indicator w) ⊆
      chartCompact (I := I) (M := M) α := by
    intro y hy
    by_contra hcontra
    apply hy
    exact Set.indicator_of_notMem hcontra _
  have h_chartCompact_closed : IsClosed (chartCompact (I := I) (M := M) α) :=
    (chartCompact_isCompact (I := I) (M := M) α).isClosed
  have h_tsupp_indic : tsupport
      ((chartCompact (I := I) (M := M) α).indicator w) ⊆
      chartCompact (I := I) (M := M) α := by
    rw [tsupport]
    exact h_chartCompact_closed.closure_subset_iff.mpr h_supp_indic
  exact pullbackToM_tsupport_subset_of_supp_in_chartCompact
    (I := I) (M := M) α _ h_tsupp_indic

omit [I.Boundaryless] in
lemma pullbackToM_chartCompact_indicator_hasCompactSupport
    (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    HasCompactSupport (pullbackToM (M := M) I α
        ((chartCompact (I := I) (M := M) α).indicator w)) := by
  exact HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
lemma chartPushedRaw_pullbackToM_chartCompact_indicator
    (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    chartPushedRaw (I := I) (M := M) α
      (pullbackToM (M := M) I α
        ((chartCompact (I := I) (M := M) α).indicator w)) =
      (chartCompact (I := I) (M := M) α).indicator w := by
  classical
  funext y
  rw [chartPushedRaw_pullbackToM_apply (I := I) (M := M) α _ y]
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]
    rw [Set.indicator_of_notMem]
    intro hy_compact
    exact hy (chartCompact_subset_chartTargetEuclid (I := I) (M := M) α hy_compact)

private lemma exists_diagonal_chart_extraction
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : ℕ → M → ℝ}
    (hu_mem : ∀ n, MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) (u n))
    {R : ℝ}
    (hu_bdd : ∀ n, wkpNormChart (I := I) (M := M) g 1 (ENNReal.ofReal p) (u n) ≤
      ENNReal.ofReal R)
    (S : Finset M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ S, ∃ w_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
        MemLp w_α (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNbhd (I := I) (M := M) α)) ∧
        Filter.Tendsto
          (fun k => eLpNorm
              (fun y => chartPushedRaw (I := I) (M := M) α
                (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y - w_α y)
              (ENNReal.ofReal p)
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartNbhd (I := I) (M := M) α)))
          Filter.atTop (𝓝 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨id, strictMono_id, fun α hα => ?_⟩
      exact absurd hα (Finset.notMem_empty α)
  | insert a S' ha_notin ih =>
      rcases ih with ⟨φ_S', hφ_S'_mono, hP_S'⟩
      rcases exists_chart_rellich_subseq_aux (I := I) (M := M) g hp_one
        hu_mem hu_bdd a φ_S' with
        ⟨σ_a, hσ_a_mono, w_a, hw_a_memLp, h_tendsto_a⟩
      refine ⟨φ_S' ∘ σ_a, hφ_S'_mono.comp hσ_a_mono, ?_⟩
      intro α hα
      rcases Finset.mem_insert.mp hα with rfl | hα_S'
      · refine ⟨w_a, hw_a_memLp, ?_⟩
        exact h_tendsto_a
      · rcases hP_S' α hα_S' with ⟨w_α, hw_α_memLp, h_tendsto_α⟩
        refine ⟨w_α, hw_α_memLp, ?_⟩
        exact h_tendsto_α.comp (Filter.tendsto_atTop_atTop_of_monotone hσ_a_mono.monotone
          (fun n => ⟨n, hσ_a_mono.id_le n⟩))

end Chart
end Sobolev
end Analysis
end DifferentialGeometry

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma chartAtlasPOU_measurable (α : M) :
    Measurable
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma pou_mul_measurable (α : M) {u : M → ℝ} (hu : Measurable u) :
    Measurable (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) :=
  (chartAtlasPOU_measurable (I := I) (M := M) α).mul hu

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma pou_mul_sub_measurable (α : M) {u v : M → ℝ}
    (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x)) :=
  ((chartAtlasPOU_measurable (I := I) (M := M) α).mul hu).sub
    ((chartAtlasPOU_measurable (I := I) (M := M) α).mul hv)

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma tsupport_pou_mul_subset_tsupport_pou
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  have h_eq : (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) =
      (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x • u x) := by
    funext x; rfl
  rw [h_eq]
  exact tsupport_smul_subset_left _ _

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma tsupport_pou_mul_sub_subset_tsupport_pou
    (α : M) (u v : M → ℝ) :
    tsupport (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x)) ⊆
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  classical
  have h_supp : Function.support (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x)) ⊆
      Function.support (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) ∪
        Function.support (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * v x) := by
    intro x hx
    by_contra hcontra
    apply hx
    rw [Set.mem_union, not_or] at hcontra
    obtain ⟨hu_zero, hv_zero⟩ := hcontra
    have hu_eq :
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x = 0 :=
      Function.notMem_support.mp hu_zero
    have hv_eq :
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x = 0 :=
      Function.notMem_support.mp hv_zero
    change ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x) = 0
    rw [hu_eq, hv_eq, sub_zero]
  have h_tsupp_closed : IsClosed
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := isClosed_tsupport _
  rw [tsupport]
  refine h_tsupp_closed.closure_subset_iff.mpr ?_
  intro x hx
  rcases h_supp hx with hu_supp | hv_supp
  · exact tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M) α u
      (subset_tsupport _ hu_supp)
  · exact tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M) α v
      (subset_tsupport _ hv_supp)

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma tsupport_pou_mul_subset_chart_source
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
  (tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M) α u).trans
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
      (I := I) (M := M) α)

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma tsupport_pou_mul_sub_subset_chart_source
    (α : M) (u v : M → ℝ) :
    tsupport (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x)) ⊆ (chartAt H α).source :=
  (tsupport_pou_mul_sub_subset_tsupport_pou (I := I) (M := M) α u v).trans
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
      (I := I) (M := M) α)

private noncomputable def kPouCompact (α : M) : Set E :=
  (extChartAt I α) ''
    (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ))

omit [I.Boundaryless] in
private lemma kPouCompact_isCompact (α : M) :
    IsCompact (kPouCompact (I := I) (M := M) α) :=
  (extChartAt_image_tsupport_pou_compact (I := I) (M := M) α).1

omit [I.Boundaryless] in
private lemma kPouCompact_subset_target (α : M) :
    kPouCompact (I := I) (M := M) α ⊆ (extChartAt I α).target :=
  (extChartAt_image_tsupport_pou_compact (I := I) (M := M) α).2

omit [CompactSpace M] [I.Boundaryless] in
private lemma kPouCompact_nonempty_of_pouNonempty
    {α : M}
    (hα_supp : (Function.support
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty) :
    (kPouCompact (I := I) (M := M) α).Nonempty := by
  obtain ⟨x, hx⟩ := hα_supp
  exact ⟨_, x, subset_tsupport _ hx, rfl⟩

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma image_extChartAt_tsupport_pou_mul_subset_kPouCompact
    (α : M) (u : M → ℝ) :
    (extChartAt I α) '' (tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ kPouCompact (I := I) (M := M) α := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M) α u hx, rfl⟩

omit [I.Boundaryless] in

omit [CompactSpace M] in
private lemma image_extChartAt_tsupport_pou_mul_sub_subset_kPouCompact
    (α : M) (u v : M → ℝ) :
    (extChartAt I α) '' (tsupport (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x))) ⊆ kPouCompact (I := I) (M := M) α := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, tsupport_pou_mul_sub_subset_tsupport_pou
    (I := I) (M := M) α u v hx, rfl⟩

omit [CompactSpace M] [I.Boundaryless] in
private lemma chartPushedRaw_pou_mul_sub_eq_zero_off_chartCompact
    (α : M) (u v : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartCompact (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
      (fun x : M =>
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) -
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * v x)) y = 0 := by
  classical
  have h_eq := chartPushedRaw_sub (I := I) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x)
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * v x)
  have h_app : chartPushedRaw (I := I) (M := M) α
        (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) -
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * v x)) y =
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) y -
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x) y := congrFun h_eq y
  rw [h_app]
  rw [chartPushedRaw_pou_mul_eq_zero_off_chartCompact
    (I := I) (M := M) α u hy]
  rw [chartPushedRaw_pou_mul_eq_zero_off_chartCompact
    (I := I) (M := M) α v hy]
  ring

omit [I.Boundaryless] in
private lemma tsupport_chartPushedRaw_pou_mul_sub_subset_chartCompact
    (α : M) (u v : M → ℝ) :
    tsupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M =>
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) -
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * v x))) ⊆ chartCompact (I := I) (M := M) α := by
  classical
  have h_supp_sub : Function.support
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) -
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * v x))) ⊆ chartCompact (I := I) (M := M) α := by
    intro y hy
    by_contra hcontra
    apply hy
    exact chartPushedRaw_pou_mul_sub_eq_zero_off_chartCompact
      (I := I) (M := M) α u v hcontra
  have h_chartCompact_closed : IsClosed (chartCompact (I := I) (M := M) α) :=
    (chartCompact_isCompact (I := I) (M := M) α).isClosed
  rw [tsupport]
  exact h_chartCompact_closed.closure_subset_iff.mpr h_supp_sub

private lemma memLp_pou_mul_riemannianMeasure
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u)
    (α : M) :
    MemLp (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) (ENNReal.ofReal p)
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
      ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hp_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_raw_w1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) (ENNReal.ofReal p)
        (chartPushedRaw (I := I) (M := M) α
          (fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) :=
    memW1p_chartPushedRaw_pou_mul_of_memWkpChart (I := I) (M := M) g hu α
  have h_raw_memLp :
      MemLp (chartPushedRaw (I := I) (M := M) α
          (fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x)) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := h_raw_w1p.1
  by_cases hPouNE : (Function.support
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty
  · have hK_compact := kPouCompact_isCompact (I := I) (M := M) α
    have hK_sub := kPouCompact_subset_target (I := I) (M := M) α
    have hK_ne := kPouCompact_nonempty_of_pouNonempty (I := I) (M := M) hPouNE
    obtain ⟨C_K, _hC_K_pos, hC_K_bnd⟩ :=
      eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform
        (I := I) (M := M) g α hK_compact hK_ne hK_sub hp_le hp_top
    have h_bnd := hC_K_bnd
      (pou_mul_measurable (I := I) (M := M) α hu_meas)
      (tsupport_pou_mul_subset_chart_source (I := I) (M := M) α u)
      (image_extChartAt_tsupport_pou_mul_subset_kPouCompact (I := I) (M := M) α u)
    refine ⟨(pou_mul_measurable (I := I) (M := M) α hu_meas).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt h_bnd ?_
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact h_raw_memLp.2
  · have hρ_zero : ∀ x : M,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := by
      intro x
      rw [Set.not_nonempty_iff_eq_empty] at hPouNE
      have : x ∉ Function.support
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        rw [hPouNE]; exact Set.notMem_empty x
      exact Function.notMem_support.mp this
    have h_zero_fn :
        (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) = (fun _ => (0 : ℝ)) := by
      funext x
      rw [hρ_zero x, zero_mul]
    rw [h_zero_fn]
    exact MemLp.zero

private lemma memLp_riemannianMeasure_of_memWkpChart
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g 1 (ENNReal.ofReal p) u) :
    MemLp u (ENNReal.ofReal p)
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M)
    with hS_def
  have h_sum : u =
      fun x : M => ∑ α ∈ S,
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x := by
    funext x
    rw [← Finset.sum_mul]
    rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x]
    rw [one_mul]
  rw [h_sum]
  exact memLp_finset_sum S
    (fun α _ => memLp_pou_mul_riemannianMeasure (I := I) (M := M) g hp_one hu_meas hu α)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
