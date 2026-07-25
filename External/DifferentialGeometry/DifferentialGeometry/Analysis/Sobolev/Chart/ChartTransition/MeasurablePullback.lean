import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Banach
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Completeness
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import DifferentialGeometry.Analysis.Sobolev.Tools.WeakPartialLimit
import DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding
import DifferentialGeometry.Analysis.Sobolev.Manifold.EmbeddingManifold
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Family
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Topology.UniformSpace.UniformEmbedding


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

def extChartAtExt (α : M) : M → E := by
  classical
  exact fun x => if x ∈ (chartAt H α).source then extChartAt I α x else 0

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma extChartAtExt_apply_of_mem (α : M)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    extChartAtExt (I := I) α x = extChartAt I α x := by
  unfold extChartAtExt; simp [hx]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma extChartAtExt_apply_of_notMem (α : M)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    extChartAtExt (I := I) α x = 0 := by
  unfold extChartAtExt; simp [hx]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma extChartAtExt_measurable (α : M) :
    Measurable (extChartAtExt (I := I) (M := M) α) := by
  classical
  have h_src_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have h_src_meas : MeasurableSet ((chartAt H α).source) := h_src_open.measurableSet
  have h_extChart_continuousOn :
      ContinuousOn (fun x : M => extChartAt I α x) ((chartAt H α).source) := by
    have h_src_eq : (chartAt H α).source = (extChartAt I α).source :=
      (DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M) α).symm
    rw [h_src_eq]
    exact continuousOn_extChartAt α
  have h_const_continuousOn :
      ContinuousOn (fun _ : M => (0 : E)) ((chartAt H α).source)ᶜ :=
    continuous_const.continuousOn
  have h_eq : extChartAtExt (I := I) (M := M) α =
      ((chartAt H α).source).piecewise
        (fun x : M => extChartAt I α x) (fun _ => 0) := by
    funext x
    unfold extChartAtExt Set.piecewise
    by_cases hx : x ∈ (chartAt H α).source <;> simp [hx]
  rw [h_eq]
  exact ContinuousOn.measurable_piecewise h_extChart_continuousOn
    h_const_continuousOn h_src_meas

def pullbackToManifold (α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) : M → ℝ := by
  classical
  exact fun x =>
    if x ∈ (chartAt H α).source then
      v ((toEuclidean (E := E)) ((extChartAt I α) x))
    else 0

omit [IsManifold I ∞ M] in
lemma pullbackToManifold_apply_of_mem (α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    pullbackToManifold (I := I) α v x =
      v ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  unfold pullbackToManifold; simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToManifold_apply_of_notMem (α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    pullbackToManifold (I := I) α v x = 0 := by
  unfold pullbackToManifold; simp [hx]

omit [IsManifold I ∞ M] in
private lemma pullbackToManifold_eq_indicator (α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    pullbackToManifold (I := I) α v =
      ((chartAt H α).source).indicator
        (fun x : M => v ((toEuclidean (E := E))
          (extChartAtExt (I := I) α x))) := by
  classical
  funext x
  unfold pullbackToManifold Set.indicator
  by_cases hx : x ∈ (chartAt H α).source
  · simp [hx, extChartAtExt_apply_of_mem (I := I) (α := α) hx]
  · simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToManifold_measurable (α : M)
    {v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hv : Measurable v) :
    Measurable (pullbackToManifold (I := I) α v) := by
  classical
  rw [pullbackToManifold_eq_indicator (I := I) (α := α) v]
  have h_src_meas : MeasurableSet ((chartAt H α).source) :=
    ((chartAt H α).open_source).measurableSet
  have h_extChart_meas : Measurable (extChartAtExt (I := I) (M := M) α) :=
    extChartAtExt_measurable (I := I) (α := α)
  have h_toEuclidean_meas : Measurable (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).continuous.measurable
  have h_comp_meas :
      Measurable (fun x : M => v ((toEuclidean (E := E))
        (extChartAtExt (I := I) α x))) :=
    hv.comp (h_toEuclidean_meas.comp h_extChart_meas)
  exact h_comp_meas.indicator h_src_meas

omit [IsManifold I ∞ M] in
lemma support_pullbackToManifold_subset (α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    Function.support (pullbackToManifold (I := I) α v) ⊆
      (chartAt H α).source := by
  intro x hx
  by_contra h_notin
  apply hx
  exact pullbackToManifold_apply_of_notMem (I := I) (α := α) v h_notin

lemma pullbackToManifold_chartPushed_apply_of_mem
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    pullbackToManifold (I := I) α
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) x =
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x * u x := by
  classical
  rw [pullbackToManifold_apply_of_mem (I := I) (α := α) _ hx]
  have hx_extchartsource : x ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact hx
  have h_symm_toEucl : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) ((extChartAt I α) x)) = (extChartAt I α) x :=
    (toEuclidean (E := E)).symm_apply_apply _
  have h_symm_extChart : (extChartAt I α).symm ((extChartAt I α) x) = x :=
    (extChartAt I α).left_inv hx_extchartsource
  unfold chartPushed
  rw [h_symm_toEucl, h_symm_extChart]

lemma pullbackToManifold_chartPushed_eq_pou_mul
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    pullbackToManifold (I := I) α
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) =
      fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x * u x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · exact pullbackToManifold_chartPushed_apply_of_mem (I := I) α u hx
  · rw [pullbackToManifold_apply_of_notMem (I := I) (α := α) _ hx]
    have h_rho_zero : (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I M α : M → ℝ) x = 0 := by
      have h_subord :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).IsSubordinate
            (fun α : M => (chartAt H α).source) :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M
      have h_tsupp : tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source := h_subord α
      have h_x_notin : x ∉ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h => hx (h_tsupp h)
      exact image_eq_zero_of_notMem_tsupport h_x_notin
    rw [h_rho_zero]; ring

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
