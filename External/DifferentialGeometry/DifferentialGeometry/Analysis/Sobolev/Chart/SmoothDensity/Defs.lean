import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
import Mathlib.Geometry.Manifold.PartitionOfUnity
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

variable (I) in

def chartPullback (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) : M → ℝ := by
  classical
  exact fun x =>
    if x ∈ (chartAt H α).source then
      ψ (toEuclidean (extChartAt I α x))
    else 0

omit [IsManifold I ∞ M] in

lemma chartPullback_apply_of_mem (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartPullback I α ψ x = ψ (toEuclidean (extChartAt I α x)) := by
  classical
  unfold chartPullback
  simp [hx]

omit [IsManifold I ∞ M] in

lemma chartPullback_apply_of_notMem (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    chartPullback I α ψ x = 0 := by
  classical
  unfold chartPullback
  simp [hx]

omit [IsManifold I ∞ M] in

lemma chartPullback_add (α : M)
    (ψ₁ ψ₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    chartPullback I α (fun y => ψ₁ y + ψ₂ y) =
      fun x => chartPullback I α ψ₁ x + chartPullback I α ψ₂ x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]

omit [IsManifold I ∞ M] in

lemma chartPullback_const_smul (α : M) (c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    chartPullback I α (fun y => c * ψ y) =
      fun x => c * chartPullback I α ψ x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]

omit [IsManifold I ∞ M] in

lemma chartPullback_zero_fun (α : M) :
    chartPullback I α (fun _ => (0 : ℝ)) = (fun _ : M => (0 : ℝ)) := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α (fun _ => (0 : ℝ)) hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α (fun _ => (0 : ℝ)) hx]

omit [IsManifold I ∞ M] in

lemma support_chartPullback_subset_chartAt_source (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    Function.support (chartPullback I α ψ) ⊆ (chartAt H α).source := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  by_contra hx_off
  apply hx
  exact chartPullback_apply_of_notMem (I := I) (M := M) α ψ hx_off

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
lemma tsupport_pou_mul_subset_tsupport_pou
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
        (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport (ρ α : M → ℝ) := by
  refine closure_mono ?_
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  simp only [Function.mem_support, ne_eq]
  intro h_pou_zero
  apply hx
  rw [h_pou_zero, zero_mul]

lemma tsupport_chartAtlasPOU_mul_subset_chartAt_source
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          u x) ⊆
      (chartAt H α).source :=
  Set.Subset.trans
    (tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

lemma hasCompactSupport_chartAtlasPOU_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    HasCompactSupport (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          u x) := by
  have h_subset := tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
  have h_compact : IsCompact (tsupport
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)) :=
    (isClosed_tsupport _).isCompact
  exact h_compact.of_isClosed_subset (isClosed_tsupport _) h_subset

omit [IsManifold I ∞ M] in
lemma chartPushed_chartPullback_apply_of_mem
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α (chartPullback I α ψ) y =
      (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y)) *
      ψ y := by
  classical
  unfold chartPushed
  set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hz_source : z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hsymm_target
  have hz_chartAt_source : z ∈ (chartAt H α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)] at hz_source
    exact hz_source
  rw [chartPullback_apply_of_mem (I := I) (M := M) α ψ hz_chartAt_source]
  have hz_inv : (extChartAt I α) z = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hsymm_target
  rw [hz_inv]
  rw [(toEuclidean (E := E)).apply_symm_apply y]

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
