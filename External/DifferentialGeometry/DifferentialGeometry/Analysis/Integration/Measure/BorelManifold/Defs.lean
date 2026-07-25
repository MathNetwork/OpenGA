import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M]

class IsBorelChartedSpace (H : Type*) (M : Type*)
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] : Prop where

  chartAt_range_countable :
    (Set.range (fun x : M => chartAt H x)).Countable

  measurableSet_chartAt_preimage :
    ∀ c : OpenPartialHomeomorph M H,
      @MeasurableSet M (borel M) {x : M | chartAt H x = c}

namespace IsBorelChartedSpace

variable [ChartedSpace H M]

theorem chartAt_preimage_subset_source
    (c : OpenPartialHomeomorph M H) :
    {x : M | chartAt H x = c} ⊆ c.source := by
  intro x hx
  have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
  rw [hx] at hxs
  exact hxs

theorem exists_countable_borel_chart_cover
    [_root_.DifferentialGeometry.Integral.Measure.IsBorelChartedSpace H M]
    [Nonempty M] :
    ∃ (s : ℕ → Set M) (c : ℕ → OpenPartialHomeomorph M H),
      (∀ n, @MeasurableSet M (borel M) (s n)) ∧
      (∀ n, c n ∈ atlas H M) ∧
      (∀ n, s n ⊆ (c n).source) ∧
      (⋃ n, s n) = univ := by
  classical
  have hcount :=
    _root_.DifferentialGeometry.Integral.Measure.IsBorelChartedSpace.chartAt_range_countable
      (H := H) (M := M)
  have hmeas :=
    _root_.DifferentialGeometry.Integral.Measure.IsBorelChartedSpace.measurableSet_chartAt_preimage
      (H := H) (M := M)
  have hrange_nonempty : (Set.range (fun x : M => chartAt H x)).Nonempty :=
    Set.range_nonempty (fun x : M => chartAt H x)
  obtain ⟨f, hf⟩ := hcount.exists_eq_range hrange_nonempty
  refine ⟨fun n => {x : M | chartAt H x = f n}, fun n => f n, ?_, ?_, ?_, ?_⟩
  · intro n; exact hmeas (f n)
  · intro n
    change f n ∈ atlas H M
    have hin : f n ∈ Set.range (fun x : M => chartAt H x) := by
      rw [hf]; exact Set.mem_range_self n
    obtain ⟨x, hx⟩ := hin
    rw [← hx]
    exact ChartedSpace.chart_mem_atlas x
  · intro n
    exact chartAt_preimage_subset_source (f n)
  · refine Set.eq_univ_of_forall (fun x => ?_)
    have hxr : chartAt H x ∈ Set.range (fun y : M => chartAt H y) :=
      Set.mem_range_self x
    rw [hf] at hxr
    obtain ⟨n, hn⟩ := hxr
    exact Set.mem_iUnion.mpr ⟨n, by simp [hn]⟩

end IsBorelChartedSpace

end Measure
end Integral
end DifferentialGeometry

end
