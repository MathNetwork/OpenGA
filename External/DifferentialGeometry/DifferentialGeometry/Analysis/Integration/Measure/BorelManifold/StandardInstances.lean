import DifferentialGeometry.Analysis.Integration.Measure.BorelManifold.Defs
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section

open Set

namespace DifferentialGeometry
namespace Integral
namespace Measure

instance chartedSpaceSelf_isBorelChartedSpace (H : Type*) [TopologicalSpace H] :
    IsBorelChartedSpace H H where
  chartAt_range_countable := by
    refine (Set.countable_singleton (OpenPartialHomeomorph.refl H)).mono ?_
    rintro c ⟨x, hx⟩
    change chartAt H (M := H) x = c at hx
    rw [chartAt_self_eq] at hx
    rw [Set.mem_singleton_iff]
    exact hx.symm
  measurableSet_chartAt_preimage := by
    intro c
    classical
    by_cases hc : c = OpenPartialHomeomorph.refl H
    · have h : {x : H | chartAt H (M := H) x = c} = Set.univ := by
        ext x
        change chartAt H (M := H) x = c ↔ True
        rw [chartAt_self_eq, hc, eq_self_iff_true, iff_true]
        trivial
      rw [h]
      exact @MeasurableSet.univ H (borel H)
    · have h : {x : H | chartAt H (M := H) x = c} = ∅ := by
        ext x
        change (chartAt H (M := H) x = c) ↔ False
        rw [chartAt_self_eq, iff_false]
        intro hcontra
        exact hc hcontra.symm
      rw [h]
      exact @MeasurableSet.empty H (borel H)

end Measure
end Integral
end DifferentialGeometry

end
