import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold Topology ContDiff BigOperators ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_image_eq_target
    [I.Boundaryless] (α : M) :
    (extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)
      = (extChartAt I α).target := by
  rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α]
  exact (extChartAt I α).image_source_eq_target

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid
    [I.Boundaryless] (α : M) :
    toEuclidean ''
        ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      = chartTargetEuclid (I := I) (M := M) α := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_target_diff_image_eq_empty
    [I.Boundaryless] (α : M) :
    ((extChartAt I α).target : Set E) \
        ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      = (∅ : Set E) := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]
  exact Set.diff_self

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
    [I.Boundaryless] (α : M) :
    chartTargetEuclid (I := I) (M := M) α \
        (toEuclidean ''
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))
      = (∅ : Set EuclN) := by
  rw [chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid (I := I) (M := M) α]
  exact Set.diff_self

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_target_diff_image_measure_zero
    [I.Boundaryless] (α : M) :
    (MeasureTheory.volume : Measure E)
        (((extChartAt I α).target : Set E) \
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))) = 0 := by
  rw [chartLeviCivitaGoodSet_target_diff_image_eq_empty (I := I) α]
  exact MeasureTheory.measure_empty

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_restrict_target_diff_image_measure_zero
    [I.Boundaryless] (α : M) (μ : Measure E) :
    (μ.restrict ((extChartAt I α).target : Set E))
        (((extChartAt I α).target : Set E) \
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))) = 0 := by
  rw [chartLeviCivitaGoodSet_target_diff_image_eq_empty (I := I) α]
  exact MeasureTheory.measure_empty

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_measure_zero
    [I.Boundaryless] (α : M) :
    (MeasureTheory.volume : Measure EuclN)
        (chartTargetEuclid (I := I) (M := M) α \
          (toEuclidean ''
            ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))) = 0 := by
  rw [chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
      (I := I) (M := M) α]
  exact MeasureTheory.measure_empty

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_image_complement_measureZero
    [I.Boundaryless] (α : M) :
    ((MeasureTheory.volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α \
          (toEuclidean ''
            ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))) = 0 := by
  rw [chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
      (I := I) (M := M) α]
  exact MeasureTheory.measure_empty

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem mem_image_chartLeviCivitaGoodSet_iff_mem_target
    [I.Boundaryless] (α : M) (y : E) :
    y ∈ (extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)
      ↔ y ∈ (extChartAt I α).target := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]

omit [NeZero (Module.finrank ℝ E)] in
theorem mem_imageEuclid_chartLeviCivitaGoodSet_iff_mem_chartTargetEuclid
    [I.Boundaryless] (α : M) (y : EuclN) :
    y ∈ toEuclidean ''
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      ↔ y ∈ chartTargetEuclid (I := I) (M := M) α := by
  rw [chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid (I := I) (M := M) α]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
