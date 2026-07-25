import DifferentialGeometry.Geometry.Boundary.InducedMetric
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Properties

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace (BoundaryManifold I M) :=
  borel (BoundaryManifold I M)
private local instance : BorelSpace (BoundaryManifold I M) := ⟨rfl⟩

noncomputable def surfaceMeasure
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    MeasureTheory.Measure (BoundaryManifold I M) :=
  Measure.riemannianVolumeMeasure
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

omit [FiniteDimensional ℝ E] in
lemma surfaceMeasure_def
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    surfaceMeasure (I := I) (M := M) g =
      Measure.riemannianVolumeMeasure
        (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g) := rfl

omit [FiniteDimensional ℝ E] in
theorem surfaceMeasure_isOpenPosMeasure
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    (surfaceMeasure (I := I) (M := M) g).IsOpenPosMeasure := by
  rw [surfaceMeasure_def]
  exact Measure.riemannianVolumeMeasure_isOpenPosMeasure
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

omit [FiniteDimensional ℝ E] in
theorem surfaceMeasure_sigmaFinite
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    SigmaFinite (surfaceMeasure (I := I) (M := M) g) := by
  rw [surfaceMeasure_def]
  exact Measure.riemannianVolumeMeasure_sigmaFinite
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

omit [FiniteDimensional ℝ E] in
theorem surfaceMeasure_isLocallyFiniteMeasure
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    IsLocallyFiniteMeasure (surfaceMeasure (I := I) (M := M) g) := by
  rw [surfaceMeasure_def]
  exact Measure.riemannianVolumeMeasure_isLocallyFiniteMeasure
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

omit [FiniteDimensional ℝ E] in
theorem surfaceMeasure_isFiniteMeasureOnCompacts
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    IsFiniteMeasureOnCompacts (surfaceMeasure (I := I) (M := M) g) := by
  rw [surfaceMeasure_def]
  exact Measure.riemannianVolumeMeasure_isFiniteMeasureOnCompacts
    (I := hI.boundaryI) (M := BoundaryManifold I M) (inducedMetric g)

omit [FiniteDimensional ℝ E] in
theorem surfaceMeasure_eq_zero_of_boundaryless
    [I.Boundaryless] [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : Measure.SmoothRiemannianMetric I M) :
    surfaceMeasure (I := I) (M := M) g = 0 := by
  haveI : IsEmpty hI.boundaryH :=
    HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless I
  haveI : IsEmpty (BoundaryManifold I M) :=
    BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
  exact MeasureTheory.Measure.eq_zero_of_isEmpty _

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
