import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import DifferentialGeometry.Integration.Volume.Invariance
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

set_option autoImplicit false

namespace DifferentialGeometry.Integral.Measure

noncomputable section

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



abbrev metricForMeasure (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric I M :=
  g

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricForMeasure_inner (g : SmoothRiemannianMetric I M) (x : M) :
    (metricForMeasure (I := I) (M := M) g).inner x = g.inner x := rfl


abbrev volumeMeasureAt [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    MeasureTheory.Measure M :=
  riemannianVolumeMeasure (I := I) (M := M) (G.metric t)

@[simp]
theorem volumeMeasureAt_eq [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    volumeMeasureAt (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metric t) := rfl


abbrev volumeMeasureOn [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) :
  MeasureTheory.Measure M :=
  riemannianVolumeMeasure (I := I) (M := M) (G.metricAt t)

@[simp]
theorem volumeMeasureOn_eq [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) :
    volumeMeasureOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metricAt t) := rfl

@[simp]
theorem volumeMeasureOn_eq_metric [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) :
    volumeMeasureOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real)) := rfl

theorem volumeMeasureAt_isLocallyFiniteMeasure [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    IsLocallyFiniteMeasure (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M)
    (G.metric t)

theorem volumeMeasureAt_sigmaFinite [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    SigmaFinite (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_sigmaFinite (I := I) (M := M)
    (G.metric t)

theorem volumeMeasureAt_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Time) (t : Time) :
    IsFiniteMeasure (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := I) (M := M) (G.metric t)

theorem volumeMeasureOn_isLocallyFiniteMeasure [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) :
    IsLocallyFiniteMeasure (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M)
    (G.metricAt t)

theorem volumeMeasureOn_sigmaFinite [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) :
    SigmaFinite (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_sigmaFinite (I := I) (M := M)
    (G.metricAt t)

theorem volumeMeasureOn_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) :
    IsFiniteMeasure (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := I) (M := M) (G.metricAt t)

end

end DifferentialGeometry.Integral.Measure
