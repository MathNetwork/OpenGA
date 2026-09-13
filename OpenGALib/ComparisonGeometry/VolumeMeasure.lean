import DifferentialGeometry.Analysis.Integration.Measure.Properties
import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Riemannian volume measure

OpenGA and DifferentialGeometry use the same Mathlib metric. This module exposes
the upstream volume measure and its local finiteness without choosing an
orientation, a global frame or an auxiliary distance.

Upstream: https://github.com/qinz1yang/differential-geometry, Apache-2.0,
v0.1.2, commit 1b535dd102b94cc42b107cca27059687888f08b3.
The original OpenGA declaration names are preserved.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Math.** The upstream Riemannian volume of an OpenGA metric. -/
noncomputable abbrev volumeMeasure (g : RiemannianMetric I M) : Measure M :=
  DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g

/-- **Math.** Compact manifolds have finite Riemannian volume. -/
theorem volumeMeasure_isFiniteMeasure [CompactSpace M] (g : RiemannianMetric I M) :
    IsFiniteMeasure g.volumeMeasure :=
  DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g

/-- **Math.** Every nonempty open set has positive Riemannian volume. -/
theorem volumeMeasure_isOpenPosMeasure (g : RiemannianMetric I M) :
    g.volumeMeasure.IsOpenPosMeasure :=
  DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure g

/-- **Math.** Compact subsets have finite Riemannian volume. -/
theorem volumeMeasure_isFiniteMeasureOnCompacts (g : RiemannianMetric I M) :
    IsFiniteMeasureOnCompacts g.volumeMeasure :=
  DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasureOnCompacts g

/-- **Math.** Every point has a neighborhood of finite Riemannian volume. -/
theorem volumeMeasure_isLocallyFiniteMeasure (g : RiemannianMetric I M) :
    IsLocallyFiniteMeasure g.volumeMeasure :=
  DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isLocallyFiniteMeasure g

end Riemannian.RiemannianMetric
