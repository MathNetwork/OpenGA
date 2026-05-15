import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import OpenGALib.Util.Attributes

/-!
# Metric measure spaces

The *metric measure space* — a triple `(M, d, μ)` consisting of a metric (or
pseudo-extended-metric) structure on `M` together with a measure `μ` — is the
foundational object of modern geometric analysis. OpenGA places it at Layer 1
alongside `LengthSpace` and `GeodesicSpace`.

## Ground truth

Gromov, *Metric Structures for Riemannian and Non-Riemannian Spaces*, §3¹⁄₂
(metric-measure spaces and the observable distance); Burago–Burago–Ivanov,
*A Course in Metric Geometry*, §1.7.

## Design choice: bundled triple, not typeclass

`MetricMeasureSpace M` is a `structure` carrying the metric and the measure as
data, so that a single carrier `M` may host multiple metric-measure structures
simultaneously (for instance an ambient Euclidean structure alongside a
Riemannian-induced one). This is the Gromov convention. To bundle existing
typeclass instances, construct directly via the anonymous constructor
`(⟨inferInstance, μ⟩ : MetricMeasureSpace M)`.

The measure is stored against an ambient `MeasurableSpace M` instance — at the
use site this is typically the Borel σ-algebra of the metric topology. No
regularity / σ-finiteness hypotheses are baked into the structure; stronger
hypotheses are added at the use site, mirroring the Mathlib
`MeasureTheory.Measure` discipline.
-/

open MeasureTheory

/-- **Math.** A metric measure space `(M, d, μ)`: a pseudo-extended-metric
structure on `M` bundled with a measure `μ`.

Ground truth: Gromov §3¹⁄₂.5 (metric-measure spaces — `mm`-spaces);
Burago–Burago–Ivanov §1.7.

The metric is stored as `PseudoEMetricSpace`-data, allowing the same carrier
`M` to host multiple inequivalent metric-measure structures. -/
structure MetricMeasureSpace (M : Type*) [MeasurableSpace M] : Type _ where
  /-- The pseudo-extended-metric on `M`. -/
  toPseudoEMetricSpace : PseudoEMetricSpace M
  /-- The measure on `M`. -/
  toMeasure : Measure M
