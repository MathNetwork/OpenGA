import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import OpenGALib.Bridges.RiemannianToLength
import OpenGALib.MetricGeometry.MetricMeasureSpace

/-!
# Layer 1 instances on real inner product spaces and Euclidean space

The canonical worked example for OpenGA's Layer 1: a finite-dimensional real
inner product space — and in particular the standard `EuclideanSpace ℝ (Fin n)`
— inherits each of the foundational structures.

* `LengthSpace` arises via Mathlib's `IsRiemannianManifold 𝓘(ℝ, F) F` instance
  composed with the `OpenGALib/Bridges/RiemannianToLength` bridge. We expose a
  concrete instance for every real inner product space below.
* `MetricMeasureSpace` is constructed explicitly, bundling the canonical
  pseudo-extended-metric (inner-product norm) with the Haar / Lebesgue
  measure on `ℝⁿ`.

`GeodesicSpace` (line segments are minimizing) is deferred to a follow-up
commit — see the PRE-PAPER block in `Bridges/RiemannianToLength.lean` for
the missing `eVariationOn ≤ Manifold.pathELength` bridge lemma it depends
on.

## Ground truth

do Carmo, *Riemannian Geometry*, §1.1 Example 1.4 (flat metric on `ℝⁿ`).
-/

open scoped ENNReal

namespace OpenGA

/-- **Math.** The standard Euclidean space `ℝⁿ` is a length space —
specialization of `OpenGA.instLengthSpaceOfInnerProductSpace` (declared in
`Bridges/RiemannianToLength`) to `EuclideanSpace ℝ (Fin n)`. -/
example (n : ℕ) : LengthSpace (EuclideanSpace ℝ (Fin n)) :=
  OpenGA.instLengthSpaceOfInnerProductSpace

/-- **Math.** The canonical metric measure space structure on `ℝⁿ`:
the standard inner-product distance paired with the Haar / Lebesgue
volume measure.

Ground truth: do Carmo §1.1 Example 1.4 (Euclidean metric); Mattila,
*Geometry of Sets and Measures in Euclidean Spaces*, §1 (Lebesgue
measure on `ℝⁿ`). -/
noncomputable def euclideanMetricMeasureSpace (n : ℕ) :
    MetricMeasureSpace (EuclideanSpace ℝ (Fin n)) where
  toPseudoEMetricSpace := inferInstance
  toMeasure := MeasureTheory.volume

end OpenGA
