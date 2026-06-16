import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Geometry.Manifold.Riemannian.Basic
import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Standard Riemannian metric on inner product spaces

A finite-dimensional real inner product space `E` viewed as a manifold
over itself with the standard inner product as a constant metric tensor.

## Main results

* `euclideanRiemannianMetric` — the flat metric as data
  (`RiemannianMetric (𝓘(ℝ, E)) E`).
* `HasMetric.metric.metricInner_euclidean` — `g.metricInner x v w = ⟪v, w⟫_ℝ` on the
  flat metric.

Reference: do Carmo, *Riemannian Geometry*, §1.1 Example 1.4.

Mathlib upstream: `Mathlib.Geometry.Manifold.Riemannian.Basic`
(`riemannianMetricVectorSpace`).
-/

namespace Riemannian

open Bundle Bornology
open scoped ContDiff Manifold InnerProductSpace
/-- **Math.** The flat metric on a finite-dim inner product space `E`:
the constant `innerSL ℝ` as bundle-section metric tensor. -/
noncomputable def euclideanRiemannianMetric
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    RiemannianMetric (𝓘(ℝ, E)) E :=
  { riemannianMetricVectorSpace E with
    contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le (by exact_mod_cast le_top) }

/-- **Math.** $\langle v, w\rangle_g = \langle v, w\rangle_\mathbb{R}$ on the flat metric. -/
@[simp]
theorem metricInner_euclidean
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (v w : E) :
    (euclideanRiemannianMetric E).metricInner x v w = ⟪v, w⟫_ℝ :=
  rfl

end Riemannian
