import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Riemannian.Metric

/-!
# Riemannian.Instances.EuclideanSpace — Standard Riemannian metric on inner product spaces

Concrete `OpenGALib.RiemannianMetric` instance on a finite-dimensional real
inner product space `E`, with the standard inner product as metric tensor.
Specialises to `EuclideanSpace ℝ (Fin n)` for the canonical Euclidean
example, and to any `[NormedAddCommGroup E] [InnerProductSpace ℝ E]`
finite-dim space (e.g., `ℝ`, `ℝ × ℝ`, function spaces with L² inner
product).

## Why this instance exists

The framework's `OpenGALib.RiemannianMetric` typeclass is abstract
(takes any manifold `M` modeled on `E`). To verify the typeclass is
inhabited and to demonstrate the API, we provide the canonical
"flat-metric" instance: a manifold-over-itself `M = E`, with the
constant metric tensor `innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ`.

This instance is the framework's `EuclideanSpace` reference example
(analogue of Mathlib `Mathlib/Geometry/Manifold/Instances/Sphere.lean`
for the sphere), demonstrating typeclass cascade resolution + concrete
`metricInner` evaluation.

## Mathematical content

For a real inner product space `E`, viewed as a manifold over itself
via `chartedSpaceSelf E` and `𝓘(ℝ, E)`:

  * The metric tensor at every point is the standard inner product on
    `E` (constant in the basepoint, since the manifold is flat).
  * Symmetry follows from `real_inner_comm`.
  * Positive-definiteness follows from `real_inner_self_pos`.
  * Smoothness is trivial (constant function).

Downstream API (`metricInner`, `metricRiesz`, `manifoldGradient`) then
specialises to the standard inner product on `E`.

**Ground truth**: this is the canonical Riemannian structure on a
Hilbert space; do Carmo 1992 §1.1 example 1.4.
-/

namespace OpenGALib

open scoped ContDiff Manifold InnerProductSpace

/-- **Standard `RiemannianMetric` instance** on a finite-dimensional real
inner product space `E`, viewed as a manifold over itself via
`chartedSpaceSelf E` with model `𝓘(ℝ, E)`. The metric tensor at every
point is the standard inner product, encoded as `innerSL ℝ`.

This instance specialises to `EuclideanSpace ℝ (Fin n)`, and to any
real Hilbert / finite-dim inner product space. -/
noncomputable instance instRiemannianMetricSelf
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    RiemannianMetric (𝓘(ℝ, E)) E where
  metricTensor _ := innerSL ℝ
  symm _ v w := by
    show ⟪v, w⟫_ℝ = ⟪w, v⟫_ℝ
    exact real_inner_comm w v
  posdef _ v hv := by
    show 0 < ⟪v, v⟫_ℝ
    exact real_inner_self_pos.mpr hv
  smoothMetric := contMDiff_const

end OpenGALib

/-! ## UXTest

Self-tests verifying the `EuclideanSpace` instance resolves and that
`metricInner` matches the standard inner product on `E`. -/
section UXTest

open OpenGALib
open scoped ContDiff Manifold InnerProductSpace

/-- The framework's `metricInner` on a real inner product space `E`
matches the standard inner product. Direct from `instRiemannianMetricSelf`
unfolding to `innerSL ℝ` and `innerSL_apply_apply`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (x : E) (v w : TangentSpace (𝓘(ℝ, E)) x) :
    metricInner (I := 𝓘(ℝ, E)) (M := E) x v w = ⟪v, w⟫_ℝ :=
  rfl

/-- The `RiemannianMetric` typeclass resolves on `EuclideanSpace ℝ (Fin n)`
for any `n : ℕ`. -/
noncomputable example (n : ℕ) :
    RiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- The `RiemannianMetric` typeclass resolves on `ℝ` (1-d Euclidean
example). -/
noncomputable example : RiemannianMetric (𝓘(ℝ, ℝ)) ℝ :=
  inferInstance

end UXTest
