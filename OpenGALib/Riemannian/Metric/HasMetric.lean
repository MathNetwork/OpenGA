import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Type-level definitions: `RiemannianMetric` and `HasMetric`

Tiny anchor for the two core type-level pieces of the Riemannian metric
infrastructure, separated from `RiemannianMetric.lean` so that `Util/`
helpers (Riesz bilinear-form bridge, fibre instances) can refer to
`RiemannianMetric I M` directly without introducing an import cycle.

  * `RiemannianMetric I M` — abbrev for Mathlib's
    `Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`.
  * `HasMetric I M` — typeclass declaring "M has a chosen
    Riemannian metric", with single field `metric : RiemannianMetric I M`.

Methods on `g : RiemannianMetric I M` live in `Metric/RiemannianMetric.lean`,
which imports this file.

Reference: do Carmo §1.2; Lee, *Smooth Manifolds*, Ch. 13.
-/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace Riemannian

/-- **Math.** A **Riemannian metric** on a smooth manifold $M$ modelled
on $(E, H, I)$. Mathlib's `Bundle.ContMDiffRiemannianMetric` aliased:
data, not a typeclass attribute. -/
abbrev RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

/-- **Math.** **`[HasMetric I M]` typeclass**: thin wrapper around
`RiemannianMetric I M` to make the metric instance-bindable when
downstream code binds `{I : ModelWithCorners ...}` independently of
the manifold's bundled `modelI`. Single-field class; bridged from
`[RiemannianManifold M]` in `Manifold.lean`. -/
class HasMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    where
  /-- The Riemannian metric on $(M, I)$. -/
  metric : RiemannianMetric I M

end Riemannian
