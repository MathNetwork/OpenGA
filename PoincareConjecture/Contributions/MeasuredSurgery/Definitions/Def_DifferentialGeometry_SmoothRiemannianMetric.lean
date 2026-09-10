/-
Reuses qinz1yang/differential-geometry, Copyright 2026 The DifferentialGeometry
contributors, Apache-2.0, commit 1b535dd102b94cc42b107cca27059687888f08b3.
The metric and distance are upstream/Mathlib constructions. The ball interface
is curated in OpenGA; source hypotheses and mathematical definitions are preserved.
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

abbrev SmoothRiemannianMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

end DifferentialGeometry

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

end Riemannian
