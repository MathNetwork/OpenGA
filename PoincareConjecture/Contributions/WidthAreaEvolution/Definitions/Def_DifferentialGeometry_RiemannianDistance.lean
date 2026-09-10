/-
Reuses qinz1yang/differential-geometry, Copyright 2026 The DifferentialGeometry
contributors, Apache-2.0, commit 1b535dd102b94cc42b107cca27059687888f08b3.
The metric and distance are upstream/Mathlib constructions. The ball interface
is curated in OpenGA; source hypotheses and mathematical definitions are preserved.
-/
import Definitions.Def_DifferentialGeometry_SmoothRiemannianMetric
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false
noncomputable section
open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

noncomputable def riemannianEDistOf
    (g : SmoothRiemannianMetric I M) (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y

theorem riemannianEDistOf_self
    (g : SmoothRiemannianMetric I M) (x : M) :
    riemannianEDistOf (I := I) g x x = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x x = 0
  exact Manifold.riemannianEDist_self

end DifferentialGeometry
