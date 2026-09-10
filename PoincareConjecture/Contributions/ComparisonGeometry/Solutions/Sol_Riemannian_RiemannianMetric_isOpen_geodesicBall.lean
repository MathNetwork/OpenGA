/-
Reuses qinz1yang/differential-geometry, Copyright 2026 The DifferentialGeometry
contributors, Apache-2.0, commit 1b535dd102b94cc42b107cca27059687888f08b3.
The metric and distance are upstream/Mathlib constructions. The ball interface
is curated in OpenGA; source hypotheses and mathematical definitions are preserved.
-/
import Definitions.Def_OpenGA_GeodesicBall
import Mathlib.Geometry.Manifold.Metrizable

noncomputable section
set_option autoImplicit false

open Bundle Set DifferentialGeometry
open scoped Manifold ContDiff ENNReal

open Riemannian Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Balls for the Riemannian distance are open in the manifold topology. -/
theorem solution [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    IsOpen (g.geodesicBall p r) := by
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  change IsOpen {x | edist p x < ENNReal.ofReal r}
  simpa only [Metric.eball, edist_comm] using
    (Metric.isOpen_eball : IsOpen (Metric.eball p (ENNReal.ofReal r)))
