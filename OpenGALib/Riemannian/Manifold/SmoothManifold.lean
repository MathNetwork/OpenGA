import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Util.Attributes
import OpenGALib.Riemannian.TangentBundle.LocallyConstant

/-!
# Smooth and Riemannian manifolds — bundled typeclass

A pure-math user reasons about a Riemannian manifold as the data
$(M, g)$; the Mathlib machinery $(E, H, I, \text{ChartedSpace},
\text{IsManifold})$ is implementation detail. The typeclasses here
bundle that machinery:

  * `[SmoothManifold M]` — $(E, H, I)$ + chart machinery + smooth
    structure (one typeclass replaces five parameters).
  * `[RiemannianManifold M]` — extends `[SmoothManifold M]` with a
    Riemannian metric (one typeclass replaces six).

Downstream operators (`metricInner`, `manifoldGradient`, `Δ_g`, `Ric`)
take `[RiemannianManifold M]` and recover everything they need. The
metric lives on the typeclass as a `RiemannianMetric modelI M` field
(data, not nested typeclass), so polymorphic notation can pull it
without `[I]`-bracket workarounds.

Other geometric structures (Lorentzian, Kähler, symplectic, contact)
extend `SmoothManifold M` analogously and provide bridge instances to
their structure-specific typeclasses.

**Ground truth**: do Carmo §1.1; Lee, *Smooth Manifolds*, Ch. 1, 13.
-/

open Bundle
open scoped ContDiff Manifold Bundle

namespace Riemannian

/-- **Math.** A **smooth manifold** as a single bundled typeclass.
Packages `(E, H, modelI)` plus the complete typeclass cascade
(`NormedAddCommGroup E`, `NormedSpace ℝ E`, `FiniteDimensional ℝ E`,
`CompleteSpace E`, `TopologicalSpace H`, `ChartedSpace H M`,
`IsManifold modelI ∞ M`, `IsLocallyConstantChartedSpace H M`) needed by
Riemannian operators. `[SmoothManifold M]` reads "M is a smooth
finite-dimensional manifold" — the textbook setting. -/
class SmoothManifold (M : Type*) [TopologicalSpace M] where
  /-- The model fibre. -/
  E : Type*
  [normedAddCommGroup_E : NormedAddCommGroup E]
  [normedSpace_E : NormedSpace ℝ E]
  [finiteDimensional_E : FiniteDimensional ℝ E]
  [completeSpace_E : CompleteSpace E]
  /-- The model chart codomain. -/
  H : Type*
  [topologicalSpace_H : TopologicalSpace H]
  /-- The model with corners specifying $M$'s smooth structure. -/
  modelI : ModelWithCorners ℝ E H
  [chartedSpace_M : ChartedSpace H M]
  [isManifold_M : IsManifold modelI ∞ M]
  [isLocallyConstantChartedSpace_M : IsLocallyConstantChartedSpace H M]

/-- **Math.** A **Riemannian manifold** $(M, g)$ as a single bundled
typeclass. Extends `SmoothManifold M` with a `metric : RiemannianMetric
modelI M` field (data). Also bundles `[InnerProductSpace ℝ E]` and
`[NeZero (Module.finrank ℝ E)]` so the full cascade for Bochner,
Lichnerowicz, second-variation is provided by `[RiemannianManifold M]`
alone. -/
class RiemannianManifold (M : Type*) [TopologicalSpace M]
    extends SmoothManifold M where
  [innerProductSpace_E : InnerProductSpace ℝ E]
  [neZero_finrank_E : NeZero (Module.finrank ℝ E)]
  /-- The metric on $M$, attached to the inherited `modelI`. -/
  metric : RiemannianMetric modelI M

/-! ## Global instance bridges

Class fields tagged `[...]` are accessible to type-class search only via
parent-chain projection from `[SmoothManifold M]` / `[RiemannianManifold
M]`. Lean's TC engine can occasionally fail to chain these projections at
the right elaboration sites (especially when the projected type appears
under an `outParam` like `E` here). The bridges below promote each
instance field to a top-level instance so synthesis is direct. -/

section SmoothManifoldBridges

variable {M : Type*} [TopologicalSpace M] [s : SmoothManifold M]

instance : NormedAddCommGroup s.E := s.normedAddCommGroup_E
instance : NormedSpace ℝ s.E := s.normedSpace_E
instance : FiniteDimensional ℝ s.E := s.finiteDimensional_E
instance : CompleteSpace s.E := s.completeSpace_E
instance : TopologicalSpace s.H := s.topologicalSpace_H
instance : ChartedSpace s.H M := s.chartedSpace_M
instance : IsManifold s.modelI ∞ M := s.isManifold_M
instance : IsLocallyConstantChartedSpace s.H M := s.isLocallyConstantChartedSpace_M

end SmoothManifoldBridges

section RiemannianManifoldBridges

variable {M : Type*} [TopologicalSpace M] [rm : RiemannianManifold M]

instance : InnerProductSpace ℝ rm.E := rm.innerProductSpace_E
instance : NeZero (Module.finrank ℝ rm.E) := rm.neZero_finrank_E

/-- **Eng.** The metric carried by `[RiemannianManifold M]` induces a
global `Bundle.RiemannianBundle (TangentSpace modelI : M → Type _)`,
activating Mathlib's scoped `NormedAddCommGroup` / `InnerProductSpace ℝ` on each
fibre. Single `NormedAddCommGroup` / `InnerProductSpace` source — sidesteps the
lean4#13063 `NormedAddCommGroup` diamond. -/
noncomputable instance instRiemannianBundleOfRiemannianManifold :
    Bundle.RiemannianBundle (TangentSpace rm.modelI : M → Type _) :=
  ⟨rm.metric.toRiemannianMetric⟩

/-- **Eng.** Bridge: `[RiemannianManifold M] → [HasMetric (SmoothManifold.modelI M) M]`.
Lets every `[HasMetric I M]`-keyed API work uniformly for bundled and
explicit-metric callers. -/
instance instHasMetricOfRiemannianManifold :
    HasMetric rm.modelI M where
  metric := rm.metric

end RiemannianManifoldBridges

end Riemannian
