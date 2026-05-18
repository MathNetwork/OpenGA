import OpenGALib.Riemannian.Metric.HasMetric

/-!
# Typeclass instances on `TangentSpace I x` and the tangent bundle

Two engineering-glue typeclass instances that bridge `TangentSpace`
def-eq and `HasMetric` to Mathlib's bundle / fibre machinery. None have
paper analogues; both are **Eng**, hence `Util/`.

  * `instFiniteDimensionalTangent` — `FiniteDimensional ℝ E` lifts to
    `FiniteDimensional ℝ (TangentSpace I x)` via the def-eq
    `TangentSpace I x = E`. The `show` tactic forces whnf unfolding
    of the non-reducible `TangentSpace` `def`, bypassing strict
    `isDefEq`'s synthesis hesitation (the issue Mathlib's
    `#defeq_abuse` diagnoses).
  * `instRiemannianBundleOfHasMetric` — `[HasMetric I M]` produces a
    global `Bundle.RiemannianBundle (TangentSpace I)` instance,
    activating Mathlib's scoped `NormedAddCommGroup` and
    `InnerProductSpace ℝ` instances on each fibre. Single
    `NormedAddCommGroup` / `InnerProductSpace` source.

Imported by `Metric/RiemannianMetric.lean` (so any downstream consumer
of the methods file transitively gets both instances).
-/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Eng.** `TangentSpace I x` inherits `FiniteDimensional ℝ` from `E`. -/
instance instFiniteDimensionalTangent [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) := by
  show FiniteDimensional ℝ E
  infer_instance

/-- **Eng.** Bridge: `[HasMetric I M]` induces a global
`Bundle.RiemannianBundle (TangentSpace I : M → Type _)`. -/
noncomputable instance instRiemannianBundleOfHasMetric
    [IsManifold I ∞ M] [hm : HasMetric I M] :
    Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
  ⟨hm.metric.toRiemannianMetric⟩

end Riemannian
