import OpenGALib.Riemannian.Operators.Divergence

/-!
# Divergence — simp def-unfold

Engineering simp lemma exposing the definition of `divergence` as a sum
of `HasMetric.metric.metricInner (∇_{B_i} X) B_i` over the smooth $g$-orthonormal frame.
Imported by callers that need to rewrite at the level of the frame sum
rather than against the opaque operator name.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold Bundle Riemannian InnerProductSpace

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Eng.** Definitional unfold of `divergence` as a sum of
`HasMetric.metric.metricInner (∇_{B_i} X) B_i` over the smooth $g$-orthonormal frame. Pure
`rfl`; tagged `@[simp]` for tactic-level rewrites. -/
@[simp] lemma divergence_def
    (g : RiemannianMetric I M)
    (X : VectorFieldSection I M) (x : M) :
    divergence (I := I) (M := M) g X x =
      ∑ i, g.metricInner x
        (covDeriv g (Riemannian.Tensor.smoothOrthoFrame (I := I) g x i) X x)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) g x i x) :=
  rfl

end Operators
end Riemannian

end
