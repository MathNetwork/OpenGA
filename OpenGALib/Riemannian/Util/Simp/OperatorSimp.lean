import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Divergence

/-!
# Operator simp def-unfolds

Engineering simp lemmas exposing definitions of small Riemannian operators
against the smooth $g$-orthonormal frame. Imported by callers that need to
rewrite at the level of frame sums rather than against opaque operator names.
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

/-- **Eng.** Definitional unfolding of `connectionLaplacian` as a sum of
`secondCovDerivSection` over the smooth $g$-orthonormal frame. Pure
`rfl`; tagged `@[simp]` for tactic-level rewrites. -/
@[simp] lemma connectionLaplacian_def
    (g : RiemannianMetric I M)
    (Z : VectorFieldSection I M) (α : M) :
    connectionLaplacian (I := I) (M := M) g Z α =
      ∑ i, Riemannian.Operators.secondCovDerivSection (I := I) (M := M) g Z
        (Riemannian.Tensor.smoothOrthoFrame (I := I) g α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) g α i) α :=
  rfl

/-- **Eng.** Definitional unfold of `divergence` as a sum of
`metricInner (∇_{B_i} X) B_i` over the smooth $g$-orthonormal frame. Pure
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
