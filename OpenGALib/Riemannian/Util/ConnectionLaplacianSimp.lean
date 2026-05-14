import OpenGALib.Riemannian.Operators.ConnectionLaplacian

/-!
# Connection Laplacian — simp def-unfold

Engineering simp lemma exposing the definition of `connectionLaplacian`
as a sum of `secondCovDerivSection` over the smooth $g$-orthonormal
frame. Imported by callers that need to rewrite at the level of the
frame sum rather than against the opaque operator name.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold Bundle Riemannian

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
    (Z : VectorFieldSection I M) (α : M) :
    connectionLaplacian (I := I) (M := M) Z α =
      ∑ i, Riemannian.Operators.secondCovDerivSection (I := I) (M := M) Z
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α :=
  rfl

end Operators
end Riemannian

end
