import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff

noncomputable def Diffeomorph.pushforward
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (W : ∀ x : M, TangentSpace I x) :
    ∀ x : M, TangentSpace I x :=
  fun x => Φ.apply_symm_apply x ▸ (mfderiv I I Φ (Φ.symm x)) (W (Φ.symm x))

end DifferentialGeometry.PDE.RicciFlow.Pullback
