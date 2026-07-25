import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifferenceCurvature

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open VectorField
open DifferentialGeometry.Integral.Measure

section Ricci

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def ricciDiffBasisSummand (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  (covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) x
      - covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) x)
    + (CovariantDerivative.difference (LeviCivita (I := I) gₖ) (LeviCivita (I := I) g₀) x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w) x)
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
        - CovariantDerivative.difference (LeviCivita (I := I) gₖ)
            (LeviCivita (I := I) g₀) x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) gₖ)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x w) x)
          (smoothExtensionTangent (I := I) x v x))

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_sub_eq_basisSum_summand (g₀ gₖ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) gₖ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (ricciDiffBasisSummand (I := I) g₀ gₖ x v w i) i := by
  rw [ricciTensor_sub_eq_basisSum_difference (I := I) g₀ gₖ x v w]
  rfl

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_sub_telescope (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₂ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (ricciDiffBasisSummand (I := I) g₀ g₁ x v w i
            - ricciDiffBasisSummand (I := I) g₀ g₂ x v w i) i := by
  have h1 := ricciTensor_sub_eq_basisSum_summand (I := I) g₀ g₁ x v w
  have h2 := ricciTensor_sub_eq_basisSum_summand (I := I) g₀ g₂ x v w
  have key : ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₂ x v w =
      (ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w)
        - (ricciTensor (I := I) g₂ x v w - ricciTensor (I := I) g₀ x v w) := by ring
  rw [key, h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (chartModelBasis E).repr
        (ricciDiffBasisSummand (I := I) g₀ g₁ x v w i
          - ricciDiffBasisSummand (I := I) g₀ g₂ x v w i)
        = (chartModelBasis E).repr (ricciDiffBasisSummand (I := I) g₀ g₁ x v w i)
          - (chartModelBasis E).repr (ricciDiffBasisSummand (I := I) g₀ g₂ x v w i)
      from map_sub _ _ _, Finsupp.sub_apply]

end Ricci

end Connection
end Integral
end DifferentialGeometry
