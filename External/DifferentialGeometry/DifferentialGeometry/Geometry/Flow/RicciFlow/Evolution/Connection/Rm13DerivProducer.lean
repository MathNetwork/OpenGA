import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.GammaCoord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.MetricCovDerivProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.RicciNorm

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false














noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]









omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem rm13Deriv_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (gInvDt : Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hmetricFrame : MetricFrameTimeRegularityInFrameOnLocal (I := I) S
      (coordInv (I := I) S x₀) gInvDt (coordinateFrameAt (I := I) x₀)
      (coordinateFrameSet (I := I) x₀))
    (hSmooth : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ t, t ∈ D.regular ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) 2
        (fun p : Real × M => (S.family.metric p.1).inner p.2
          (coordinateFrameAt (I := I) x₀ a p.2) (coordinateFrameAt (I := I) x₀ b p.2)) (t, x))
    (hFdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ s, s ∈ D.carrier ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => (S.family.metric s).inner y
          (coordinateFrameAt (I := I) x₀ a y) (coordinateFrameAt (I := I) x₀ b y)) x)
    (hFtdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E, ∀ t, t ∈ D.regular ->
        ∀ x : M, x ∈ coordinateFrameSet (I := I) x₀ ->
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t y a b) x)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
        (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b)))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i k j m : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
          (S.family.connection s) x₀ i k j m)
      (christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
            (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
          (t : Real) x₀ i m k j -
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
            (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
          (t : Real) x₀ k m i j)
      D.carrier
      (t : Real) :=
  christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation
    (I := I) S hS
    (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
      (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
    x₀
    (christoffelEvolution_of_solution (I := I) S hS (coordInv (I := I) S x₀) gInvDt
      (coordinateFrameAt (I := I) x₀) (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (coordinateFrameSet_open (I := I) x₀) hmetricFrame hSmooth hFdiff hFtdiff)
    hmix t i k j m

end DifferentialGeometry.PDE.RicciFlow
