import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge
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
theorem realizedChr_hasDerivWithinAt
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
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i a p : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real => realizedChr (I := I) S x₀ s x i a p)
      (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
        (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b)
        (t : Real) x i a p)
      D.carrier
      (t : Real) :=
  christoffelEvolution_of_solution (I := I) S hS (coordInv (I := I) S x₀) gInvDt
    (coordinateFrameAt (I := I) x₀) (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordinateFrameSet_open (I := I) x₀) hmetricFrame hSmooth hFdiff hFtdiff t x hx i a p




omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem nablaKRm_timeDeriv_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (gInvDt : Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (rm04Dt : Real -> M -> (Fin 4 -> CoordinateIdx (𝕜 := Real) E) -> Real)
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
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (hrm : ∀ m : Fin 4 -> CoordinateIdx (𝕜 := Real) E,
      HasDerivWithinAt
        (fun s : Real => realizedRmBase (I := I) S x₀ s x₀ m)
        (rm04Dt (t : Real) x₀ m) D.carrier (t : Real))
    (hswap : ∀ (k : ℕ) (d : CoordinateIdx (𝕜 := Real) E)
        (m : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E),
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun y : M => iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
              (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k s y m) x₀
            (coordinateFrameAt (I := I) x₀ d x₀))
        (extDerivFun (I := I)
          (fun y : M => iteratedRmCompDt (I := I) (coordinateFrameAt (I := I) x₀)
            (realizedChr (I := I) S x₀)
            (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
              (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
            (realizedRmBase (I := I) S x₀) rm04Dt k (t : Real) y m) x₀
          (coordinateFrameAt (I := I) x₀ d x₀))
        D.carrier (t : Real))
    (k : ℕ) (n : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real => iteratedRmComp (I := I) (coordinateFrameAt (I := I) x₀)
        (realizedChr (I := I) S x₀) (realizedRmBase (I := I) S x₀) k s x₀ n)
      (iteratedRmCompDt (I := I) (coordinateFrameAt (I := I) x₀)
        (realizedChr (I := I) S x₀)
        (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
          (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
        (realizedRmBase (I := I) S x₀) rm04Dt k (t : Real) x₀ n)
      D.carrier
      (t : Real) :=
  iteratedRmComp_hasDerivWithinAt (I := I) (coordinateFrameAt (I := I) x₀)
    (realizedChr (I := I) S x₀)
    (christoffelEvolutionRHSInFrame (M := M) (coordInv (I := I) S x₀)
      (fun t x d a b => ricciCovDerivCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x d a b))
    (realizedRmBase (I := I) S x₀) rm04Dt x₀ hrm
    (fun i a p => realizedChr_hasDerivWithinAt (I := I) S hS x₀ gInvDt hmetricFrame
      hSmooth hFdiff hFtdiff t x₀ (coordinateFrameAt_mem (I := I) x₀) i a p)
    hswap k n

end DifferentialGeometry.PDE.RicciFlow
