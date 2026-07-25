import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannCommutatorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannOrthoFrame
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false





























































































































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]




















omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_T1_eq_covDerivK
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m) =
      extDerivFun (I := I)
          (fun p : M =>
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
              (S.base.rm04 (t : Real) p)
              (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
              (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m))
          x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
        ∑ q : Fin 6,
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 0)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 1)
            (fun r : Fin 4 =>
              nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q (Fin.succ (Fin.succ r))) :=
  nablaLapComm_T1_eq_covDeriv_curvatureAction (I := I) S hS t x₀ a b c m

end DifferentialGeometry.PDE.RicciFlow
