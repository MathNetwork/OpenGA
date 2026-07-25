import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.CoordinateRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmCoordinateRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.TowerRegularity

set_option autoImplicit false








noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]



omit [NeZero (Module.finrank ℝ E)] in
theorem coordTowerSmooth [CompactSpace M]
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (x0 : M)
    (t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
    (x : M) (hx : x ∈ chartLeviCivitaGoodSet (I := I) x0)
    (k : Nat) (idx : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        iteratedRmComp (I := I) (coordinateFrameAt (I := I) x0)
          (realizedChr (I := I) S x0) (realizedRmBase (I := I) S x0)
          k p.1 p.2 idx)
      ((t : Real), x) := by
  have hxframe : x ∈ coordinateFrameSet (I := I) x0 :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  refine iterRmComp_smoothAt (I := I)
    (frame := coordinateFrameAt (I := I) x0)
    (hframe := coordinateFrameAt_isLocalFrame (I := I) x0)
    (hu := coordinateFrameSet_open (I := I) x0) hxframe
    (chr := realizedChr (I := I) S x0)
    (base := realizedRmBase (I := I) S x0) ?_ ?_ k idx
  · intro i j l
    simpa [realizedChr] using
      coordGammaSmoothInf (I := I) S hS x0 t x hxframe i j l
  · intro slots
    exact coordRmFinSmooth (I := I) hS x0 t x hx slots

end DifferentialGeometry.PDE.RicciFlow
