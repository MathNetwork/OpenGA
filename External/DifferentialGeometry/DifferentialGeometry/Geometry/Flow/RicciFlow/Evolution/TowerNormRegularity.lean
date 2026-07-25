import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CoordinateTowerRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridgeAllK










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]



omit [NeZero (Module.finrank ℝ E)] in
theorem towerNorm_joint
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S) (k : Nat) :
    ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M => nablaKRm04NormSqIntrinsic (I := I) S k p.1 p.2)
      ((RealTimeInterval.closedOpen alpha omega hAlphaOmega).regular ×ˢ
        (Set.univ : Set M)) := by
  classical
  intro p hp
  let x0 : M := p.2
  let frame := coordinateFrameAt (I := I) x0
  let t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega) := ⟨p.1, hp.1⟩
  have hx : p.2 ∈ coordinateFrameSet (I := I) x0 := by
    simpa only [x0] using coordinateFrameAt_mem (I := I) p.2
  have hdomain :
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega).regular ×ˢ
          coordinateFrameSet (I := I) x0 ∈ nhds p :=
    prod_mem_nhds
      ((RealTimeInterval.closedOpen alpha omega hAlphaOmega).regular_isOpen.mem_nhds hp.1)
      ((coordinateFrameSet_open (I := I) x0).mem_nhds hx)
  have hinv (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M => coordInv (I := I) S x0 q.1 q.2 i j) p := by
    simpa only [t] using coordInvSmoothAt (I := I) S hS x0 t p.2 hx i j
  have hcomp (slots : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M => tensor0SComponent (I := I)
          (nablaKRm04Field (I := I) S q.1 k q.2)
          (fun i => frame i q.2) slots) p := by
    have hsmooth := coordTowerSmooth (I := I) hS x0 t p.2
      (self_mem_chartLeviCivitaGoodSet (I := I) p.2) k slots
    refine hsmooth.congr_of_eventuallyEq ?_
    filter_upwards [hdomain] with q hq
    simpa only [frame, tensor0SComponent_apply, frameTuple] using
      (iteratedRmComp_eq_nablaKRm04Field (I := I) S x0 q.1 k hq.2 slots).symm
  have hcontract :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          ∑ I0 : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E,
            ∑ J0 : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E,
              (∏ a : Fin (4 + k), coordInv (I := I) S x0 q.1 q.2 (I0 a) (J0 a)) *
                tensor0SComponent (I := I)
                  (nablaKRm04Field (I := I) S q.1 k q.2)
                  (fun i => frame i q.2) I0 *
                tensor0SComponent (I := I)
                  (nablaKRm04Field (I := I) S q.1 k q.2)
                  (fun i => frame i q.2) J0) p := by
    refine ContMDiffAt.sum fun I0 _ => ContMDiffAt.sum fun J0 _ => ?_
    have hprod :
        ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
          (modelWithCornersSelf Real Real) ∞
          (fun q : Real × M =>
            ∏ a : Fin (4 + k),
              coordInv (I := I) S x0 q.1 q.2 (I0 a) (J0 a)) p :=
      ContMDiffAt.prod fun a _ => hinv (I0 a) (J0 a)
    exact (hprod.mul (hcomp I0)).mul (hcomp J0)
  refine (hcontract.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hdomain] with q hq
  let basis := coordinateFrameAt_basis (I := I) x0 hq.2
  have hinvBasis : MetricInverseInBasis_gen
      (I := I) (S.base.metric q.1) q.2 basis
      (fun i j => coordInv (I := I) S x0 q.1 q.2 i j) := by
    simpa only [basis, coordInv] using
      (gInvBasisAt (I := I) (S.base.metric q.1) x0 hq.2)
  change normSq0S (I := I) (S.base.metric q.1) q.2 (4 + k)
      (nablaKRm04Field (I := I) S q.1 k q.2) = _
  rw [normSq0S_eq_coord (I := I) (S.base.metric q.1) q.2 (4 + k)
    basis (fun i j => coordInv (I := I) S x0 q.1 q.2 i j) hinvBasis]
  simp only [coordInner0S, basis, coordinateFrameAt_basis_apply, frame]

end DifferentialGeometry.PDE.RicciFlow
