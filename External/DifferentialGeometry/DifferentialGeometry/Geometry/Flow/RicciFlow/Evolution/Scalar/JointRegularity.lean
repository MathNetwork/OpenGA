import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TraceAlgebra

set_option autoImplicit false










noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff BigOperators Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E



theorem scalar_joint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M => S.scalar p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
  classical
  intro p hp
  let x₀ : M := p.2
  let frame := coordinateFrameAt (I := I) x₀
  let t : D.RegularTime := ⟨p.1, hp.1⟩
  have hx : p.2 ∈ coordinateFrameSet (I := I) x₀ := by
    simpa only [x₀] using coordinateFrameAt_mem (I := I) p.2
  have hdomain :
      D.regular ×ˢ coordinateFrameSet (I := I) x₀ ∈ 𝓝 p :=
    prod_mem_nhds (D.regular_isOpen.mem_nhds hp.1)
      ((coordinateFrameSet_open (I := I) x₀).mem_nhds hx)
  have hmetric (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          metricCompInFrame (I := I) S frame q.1 q.2 i j) p := by
    simpa only [frame] using
      (coordMetricSmooth (I := I) S hS x₀ i j).contMDiffAt hdomain
  have hderiv (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          deriv (fun s : Real =>
            metricCompInFrame (I := I) S frame s q.2 i j) q.1) p := by
    exact timeDeriv_smoothAt (hmetric i j) (by simp)
  have hricci (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          ricciCompInFrame (I := I) S frame q.1 q.2 i j) p := by
    have hsmooth :
        ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
          (modelWithCornersSelf Real Real) ∞
          (fun q : Real × M => (-1 / 2 : Real) *
            deriv (fun s : Real =>
              metricCompInFrame (I := I) S frame s q.2 i j) q.1) p :=
      contMDiffAt_const.mul (hderiv i j)
    refine hsmooth.congr_of_eventuallyEq ?_
    filter_upwards [hdomain] with q hq
    have heq :=
      ((metricCompInFrame_hasDerivWithinAt
        (I := I) S hS frame
        (⟨q.1, hq.1⟩ : D.RegularTime) q.2 i j).hasDerivAt
          (D.regular_mem_nhds hq.1)).deriv
    rw [heq]
    ring
  have hinv (i j : CoordinateIdx (𝕜 := Real) E) :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M => coordInv (I := I) S x₀ q.1 q.2 i j) p := by
    simpa only [t] using
      coordInvSmoothAt (I := I) S hS x₀ t p.2 hx i j
  have htrace :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun q : Real × M =>
          ∑ i, ∑ j,
            coordInv (I := I) S x₀ q.1 q.2 i j *
              ricciCompInFrame (I := I) S frame q.1 q.2 i j) p := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (hinv i j).mul (hricci i j)
  refine (htrace.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hdomain] with q hq
  change S.scalar q.1 q.2 =
    scalarTraceInFrame (I := I) S (coordInv (I := I) S x₀)
      frame q.1 q.2
  symm
  rw [scalarTraceInFrame_eq_metricTracePair
    (I := I) S (coordInv (I := I) S x₀) frame
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
    (coordInvLocal (I := I) S x₀) q.1 hq.2]
  rw [SolutionOn.scalar_eq_metricTrace]
  simp only [SolutionOn.ricci, SolutionFamily.ricci_apply]
  rfl

end DifferentialGeometry.PDE.RicciFlow

end
