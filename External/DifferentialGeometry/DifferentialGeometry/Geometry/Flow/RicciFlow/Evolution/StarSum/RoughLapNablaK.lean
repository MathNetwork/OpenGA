import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridgeAllK
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTraceGen

set_option autoImplicit false
set_option linter.style.longLine false






















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
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
omit [SigmaCompactSpace M] in
theorem nabla_roughLap0S_nablaKRm
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric t) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t)
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
          (nablaKRm04Field (I := I) S t (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          nablaKRm04Field (I := I) S t (k + 3) x
            (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (1 : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) (S.base.metric t)
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection t) (S.base.metric t) := by
    simpa [SolutionFamily.connection, metricCov] using
      leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (S.base.metric t)
  refine (nabla_metricTraceFirstTwo0S (I := I) (M := M) (S.family.connection t) hcov
    (S.base.metric t) hmc (nablaKRm04Field (I := I) S t (k + 2)) basis gInv hinv X
    tail).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1















omit [Module.Finite ℝ E] in
omit [SigmaCompactSpace M] in
theorem spatialComm_nablaKRm_traceDiff
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric t) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) (S.base.metric t)
        (nablaKRm04Field (I := I) S t (k + 3) x)
        (Fin.cons X tail) -
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t)
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
          (nablaKRm04Field (I := I) S t (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (nablaKRm04Field (I := I) S t (k + 3) x
              (metricTraceInput (I := I) (basis i) (basis j) (Fin.cons X tail)) -
            nablaKRm04Field (I := I) S t (k + 3) x
              (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail))) := by
  rw [metricTraceFirstTwo0STensor_apply (I := I) (S.base.metric t)
    (nablaKRm04Field (I := I) S t (k + 3) x) (Fin.cons X tail)]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) (S.base.metric t) basis gInv hinv
    (nablaKRm04Field (I := I) S t (k + 3) x) (Fin.cons X tail)]
  rw [metricTrace0S2InBasis]
  rw [nabla_roughLap0S_nablaKRm (I := I) (M := M) S t k basis gInv hinv X tail]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_sub]













omit [Module.Finite ℝ E] in
omit [SigmaCompactSpace M] in
theorem spatialComm_nablaKRm_split
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric (t : Real)) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) (S.base.metric (t : Real))
        (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
        (Fin.cons X tail) -
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection (t : Real))
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric (t : Real))
          (nablaKRm04Field (I := I) S (t : Real) (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          ((nablaKRm04Field (I := I) S (t : Real) (k + 3) x
                (metricTraceInput (I := I) (basis i) (basis j) (Fin.cons X tail)) -
              nablaKRm04Field (I := I) S (t : Real) (k + 3) x
                (metricTraceInput (I := I) (basis i) X (Fin.cons (basis j) tail))) +
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
              (nablaKRm04Field (I := I) S (t : Real) (k + 1) x)
              (basis i) X (Fin.cons (basis j) tail)) := by
  rw [spatialComm_nablaKRm_traceDiff (I := I) S (t : Real) k basis gInv hinv X tail]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := (nablaKRm04_ricciIdentityAt (I := I) S hS t (k + 1) x)
    (basis i) X (Fin.cons (basis j) tail)
  have hCC :
      (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
          (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) =
        (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
          (metricTraceInput (I := I) X (basis i) (Fin.cons (basis j) tail)) := rfl
  rw [hCC]
  linarith [h]

end DifferentialGeometry.PDE.RicciFlow
