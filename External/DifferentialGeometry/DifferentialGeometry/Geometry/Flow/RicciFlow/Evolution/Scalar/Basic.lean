import DifferentialGeometry.Geometry.Curvature.Contractions
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option linter.style.longLine false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

def ScalarPreBianchiEvolutionEquationOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x +
        2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)



def ScalarContractedBianchiReductionOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x =
      scalarLap (t : Real) x



def ScalarSecondDerivativeContractedBianchiOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    contractedRicciHessian (t : Real) x =
      (1 / 2 : Real) * scalarLap (t : Real) x



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real)
    (hbianchi : ScalarSecondDerivativeContractedBianchiOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian := by
  intro t x
  rw [hbianchi t x]
  ring





omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem scalarEvolutionEquationOn_of_contractedBianchi
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq := by
  intro t x
  exact (hpre t x).congr_deriv (by
    rw [hbianchi t x])



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem msm110_ch6_1_scalar_curvature_evolution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq :=
  scalarEvolutionEquationOn_of_contractedBianchi
    (M := M) scalar scalarLap contractedRicciHessian ricciNormSq hpre hbianchi








theorem scalarEvolOfSmooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hmetric : ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      G.metric (t : Real) = S.family.metric (t : Real))
    (hconnection : ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      G.connection (t : Real) = S.family.connection (t : Real)) :
    ScalarEvolutionEquationOn (D := D)
      S.scalar
      (fun t x => DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (S.scalar t) x)
      (fun t x =>
        normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)) := by
  intro t x
  exact hS.scalarEvolution G hmetric hconnection t x





def ScalarLaplacianRealizesHeatOperatorOn
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (scalar scalarLap : Real -> M -> Real) : Prop :=
  forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
    scalarLap t x =
      DifferentialGeometry.Integral.Connection.heatOperator (I := I) G t (scalar t) x

namespace ScalarLaplacianRealizesHeatOperatorOn

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem zero_drift
    {G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real}
    {T : Real} {scalar scalarLap : Real -> M -> Real}
    (h : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      scalarLap t x =
        DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
          (fun y : M => (0 : TangentSpace I y)) (scalar t) x := by
  intro t ht x
  calc
    scalarLap t x = DifferentialGeometry.Integral.Connection.heatOperator (I := I) G t (scalar t) x := h t ht x
    _ = DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
          (fun y : M => (0 : TangentSpace I y)) (scalar t) x := by
        rw [DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_zero_drift]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem of_laplacianAt
    {G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real}
    {T : Real} {scalar scalarLap : Real -> M -> Real}
    (h : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      scalarLap t x = DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (scalar t) x) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap := by
  intro t ht x
  simpa [DifferentialGeometry.Integral.Connection.heatOperator] using h t ht x

end ScalarLaplacianRealizesHeatOperatorOn

end DifferentialGeometry.PDE.RicciFlow
