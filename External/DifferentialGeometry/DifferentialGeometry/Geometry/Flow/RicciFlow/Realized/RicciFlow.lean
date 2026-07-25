import DifferentialGeometry.Geometry.Connection.Smoothness
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
set_option linter.style.longLine false








namespace DifferentialGeometry.Integral.Connection

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {A Time : Type*} [CommRing A] [Algebra Real A]





abbrev RicciTensorField (Time : Type*) :=
  Time -> (x : M) -> TangentSpace I x -> TangentSpace I x -> Real




def MetricVariationEquation
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (Ric : RicciTensorField (I := I) (M := M) Time) : Prop :=
  forall (t : Time) (x : M) (X Y : TangentSpace I x),
    metricTimeDerivative td G t x X Y = (-2 : Real) * Ric t x X Y


theorem metric_dt_eq_neg_two_ricci_of_metricVariationEquation
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (Ric : RicciTensorField (I := I) (M := M) Time)
    (hEq : MetricVariationEquation td G Ric)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td G t x X Y = (-2 : Real) * Ric t x X Y :=
  hEq t x X Y





def MetricVariationEquationDerivAt
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciTensorField (I := I) (M := M) Real) (t : Real) : Prop :=
  forall (x : M) (X Y : TangentSpace I x),
    HasDerivAt
      (fun s : Real => (G.metric s).inner x X Y)
      ((-2 : Real) * Ric t x X Y)
      t



theorem metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciTensorField (I := I) (M := M) Real) {t : Real}
    (hEq : MetricVariationEquationDerivAt (I := I) G Ric t)
    (x : M) (X Y : TangentSpace I x) :
    deriv (fun s : Real => (G.metric s).inner x X Y) t =
      (-2 : Real) * Ric t x X Y :=
  (hEq x X Y).deriv





structure RealizedRicciFlowData where
  family : RealizedMetricFamily (I := I) (M := M) Time



def IsRealizedRicciFlow
    (td : TimeDerivativeData Real A Time)
    (S : RealizedRicciFlowData (I := I) (M := M) (Time := Time))
    (Ric : RicciTensorField (I := I) (M := M) Time) : Prop :=
  MetricVariationEquation td S.family Ric

theorem metric_dt_eq_neg_two_ricci_of_isRealizedRicciFlow
    (td : TimeDerivativeData Real A Time)
    (S : RealizedRicciFlowData (I := I) (M := M) (Time := Time))
    (Ric : RicciTensorField (I := I) (M := M) Time)
    (hS : IsRealizedRicciFlow td S Ric)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td S.family t x X Y = (-2 : Real) * Ric t x X Y :=
  metric_dt_eq_neg_two_ricci_of_metricVariationEquation td S.family Ric hS t x X Y

section Interval

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]
variable [IsManifold I 1 M]





def MetricVariationEquationOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (Ric : RicciTensorField (I := I) (M := M) Real) : Prop :=
  forall (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x),
    HasDerivWithinAt
      (fun s : Real => (G.metric s).inner x X Y)
      ((-2 : Real) * Ric (t : Real) x X Y)
      D.carrier
      (t : Real)


structure RealizedRicciFlowCandidateOn (D : RealTimeInterval) where
  family : RealizedMetricFamilyOn (I := I) (M := M) D
  ricci : RicciTensorField (I := I) (M := M) Real




structure IsRealizedRicciFlowSolutionOn
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D) : Prop where
  smoothMetric : MetricFamilySmoothOn (I := I) (M := M) D S.family
  smoothConnection : DifferentialGeometry.Integral.Connection.ConnectionFamilySmoothOn (I := I) (M := M) S.family
  leviCivita : DifferentialGeometry.Integral.Connection.IsLeviCivitaFamilyOn (I := I) S.family
  equation : MetricVariationEquationOn (I := I) S.family S.ricci



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] in
theorem metric_derivWithin_eq_neg_two_ricci_of_metricVariationEquationOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (Ric : RicciTensorField (I := I) (M := M) Real)
    (hEq : MetricVariationEquationOn (I := I) G Ric)
    (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (G.metric s).inner x X Y)
      ((-2 : Real) * Ric (t : Real) x X Y)
      D.carrier
      (t : Real) :=
  hEq t x X Y



omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] in
theorem metric_derivWithin_eq_neg_two_ricci_of_isRealizedRicciFlowSolutionOn
    {D : RealTimeInterval}
    (S : RealizedRicciFlowCandidateOn (I := I) (M := M) D)
    (hS : IsRealizedRicciFlowSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.ricci (t : Real) x X Y)
      D.carrier
      (t : Real) :=
  hS.equation t x X Y

end Interval

end DifferentialGeometry.Integral.Connection
