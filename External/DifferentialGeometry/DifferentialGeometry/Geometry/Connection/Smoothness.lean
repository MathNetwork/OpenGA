import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily

set_option autoImplicit false
set_option linter.style.longLine false










namespace DifferentialGeometry.Integral.Connection

open Bundle
open CovariantDerivative
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

section Smoothness

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]




def ConnectionFamilySmooth
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time, ContMDiffCovariantDerivative (G.connection t) ∞


theorem connection_smooth_at_of_connectionFamilySmooth
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hG : ConnectionFamilySmooth G) (t : Time) :
    ContMDiffCovariantDerivative (G.connection t) ∞ :=
  hG t


def ConnectionFamilySmoothOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D, ContMDiffCovariantDerivative (G.connectionAt t) ∞


theorem connection_smooth_at_of_connectionFamilySmoothOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : ConnectionFamilySmoothOn (I := I) (M := M) G)
    (t : RealTimeInterval.FlowTime D) :
    ContMDiffCovariantDerivative (G.connectionAt t) ∞ :=
  hG t

end Smoothness

end DifferentialGeometry.Integral.Connection
