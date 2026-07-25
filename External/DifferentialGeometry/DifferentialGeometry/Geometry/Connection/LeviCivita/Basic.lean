import DifferentialGeometry.Geometry.Connection.MetricCompatibility
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import DifferentialGeometry.Geometry.Connection.LeviCivita.MetricCompatible

set_option autoImplicit false
set_option linter.style.longLine false









namespace DifferentialGeometry.Integral.Connection

open Bundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Pointwise

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]

def IsTorsionFreeAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) : Prop :=
  cov.torsion x = 0


def IsLeviCivitaAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  IsMetricCompatibleAt_gen (I := I) cov g x /\ IsTorsionFreeAt (I := I) cov x

def IsTorsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) : Prop :=
  forall x : M, IsTorsionFreeAt (I := I) cov x


def IsLeviCivita
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  IsMetricCompatible_gen (I := I) cov g /\ IsTorsionFree (I := I) cov

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCompatible_of_isLeviCivita
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (h : IsLeviCivita (I := I) cov g) :
    IsMetricCompatible_gen (I := I) cov g :=
  h.1

omit [SigmaCompactSpace M] [T2Space M] in
theorem torsionFree_of_isLeviCivita
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (h : IsLeviCivita (I := I) cov g) :
    IsTorsionFree (I := I) cov :=
  h.2

omit [SigmaCompactSpace M] [T2Space M] in
theorem isLeviCivita_of_parts
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hmc : IsMetricCompatible_gen (I := I) cov g)
    (htf : IsTorsionFree (I := I) cov) :
    IsLeviCivita (I := I) cov g :=
  ⟨hmc, htf⟩

end Pointwise

section Family

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]


def IsTorsionFreeFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D,
    IsTorsionFree (I := I) (G.connectionAt t)


def IsLeviCivitaFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  IsMetricCompatibleFamilyOn (I := I) G /\ IsTorsionFreeFamilyOn (I := I) G


structure LeviCivitaCalculusOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop where
  metricCompatible : IsMetricCompatibleFamilyOn (I := I) G
  torsionFree : IsTorsionFreeFamilyOn (I := I) G

omit [SigmaCompactSpace M] [T2Space M] in
theorem isLeviCivitaFamilyOn_of_calculus
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : LeviCivitaCalculusOn (I := I) G) :
    IsLeviCivitaFamilyOn (I := I) G :=
  ⟨hG.metricCompatible, hG.torsionFree⟩

end Family

end DifferentialGeometry.Integral.Connection
