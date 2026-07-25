import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Analysis.Integration.Measure.RealizedMetricForMeasure
import DifferentialGeometry.Geometry.Metric.DistanceScaling

set_option autoImplicit false
set_option linter.style.longLine false











namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

universe u uE uH

open Bundle Tensor0SBundle MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}






structure FlowMetricBall (S : SolutionOn (I := I) (M := M) D)
    (time : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) where
  center : M
  radius : Real
  radius_pos : 0 < radius

namespace FlowMetricBall

variable {S : SolutionOn (I := I) (M := M) D}
variable {time : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D}



def setAt (B : FlowMetricBall S time) (t : Real) : Set M :=
  {x : M | DifferentialGeometry.riemannianEDistOf
    (I := I) (S.base.metric t) B.center x < ENNReal.ofReal B.radius}


def set (B : FlowMetricBall S time) : Set M :=
  B.setAt (time : Real)


def volume (B : FlowMetricBall S time) : ℝ≥0∞ :=
  DifferentialGeometry.Integral.Measure.volumeMeasureOn
    (I := I) (M := M) S.family time B.set


def rmNormSq (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) : Real :=
  Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)




def IsRmControlled (B : FlowMetricBall S time) : Prop :=
  Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.carrier ∧
    ∀ t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real), ∀ x ∈ B.setAt t,
      B.radius ^ 4 * rmNormSq S t x ≤ 1



def IsKappaNoncollapsed (kappa : Real) (B : FlowMetricBall S time) : Prop :=
  0 < kappa ∧
    ENNReal.ofReal kappa * ENNReal.ofReal B.radius ^ Module.finrank Real E ≤ B.volume


def Nested (small large : FlowMetricBall S time) : Prop :=
  small.set ⊆ large.set


theorem volume_mono {small large : FlowMetricBall S time} (h : small.Nested large) :
    small.volume ≤ large.volume := by
  unfold volume
  exact measure_mono h

end FlowMetricBall



def KappaNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) (kappa rho : Real) : Prop :=
  0 < rho ∧ ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D)
    (B : FlowMetricBall S t), B.radius ≤ rho →
    B.IsRmControlled → B.IsKappaNoncollapsed kappa



def NoLocalCollapsing
    (S : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  ∃ kappa : Real, 0 < kappa ∧ KappaNoncollapsedBelowScale S kappa rho

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
