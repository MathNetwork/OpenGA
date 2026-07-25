import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.SolutionCompactnessInputs

set_option autoImplicit false
set_option linter.style.longLine false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]




theorem compactnessSol_cond
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (inp : MetricCompactnessInputs (I := I) (X.atZero (I := I)))
    (hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (hflowInj : FlowBaseInjBound (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace ((X.atZero (I := I)).obj k).M :=
        ((X.atZero (I := I)).obj k).topology
      ConnectedSpace ((X.atZero (I := I)).obj k).M)
    (hderiv : FlowDerivativeInput (I := I) X)
    (hflow : FlowUpgradeData (I := I) X
      (MetricCompactnessInputs.metricCompactness (I := I)
        inp hcomplete0 hderiv.at_zero_geom hflowInj hconn)) :
    CompactnessConclusion (I := I) X :=
  solutionComp_cond (I := I) X inp hcomplete0 hflowInj hconn hderiv hflow

end HCGCompactness
end DifferentialGeometry
