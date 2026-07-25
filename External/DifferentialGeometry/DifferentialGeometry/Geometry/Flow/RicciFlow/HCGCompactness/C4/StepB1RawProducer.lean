import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageFill

set_option autoImplicit false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]





theorem MetricCompactBase.exists_b1_raw
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j) :=
      fun j => properMetricOn (I := I) (X.obj j)
        (hcomplete.complete j) (hconn j)
    ∃ psi : Nat → Nat, StrictMono psi ∧
      let Xpsi := X.subseq psi
      let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) (Xpsi.obj k) :=
        fun k => P (psi k)
      StepB1RawInput (I := I) (X := Xpsi) Ppsi := by
  classical
  dsimp only



  sorry

end HCGCompactness
end DifferentialGeometry
