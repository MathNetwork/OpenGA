import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.InjectivityRadius

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
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace PointedFlowData



def baseFlowBall
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (hzero : 0 ∈ D.carrier) (r : Real) (hr : 0 < r) :
    letI : TopologicalSpace F.M := F.topology
    letI : ChartedSpace H F.M := F.charted
    letI : IsManifold I ∞ F.M := F.smooth
    letI : IsManifold I 1 F.M :=
      IsManifold.of_le (I := I) (M := F.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
      change IsManifold I ∞ F.M
      infer_instance
    letI : SigmaCompactSpace F.M := F.sigmaCompact
    letI : T2Space F.M := F.t2
    DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall
      F.S ⟨0, hzero⟩ := by
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I 1 F.M :=
    IsManifold.of_le (I := I) (M := F.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  exact { center := F.basepoint, radius := r, radius_pos := hr }

end PointedFlowData




structure FlowBaseVolData
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  zero_mem : 0 ∈ X.D.carrier
  kappa : Real
  kappa_pos : 0 < kappa
  radius : Real
  radius_pos : 0 < radius



structure IsFlowBaseVolBound
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (V : FlowBaseVolData (I := I) X) : Prop where
  curvature : ∀ i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (PointedFlowData.baseFlowBall (I := I) (X.term i)
      V.zero_mem V.radius V.radius_pos).IsRmControlled
  noncollapsed : ∀ i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (PointedFlowData.baseFlowBall (I := I) (X.term i)
      V.zero_mem V.radius V.radius_pos).IsKappaNoncollapsed V.kappa





noncomputable def flowInj_of_vol
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (V : FlowBaseVolData (I := I) X)
    (hvol : IsFlowBaseVolBound (I := I) V) :
    FlowBaseInjBound (I := I) X := by
  sorry

end HCGCompactness
end DifferentialGeometry
