import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic

set_option autoImplicit false
set_option linter.style.longLine false












noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}






structure PointedFlowData
    (I : ModelWithCorners Real E H) (D : DifferentialGeometry.Integral.Connection.RealTimeInterval) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace H M]
  [smooth : IsManifold I ∞ M]
  [sigmaCompact : SigmaCompactSpace M]
  [t2 : T2Space M]
  [t2TangentBundle : T2Space (TangentBundle I M)]
  basepoint : M
  S :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D
  isSolution :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S

namespace PointedFlowData

variable {I : ModelWithCorners Real E H}
variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}



def atTime (F : PointedFlowData.{u, uE, uH} (I := I) D) (t : Real) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := F.M
  topology := F.topology
  charted := F.charted
  smooth := F.smooth
  sigmaCompact := F.sigmaCompact
  t2 := F.t2
  t2TangentBundle := F.t2TangentBundle
  basepoint := F.basepoint
  metric := by
    letI : TopologicalSpace F.M := F.topology
    letI : ChartedSpace H F.M := F.charted
    letI : IsManifold I ∞ F.M := F.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
      change IsManifold I ∞ F.M
      infer_instance
    letI : SigmaCompactSpace F.M := F.sigmaCompact
    letI : T2Space F.M := F.t2
    exact F.S.family.metric t


def rmNormSq (F : PointedFlowData (I := I) D) (t : Real) (x : F.M) : Real :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  Tensor0SBundle.normSq0S (I := I) (F.S.family.metric t) x 4
    (F.S.base.rm04 t x)

end PointedFlowData



structure PointedFlowSeq (I : ModelWithCorners Real E H) where
  D : DifferentialGeometry.Integral.Connection.RealTimeInterval
  term : Nat -> PointedFlowData.{u, uE, uH} (I := I) D

namespace PointedFlowSeq

variable {I : ModelWithCorners Real E H}


def basepoint (X : PointedFlowSeq.{u, uE, uH} (I := I)) (i : Nat) :
    (X.term i).M :=
  (X.term i).basepoint


def atTime (X : PointedFlowSeq.{u, uE, uH} (I := I)) (t : Real) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := fun i => (X.term i).atTime (I := I) t



def atZero (X : PointedFlowSeq.{u, uE, uH} (I := I)) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) :=
  X.atTime (I := I) 0

end PointedFlowSeq



structure CompleteInput {I : ModelWithCorners Real E H}
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  complete_on :
    forall i : Nat, forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) ((X.term i).atTime (I := I) t)




structure CurvBoundInput {I : ModelWithCorners Real E H}
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop where
  bound_on_window :
    forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
      exists C : Real, 0 <= C /\
        forall i : Nat, forall t : Real, t ∈ Set.Icc a b ->
          forall x : (X.term i).M,
            (X.term i).rmNormSq (I := I) t x <= C







structure InjInput {I : ModelWithCorners Real E H}
    (_X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  injRadiusAtBase : Nat -> Real
  iota : Real
  iota_pos : 0 < iota
  inj_lower : forall i : Nat, iota <= injRadiusAtBase i

end HCGCompactness
end DifferentialGeometry
