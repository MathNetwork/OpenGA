import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.InjectivityRadius

set_option autoImplicit false
set_option linter.style.longLine false




















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology ENNReal Bundle

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]







abbrev PointedSeqDistance
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Type _ :=
  forall k : Nat, (X.obj k).M -> (X.obj k).M -> Real







structure InjRadiusDecayInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  baseInj : BaseInjBound (I := I) X
  dist : PointedSeqDistance (I := I) X
  a : Real
  C : Real
  a_pos : 0 < a
  C_nonneg : 0 <= C
  decay :
    forall k : Nat, forall x : (X.obj k).M,
      HasInjRadiusAt (I := I) (X.obj k) x
        (a * (min baseInj.ρ 1) ^ Module.finrank Real E *
          Real.exp (-C * dist k x (X.obj k).basepoint))

namespace InjRadiusDecayInput


def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (f : Nat -> Nat) :
    InjRadiusDecayInput (I := I) (X.subseq f) where
  baseInj := hd.baseInj.subseq f
  dist := fun k x y => hd.dist (f k) x y
  a := hd.a
  C := hd.C
  a_pos := hd.a_pos
  C_nonneg := hd.C_nonneg
  decay := by
    intro k x
    simpa [PointedRiemannianSeq.subseq] using hd.decay (f k) x

end InjRadiusDecayInput


















structure VolumeComparisonInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  dist : PointedSeqDistance (I := I) X

  r0 : Real
  r0_pos : 0 < r0
  Imult : Real -> Nat



  ballMult :
    forall (m : Real), forall k : Nat, forall {α : Type u}, [Fintype α] -> [DecidableEq α] ->
      forall centers : α -> (X.obj k).M, forall r : Real, 0 < r -> m * r <= r0 ->
        (forall i j : α, i ≠ j ->
          r <= dist k (centers i) (centers j)) ->
        forall z : (X.obj k).M, forall J : Finset α,
          (forall j : α, j ∈ J ->
            dist k (centers j) z <= m * r) ->
          J.card <= Imult m

namespace VolumeComparisonInput


def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (vc : VolumeComparisonInput (I := I) X) (f : Nat -> Nat) :
    VolumeComparisonInput (I := I) (X.subseq f) where
  dist := fun k x y => vc.dist (f k) x y
  r0 := vc.r0
  r0_pos := vc.r0_pos
  Imult := vc.Imult
  ballMult := by
    intro m k α _ _ centers r hr hcap hsep z J hJz
    exact vc.ballMult m (f k) centers r hr hcap hsep z J hJz

end VolumeComparisonInput

end HCGCompactness
end DifferentialGeometry
