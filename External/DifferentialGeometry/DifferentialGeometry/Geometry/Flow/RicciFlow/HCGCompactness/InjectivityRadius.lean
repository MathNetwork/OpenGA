import DifferentialGeometry.Geometry.Comparison.InjectivityRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Basic

set_option autoImplicit false
set_option linter.style.longLine false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]










def HasInjRadiusAt
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  0 < rho ∧
    ENNReal.ofReal rho ≤ Geometry.Riemannian.injRadius (I := I) X.metric x



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hasInjRadiusAt_iff
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) :
    HasInjRadiusAt (I := I) X x rho ↔
      (letI : TopologicalSpace X.M := X.topology
       letI : ChartedSpace H X.M := X.charted
       letI : IsManifold I ∞ X.M := X.smooth
       letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
       0 < rho ∧
         ENNReal.ofReal rho ≤ Geometry.Riemannian.injRadius (I := I) X.metric x) :=
  Iff.rfl



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem hasInjRadiusAt_of_le_injRadius
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho : Real} (hpos : 0 < rho)
    (h :
      letI : TopologicalSpace X.M := X.topology
      letI : ChartedSpace H X.M := X.charted
      letI : IsManifold I ∞ X.M := X.smooth
      letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
      ENNReal.ofReal rho ≤ Geometry.Riemannian.injRadius (I := I) X.metric x) :
    HasInjRadiusAt (I := I) X x rho :=
  ⟨hpos, h⟩


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem HasInjRadiusAt.mono
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho rho' : Real} (h : HasInjRadiusAt (I := I) X x rho)
    (hpos : 0 < rho') (hle : rho' <= rho) :
    HasInjRadiusAt (I := I) X x rho' := by
  rw [hasInjRadiusAt_iff] at h ⊢
  exact ⟨hpos, (ENNReal.ofReal_le_ofReal hle).trans h.2⟩



structure BaseInjBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  ρ : Real
  pos : 0 < ρ
  bound : forall i : Nat, HasInjRadiusAt (I := I) (X.obj i) (X.obj i).basepoint ρ

namespace BaseInjBound


def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : BaseInjBound (I := I) X) (f : Nat -> Nat) :
    BaseInjBound (I := I) (X.subseq f) where
  ρ := h.ρ
  pos := h.pos
  bound := by
    intro i
    simpa [PointedRiemannianSeq.subseq] using h.bound (f i)

end BaseInjBound


abbrev FlowBaseInjBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) :=
  BaseInjBound (I := I) (X.atZero (I := I))

end HCGCompactness
end DifferentialGeometry
