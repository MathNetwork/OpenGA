import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian

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




@[reducible] def PointedRiemannianManifold.emetricSpace
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) : EMetricSpace Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : Y.M => TangentSpace I x) :=
    ⟨⟨Y.metric.inner, Y.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
  exact EMetricSpace.ofRiemannianMetric I Y.M




@[reducible] def PointedRiemannianManifold.riemBundle
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  exact ⟨Y.metric.toRiemannianMetric⟩



@[reducible] def PointedRiemannianManifold.riemInner
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      Y.riemBundle (I := I)
    (x : Y.M) → InnerProductSpace Real (TangentSpace I x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    Y.riemBundle (I := I)
  exact fun _ => inferInstance



@[reducible] def PointedRiemannianManifold.riemBundle_cont
    {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      Y.riemBundle (I := I)
    IsContinuousRiemannianBundle E (fun x : Y.M => TangentSpace I x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    Y.riemBundle (I := I)
  exact ⟨⟨Y.metric.inner, Y.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩

end HCGCompactness
end DifferentialGeometry
