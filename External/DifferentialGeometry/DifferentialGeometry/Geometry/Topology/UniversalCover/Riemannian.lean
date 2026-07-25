import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Topology.UniversalCover.Manifold
import DifferentialGeometry.Geometry.Topology.UniversalCover.LiftedMetricSmoothness
import Mathlib.Topology.VectorBundle.Riemannian



































open Set Function Filter Bundle
open scoped Topology ContDiff
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric)

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]














noncomputable def liftedMetric (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  inner x' := g.inner (proj x')
  symm x' v w := g.symm (proj x') v w
  pos x' v hv := g.pos (proj x') v hv
  isVonNBounded x' := g.isVonNBounded (proj x')
  contMDiff := uc_liftedMetric_contMDiff (I := I) (M := M) g

















@[reducible] noncomputable def uc_pseudoEMetricSpace
    (g : SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
    [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)] :
    PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  letI : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  PseudoEMetricSpace.ofRiemannianMetric I _









omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem isRiemannianManifold
    (g : SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
    [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)] :
    letI : RiemannianBundle
        (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
      uc_pseudoEMetricSpace (I := I) (M := M) g
    IsRiemannianManifold I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  letI : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) g
  exact ⟨fun _ _ => rfl⟩





















omit [InnerProductSpace ℝ E] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem uc_regularSpace (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  infer_instance










omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [ConnectedSpace M] in
theorem liftedMetric_inner_eq (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ∀ (v w : E),
      g.inner (proj x') v w =
        (liftedMetric (I := I) g).inner x' v w :=
  fun _ _ => rfl

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
