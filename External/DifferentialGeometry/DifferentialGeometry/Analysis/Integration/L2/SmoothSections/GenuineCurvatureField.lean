import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothCcTensor


def toFunAddHom {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    SmoothCcTensor g r s →+ (M → TensorRSModel r s ℝ E) where
  toFun := fun S => S.toFun
  map_zero' := SmoothCcTensor.toFun_zero
  map_add' := SmoothCcTensor.toFun_add


lemma toSection_sum {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) :
    (∑ i ∈ t, F i).toSection = ∑ i ∈ t, (F i).toSection :=
  map_sum (SmoothCcTensor.toSectionAddHom (I := I) (M := M) (g := g) (r := r) (s := s)) F t


lemma toFun_sum {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) :
    (∑ i ∈ t, F i).toFun = ∑ i ∈ t, (F i).toFun :=
  map_sum (SmoothCcTensor.toFunAddHom (I := I) (M := M) (g := g) (r := r) (s := s)) F t


lemma toSection_sum_apply {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) (x : M) :
    (∑ i ∈ t, F i).toSection x = ∑ i ∈ t, (F i).toSection x := by
  rw [toSection_sum]
  have hcoe : (⇑(∑ i ∈ t, (F i).toSection) :
        Π x : M, TensorRSSpace r s I x) =
      ∑ i ∈ t, (⇑((F i).toSection) : Π x : M, TensorRSSpace r s I x) :=
    map_sum (ContMDiffSection.coeAddHom I (TensorRSModel r s ℝ E) ∞
      (fun x : M => TensorRSSpace r s I x)) (fun i => (F i).toSection) t
  calc (∑ i ∈ t, (F i).toSection) x
      = (⇑(∑ i ∈ t, (F i).toSection) : Π x : M, TensorRSSpace r s I x) x := rfl
    _ = (∑ i ∈ t, (⇑((F i).toSection) : Π x : M, TensorRSSpace r s I x)) x := by rw [hcoe]
    _ = ∑ i ∈ t, (F i).toSection x := Finset.sum_apply x t _

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
