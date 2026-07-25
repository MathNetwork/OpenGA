import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


omit [NeZero (Module.finrank ℝ E)] in
theorem smoothCcTensor_denseRange_toHs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    DenseRange
      (SmoothCcTensor.toHs (g := g) (r := r) (s := s) (k := k)) := by
  have hwrap_surj :
      Function.Surjective
        (fun T : SmoothCcTensor g r s =>
          (⟨T⟩ : SmoothCcTensorHs g r s k)) := by
    intro S; exact ⟨S.toCcTensor, by cases S; rfl⟩
  have hcoe :
      DenseRange
        (fun S : SmoothCcTensorHs g r s k =>
          (S : TensorPouSobolevHilbert g r s k)) :=
    UniformSpace.Completion.denseRange_coe
  have hcont :
      Continuous
        (fun S : SmoothCcTensorHs g r s k =>
          (S : TensorPouSobolevHilbert g r s k)) :=
    UniformSpace.Completion.continuous_coe _
  have hfun :
      (SmoothCcTensor.toHs (g := g) (r := r) (s := s) (k := k)) =
        (fun S : SmoothCcTensorHs g r s k =>
            (S : TensorPouSobolevHilbert g r s k)) ∘
          (fun T : SmoothCcTensor g r s =>
            (⟨T⟩ : SmoothCcTensorHs g r s k)) := by
    funext T; rfl
  rw [hfun]
  exact hcoe.comp (hwrap_surj.denseRange) hcont

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
