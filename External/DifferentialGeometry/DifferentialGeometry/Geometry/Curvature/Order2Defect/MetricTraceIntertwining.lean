import DifferentialGeometry.Geometry.Curvature.Order2Defect.GradientSlotLeibniz

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] [I.Boundaryless] in
theorem metricTrace2_covDeriv_comm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) (w : TangentSpace I x) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
          (fun z : M => T.toSection z) y) x w =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => T.toSection z) y) x w := by
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  rw [show (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
        (fun z : M => T.toSection z) y) =
      (fun y : M => rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y) from by
    funext y
    exact (rawTensorConnLap_eq_metricTrace2 (I := I) g r s
      (fun z : M => T.toSection z) y).symm]
  exact covDeriv_rawConnLap_eq_frozenFrameTrace_sum (I := I) g r s hT x w

omit [CompactSpace M] [I.Boundaryless] in
theorem metricTrace2_covDeriv_comm_map
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
          (fun z : M => T.toSection z) y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => T.toSection z) y) x := by
  refine ContinuousLinearMap.ext (fun w => ?_)
  rw [ContinuousLinearMap.sum_apply]
  exact metricTrace2_covDeriv_comm (I := I) g r s T x w

end Connection
end Integral
end DifferentialGeometry

end
