import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradChartIdentity

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem chartCovariantSecondGrad_eq
    (g : SmoothRiemannianMetric I M) (h : SmoothCcTensor g 0 2) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin (2 + 2) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g 0 (2 + 2)
        (iteratedCovGrad (I := I) g 0 2 2 h) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Jdx 0)
          (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 h) α Idx (Matrix.vecTail Jdx))) y
        + covDerivLowerOrderTerm (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 h) α (Jdx 0) Idx
            (Matrix.vecTail Jdx) y := by
  have hrec : iteratedCovGrad (I := I) g 0 2 2 h =
      covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 h) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hrec]
  exact tensorChartComponentRaw_covGrad (I := I) (M := M) g 0 3
    (covGrad (I := I) (M := M) g 0 2 h) α Idx Jdx hy

omit [NeZero (Module.finrank ℝ E)] in
theorem chartCovariantSecondGrad_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothCcTensor g 0 2) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Kdx : Fin 3 → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g 0 3
        (covGrad (I := I) (M := M) g 0 2 h) α Idx Kdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Kdx 0)
          (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 2
            h α Idx (Matrix.vecTail Kdx))) y
        + covDerivLowerOrderTerm (I := I) (M := M) g 0 2 h α (Kdx 0) Idx
            (Matrix.vecTail Kdx) y :=
  tensorChartComponentRaw_covGrad (I := I) (M := M) g 0 2 h α Idx Kdx hy

omit [NeZero (Module.finrank ℝ E)] in
theorem chartCovariantSecondGrad_chartHessian_sub_correction
    (g : SmoothRiemannianMetric I M) (h : SmoothCcTensor g 0 2) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin (2 + 2) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentRaw (I := I) (M := M) g 0 (2 + 2)
        (iteratedCovGrad (I := I) g 0 2 2 h) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      euclidPartial (E := E) (Jdx 0)
          (fun y' =>
            euclidPartial (E := E) ((Matrix.vecTail Jdx) 0)
                (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 2
                  h α Idx (Matrix.vecTail (Matrix.vecTail Jdx)))) y'
              + covDerivLowerOrderTerm (I := I) (M := M) g 0 2 h α
                  ((Matrix.vecTail Jdx) 0) Idx
                  (Matrix.vecTail (Matrix.vecTail Jdx)) y') y
        + covDerivLowerOrderTerm (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 h) α (Jdx 0) Idx
            (Matrix.vecTail Jdx) y := by
  rw [chartCovariantSecondGrad_eq (I := I) (M := M) g h α Idx Jdx hy]
  have hEqOn : Set.EqOn
      (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 3
        (covGrad (I := I) (M := M) g 0 2 h) α Idx (Matrix.vecTail Jdx)))
      (fun y' =>
        euclidPartial (E := E) ((Matrix.vecTail Jdx) 0)
            (chartPushedRaw I α (tensorChartComponentRaw (I := I) (M := M) g 0 2
              h α Idx (Matrix.vecTail (Matrix.vecTail Jdx)))) y'
          + covDerivLowerOrderTerm (I := I) (M := M) g 0 2 h α
              ((Matrix.vecTail Jdx) 0) Idx
              (Matrix.vecTail (Matrix.vecTail Jdx)) y')
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro y' hy'
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy']
    exact chartCovariantSecondGrad_inner (I := I) (M := M) g h α Idx
      (Matrix.vecTail Jdx) hy'
  have hEv := Filter.eventuallyEq_of_mem
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy) hEqOn
  congr 1
  rw [euclidPartial_def, euclidPartial_def, hEv.fderiv_eq]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
