import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.ChartPartialUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentEuclid_eq_cutoff_mul_rawPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y =
      chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
        chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y := by
  classical
  rw [cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hy]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_rawPushed_eq_covDerivComponent_sub'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y =
      tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
              (chartBasisVecFiber (I := I) α k)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))
        - covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y := by
  have h := covDerivComponent_eq_euclidPartial_add_lowerOrder
    (I := I) (M := M) g r s S α k Idx Jdx hy
  linarith [h]

def cutoffLeibnizCrossTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯))) y *
      chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) y

def cutoffLowerOrderTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y : EuclN =>
    chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
      covDerivLowerOrderTerm (I := I) (M := M) g r s S α k Idx Jdx y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPushedRaw_cutoff_mul_raw_eq_cutoffComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
          (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) hy,
    cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffLowerOrderTerm_eq_linearCombination
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    cutoffLowerOrderTerm (I := I) (M := M) g r s S α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          cutoffComponentEuclid (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  unfold cutoffLowerOrderTerm
  rw [covDerivComponent_lowerOrder_eq_linearCombination
    (I := I) (M := M) g r s S α m Idx Jdx y, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← mul_assoc, mul_comm (chartPushedRaw (I := I) (M := M) α
        (⇑(chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯)) y)
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y),
    mul_assoc,
    chartPushedRaw_cutoff_mul_raw_eq_cutoffComponent (I := I) (M := M)
      g r s S α p.1 p.2 hy]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
