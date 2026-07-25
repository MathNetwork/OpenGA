import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothChartComponent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorSmooth_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) =
      tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i :=
  tensorL2_eq_of_chartComponent_eq (I := I) (M := M) g r s
    (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g)
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    (fun β P₀ => eigenvectorSmooth_tensorL2ChartComponent_eq
      (I := I) (M := M) g r s i β P₀)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem tensorEigenvector_exists_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∃ T : SmoothCcTensor g r s,
      (T : TensorL2 r s g) =
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i :=
  ⟨eigenvectorSmooth (I := I) (M := M) g r s i,
    eigenvectorSmooth_toL2 (I := I) (M := M) g r s i⟩

omit [CompleteSpace E] in
theorem eigenvectorSmooth_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        TotalSpace.mk' (TensorRSModel r s ℝ E) x
          ((eigenvectorSmooth (I := I) (M := M) g r s i).toSection x)) :=
  (eigenvectorSmooth (I := I) (M := M) g r s i).toSection.contMDiff

omit [CompleteSpace E] in
theorem eigenvectorSmooth_weak_eigen
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S : SmoothCcTensorH1 g r s) :
    ⟪eigenvectorResolvent (I := I) (M := M) g r s i,
        (smoothToTensorH1Compl (I := I) (M := M) g r s S)⟫_ℝ =
      ⟪(S.toCcTensor : TensorL2 r s g),
        (eigenvectorSmooth (I := I) (M := M) g r s i :
          TensorL2 r s g)⟫_ℝ := by
  rw [eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]
  exact eigenWeakEquation (I := I) (M := M) g r s i S

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
