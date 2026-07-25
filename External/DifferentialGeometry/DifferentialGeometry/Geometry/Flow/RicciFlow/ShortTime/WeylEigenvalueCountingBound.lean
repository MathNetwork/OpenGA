import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralDiagonalCounting
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize





























namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


































theorem weyl_pointwise_diagonalKernel_bound_of_closed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (∃ (q : ℕ) (B : ℝ), 0 ≤ B ∧
      ∃ count : ℝ → Finset
          (Analysis.Parabolic.TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
        (∀ (Λ : ℝ)
            (i : Analysis.Parabolic.TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
          1 + Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) i < Λ → i ∈ count Λ) ∧
        (∀ (Λ : ℝ) (x : M),
          diagonalKernel (I := I) (M := M) g r s (count Λ) x ≤ B * Λ ^ q)) ∧
    (∀ (a : ℕ), 2 * a > Module.finrank ℝ E + 4 →
      (∀ (x : M) (v w : TangentSpace I x),
        Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g 0 2 =>
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
            (ccTensorBilinSymm (I := I) g
                (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w *
              (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) ^ 2)) ∧
      (∀ (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x),
        HasSum
          (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2 =>
            tensorL2Coeff (I := I) (M := M)
                (hCompact (I := I) (M := M) g) (SmoothCcTensor.toL2 T) i *
              ccTensorBilinSymm (I := I) g
                (eigenvectorSmooth (I := I) (M := M) g 0 2 i) x v w)
          (ccTensorBilinSymm (I := I) g T x v w))) := sorry









theorem weyl_eigenvalue_counting_bound_of_closed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    EigenvalueCountingBound (I := I) (M := M) g r s := by
  obtain ⟨⟨q, B, hB, count, hmem, hkernel⟩, _⟩ :=
    weyl_pointwise_diagonalKernel_bound_of_closed (I := I) (M := M) g r s
  exact eigenvalueCountingBound_of_pointwiseDiagonalKernelBound
    (I := I) (M := M) g r s q B hB count hmem hkernel

end DifferentialGeometry.PDE.RicciFlow
