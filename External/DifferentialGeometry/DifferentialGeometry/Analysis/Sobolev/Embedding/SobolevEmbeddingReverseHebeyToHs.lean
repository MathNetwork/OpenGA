import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebey
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
theorem exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k T‖ ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            tensorL2Norm (I := I) (M := M) g r (s + j)
              (iteratedCovGrad g r s j T).toFun := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g r s k
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq]
  exact hC T

end DifferentialGeometry.PDE.RicciFlow

end
