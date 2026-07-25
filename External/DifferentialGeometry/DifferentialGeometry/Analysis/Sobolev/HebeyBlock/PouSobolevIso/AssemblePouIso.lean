import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.ChartFrameNorm
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.GramTwist
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCkBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.NablaTensorFormula
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.IteratedNabla
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.UniformChartBounds
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.PouNormChartComp
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem assemble_pou_h1_iso_intrinsic_h1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
  obtain ⟨c₁, C₁, hc₁_pos, hc₁_le_C₁, h₁⟩ :=
    iterated_nabla_vs_iterated_partial_equivalence_H1
      (I := I) (M := M) g r s 1
  obtain ⟨c₀, C₀, hc₀_pos, hc₀_le_C₀, h₀⟩ :=
    pou_weighted_norm_equals_chart_component_norm_up_to_constant
      (I := I) (M := M) g r s
  refine ⟨min c₀ c₁, max C₀ C₁, lt_min hc₀_pos hc₁_pos, ?_, ?_⟩
  · exact (min_le_right c₀ c₁).trans (hc₁_le_C₁.trans (le_max_right C₀ C₁))
  · intro T
    obtain ⟨h_low, h_up⟩ := h₁ T
    refine ⟨?_, ?_⟩
    · have h_norm_op_nn :
          (0 : ℝ) ≤ (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
        ENNReal.toReal_nonneg
      calc
        min c₀ c₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal
            ≤ c₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
              exact mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) h_norm_op_nn
        _ ≤ (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal := h_low
    · have h_norm_op_nn :
          (0 : ℝ) ≤ (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal :=
        ENNReal.toReal_nonneg
      calc
        (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal
            ≤ C₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := h_up
        _ ≤ max C₀ C₁ * (tensorPouSobolevNorm (I := I) (M := M) g 1 T).toReal := by
              exact mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) h_norm_op_nn

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
