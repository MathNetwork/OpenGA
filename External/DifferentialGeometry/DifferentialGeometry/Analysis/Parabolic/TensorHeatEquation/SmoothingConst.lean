import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs

noncomputable section

namespace DifferentialGeometry
namespace Analysis
namespace SpectralBounds

noncomputable def spectralSmoothingConst (μ : ℝ) : ℝ :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSmoothingConst μ

lemma one_le_spectralSmoothingConst (μ : ℝ) : 1 ≤ spectralSmoothingConst μ :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.one_le_tensorSmoothingConst μ

lemma spectralSmoothingConst_pos (μ : ℝ) : 0 < spectralSmoothingConst μ :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSmoothingConst_pos μ

lemma spectralSmoothingConst_nonneg (μ : ℝ) : 0 ≤ spectralSmoothingConst μ :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSmoothingConst_nonneg μ

theorem spectralSmoothingScalarBound {μ : ℝ} (hμ : 0 ≤ μ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    (1 + lam) ^ μ * Real.exp (-(2 * lam * t)) ≤
      spectralSmoothingConst μ * t ^ (-μ) :=
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorSmoothingScalarBound
    hμ ht ht1 hlam

end SpectralBounds
end Analysis
end DifferentialGeometry

end
