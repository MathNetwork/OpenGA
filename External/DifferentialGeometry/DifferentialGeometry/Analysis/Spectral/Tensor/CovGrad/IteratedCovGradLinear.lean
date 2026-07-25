import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm


noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_neg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : Integral.L2.SmoothCcTensor g r s) :
    covGrad g r s (-w) = -covGrad g r s w := by
  rw [← neg_one_smul ℝ w, covGrad_smul, neg_one_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    covGrad g r s (w₁ - w₂) = covGrad g r s w₁ - covGrad g r s w₂ := by
  rw [sub_eq_add_neg, covGrad_add, covGrad_neg, sub_eq_add_neg]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_add (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (w₁ + w₂)
      = iteratedCovGrad g r s j w₁ + iteratedCovGrad g r s j w₂ := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_add]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (c • w) = c • iteratedCovGrad g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_neg (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (-w) = -iteratedCovGrad g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_neg]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_sub (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (w₁ - w₂)
      = iteratedCovGrad g r s j w₁ - iteratedCovGrad g r s j w₂ := by
  rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, sub_eq_add_neg]

end RicciFlow
end PDE
end DifferentialGeometry

end
