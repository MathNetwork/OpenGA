import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3Principal










namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]







theorem lower_coeff_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ₀ : SmoothCcTensor g 2 2) (Φ₁ : SmoothCcTensor g 3 2)
        (U : SmoothCcTensor g 0 2) (B₀ B₀' B₁ : ℝ),
        0 ≤ B₀ → 0 ≤ B₀' → 0 ≤ B₁ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
              (Φ₀.toSection x) ≤ B₀ ^ 2) →
        ‖covGrad (I := I) (M := M) g 2 2 Φ₀‖ ≤ B₀' →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 3 2 x
              (Φ₁.toSection x) ≤ B₁ ^ 2) →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 3 2 j Φ₁‖ ^ 2) ≤ B₁ ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 2 2 Φ₀ U +
              operatorFieldApply (I := I) (M := M) g 3 2 Φ₁
                (covGrad (I := I) (M := M) g 0 2 U))‖ ≤
          C * (B₀ + B₀' + B₁) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨C₀, hC₀, hzero⟩ := appCc_c1_h2_h1 (I := I) (M := M) hDim g 2 2
  obtain ⟨C₁, hC₁, hone⟩ := appCc_h2_cov_h1 (I := I) (M := M) hDim g 1 2
  refine ⟨C₀ + C₁, add_nonneg hC₀ hC₁, ?_⟩
  intro Φ₀ Φ₁ U B₀ B₀' B₁ hB₀ hB₀' hB₁ hΦ₀ hΦ₀' hΦ₁ hΦ₁'
  have hzero' := hzero Φ₀ U B₀ B₀' hB₀ hB₀' hΦ₀ hΦ₀'
  have hone' := hone Φ₁ U B₁ hB₁ hΦ₁ hΦ₁'
  have hsum : 0 ≤ B₀ + B₀' + B₁ := by positivity
  have hnorm : 0 ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := norm_nonneg _
  rw [ccTensorToHs_add]
  calc
    _ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 2 2 Φ₀ U)‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g 3 2 Φ₁
              (covGrad (I := I) (M := M) g 0 2 U))‖ := norm_add_le _ _
    _ ≤ C₀ * (B₀ + B₀') *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * B₁ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
      add_le_add hzero' hone'
    _ ≤ C₀ * (B₀ + B₀' + B₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        C₁ * (B₀ + B₀' + B₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₀) hnorm
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hC₁) hnorm
    _ = (C₀ + C₁) * (B₀ + B₀' + B₁) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
