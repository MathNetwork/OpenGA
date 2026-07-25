import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ricciArmOrder0RiemannCoeff ricciArmOrder0CurvCoeff)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

private theorem ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i :=
  ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

private theorem ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i :=
  ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

private theorem ricciArmOrder0RiemannCoeff_perOrder_l2_ballUniform_g1
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨KD, hKD_nn, hKD⟩ :=
    ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + KD i),
    fun i => by
      linarith [hKD_nn i, sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hD := hKD g₁ P hδ_le hδ htie hPball i hi
  have hsplit : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ =
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ +
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) := by
    abel
  rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
      - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)]
  exact sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
      + iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖
    (‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
    (KD i)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) le_rfl hD

private theorem ricciArmOrder0CurvCoeff_perOrder_l2_ballUniform_g1
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨KD, hKD_nn, hKD⟩ :=
    ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform_g1
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + KD i),
    fun i => by
      linarith [hKD_nn i, sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hD := hKD g₁ P hδ_le hδ htie hPball i hi
  have hsplit : ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀ +
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) := by
    abel
  rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
      - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]
  exact sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
      + iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    (‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
    (KD i)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) le_rfl hD

theorem ricciArmOrder0BaseCoeff_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨KR, hKR_nn, hKR⟩ :=
    ricciArmOrder0RiemannCoeff_perOrder_l2_ballUniform_g1
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    ricciArmOrder0CurvCoeff_perOrder_l2_ballUniform_g1
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (KR i + KC i), fun i => by linarith [hKR_nn i, hKC_nn i], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hR2 := hKR g₁ P hδ_le hδ htie hPball i hi
  have hC2 := hKC g₁ P hδ_le hδ htie hPball i hi
  rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)]
  exact sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
      - iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖
    (KR i) (KC i)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_sub_le _ _) hR2 hC2

end DifferentialGeometry.Integral.Connection

end
