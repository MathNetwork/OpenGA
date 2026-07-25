import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul_local (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_convexPerturbation_norm_le
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) {R : ℝ} (j : ℕ)
    (hT : ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (hT' : ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ 2 * R := by
  rw [Set.mem_Icc] at hs
  obtain ⟨hs0, hs1⟩ := hs
  rw [convexPerturbation, iteratedCovGrad_add, iteratedCovGrad_smul_local,
    iteratedCovGrad_smul_local]
  have habs_s : |s| ≤ 1 := by rw [abs_of_nonneg hs0]; exact hs1
  have habs_1s : |1 - s| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T' +
          s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
      ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
          ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
    _ = |1 - s| * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
          |s| * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * R + 1 * R := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul habs_1s hT' (norm_nonneg _) zero_le_one
        · exact mul_le_mul habs_s hT (norm_nonneg _) zero_le_one
    _ = 2 * R := by ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem exists_Csob_convexPerturbation_pointwise_C2_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          (∑ j ∈ Finset.range 3,
              (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
                Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
              ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                  (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ Csob * R := by
  classical
  set k : ℕ := Module.finrank ℝ E / 2 + 3 with hk_def
  have hk_super : 2 * k > Module.finrank ℝ E + 4 := by rw [hk_def]; omega
  have h4k_le : 4 * k ≤ a + 2 := by rw [hk_def]; omega
  obtain ⟨Cc, hCc_pos, hCc⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_singleNorm (I := I) (M := M) g₀ k hk_super
  obtain ⟨Ch, hCh_nn, hCh⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * k)
  refine ⟨Cc * Ch * ((4 * k + 1 : ℕ) : ℝ) * 2, ?_, ?_⟩
  · positivity
  intro T T' R _hR hbudgetT hbudgetT' s hs x
  set W : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hW_def
  have hWbudget : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ 2 * R := by
    intro j hj
    exact iteratedCovGrad_convexPerturbation_norm_le (I := I) (M := M) g₀ T T' j
      (hbudgetT j hj) (hbudgetT' j hj) s hs
  have hCol := hCc W x
  set Mn : ℝ := ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) W‖ with hMn_def
  have hMn_nn : 0 ≤ Mn := norm_nonneg _
  have hHebey : Mn ≤ Ch * ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    refine le_trans (hCh W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCh_nn
    refine le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))
    exact (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm
  have hSumBudget : ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ ((4 * k + 1 : ℕ) : ℝ) * (2 * R) := by
    have hterm : ∀ j ∈ Finset.range (2 * (2 * k) + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ 2 * R := by
      intro j hj
      have hjle : j ≤ a + 2 := by
        have := Finset.mem_range.mp hj; omega
      exact hWbudget j hjle
    calc ∑ j ∈ Finset.range (2 * (2 * k) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖
        ≤ ∑ _j ∈ Finset.range (2 * (2 * k) + 1), (2 * R) := Finset.sum_le_sum hterm
      _ = ((2 * (2 * k) + 1 : ℕ) : ℝ) * (2 * R) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((4 * k + 1 : ℕ) : ℝ) * (2 * R) := by
          congr 2
          omega
  have hMn_le : Mn ≤ Ch * (((4 * k + 1 : ℕ) : ℝ) * (2 * R)) := by
    refine le_trans hHebey ?_
    exact mul_le_mul_of_nonneg_left hSumBudget hCh_nn
  calc (∑ j ∈ Finset.range 3,
          (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
          ‖(iteratedCovGrad (I := I) g₀ 0 2 j W).toSection x‖))
      ≤ Cc * Mn := hCol
    _ ≤ Cc * (Ch * (((4 * k + 1 : ℕ) : ℝ) * (2 * R))) :=
        mul_le_mul_of_nonneg_left hMn_le hCc_pos.le
    _ = (Cc * Ch * ((4 * k + 1 : ℕ) : ℝ) * 2) * R := by ring

end DifferentialGeometry.PDE.RicciFlow

end
