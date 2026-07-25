import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.NablaTensorFormula
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCkBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.GramTwist
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.UniformChartBounds


namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iterated_nabla_vs_iterated_partial_equivalence_H1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal := by
  match k with
  | 0 =>
    exact fibrewise_gram_twist_estimate (I := I) (M := M) g r s
  | k' + 1 =>
    obtain ⟨Cfwd, hCfwd_nn, hCfwd_bound⟩ :=
      nabla_tensor_iterated_Hk_formula (I := I) (M := M) g r s (k' + 1)
    obtain ⟨Crev, hCrev_nn, hCrev_bound⟩ :=
      uniform_chart_bounds_from_compactness (I := I) (M := M) g r s (k' + 1)
    set Mc : ℝ := max 1 Crev with hMc_def
    have hMc_ge_one : (1 : ℝ) ≤ Mc := le_max_left _ _
    have hMc_pos : (0 : ℝ) < Mc := lt_of_lt_of_le one_pos hMc_ge_one
    have hCrev_le_Mc : Crev ≤ Mc := le_max_right _ _
    set c : ℝ := 1 / Mc with hc_def
    set C : ℝ := max Cfwd Mc with hC_def
    have hc_pos : (0 : ℝ) < c := by
      rw [hc_def]; exact one_div_pos.mpr hMc_pos
    have hc_le_one : c ≤ 1 := by
      rw [hc_def]; exact (div_le_one hMc_pos).mpr hMc_ge_one
    have hMc_le_C : Mc ≤ C := le_max_right _ _
    have hc_le_C : c ≤ C := le_trans hc_le_one (le_trans hMc_ge_one hMc_le_C)
    refine ⟨c, C, hc_pos, hc_le_C, ?_⟩
    intro T
    set P : ℝ := (tensorPouSobolevNorm (I := I) (M := M) g (k' + 1) T).toReal
      with hP_def
    set Hs : ℝ := (tensorPouSobolevHsNorm (I := I) (M := M) g (k' + 1) T).toReal
      with hHs_def
    have hP_nn : 0 ≤ P := by rw [hP_def]; exact ENNReal.toReal_nonneg
    have hHs_nn : 0 ≤ Hs := by rw [hHs_def]; exact ENNReal.toReal_nonneg
    have hfwd : Hs ≤ Cfwd * P := hCfwd_bound T
    have hrev : P ≤ Crev * Hs := hCrev_bound T
    have hP_le_Mc_Hs : P ≤ Mc * Hs := by
      calc P ≤ Crev * Hs := hrev
        _ ≤ Mc * Hs := mul_le_mul_of_nonneg_right hCrev_le_Mc hHs_nn
    have hc_P_le_Hs : c * P ≤ Hs := by
      rw [hc_def]
      have h_div_mul : (1 / Mc) * P ≤ (1 / Mc) * (Mc * Hs) :=
        mul_le_mul_of_nonneg_left hP_le_Mc_Hs
          (le_of_lt (one_div_pos.mpr hMc_pos))
      have h_simp : (1 / Mc) * (Mc * Hs) = Hs := by
        rw [← mul_assoc]
        rw [one_div_mul_cancel (ne_of_gt hMc_pos)]
        rw [one_mul]
      rw [h_simp] at h_div_mul
      exact h_div_mul
    have hCfwd_le_C : Cfwd ≤ C := le_max_left _ _
    have hHs_le_C_P : Hs ≤ C * P := by
      calc Hs ≤ Cfwd * P := hfwd
        _ ≤ C * P := mul_le_mul_of_nonneg_right hCfwd_le_C hP_nn
    exact ⟨hc_P_le_Hs, hHs_le_C_P⟩

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
