import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseOrderPeeling
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero

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

section ReverseBridge

omit [BoundarylessManifold I M] in
theorem exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            tensorL2Norm (I := I) (M := M) g r (s + j)
              (iteratedCovGrad g r s j T).toFun := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    exists_tensorPouSobolevHsNorm_le_iteratedCovGrad_zero_sum
      (I := I) (M := M) g r s k
  set CAfun : ℕ → ℝ := fun j =>
    (tensorPouSobolevHsNorm_zero_le_tensorL2Norm
      (I := I) (M := M) g r (s + j)).choose with hCAfun_def
  have hCAfun_nn : ∀ j : ℕ, 0 ≤ CAfun j := fun j =>
    (tensorPouSobolevHsNorm_zero_le_tensorL2Norm
      (I := I) (M := M) g r (s + j)).choose_spec.1
  have hCAfun_spec : ∀ (j : ℕ) (S : SmoothCcTensor g r (s + j)),
      (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal ≤
        CAfun j * tensorL2Norm (I := I) (M := M) g r (s + j) S.toFun := fun j S =>
    (tensorPouSobolevHsNorm_zero_le_tensorL2Norm
      (I := I) (M := M) g r (s + j)).choose_spec.2 S
  set CAmax : ℝ :=
    (Finset.range (2 * k + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos (2 * k))⟩ CAfun with hCAmax_def
  have hCAmax_nn : 0 ≤ CAmax :=
    le_trans (hCAfun_nn 0)
      (Finset.le_sup' CAfun (Finset.mem_range.mpr (Nat.succ_pos (2 * k))))
  have hCAfun_le_max : ∀ j ∈ Finset.range (2 * k + 1), CAfun j ≤ CAmax :=
    fun j hj => Finset.le_sup' CAfun hj
  refine ⟨CB * CAmax, mul_nonneg hCB_nn hCAmax_nn, fun T => ?_⟩
  set L : ℕ → ℝ := fun j =>
    tensorL2Norm (I := I) (M := M) g r (s + j) (iteratedCovGrad g r s j T).toFun
    with hL_def
  have hL_nn : ∀ j : ℕ, 0 ≤ L j := fun j =>
    tensorL2Norm_nonneg (I := I) (M := M) g r (s + j)
      (iteratedCovGrad g r s j T).toFun
  have h_term_le : ∀ j ∈ Finset.range (2 * k + 1),
      tensorPouSobolevHsNorm (I := I) (M := M) g 0 (iteratedCovGrad g r s j T) ≤
        ENNReal.ofReal (CAmax * L j) := by
    intro j hj
    have h_ne_top :
        tensorPouSobolevHsNorm (I := I) (M := M) g 0
          (iteratedCovGrad g r s j T) ≠ ⊤ :=
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g 0
        (iteratedCovGrad g r s j T)).ne
    rw [← ENNReal.ofReal_toReal h_ne_top]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (tensorPouSobolevHsNorm (I := I) (M := M) g 0
            (iteratedCovGrad g r s j T)).toReal
        ≤ CAfun j * L j := hCAfun_spec j (iteratedCovGrad g r s j T)
      _ ≤ CAmax * L j :=
          mul_le_mul_of_nonneg_right (hCAfun_le_max j hj) (hL_nn j)
  have h_sum_le :
      ∑ j ∈ Finset.range (2 * k + 1),
          tensorPouSobolevHsNorm (I := I) (M := M) g 0 (iteratedCovGrad g r s j T) ≤
        ENNReal.ofReal (CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
    calc ∑ j ∈ Finset.range (2 * k + 1),
            tensorPouSobolevHsNorm (I := I) (M := M) g 0 (iteratedCovGrad g r s j T)
        ≤ ∑ j ∈ Finset.range (2 * k + 1), ENNReal.ofReal (CAmax * L j) :=
          Finset.sum_le_sum h_term_le
      _ = ENNReal.ofReal (∑ j ∈ Finset.range (2 * k + 1), CAmax * L j) :=
          (ENNReal.ofReal_sum_of_nonneg
            (fun j _ => mul_nonneg hCAmax_nn (hL_nn j))).symm
      _ = ENNReal.ofReal (CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
          rw [Finset.mul_sum]
  have h_enn :
      tensorPouSobolevHsNorm (I := I) (M := M) g k T ≤
        ENNReal.ofReal
          (CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
    refine (hCB T).trans ?_
    calc ENNReal.ofReal CB *
            ∑ j ∈ Finset.range (2 * k + 1),
              tensorPouSobolevHsNorm (I := I) (M := M) g 0
                (iteratedCovGrad g r s j T)
        ≤ ENNReal.ofReal CB *
            ENNReal.ofReal (CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
          exact mul_le_mul_of_nonneg_left h_sum_le (zero_le _)
      _ = ENNReal.ofReal
            (CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
          rw [← ENNReal.ofReal_mul hCB_nn, mul_assoc]
  have h_rhs_nn :
      0 ≤ CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j :=
    mul_nonneg (mul_nonneg hCB_nn hCAmax_nn)
      (Finset.sum_nonneg (fun j _ => hL_nn j))
  have h_toReal :=
    ENNReal.toReal_le_of_le_ofReal h_rhs_nn h_enn
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal
      ≤ CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j := h_toReal
    _ = CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1),
          tensorL2Norm (I := I) (M := M) g r (s + j)
            (iteratedCovGrad g r s j T).toFun := rfl

end ReverseBridge

end DifferentialGeometry.PDE.RicciFlow

end
