import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.GramInvUniformEigenvalueLowerBound
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Compact


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem _root_.Matrix.inv_entry_sub_abs_le_of_entry_bound
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit A) (hB : IsUnit B) {M D : ℝ}
    (hMinvA : ∀ p q, |A⁻¹ p q| ≤ M) (hMinvB : ∀ p q, |B⁻¹ p q| ≤ M)
    (hD : ∀ p q, |(B - A) p q| ≤ D) (i j : Fin n) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (n : ℝ) ^ 2 * M ^ 2 * D := by
  classical
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hMinvA i j)
  have hD_nonneg : 0 ≤ D :=
    le_trans (abs_nonneg ((B - A) i j)) (hD i j)
  have hAB : IsUnit A ↔ IsUnit B := ⟨fun _ => hB, fun _ => hA⟩
  have h_id : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := Matrix.inv_sub_inv hAB
  have h_entry : A⁻¹ i j - B⁻¹ i j = (A⁻¹ * (B - A) * B⁻¹) i j := by
    have := congrArg (fun (X : Matrix (Fin n) (Fin n) ℝ) => X i j) h_id
    simpa using this
  have h_expand : (A⁻¹ * (B - A) * B⁻¹) i j =
      ∑ q : Fin n, ∑ p : Fin n,
        A⁻¹ i p * (B - A) p q * B⁻¹ q j := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
  rw [h_entry, h_expand]
  calc |∑ q : Fin n, ∑ p : Fin n, A⁻¹ i p * (B - A) p q * B⁻¹ q j|
      ≤ ∑ q : Fin n, |∑ p : Fin n, A⁻¹ i p * (B - A) p q * B⁻¹ q j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : Fin n, ∑ p : Fin n, |A⁻¹ i p * (B - A) p q * B⁻¹ q j| := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : Fin n, ∑ p : Fin n, M * D * M := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        refine Finset.sum_le_sum (fun p _ => ?_)
        rw [abs_mul, abs_mul]
        have h1 : |A⁻¹ i p| ≤ M := hMinvA i p
        have h2 : |(B - A) p q| ≤ D := hD p q
        have h3 : |B⁻¹ q j| ≤ M := hMinvB q j
        have hstep : |A⁻¹ i p| * |(B - A) p q| ≤ M * D :=
          mul_le_mul h1 h2 (abs_nonneg _) hM_nonneg
        calc |A⁻¹ i p| * |(B - A) p q| * |B⁻¹ q j|
            ≤ (M * D) * |B⁻¹ q j| :=
              mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
          _ ≤ (M * D) * M :=
              mul_le_mul_of_nonneg_left h3
                (mul_nonneg hM_nonneg hD_nonneg)
    _ = (n : ℝ) ^ 2 * M ^ 2 * D := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

def matrixEntryL1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ pq : (Fin n) × (Fin n), |A pq.1 pq.2|

lemma matrixEntryL1_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ matrixEntryL1 A :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma abs_entry_le_matrixEntryL1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n) : |A p q| ≤ matrixEntryL1 A := by
  classical
  exact Finset.single_le_sum
    (f := fun pq : (Fin n) × (Fin n) => |A pq.1 pq.2|)
    (fun pq _ => abs_nonneg _) (Finset.mem_univ (p, q))

def chartGramDiffSup (g₁ g₂ : SmoothRiemannianMetric I M) (α x : M) : ℝ :=
  matrixEntryL1 (chartGramMatrix g₁ α x - chartGramMatrix g₂ α x)

lemma chartGramDiffSup_nonneg (g₁ g₂ : SmoothRiemannianMetric I M) (α x : M) :
    0 ≤ chartGramDiffSup (I := I) (M := M) g₁ g₂ α x :=
  matrixEntryL1_nonneg _

lemma chartGramMatrix_sub_entry_abs_le_gramDiffSup
    (g₁ g₂ : SmoothRiemannianMetric I M) (α x : M)
    (p q : Fin (Module.finrank ℝ E)) :
    |chartGramMatrix g₁ α x p q - chartGramMatrix g₂ α x p q| ≤
      chartGramDiffSup (I := I) (M := M) g₁ g₂ α x := by
  have h := abs_entry_le_matrixEntryL1
    (chartGramMatrix g₁ α x - chartGramMatrix g₂ α x) p q
  rwa [Matrix.sub_apply] at h

theorem chartInvGramMatrix_entry_sub_abs_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {M_b D : ℝ}
    (hM1 : ∀ p q, |chartInvGramMatrix (I := I) g₁ α x p q| ≤ M_b)
    (hM2 : ∀ p q, |chartInvGramMatrix (I := I) g₂ α x p q| ≤ M_b)
    (hD : ∀ p q,
      |chartGramMatrix g₁ α x p q - chartGramMatrix g₂ α x p q| ≤ D)
    (k l : Fin (Module.finrank ℝ E)) :
    |chartInvGramMatrix (I := I) g₁ α x k l -
        chartInvGramMatrix (I := I) g₂ α x k l| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 * D := by
  classical
  have hA_unit : IsUnit (chartGramMatrix g₁ α x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) g₁ α hx))
  have hB_unit : IsUnit (chartGramMatrix g₂ α x) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) g₂ α hx))
  have hD' : ∀ p q,
      |(chartGramMatrix g₂ α x - chartGramMatrix g₁ α x) p q| ≤ D := by
    intro p q
    rw [Matrix.sub_apply, abs_sub_comm]
    exact hD p q
  have hinvA : ∀ p q, |(chartGramMatrix g₁ α x)⁻¹ p q| ≤ M_b := by
    intro p q
    have := hM1 p q
    unfold chartInvGramMatrix at this
    exact this
  have hinvB : ∀ p q, |(chartGramMatrix g₂ α x)⁻¹ p q| ≤ M_b := by
    intro p q
    have := hM2 p q
    unfold chartInvGramMatrix at this
    exact this
  have h := Matrix.inv_entry_sub_abs_le_of_entry_bound
    (A := chartGramMatrix g₁ α x) (B := chartGramMatrix g₂ α x)
    hA_unit hB_unit hinvA hinvB hD' k l
  unfold chartInvGramMatrix
  exact h

theorem chartInvGramMatrix_entry_sub_abs_le_gramDiffSup
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {M_b : ℝ}
    (hM1 : ∀ p q, |chartInvGramMatrix (I := I) g₁ α x p q| ≤ M_b)
    (hM2 : ∀ p q, |chartInvGramMatrix (I := I) g₂ α x p q| ≤ M_b)
    (k l : Fin (Module.finrank ℝ E)) :
    |chartInvGramMatrix (I := I) g₁ α x k l -
        chartInvGramMatrix (I := I) g₂ α x k l| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 *
        chartGramDiffSup (I := I) (M := M) g₁ g₂ α x :=
  chartInvGramMatrix_entry_sub_abs_le (I := I) (M := M) g₁ g₂ α hx hM1 hM2
    (fun p q => chartGramMatrix_sub_entry_abs_le_gramDiffSup (I := I) (M := M)
      g₁ g₂ α x p q) k l

lemma exists_chartInvGramMatrix_entry_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ M_b : ℝ, 0 ≤ M_b ∧ ∀ x ∈ K, ∀ p q,
      |chartInvGramMatrix (I := I) g α x p q| ≤ M_b := by
  classical
  have h_cont : ContinuousOn
      (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) (chartAt H α).source :=
    chartInvGramMatrix_l1Sum_continuousOn (I := I) (M := M) g α
  have h_cont_K : ContinuousOn
      (chartInvGramMatrix_l1Sum (I := I) (M := M) g α) K := h_cont.mono hKsub
  by_cases h_empty : K = ∅
  · exact ⟨0, le_refl 0, fun x hx => absurd (h_empty ▸ hx) (Set.notMem_empty _)⟩
  obtain ⟨C, hC⟩ := hK.bddAbove_image h_cont_K
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx p q
  have h_l1_le : chartInvGramMatrix_l1Sum (I := I) (M := M) g α x ≤ C :=
    hC ⟨x, hx, rfl⟩
  have h_l1_eq :
      chartInvGramMatrix_l1Sum (I := I) (M := M) g α x =
        matrixEntryL1 (chartInvGramMatrix (I := I) g α x) := rfl
  have h_entry_le :
      |chartInvGramMatrix (I := I) g α x p q| ≤
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α x := by
    rw [h_l1_eq]
    exact abs_entry_le_matrixEntryL1 (chartInvGramMatrix (I := I) g α x) p q
  exact h_entry_le.trans (h_l1_le.trans (le_max_left _ _))

theorem exists_chartInvGramMatrix_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK : IsCompact K)
    (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ k l : Fin (Module.finrank ℝ E),
      |chartInvGramMatrix (I := I) g₁ α x k l -
          chartInvGramMatrix (I := I) g₂ α x k l| ≤
        C * chartGramDiffSup (I := I) (M := M) g₁ g₂ α x := by
  classical
  obtain ⟨M₁, hM₁_nn, hM₁⟩ :=
    exists_chartInvGramMatrix_entry_bound_on_compact (I := I) (M := M) g₁ α hK hKsub
  obtain ⟨M₂, hM₂_nn, hM₂⟩ :=
    exists_chartInvGramMatrix_entry_bound_on_compact (I := I) (M := M) g₂ α hK hKsub
  set M_b : ℝ := max M₁ M₂ with hM_def
  have hM_nn : 0 ≤ M_b := le_max_of_le_left hM₁_nn
  have h_base_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source := rfl
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 + 1, ?_, ?_⟩
  · have h_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  intro x hx k l
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [h_base_eq]; exact hKsub hx
  have hM1' : ∀ p q, |chartInvGramMatrix (I := I) g₁ α x p q| ≤ M_b :=
    fun p q => (hM₁ x hx p q).trans (le_max_left _ _)
  have hM2' : ∀ p q, |chartInvGramMatrix (I := I) g₂ α x p q| ≤ M_b :=
    fun p q => (hM₂ x hx p q).trans (le_max_right _ _)
  have h_pt := chartInvGramMatrix_entry_sub_abs_le_gramDiffSup
    (I := I) (M := M) g₁ g₂ α hx_base hM1' hM2' k l
  have h_gram_nn : 0 ≤ chartGramDiffSup (I := I) (M := M) g₁ g₂ α x :=
    chartGramDiffSup_nonneg (I := I) (M := M) g₁ g₂ α x
  calc |chartInvGramMatrix (I := I) g₁ α x k l -
            chartInvGramMatrix (I := I) g₂ α x k l|
      ≤ (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 *
          chartGramDiffSup (I := I) (M := M) g₁ g₂ α x := h_pt
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 + 1) *
          chartGramDiffSup (I := I) (M := M) g₁ g₂ α x := by
        refine mul_le_mul_of_nonneg_right ?_ h_gram_nn
        linarith



theorem chartInvGram_pou_lip
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hequiv : ∀ k : ι, ∀ b : M, ∀ v : TangentSpace I b,
      Λ⁻¹ * gBase.inner b v v ≤ (gSeq k).inner b v v ∧
        (gSeq k).inner b v v ≤ Λ * gBase.inner b v v) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k₁ k₂ : ι, ∀ b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ p q : Fin (Module.finrank ℝ E),
            |chartInvGramMatrix (I := I) (gSeq k₁) α b p q -
                chartInvGramMatrix (I := I) (gSeq k₂) α b p q| ≤
              C * chartGramDiffSup (I := I) (M := M)
                (gSeq k₁) (gSeq k₂) α b := by
  obtain ⟨M_b, hM_b, hM⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartInvGram_pou_bnd
      (I := I) (M := M) gBase gSeq Λ hΛ hequiv
  let C : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * M_b ^ 2 + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro α hα k₁ k₂ b hb p q
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hb
  have hpt := chartInvGramMatrix_entry_sub_abs_le_gramDiffSup
    (I := I) (M := M) (gSeq k₁) (gSeq k₂) α hb_base
      (hM α hα k₁ b hb) (hM α hα k₂ b hb) p q
  have hdiff_nonneg : 0 ≤ chartGramDiffSup (I := I) (M := M)
      (gSeq k₁) (gSeq k₂) α b := chartGramDiffSup_nonneg _ _ _ _
  exact hpt.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hdiff_nonneg)

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
