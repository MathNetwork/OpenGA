import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.GramInvUniformEigenvalueLowerBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_sum_tensorInnerPointwise_cov_chartBasis_diagonal_le_const_mul_tensorCovDerivPointwiseInner_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ K_M →
        ∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b))) ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
  classical
  obtain ⟨c, hc_pos, hc_bound⟩ :=
    exists_chartInvGramMatrix_quadForm_lower_bound_on_compact
      (I := I) (M := M) g α hK_M_compact hK_M_sub_baseSet
  refine ⟨c⁻¹, inv_nonneg.mpr hc_pos.le, ?_⟩
  intro S b hb
  set n := Module.finrank ℝ E with hn_def
  set A : Matrix (Fin n) (Fin n) ℝ :=
    chartInvGramMatrix (I := I) g α b with hA_def
  have hA_herm : A.IsHermitian := by
    rw [hA_def]; unfold chartInvGramMatrix
    exact (chartGramMatrix_isHermitian (I := I) g α b).inv
  set cov : Fin n → TensorRSModel r s ℝ E := fun i =>
    TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)) with hcov_def
  set U : Matrix (Fin n) (Fin n) ℝ :=
    (hA_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU_def
  set μ : Fin n → ℝ := hA_herm.eigenvalues with hμ_def
  have hU_unit :
      (hA_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) ∈
        Matrix.unitaryGroup (Fin n) ℝ :=
    (hA_herm.eigenvectorUnitary).property
  have hUTU : ∀ k l : Fin n,
      ∑ i : Fin n, U i k * U i l = if k = l then 1 else 0 := by
    intro k l
    have hkl : (star U * U) k l = if k = l then 1 else 0 := by
      rw [(Matrix.mem_unitaryGroup_iff' (A := U)).mp hU_unit]
      simp [Matrix.one_apply]
    rw [Matrix.mul_apply] at hkl
    refine (?_ : _ = _).trans hkl
    refine Finset.sum_congr rfl ?_
    intro i _; rw [Matrix.star_apply, star_trivial]
  have hUUT : ∀ i j : Fin n,
      ∑ k : Fin n, U i k * U j k = if i = j then 1 else 0 := by
    intro i j
    have hij : (U * star U) i j = if i = j then 1 else 0 := by
      rw [(Matrix.mem_unitaryGroup_iff (A := U)).mp hU_unit]
      simp [Matrix.one_apply]
    rw [Matrix.mul_apply] at hij
    refine (?_ : _ = _).trans hij
    refine Finset.sum_congr rfl ?_
    intro k _; rw [Matrix.star_apply, star_trivial]
  have hA_entry : ∀ i j : Fin n,
      A i j = ∑ k : Fin n, μ k * (U i k * U j k) := by
    intro i j
    have hUDstar : A = U * (Matrix.diagonal μ) * star U := by
      have := hA_herm.spectral_theorem
      simp only [Unitary.conjStarAlgAut_apply] at this
      have hofReal : (RCLike.ofReal ∘ hA_herm.eigenvalues : Fin n → ℝ) =
          hA_herm.eigenvalues := by funext k; simp
      rw [hofReal] at this; exact this
    rw [hUDstar, Matrix.mul_apply]
    have hUD : ∀ k : Fin n, (U * Matrix.diagonal μ) i k = U i k * μ k := by
      intro k
      rw [Matrix.mul_apply, Finset.sum_eq_single k]
      · simp [Matrix.diagonal]
      · intro l _ hl; simp [Matrix.diagonal, hl]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hUD k]
    have : (star U) k j = U j k := by simp [Matrix.star_apply, star_trivial]
    rw [this]; ring
  have hμ_ge_c : ∀ k : Fin n, c ≤ μ k := by
    intro k
    have hbnd := hc_bound b hb (fun i => U i k)
    have hcol_norm : ∑ i : Fin n, (U i k) ^ 2 = 1 := by
      have hkk := hUTU k k; simp only [if_true] at hkk
      calc ∑ i : Fin n, (U i k) ^ 2 = ∑ i : Fin n, U i k * U i k := by
            refine Finset.sum_congr rfl ?_; intro i _; rw [sq]
        _ = 1 := hkk
    have hcol_eq :
        (fun i' => U i' k) = ⇑(hA_herm.eigenvectorBasis k) := by
      funext i'; exact Matrix.IsHermitian.eigenvectorUnitary_apply hA_herm i' k
    have hev : ∀ i : Fin n, (A *ᵥ (fun i' => U i' k)) i = μ k * U i k := by
      intro i
      have hcomp := congrArg (fun f => f i)
        (Matrix.IsHermitian.mulVec_eigenvectorBasis hA_herm k)
      simp only at hcomp
      have h_smul_apply :
          ((μ k : ℝ) • ⇑(hA_herm.eigenvectorBasis k)) i =
            μ k * ⇑(hA_herm.eigenvectorBasis k) i := by
        simp [Pi.smul_apply, smul_eq_mul]
      have hLHS_eq :
          A *ᵥ ⇑(hA_herm.eigenvectorBasis k) = A *ᵥ (fun i' => U i' k) := by
        rw [hcol_eq]
      rw [← hLHS_eq, hcomp, h_smul_apply]
      have : ⇑(hA_herm.eigenvectorBasis k) i = U i k := by rw [← hcol_eq]
      rw [this]
    have hRHS : ∑ i : Fin n, ∑ j : Fin n,
          A i j * U i k * U j k = μ k := by
      have hdouble :
          ∑ i : Fin n, ∑ j : Fin n, A i j * U i k * U j k =
            ∑ i : Fin n, U i k * (A *ᵥ (fun j' => U j' k)) i := by
        refine Finset.sum_congr rfl ?_; intro i _
        change _ = U i k * (∑ j : Fin n, A i j * U j k)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro j _; ring
      rw [hdouble]
      have hcalc :
          ∑ i : Fin n, U i k * (A *ᵥ (fun j' => U j' k)) i =
            μ k * ∑ i : Fin n, (U i k) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro i _
        rw [hev i, sq]; ring
      rw [hcalc, hcol_norm, mul_one]
    rw [hcol_norm, mul_one] at hbnd
    have hbnd' :
        c ≤ ∑ i : Fin n, ∑ j : Fin n, A i j * U i k * U j k := by
      rw [hA_def]; exact hbnd
    rw [hRHS] at hbnd'; exact hbnd'
  set w : Fin n → TensorRSModel r s ℝ E := fun k =>
    ∑ i : Fin n, U i k • cov i with hw_def
  set tip : TensorRSModel r s ℝ E → TensorRSModel r s ℝ E → ℝ :=
    tensorInnerPointwise (I := I) (M := M) g r s b with htip_def
  have hwkwk : ∀ k : Fin n,
      tip (w k) (w k) =
        ∑ i : Fin n, ∑ j : Fin n, U i k * U j k * tip (cov i) (cov j) := by
    intro k
    rw [hw_def, htip_def,
        tensorInnerPointwise_sum_left (I := I) (M := M) g r s b
          Finset.univ cov (fun i => U i k) _]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [tensorInnerPointwise_sum_right (I := I) (M := M) g r s b
          Finset.univ _ cov (fun j => U j k), Finset.mul_sum]
    refine Finset.sum_congr rfl ?_; intro j _; ring
  have hquad_eq : ∑ i : Fin n, ∑ j : Fin n,
        A i j * tip (cov i) (cov j) =
      ∑ k : Fin n, μ k * tip (w k) (w k) := by
    have hLHS_eq :
        ∑ i : Fin n, ∑ j : Fin n, A i j * tip (cov i) (cov j)
          = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              (μ k * (U i k * U j k)) * tip (cov i) (cov j) := by
      refine Finset.sum_congr rfl ?_; intro i _
      refine Finset.sum_congr rfl ?_; intro j _
      rw [hA_entry i j, Finset.sum_mul]
    have hRHS_eq :
        ∑ k : Fin n, μ k * tip (w k) (w k)
          = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              (μ k * (U i k * U j k)) * tip (cov i) (cov j) := by
      refine Finset.sum_congr rfl ?_; intro k _
      rw [hwkwk k, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro j _; ring
    rw [hLHS_eq, hRHS_eq]
    have hswap1 :
        (∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            (μ k * (U i k * U j k)) * tip (cov i) (cov j))
          = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
            (μ k * (U i k * U j k)) * tip (cov i) (cov j) := by
      rw [Finset.sum_comm]
    rw [hswap1]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [Finset.sum_comm]
  have hdiag_eq : ∑ i : Fin n, tip (cov i) (cov i) =
      ∑ k : Fin n, tip (w k) (w k) := by
    have hRHS_swap :
        ∑ k : Fin n, tip (w k) (w k) =
          ∑ i : Fin n, ∑ j : Fin n,
            (∑ k : Fin n, U i k * U j k) * tip (cov i) (cov j) := by
      conv_lhs => rhs; ext k; rw [hwkwk k]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro j _
      rw [Finset.sum_mul]
    rw [hRHS_swap]
    refine (Finset.sum_congr rfl ?_).symm
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [hUUT i i]; simp
    · intro j _ hji; rw [hUUT i j]; simp [hji.symm]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hw_nonneg : ∀ k, 0 ≤ tip (w k) (w k) :=
    fun k => tensorInnerPointwise_nonneg (I := I) (M := M) g r s b (w k)
  have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc_pos
  have hsum_bound :
      ∑ k : Fin n, tip (w k) (w k) ≤
        c⁻¹ * (∑ k : Fin n, μ k * tip (w k) (w k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro k _
    have hμk : c ≤ μ k := hμ_ge_c k
    calc tip (w k) (w k)
        = c⁻¹ * (c * tip (w k) (w k)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
      _ ≤ c⁻¹ * (μ k * tip (w k) (w k)) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hc_pos).le
          exact mul_le_mul_of_nonneg_right hμk (hw_nonneg k)
  have hb_baseSet :
      b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    hK_M_sub_baseSet hb
  have hcov_quad_eq :
      ∑ i : Fin n, ∑ j : Fin n, A i j * tip (cov i) (cov j) =
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
    rw [← chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
      (I := I) (M := M) g α r s S S hb_baseSet]
    rw [htip_def]
    unfold chartTensorCovDerivPointwiseInner
    rw [hA_def, hcov_def]
    unfold DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
    rfl
  rw [hdiag_eq, ← hcov_quad_eq, hquad_eq]
  exact hsum_bound

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_sum_tensorInnerPointwise_cov_chartBasis_diagonal_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b))) ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b :=
  exists_sum_tensorInnerPointwise_cov_chartBasis_diagonal_le_const_mul_tensorCovDerivPointwiseInner_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
