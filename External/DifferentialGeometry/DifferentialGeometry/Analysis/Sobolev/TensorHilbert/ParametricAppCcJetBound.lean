import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HomFieldActionL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetBound








noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E



theorem app_jet_sq_le
    (g : SmoothRiemannianMetric I M) (b c j : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b) (B : ℕ → ℝ)
    (hB : ∀ i, i ≤ j → 0 ≤ B i)
    (hΦ : ∀ i, i ≤ j → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
          ((iteratedCovGrad (I := I) g b c i Φ).toSection x) ≤ B i) :
    ‖iteratedCovGrad (I := I) g 0 c j
        (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ^ 2 ≤
      diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1), B i *
          ∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2 := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  set F : M → ℝ := fun x => diagonalGridGrowthFactor (E := E) j *
    ∑ i ∈ Finset.range (j + 1), B i *
      ∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b + l) x
          ((iteratedCovGrad (I := I) g 0 b l W).toSection x) with hF_def
  have hF_int : MeasureTheory.Integrable F μ := by
    rw [hF_def]
    exact (MeasureTheory.integrable_finset_sum (Finset.range (j + 1)) (fun i _ =>
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
          (iteratedCovGrad (I := I) g 0 b l W))).const_mul (B i))).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (c + j) x
          ((iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c Φ W)).toSection x) ≤ F x := by
    intro x
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le
        (I := I) (M := M) g b c Φ W j x) ?_
    rw [hF_def]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j)
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact mul_le_mul (hΦ i hij x) le_rfl
      (Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (b + l) x _))
      (hB i hij)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 0 (c + j)
    (iteratedCovGrad (I := I) g 0 c j
      (operatorFieldApply (I := I) (M := M) g b c Φ W)) F hF_int hpt
  refine le_trans hnorm (le_of_eq ?_)
  rw [hF_def, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum (Finset.range (j + 1)) (fun i _ =>
      (MeasureTheory.integrable_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
          (iteratedCovGrad (I := I) g 0 b l W))).const_mul (B i))]
  apply congrArg (fun z : ℝ => diagonalGridGrowthFactor (E := E) j * z)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum (Finset.range (j + 1 - i)) (fun l _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (b + l)
        (iteratedCovGrad (I := I) g 0 b l W))]
  apply congrArg (fun z : ℝ => B i * z)
  exact Finset.sum_congr rfl (fun l _ => by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 0 (b + l)])



theorem app_jet_of_bdd
    (g : SmoothRiemannianMetric I M) (b c : ℕ) {α : Type*}
    (Φ : α → SmoothCcTensor g b c) (K : Set α) (B : ℕ → ℝ)
    (hB_nn : ∀ i, 0 ≤ B i)
    (hB : ∀ i t, t ∈ K → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g b (c + i) x
        ((iteratedCovGrad (I := I) g b c i (Φ t)).toSection x) ≤ B i) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t, t ∈ K → ∀ (W : SmoothCcTensor g 0 b) (j : ℕ),
        ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖ ≤
          C j * ∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ := by
  classical
  let C : ℕ → ℝ := fun j =>
    diagonalGridGrowthFactor (E := E) j * (∑ i ∈ Finset.range (j + 1), B i) + 1
  refine ⟨C, fun j => ?_, ?_⟩
  · exact add_nonneg
      (mul_nonneg (appCcGdiag_nonneg (E := E) j)
        (Finset.sum_nonneg fun i _ => hB_nn i)) zero_le_one
  · intro t ht W j
    have hsq := app_jet_sq_le (I := I) (M := M) g b c j (Φ t) W B
      (fun i _ => hB_nn i) (fun i _ x => hB i t ht x)
    set J : ℝ := ∑ l ∈ Finset.range (j + 1),
      ‖iteratedCovGrad (I := I) g 0 b l W‖ with hJ_def
    set A : ℝ := diagonalGridGrowthFactor (E := E) j *
      (∑ i ∈ Finset.range (j + 1), B i) with hA_def
    have hJ_nn : 0 ≤ J := by
      rw [hJ_def]
      exact Finset.sum_nonneg fun l _ => norm_nonneg _
    have hA_nn : 0 ≤ A := by
      rw [hA_def]
      exact mul_nonneg (appCcGdiag_nonneg (E := E) j)
        (Finset.sum_nonneg fun i _ => hB_nn i)
    have hinner : ∀ i ∈ Finset.range (j + 1),
        (∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤ J ^ 2 := by
      intro i hi
      let Jsmall : ℝ := ∑ l ∈ Finset.range (j + 1 - i),
        ‖iteratedCovGrad (I := I) g 0 b l W‖
      have hJsmall_nn : 0 ≤ Jsmall := by
        exact Finset.sum_nonneg fun l _ => norm_nonneg _
      have hsmall : Jsmall ≤ J := by
        rw [hJ_def]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.sub_le (j + 1) i))
          (fun l _ _ => norm_nonneg _)
      have hsquares : (∑ l ∈ Finset.range (j + 1 - i),
          ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤ Jsmall ^ 2 := by
        exact Finset.sum_sq_le_sq_sum_of_nonneg
          (fun l _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 b l W))
      exact hsquares.trans (by nlinarith)
    have hgrid :
        (∑ i ∈ Finset.range (j + 1), B i *
          ∑ l ∈ Finset.range (j + 1 - i),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤
          (∑ i ∈ Finset.range (j + 1), B i) * J ^ 2 := by
      calc
        (∑ i ∈ Finset.range (j + 1), B i *
            ∑ l ∈ Finset.range (j + 1 - i),
              ‖iteratedCovGrad (I := I) g 0 b l W‖ ^ 2) ≤
            ∑ i ∈ Finset.range (j + 1), B i * J ^ 2 := by
              exact Finset.sum_le_sum fun i hi =>
                mul_le_mul_of_nonneg_left (hinner i hi) (hB_nn i)
        _ = (∑ i ∈ Finset.range (j + 1), B i) * J ^ 2 := by
          rw [Finset.sum_mul]
    have hsqA :
        ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖ ^ 2 ≤
          A * J ^ 2 := by
      refine hsq.trans ?_
      rw [hA_def]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hgrid
          (appCcGdiag_nonneg (E := E) j))
    have hA_le : A ≤ (A + 1) ^ 2 := by
      nlinarith [sq_nonneg A]
    have htarget :
        ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖ ^ 2 ≤
          ((A + 1) * J) ^ 2 := by
      calc
        _ ≤ A * J ^ 2 := hsqA
        _ ≤ (A + 1) ^ 2 * J ^ 2 :=
          mul_le_mul_of_nonneg_right hA_le (sq_nonneg J)
        _ = ((A + 1) * J) ^ 2 := by ring
    change ‖iteratedCovGrad (I := I) g 0 c j
        (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖ ≤ (A + 1) * J
    exact le_of_sq_le_sq htarget (mul_nonneg (add_nonneg hA_nn zero_le_one) hJ_nn)




theorem param_app_jet
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun z : M => TensorRSSpace b c I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t, t ∈ K → ∀ (W : SmoothCcTensor g 0 b) (j : ℕ),
        ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g b c (Φ t) W)‖ ≤
          C j * ∑ l ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g 0 b l W‖ := by
  obtain ⟨B, hB_nn, hB⟩ :=
    joint_jet_bdd (I := I) (M := M) g b c Φ hK hKS hjoint
  exact app_jet_of_bdd (I := I) (M := M) g b c Φ K B hB_nn hB

end Connection
end Integral
end DifferentialGeometry

end
