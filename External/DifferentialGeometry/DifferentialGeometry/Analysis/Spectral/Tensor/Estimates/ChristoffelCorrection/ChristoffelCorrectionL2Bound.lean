import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTensorRSInputSlotCorrection_norm_sq_le_of_F_bound
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r)
    {M_F : ℝ}
    (hF_bound : ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ≤
        M_F * ‖T b‖) :
    ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ^ 2 ≤
      M_F ^ 2 * ‖T b‖ ^ 2 := by
  classical
  have hLHS_nn : 0 ≤ ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ :=
    norm_nonneg _
  have hT_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hsq : ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ^ 2 ≤
      (M_F * ‖T b‖) ^ 2 := by
    have := mul_self_le_mul_self hLHS_nn hF_bound
    have h_lhs_sq :
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ *
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ =
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ^ 2 := by rw [sq]
    have h_rhs_sq : (M_F * ‖T b‖) * (M_F * ‖T b‖) = (M_F * ‖T b‖) ^ 2 := by rw [sq]
    linarith
  have h_expand : (M_F * ‖T b‖) ^ 2 = M_F ^ 2 * ‖T b‖ ^ 2 := by ring
  linarith

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTensorRSOutputSlotCorrection_norm_sq_le_of_F_bound
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s)
    {M_F : ℝ}
    (hF_bound : ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ≤
        M_F * ‖T b‖) :
    ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ^ 2 ≤
      M_F ^ 2 * ‖T b‖ ^ 2 := by
  classical
  have hLHS_nn : 0 ≤ ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ :=
    norm_nonneg _
  have hT_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hsq : ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ^ 2 ≤
      (M_F * ‖T b‖) ^ 2 := by
    have := mul_self_le_mul_self hLHS_nn hF_bound
    have h_lhs_sq :
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ *
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ =
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ^ 2 := by rw [sq]
    have h_rhs_sq : (M_F * ‖T b‖) * (M_F * ‖T b‖) = (M_F * ‖T b‖) ^ 2 := by rw [sq]
    linarith
  have h_expand : (M_F * ‖T b‖) ^ 2 = M_F ^ 2 * ‖T b‖ ^ 2 := by ring
  linarith

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma section_norm_eq_toFun_norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (b : M) :
    ‖S.toSection b‖ = ‖S.toFun b‖ := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem exists_sum_chart_christoffel_correction_norm_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b')
    (M_F : ℝ) (_hM_F_nn : 0 ≤ M_F)
    (hM_F_input : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b k‖ ≤
            M_F * ‖S.toSection b‖)
    (hM_F_output : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b l‖ ≤
            M_F * ‖S.toSection b‖)
    (K_S : ℝ) (hK_S_nn : 0 ≤ K_S)
    (hK_S_bound : ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖S.toSection b‖ ^ 2 ≤
          K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          ((∑ k : Fin r, ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b k‖ ^ 2) +
            (∑ l : Fin s, ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toSection b') X b l‖ ^ 2)) ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  refine ⟨((r : ℝ) + (s : ℝ)) * M_F ^ 2 * K_S, ?_, ?_⟩
  · positivity
  intro S b hb
  have h_sec : ‖S.toSection b‖ ^ 2 ≤
      K_S * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := hK_S_bound S hb
  have h_in_each : ∀ k : Fin r,
      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => S.toSection b') X b k‖ ^ 2 ≤
        M_F ^ 2 * ‖S.toSection b‖ ^ 2 := by
    intro k
    exact chartTensorRSInputSlotCorrection_norm_sq_le_of_F_bound
      (I := I) r s g α (fun b' => S.toSection b') X b k
      (hM_F_input S hb k)
  have h_out_each : ∀ l : Fin s,
      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
          (fun b' => S.toSection b') X b l‖ ^ 2 ≤
        M_F ^ 2 * ‖S.toSection b‖ ^ 2 := by
    intro l
    exact chartTensorRSOutputSlotCorrection_norm_sq_le_of_F_bound
      (I := I) r s g α (fun b' => S.toSection b') X b l
      (hM_F_output S hb l)
  have h_in_sum : (∑ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b k‖ ^ 2) ≤
      (r : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
    have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
      (f := fun k => ‖chartTensorRSInputSlotCorrection (I := I) r s g α
        (fun b' => S.toSection b') X b k‖ ^ 2)
      (g := fun _ => M_F ^ 2 * ‖S.toSection b‖ ^ 2)
      (fun k _ => h_in_each k)
    have h_sum_const :
        (∑ _k : Fin r, M_F ^ 2 * ‖S.toSection b‖ ^ 2) =
          (r : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    linarith
  have h_out_sum : (∑ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b l‖ ^ 2) ≤
      (s : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
    have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s)))
      (f := fun l => ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
        (fun b' => S.toSection b') X b l‖ ^ 2)
      (g := fun _ => M_F ^ 2 * ‖S.toSection b‖ ^ 2)
      (fun l _ => h_out_each l)
    have h_sum_const :
        (∑ _l : Fin s, M_F ^ 2 * ‖S.toSection b‖ ^ 2) =
          (s : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul]
    linarith
  have h_combined :
      ((∑ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b k‖ ^ 2) +
        (∑ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') X b l‖ ^ 2)) ≤
      ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by
    have h_dist : ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) =
        (r : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) +
          (s : ℝ) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) := by ring
    linarith
  have h_M_F_sq_nn : 0 ≤ M_F ^ 2 := sq_nonneg _
  have h_rs_M_F_nn : 0 ≤ ((r : ℝ) + (s : ℝ)) * M_F ^ 2 := by positivity
  have h_chain :
      ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 * ‖S.toSection b‖ ^ 2) ≤
        ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 *
          (K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b))) := by
    have h_inner : M_F ^ 2 * ‖S.toSection b‖ ^ 2 ≤
        M_F ^ 2 *
          (K_S * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
      mul_le_mul_of_nonneg_left h_sec h_M_F_sq_nn
    have h_rs_nn : 0 ≤ ((r : ℝ) + (s : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left h_inner h_rs_nn
  have h_rearrange :
      ((r : ℝ) + (s : ℝ)) * (M_F ^ 2 *
        (K_S * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b))) =
      ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * K_S *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by ring
  linarith

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
