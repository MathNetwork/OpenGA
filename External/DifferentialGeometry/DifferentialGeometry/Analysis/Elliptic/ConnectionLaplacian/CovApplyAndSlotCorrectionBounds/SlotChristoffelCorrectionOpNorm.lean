import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Tensor.RSTensor.TensorRSSpaceOperatorNorm
import Mathlib.Analysis.Normed.Module.Multilinear.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorSlotSubstCLM_apply_norm_le (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (x : Tensor0SSpace n I b) :
    ‖tensorSlotSubstCLM (I := I) n b Φ x‖ ≤
      (∏ i : Fin n, ‖Φ i‖) * ‖x‖ := by
  classical
  have hsubst_eq :
      tensorSlotSubstCLM (I := I) n b Φ x =
        (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          ((ContinuousMultilinearMap.compContinuousLinearMapL
              (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
            ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)) := by
    change ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
              Tensor0SSpace n I b).comp
        ((tangentCompCLML_E (I := I) (M := M) n b Φ).comp
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b)
            : Tensor0SSpace n I b →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)) x =
        (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
          ((ContinuousMultilinearMap.compContinuousLinearMapL
              (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
            ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x))
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [hsubst_eq]
  rw [tensor0SSpace_continuousLinearEquiv_symm_norm_apply (𝕜 := ℝ) (E := E)
      (I := I) (M := M) n b _]
  have hopBound :
      ‖ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ‖ ≤
        ∏ i : Fin n, ‖Φ i‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin n => E) ℝ Φ
  have hCLEx_nn :
      0 ≤ ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    norm_nonneg _
  have hCLM_le :
      ‖(ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)‖ ≤
        ‖ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ‖ *
          ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hCLM_le' :
      ‖(ContinuousMultilinearMap.compContinuousLinearMapL
            (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ) Φ)
          ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x)‖ ≤
        (∏ i : Fin n, ‖Φ i‖) *
          ‖(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b) x‖ :=
    hCLM_le.trans (mul_le_mul_of_nonneg_right hopBound hCLEx_nn)
  rw [tensor0SSpace_continuousLinearEquiv_norm_apply (𝕜 := ℝ) (E := E)
      (I := I) (M := M) n b x] at hCLM_le'
  exact hCLM_le'

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
lemma tangentSlotCLM_factor_norm_le (n : ℕ) (b : M)
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin n) :
    ‖tangentSlotCLM (I := I) n k Φ i‖ ≤ max ‖Φ‖ 1 := by
  classical
  by_cases hi : i = k
  · rw [hi, tangentSlotCLM_self]
    exact le_max_left _ _
  · rw [tangentSlotCLM_other (I := I) n k Φ hi]
    have h_id : ‖(ContinuousLinearMap.id ℝ (TangentSpace I b))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    exact h_id.trans (le_max_right _ _)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
lemma tangentSlotCLM_prod_norm_le (n : ℕ) (b : M)
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    (∏ i : Fin n, ‖tangentSlotCLM (I := I) n k Φ i‖) ≤
      (max ‖Φ‖ 1) ^ n := by
  classical
  have h_pow : (max ‖Φ‖ 1) ^ n = ∏ _i : Fin n, max ‖Φ‖ 1 := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro i _; exact norm_nonneg _
  · intro i _; exact tangentSlotCLM_factor_norm_le (I := I) n b k Φ i

def tensorSlotSubstCLMRS (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    TensorRSSpace n n I b :=
  tensorSlotSubstCLM (I := I) n b Φ

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma tensorSlotSubstCLMRS_apply (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (x : Tensor0SSpace n I b) :
    (show Tensor0SSpace n I b →L[ℝ] Tensor0SSpace n I b from
      tensorSlotSubstCLMRS (I := I) n b Φ) x =
      tensorSlotSubstCLM (I := I) n b Φ x := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private lemma slotSubstCLM_factor_prod_nonneg (n : ℕ) {b : M}
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    0 ≤ ∏ i : Fin n, ‖Φ i‖ :=
  Finset.prod_nonneg (fun _ _ => norm_nonneg _)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensorSlotSubstCLM_opNorm_le (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    ‖tensorSlotSubstCLMRS (I := I) n b Φ‖ ≤ ∏ i : Fin n, ‖Φ i‖ := by
  refine tensorRSSpace_opNorm_le_bound (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (tensorSlotSubstCLMRS (I := I) n b Φ)
    (slotSubstCLM_factor_prod_nonneg (I := I) (M := M) n Φ) ?_
  intro x
  exact tensorSlotSubstCLM_apply_norm_le (I := I) n b Φ x

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensorSlotSubstCLM_tangentSlotCLM_opNorm_le (n : ℕ) (b : M)
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    ‖tensorSlotSubstCLMRS (I := I) n b
        (tangentSlotCLM (I := I) n k Φ)‖ ≤ (max ‖Φ‖ 1) ^ n :=
  (tensorSlotSubstCLM_opNorm_le (I := I) n b
      (tangentSlotCLM (I := I) n k Φ)).trans
    (tangentSlotCLM_prod_norm_le (I := I) n b k Φ)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensorSlotSubstCLM_inputSlotChartCLM_opNorm_le (r : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    ‖tensorSlotSubstCLMRS (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b X))‖ ≤
      (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ r :=
  tensorSlotSubstCLM_tangentSlotCLM_opNorm_le (I := I) r b k _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensorSlotSubstCLM_outputSlotChartCLM_opNorm_le (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    ‖tensorSlotSubstCLMRS (I := I) s b
        (tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b X))‖ ≤
      (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ s :=
  tensorSlotSubstCLM_tangentSlotCLM_opNorm_le (I := I) s b l _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem chartTensorRSInputSlotCorrection_opNorm_le (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    ‖chartTensorRSInputSlotCorrection (I := I) r s g α T X b k‖ ≤
      (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ r * ‖T b‖ := by
  classical
  set Φ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b X with hΦ_def
  set Ψ : Fin r → (TangentSpace I b →L[ℝ] TangentSpace I b) :=
    tangentSlotCLM (I := I) r k Φ with hΨ_def
  set M_F : ℝ := (max ‖Φ‖ 1) ^ r with hM_F_def
  have hM_F_nn : 0 ≤ M_F := by
    have h1 : 0 ≤ max ‖Φ‖ 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg h1 r
  have hΨ_prod_le : (∏ i : Fin r, ‖Ψ i‖) ≤ M_F := by
    rw [hΨ_def, hM_F_def]
    exact tangentSlotCLM_prod_norm_le (I := I) r b k Φ
  have hRHS_nn : 0 ≤ M_F * ‖T b‖ :=
    mul_nonneg hM_F_nn (norm_nonneg _)
  refine tensorRSSpace_opNorm_le_bound (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (chartTensorRSInputSlotCorrection (I := I) r s g α T X b k) hRHS_nn ?_
  intro x
  have hcomp : (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      chartTensorRSInputSlotCorrection (I := I) r s g α T X b k) x =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
        (tensorSlotSubstCLM (I := I) r b Ψ x) := by
    change ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
        (tensorSlotSubstCLM (I := I) r b Ψ)) x =
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
        (tensorSlotSubstCLM (I := I) r b Ψ x)
    rw [ContinuousLinearMap.comp_apply]
  rw [hcomp]
  have hT_apply :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ :=
    tensorRSSpace_norm_apply_le (𝕜 := ℝ) (E := E) (I := I) (M := M) (T b) _
  have hsubst :
      ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ ≤
        (∏ i : Fin r, ‖Ψ i‖) * ‖x‖ :=
    tensorSlotSubstCLM_apply_norm_le (I := I) r b Ψ x
  have hTb_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
  have h_step1 :
      ‖T b‖ * ‖tensorSlotSubstCLM (I := I) r b Ψ x‖ ≤
        ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) :=
    mul_le_mul_of_nonneg_left hsubst hTb_nn
  have h_step2 :
      ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) ≤
        ‖T b‖ * (M_F * ‖x‖) := by
    have h_prod_factor : (∏ i : Fin r, ‖Ψ i‖) * ‖x‖ ≤ M_F * ‖x‖ :=
      mul_le_mul_of_nonneg_right hΨ_prod_le hx_nn
    exact mul_le_mul_of_nonneg_left h_prod_factor hTb_nn
  have h_rearrange : ‖T b‖ * (M_F * ‖x‖) = M_F * ‖T b‖ * ‖x‖ := by ring
  have hChain1 :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * ((∏ i : Fin r, ‖Ψ i‖) * ‖x‖) :=
    hT_apply.trans h_step1
  have hChain2 :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b Ψ x)‖ ≤
        ‖T b‖ * (M_F * ‖x‖) :=
    hChain1.trans h_step2
  rw [h_rearrange] at hChain2
  exact hChain2

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem chartTensorRSOutputSlotCorrection_opNorm_le (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l‖ ≤
      (max ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ 1) ^ s * ‖T b‖ := by
  classical
  set Φ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    chartLeviCivitaParallelCLM (I := I) g α b X with hΦ_def
  set Ψ : Fin s → (TangentSpace I b →L[ℝ] TangentSpace I b) :=
    tangentSlotCLM (I := I) s l Φ with hΨ_def
  set M_F : ℝ := (max ‖Φ‖ 1) ^ s with hM_F_def
  have hM_F_nn : 0 ≤ M_F := by
    have h1 : 0 ≤ max ‖Φ‖ 1 := le_trans zero_le_one (le_max_right _ _)
    exact pow_nonneg h1 s
  have hΨ_prod_le : (∏ i : Fin s, ‖Ψ i‖) ≤ M_F := by
    rw [hΨ_def, hM_F_def]
    exact tangentSlotCLM_prod_norm_le (I := I) s b l Φ
  have hRHS_nn : 0 ≤ M_F * ‖T b‖ :=
    mul_nonneg hM_F_nn (norm_nonneg _)
  refine tensorRSSpace_opNorm_le_bound (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) hRHS_nn ?_
  intro x
  have hcomp : (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) x =
      tensorSlotSubstCLM (I := I) s b Ψ
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x) := by
    change ((tensorSlotSubstCLM (I := I) s b Ψ).comp
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)) x =
      tensorSlotSubstCLM (I := I) s b Ψ
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)
    rw [ContinuousLinearMap.comp_apply]
  rw [hcomp]
  have hsubst :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        (∏ i : Fin s, ‖Ψ i‖) *
          ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ :=
    tensorSlotSubstCLM_apply_norm_le (I := I) s b Ψ _
  have hT_apply :
      ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ ≤
        ‖T b‖ * ‖x‖ :=
    tensorRSSpace_norm_apply_le (𝕜 := ℝ) (E := E) (I := I) (M := M) (T b) x
  have hTb_nn : 0 ≤ ‖T b‖ := norm_nonneg _
  have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
  have h_prod_nn : 0 ≤ ∏ i : Fin s, ‖Ψ i‖ :=
    Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have h_step1 :
      (∏ i : Fin s, ‖Ψ i‖) *
        ‖(show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x‖ ≤
      (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) :=
    mul_le_mul_of_nonneg_left hT_apply h_prod_nn
  have h_step2 :
      (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) ≤
        M_F * (‖T b‖ * ‖x‖) := by
    have h_inner_nn : 0 ≤ ‖T b‖ * ‖x‖ := mul_nonneg hTb_nn hx_nn
    exact mul_le_mul_of_nonneg_right hΨ_prod_le h_inner_nn
  have h_rearrange : M_F * (‖T b‖ * ‖x‖) = M_F * ‖T b‖ * ‖x‖ := by ring
  have hChain1 :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        (∏ i : Fin s, ‖Ψ i‖) * (‖T b‖ * ‖x‖) :=
    hsubst.trans h_step1
  have hChain2 :
      ‖tensorSlotSubstCLM (I := I) s b Ψ
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) x)‖ ≤
        M_F * (‖T b‖ * ‖x‖) :=
    hChain1.trans h_step2
  rw [h_rearrange] at hChain2
  exact hChain2

end Connection
end Integral
end DifferentialGeometry

end
