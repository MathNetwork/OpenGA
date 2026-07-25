import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.LowerAllUpperIndices
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma chartGramMatrix_inv_isHermitian
    (g : SmoothRiemannianMetric I M) (α b : M) :
    (chartGramMatrix g α b)⁻¹.IsHermitian :=
  (chartGramMatrix_isHermitian (I := I) g α b).inv

private lemma chartTensorInnerPointwise_0s_symm_aux
    (g : SmoothRiemannianMetric I M) (α b : M) (n : ℕ)
    (S T : Tensor0SModel n ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) n g α b S T =
      chartTensorInnerPointwise_0s (I := I) (M := M) n g α b T S := by
  induction n with
  | zero =>
      change S _ * T _ = T _ * S _
      ring
  | succ n ih =>
      rw [chartTensorInnerPointwise_0s_succ, chartTensorInnerPointwise_0s_succ]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      have hG :
          (chartGramMatrix g α b)⁻¹ j i =
            (chartGramMatrix g α b)⁻¹ i j := by
        have hherm := chartGramMatrix_inv_isHermitian (I := I) (M := M) g α b
        have := hherm.apply i j
        simpa [star_trivial] using this
      rw [ih, hG]

private lemma chartTensorInnerPointwise_0s_nonneg_aux
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (n : ℕ)
    (T : Tensor0SModel n ℝ E) :
    0 ≤ chartTensorInnerPointwise_0s (I := I) (M := M) n g α b T T := by
  set Tback : Tensor0SModel n ℝ E :=
    T.compContinuousLinearMap (fun _ : Fin n =>
      chartTrivializationLinearMap (I := I) (M := M) α b) with hTback_def
  have hbridge :=
    tensorInnerPointwise_0s_bridge_identity (I := I) (M := M) g α n hb Tback Tback
  have hcomp_id :
      Tback.compContinuousLinearMap
          (fun _ : Fin n => chartTrivializationLinearMapSymm (I := I) (M := M) α b)
        = T := by
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [hTback_def]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (v k)
  rw [hcomp_id] at hbridge
  rw [← hbridge]
  exact tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b n Tback

def chartTensorInnerPointwise_rs_model
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T₀ T₁ : TensorRSModel r s ℝ E) : ℝ :=
  chartTensorInnerPointwise_0s (I := I) (M := M) (r + s) g α b
    (chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T₀)
    (chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T₁)

lemma chartTensorInnerPointwise_rs_model_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ =
      chartTensorInnerPointwise_0s (I := I) (M := M) (r + s) g α b
        (chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T₀)
        (chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T₁) :=
  rfl

lemma chartTensorInnerPointwise_rs_model_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T₀ T₀' T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        (T₀ + T₀') T₁ =
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ +
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀' T₁ := by
  rw [chartTensorInnerPointwise_rs_model_def,
      chartTensorInnerPointwise_rs_model_def,
      chartTensorInnerPointwise_rs_model_def]
  rw [chartLowerAllUpperIndices_model_add]
  rw [chartTensorInnerPointwise_0s_add_left]

lemma chartTensorInnerPointwise_rs_model_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (c : ℝ) (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        (c • T₀) T₁ =
      c * chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ := by
  rw [chartTensorInnerPointwise_rs_model_def,
      chartTensorInnerPointwise_rs_model_def]
  rw [chartLowerAllUpperIndices_model_smul]
  rw [chartTensorInnerPointwise_0s_smul_left]

lemma chartTensorInnerPointwise_rs_model_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ =
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₁ T₀ := by
  rw [chartTensorInnerPointwise_rs_model_def,
      chartTensorInnerPointwise_rs_model_def]
  exact chartTensorInnerPointwise_0s_symm_aux (I := I) (M := M) g α b (r + s) _ _

lemma chartTensorInnerPointwise_rs_model_add_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T₀ T₁ T₁' : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        T₀ (T₁ + T₁') =
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ +
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁' := by
  rw [chartTensorInnerPointwise_rs_model_symm (I := I) (M := M) g r s α b
        T₀ (T₁ + T₁')]
  rw [chartTensorInnerPointwise_rs_model_add_left]
  rw [chartTensorInnerPointwise_rs_model_symm (I := I) (M := M) g r s α b T₁ T₀,
      chartTensorInnerPointwise_rs_model_symm (I := I) (M := M) g r s α b T₁' T₀]

lemma chartTensorInnerPointwise_rs_model_smul_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (c : ℝ) (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        T₀ (c • T₁) =
      c * chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ := by
  rw [chartTensorInnerPointwise_rs_model_symm (I := I) (M := M) g r s α b
        T₀ (c • T₁)]
  rw [chartTensorInnerPointwise_rs_model_smul_left]
  rw [chartTensorInnerPointwise_rs_model_symm (I := I) (M := M) g r s α b T₁ T₀]

lemma chartTensorInnerPointwise_rs_model_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSModel r s ℝ E) :
    0 ≤ chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T := by
  rw [chartTensorInnerPointwise_rs_model_def]
  exact chartTensorInnerPointwise_0s_nonneg_aux (I := I) (M := M) g α hb (r + s) _

section Smoothness

variable [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]

private noncomputable def localEvalBasisLinear (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [ContinuousMultilinearMap.add_apply]
  map_smul' c Φ := by
    funext φ
    simp [ContinuousMultilinearMap.smul_apply]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma localEvalBasisLinear_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    localEvalBasisLinear (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma localEvalBasisLinear_injective (n : ℕ) :
    Function.Injective (localEvalBasisLinear (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => chartModelBasis E) ?_
  intro v
  exact congr_fun h v

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma local_finrank_tensor0SModel (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) =
      (Module.finrank ℝ E) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      rw [(continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ n ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel n ℝ E) ≃ₗ[ℝ]
          (E →ₗ[ℝ] Tensor0SModel n ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma local_finrank_basis_pi (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma localEvalBasisLinear_bijective (n : ℕ) :
    Function.Bijective (localEvalBasisLinear (E := E) n) := by
  have h_inj := localEvalBasisLinear_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [local_finrank_tensor0SModel, local_finrank_basis_pi]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

private noncomputable def localEvalBasisCLE (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (LinearEquiv.ofBijective (localEvalBasisLinear (E := E) n)
    (localEvalBasisLinear_bijective (E := E) n)).toContinuousLinearEquiv

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma localEvalBasisCLE_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    localEvalBasisCLE (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

omit [IsManifold I ∞ M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma local_contMDiffOn_into_tensor0SModel_of_eval_basis
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
        Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U := by
  have hpi : ContMDiffOn I 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun b : M => localEvalBasisCLE (E := E) n (Φ b)) U := by
    rw [contMDiffOn_pi_space]
    intro φ
    exact h φ
  have hsymm_smooth :
      ContMDiff 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ)
        𝓘(ℝ, Tensor0SModel n ℝ E) ∞
        (localEvalBasisCLE (E := E) n).symm :=
    (localEvalBasisCLE (E := E) n).symm.toContinuousLinearMap.contMDiff
  have hcomp := hsymm_smooth.comp_contMDiffOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((localEvalBasisCLE (E := E) n).symm_apply_apply (Φ b)).symm

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chartSeparableFormAt_basis_scalar_contMDiffOn
    (g : SmoothRiemannianMetric I M) {r : ℕ} (α : M)
    (φ_first ψ : Fin r → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
          chartSeparableFormAt (I := I) (M := M) g α b r
            (fun k : Fin r => (chartModelBasis E) (φ_first k))
            (fun k : Fin r => (chartModelBasis E) (ψ k)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have heq :
      (fun b : M =>
          chartSeparableFormAt (I := I) (M := M) g α b r
            (fun k : Fin r => (chartModelBasis E) (φ_first k))
            (fun k : Fin r => (chartModelBasis E) (ψ k)))
        = fun b : M =>
            ∏ k : Fin r,
              chartGramBilin (I := I) (M := M) g α b
                ((chartModelBasis E) (φ_first k))
                ((chartModelBasis E) (ψ k)) := by
    funext b
    exact chartSeparableFormAt_apply (I := I) (M := M) g α b r _ _
  rw [heq]
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  have hentry :
      (fun b : M =>
          chartGramBilin (I := I) (M := M) g α b
            ((chartModelBasis E) (φ_first k))
            ((chartModelBasis E) (ψ k)))
        = fun b : M =>
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ kk : Fin (Module.finrank ℝ E),
                chartGramMatrix g α b j kk *
                  (chartModelBasis E).equivFun
                    ((chartModelBasis E) (φ_first k)) j *
                  (chartModelBasis E).equivFun
                    ((chartModelBasis E) (ψ k)) kk := by
    funext b
    rw [chartGramBilin_apply]
  rw [hentry]
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  refine contMDiffOn_finset_sum (fun kk _ => ?_)
  refine ContMDiffOn.mul ?_ contMDiffOn_const
  refine ContMDiffOn.mul ?_ contMDiffOn_const
  exact chartGramMatrix_entry_contMDiffOn (I := I) g α j kk

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chartLowerAllUpperIndices_model_basis_eval_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : TensorRSModel r s ℝ E)
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
          (chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T)
            (fun k : Fin (r + s) => (chartModelBasis E) (φ k)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  set v_last : Fin s → E :=
    fun j => (chartModelBasis E) (φ (Fin.natAdd r j)) with hv_last
  set v_first : Fin r → E :=
    fun k => (chartModelBasis E) (φ (Fin.castAdd s k)) with hv_first
  have hrewrite :
      (fun b : M =>
          (chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T)
            (fun k : Fin (r + s) => (chartModelBasis E) (φ k)))
        = fun b : M =>
            T (chartSeparableFormAt (I := I) (M := M) g α b r v_first) v_last := by
    funext b
    rw [chartLowerAllUpperIndices_model_apply]
  rw [hrewrite]
  let evalLast : Tensor0SModel s ℝ E →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ v_last
  let composed : Tensor0SModel r ℝ E →L[ℝ] ℝ := evalLast.comp T
  have hcomposed_apply : ∀ Φ : Tensor0SModel r ℝ E,
      composed Φ = T Φ v_last := fun _ => rfl
  have hSep : ContMDiffOn I 𝓘(ℝ, Tensor0SModel r ℝ E) ∞
      (fun b : M => chartSeparableFormAt (I := I) (M := M) g α b r v_first)
      (trivializationAt E (TangentSpace I) α).baseSet := by
    refine
      local_contMDiffOn_into_tensor0SModel_of_eval_basis (I := I) (M := M) _ ?_
    intro ψ
    have h_unfold :
        (fun b : M =>
            (chartSeparableFormAt (I := I) (M := M) g α b r v_first)
              (fun k : Fin r => (chartModelBasis E) (ψ k)))
          = fun b : M =>
              chartSeparableFormAt (I := I) (M := M) g α b r
                (fun k : Fin r => (chartModelBasis E)
                  (φ (Fin.castAdd s k)))
                (fun k : Fin r => (chartModelBasis E) (ψ k)) := by
      funext b
      rfl
    rw [h_unfold]
    exact chartSeparableFormAt_basis_scalar_contMDiffOn
      (I := I) (M := M) g (r := r) α _ _
  have hcomp : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => composed
        (chartSeparableFormAt (I := I) (M := M) g α b r v_first))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    composed.contMDiff.comp_contMDiffOn hSep
  refine hcomp.congr ?_
  intro b _
  exact hcomposed_apply _

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartTensorInnerPointwise_rs_model_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T₀ T₁)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hunfold :
      (fun b : M =>
          chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T₀ T₁)
        = fun b : M =>
            chartTensorInnerPointwise_0s (I := I) (M := M) (r + s) g α b
              (chartLowerAllUpperIndices_model (I := I) (M := M)
                r s g α b T₀)
              (chartLowerAllUpperIndices_model (I := I) (M := M)
                r s g α b T₁) := by
    funext b
    rw [chartTensorInnerPointwise_rs_model_def]
  rw [hunfold]
  exact chartTensorInnerPointwise_0s_contMDiffOn_smooth_args
    (I := I) (M := M) g α (r + s)
    (fun b : M => chartLowerAllUpperIndices_model
      (I := I) (M := M) r s g α b T₀)
    (fun b : M => chartLowerAllUpperIndices_model
      (I := I) (M := M) r s g α b T₁)
    (fun φ =>
      chartLowerAllUpperIndices_model_basis_eval_contMDiffOn
        (I := I) (M := M) g r s α T₀ φ)
    (fun φ =>
      chartLowerAllUpperIndices_model_basis_eval_contMDiffOn
        (I := I) (M := M) g r s α T₁ φ)

end Smoothness

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
