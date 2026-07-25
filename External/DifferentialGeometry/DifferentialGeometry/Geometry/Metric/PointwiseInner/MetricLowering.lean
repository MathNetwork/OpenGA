import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace TensorMetricLowering

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Tensor.TensorRSRiemannian

private noncomputable def evalAtBasisLinear (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [ContinuousMultilinearMap.add_apply]
  map_smul' c Φ := by
    funext φ
    simp [ContinuousMultilinearMap.smul_apply]

omit [InnerProductSpace ℝ E] in
@[simp] private lemma evalAtBasisLinear_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisLinear (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

omit [InnerProductSpace ℝ E] in
private lemma evalAtBasisLinear_injective (n : ℕ) :
    Function.Injective (evalAtBasisLinear (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => chartModelBasis E) ?_
  intro v
  exact congr_fun h v

omit [InnerProductSpace ℝ E] in
private lemma finrank_tensor0SModel (n : ℕ) :
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

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] in
private lemma finrank_basis_pi (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

omit [InnerProductSpace ℝ E] in
private lemma evalAtBasisLinear_bijective (n : ℕ) :
    Function.Bijective (evalAtBasisLinear (E := E) n) := by
  have h_inj := evalAtBasisLinear_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [finrank_tensor0SModel, finrank_basis_pi]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

private noncomputable def evalAtBasisCLE (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (LinearEquiv.ofBijective (evalAtBasisLinear (E := E) n)
    (evalAtBasisLinear_bijective (E := E) n)).toContinuousLinearEquiv

omit [InnerProductSpace ℝ E] in
@[simp] private lemma evalAtBasisCLE_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLE (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

omit [InnerProductSpace ℝ E] in
private lemma continuousOn_into_tensor0SModel_of_eval_basis
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContinuousOn (fun b : M =>
        Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U) :
    ContinuousOn Φ U := by
  have hpi : ContinuousOn
      (fun b : M => evalAtBasisCLE (E := E) n (Φ b)) U := by
    rw [continuousOn_pi]
    intro φ
    exact h φ
  have hcomp := (evalAtBasisCLE (E := E) n).symm.continuous.comp_continuousOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((evalAtBasisCLE (E := E) n).symm_apply_apply (Φ b)).symm

omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
private lemma contMDiffOn_into_tensor0SModel_of_eval_basis
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
        Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U := by
  have hpi : ContMDiffOn I 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun b : M => evalAtBasisCLE (E := E) n (Φ b)) U := by
    rw [contMDiffOn_pi_space]
    intro φ
    exact h φ
  have hsymm_smooth :
      ContMDiff 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ)
        𝓘(ℝ, Tensor0SModel n ℝ E) ∞
        (evalAtBasisCLE (E := E) n).symm :=
    (evalAtBasisCLE (E := E) n).symm.toContinuousLinearMap.contMDiff
  have hcomp := hsymm_smooth.comp_contMDiffOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((evalAtBasisCLE (E := E) n).symm_apply_apply (Φ b)).symm

omit [InnerProductSpace ℝ E] in
private lemma loweredCompose_at_basis_tuple
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E)
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    loweredCompose (I := I) (M := M) g r s α b T
        (fun i : Fin (r + s) => (chartModelBasis E) (φ i)) =
      lowerAllUpperIndices (I := I) (M := M) g r s b T
        (fun i : Fin (r + s) =>
          chartBasisVecFiber (I := I) α (φ i) b) := by
  rw [loweredCompose_apply]
  rfl

omit [InnerProductSpace ℝ E] in
private theorem trivializationAt_lowered_section_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E) :
    (trivializationAt (Tensor0SModel (r + s) ℝ E)
        (fun y : M => Tensor0SSpace (r + s) I y) α
        ⟨b, Tensor0SSpace.ofModel
          (lowerAllUpperIndices (I := I) (M := M) g r s b T)⟩).2
      = loweredCompose (I := I) (M := M) g r s α b T := by
  change ((lowerAllUpperIndices (I := I) (M := M) g r s b T).compContinuousLinearMap
    (fun _ : Fin (r + s) =>
      (trivializationAt E (TangentSpace I) α).symmL ℝ b)) =
    loweredCompose (I := I) (M := M) g r s α b T
  rfl

private noncomputable def separableFormBundleSection
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    M → TotalSpace (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) :=
  fun b => TotalSpace.mk' (Tensor0SModel r ℝ E)
    (E := fun y : M => Tensor0SSpace r I y) b
    (Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)))

omit [InnerProductSpace ℝ E] in
private theorem trivializationAt_separableFormBundleSection_eq
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) (b : M) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α
        (separableFormBundleSection (I := I) (M := M) g r α φ_first b)).2 =
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)).compContinuousLinearMap
        (fun _ : Fin r => (trivializationAt E (TangentSpace I) α).symmL ℝ b) := by
  unfold separableFormBundleSection
  rfl

omit [InnerProductSpace ℝ E] in
private theorem trivializationAt_separableFormBundleSection_eval_basis
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) {b : M}
    (ψ : Fin r → Fin (Module.finrank ℝ E)) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α
        (separableFormBundleSection (I := I) (M := M) g r α φ_first b)).2
        (fun k : Fin r => (chartModelBasis E) (ψ k)) =
      ∏ k : Fin r,
        chartGramMatrix (I := I) g α b (φ_first k) (ψ k) := by
  rw [trivializationAt_separableFormBundleSection_eq (I := I) (M := M) g r α φ_first b]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _

  rw [chartGramMatrix_apply]

  rfl

omit [InnerProductSpace ℝ E] in
private lemma contMDiffOn_separableFormBundleSection
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (separableFormBundleSection (I := I) (M := M) g r α φ_first)
      (trivializationAt E (TangentSpace I) α).baseSet := by

  set e : Trivialization (Tensor0SModel r ℝ E)
    (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) → M) :=
    trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α
  have hbaseSet_eq : e.baseSet = (trivializationAt E (TangentSpace I) α).baseSet := rfl
  have h_iff := e.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)
    (s := fun b => Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)))
  rw [hbaseSet_eq] at h_iff

  refine h_iff.mpr ?_

  refine contMDiffOn_into_tensor0SModel_of_eval_basis _ ?_
  intro ψ

  have h_prod_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ∏ k : Fin r,
        chartGramMatrix (I := I) g α b (φ_first k) (ψ k))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    refine contMDiffOn_finset_prod (fun k _ => ?_)
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (φ_first k) (ψ k)

  refine h_prod_smooth.congr (fun b _hb => ?_)
  exact trivializationAt_separableFormBundleSection_eval_basis
    (I := I) (M := M) g r α φ_first ψ

omit [InnerProductSpace ℝ E] in
private lemma contMDiffOn_lower_at_chartBasis_aux_general
    (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (S : ∀ b : M, TensorRSSpace r s I b)
    (hS : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y) b (S b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lowerAllUpperIndices (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (S b))
        (fun i : Fin (r + s) =>
          chartBasisVecFiber (I := I) α (φ i) b))
      (trivializationAt E (TangentSpace I) α).baseSet := by

  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_

  have h_sep_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (separableFormBundleSection (I := I) (M := M) g r α
          (fun k : Fin r => φ (Fin.castAdd s k)))
        x₀ :=
    (contMDiffOn_separableFormBundleSection (I := I) (M := M) g r α
      (fun k : Fin r => φ (Fin.castAdd s k))).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)

  have h_S_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) b (S b)) x₀ :=
    hS.contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)

  have h_applied : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel s ℝ E)
          (E := fun y : M => Tensor0SSpace s I y) b
          ((S b)
            (Tensor0SSpace.ofModel
              (separableFormAt (I := I) (M := M) g b r
                (fun k : Fin r =>
                  chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b))))) x₀ :=
    ContMDiffAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel r ℝ E) (F₂ := Tensor0SModel s ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (IM := I) (IB := I)
      (b := id) (ϕ := fun b : M => S b)
      (v := fun b : M =>
        Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g b r
            (fun k : Fin r =>
              chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b)))
      h_S_smooth_at h_sep_smooth_at

  have h_tangent_smooth_at : ∀ j : Fin s,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
            (chartBasisVecFiber (I := I) α (φ (Fin.natAdd r j)) b)) x₀ := by
    intro j
    have hcm := chartBasisVec_contMDiffOn (I := I) α (φ (Fin.natAdd r j))
    exact hcm.contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)

  have h_eval := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := M)
    (T := fun b : M =>
      (S b)
        (Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g b r
            (fun k : Fin r =>
              chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b))))
    h_applied
    (v := fun (j : Fin s) (b : M) =>
      chartBasisVecFiber (I := I) α (φ (Fin.natAdd r j)) b)
    h_tangent_smooth_at

  refine h_eval.congr_of_eventuallyEq ?_
  filter_upwards with b
  rw [lowerAllUpperIndices_apply]
  rfl

omit [InnerProductSpace ℝ E] in
private lemma contMDiffOn_lower_at_chartBasis_aux
    (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lowerAllUpperIndices (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (S b))
        (fun i : Fin (r + s) =>
          chartBasisVecFiber (I := I) α (φ i) b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
  contMDiffOn_lower_at_chartBasis_aux_general (I := I) (M := M) r s g α
    (fun b : M => S b)
    (S.contMDiff.contMDiffOn)
    φ

omit [InnerProductSpace ℝ E] in
theorem contMDiffOn_loweredCompose
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
    (α : M) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  refine contMDiffOn_into_tensor0SModel_of_eval_basis _ ?_
  intro φ
  refine ContMDiffOn.congr ?_ (fun b _ =>
    (loweredCompose_at_basis_tuple (I := I) (M := M) g r s α b
      (TensorRSSpace.toModel (S b)) φ).symm)
  exact contMDiffOn_lower_at_chartBasis_aux r s g α S φ

omit [InnerProductSpace ℝ E] in
theorem contMDiffOn_loweredCompose_of_section_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : ∀ b : M, TensorRSSpace r s I b) (α : M)
    (hS : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y) b (S b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  refine contMDiffOn_into_tensor0SModel_of_eval_basis _ ?_
  intro φ
  refine ContMDiffOn.congr ?_ (fun b _ =>
    (loweredCompose_at_basis_tuple (I := I) (M := M) g r s α b
      (TensorRSSpace.toModel (S b)) φ).symm)
  exact contMDiffOn_lower_at_chartBasis_aux_general (I := I) (M := M) r s g α S hS φ

omit [InnerProductSpace ℝ E] in
theorem continuous_loweredCompose
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)
    (α : M) :
    ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
  (contMDiffOn_loweredCompose (I := I) (M := M) g r s S α).continuousOn

omit [InnerProductSpace ℝ E] in
theorem contMDiff_lifted_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (r + s) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun y : M => Tensor0SSpace (r + s) I y) b
        (Tensor0SSpace.ofModel
          (lowerAllUpperIndices (I := I) (M := M) g r s b
            (TensorRSSpace.toModel (S b))))) := by
  intro x₀
  rw [Bundle.contMDiffAt_section]
  refine ((contMDiffOn_loweredCompose (I := I) (M := M) g r s S x₀).contMDiffAt
    ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _))).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _)] with b _
  exact (trivializationAt_lowered_section_eq (I := I) (M := M) g r s x₀ b
    (TensorRSSpace.toModel (S b))).symm

omit [InnerProductSpace ℝ E] in
theorem continuous_lifted_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    Continuous (fun b : M => TotalSpace.mk' (Tensor0SModel (r + s) ℝ E)
        (E := fun y : M => Tensor0SSpace (r + s) I y) b
        (Tensor0SSpace.ofModel
          (lowerAllUpperIndices (I := I) (M := M) g r s b
            (TensorRSSpace.toModel (S b))))) :=
  (contMDiff_lifted_section (I := I) (M := M) g r s S).continuous

end TensorMetricLowering

end
