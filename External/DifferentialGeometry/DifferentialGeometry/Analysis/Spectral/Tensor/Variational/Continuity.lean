import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivSupport
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Operator.Gradient
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn


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
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDeriv_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun y : M => TensorRSSpace r s I y) b
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
  haveI hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun b : M => (⟨b, covLC.toFun (fun y : M => S.toSection y) b⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => S.toSection y)
      (S.toSection.contMDiff.contMDiffOn)
  have hX_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (chartBasisVecFiber (I := I) α i b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have := chartBasisVec_contMDiffOn (I := I) α i
    exact this
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hcov_at : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun b : M => (⟨b, covLC.toFun (fun y : M => S.toSection y) b⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)) x₀ :=
    hop.contMDiffAt (Filter.univ_mem)
  have hX_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (chartBasisVecFiber (I := I) α i b)) x₀ :=
    (hX_on x₀ hx₀).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  exact hcov_at.clm_bundle_apply hX_at

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDeriv_chartBasis_trivImage_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)⟩).2)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hsection := tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g r s S α i
  have hbase_eq : (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet =
        (trivializationAt E (TangentSpace I) α).baseSet := by
    change ((trivializationAt (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((trivializationAt (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (trivializationAt E (TangentSpace I) α).baseSet
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet =
            (trivializationAt E (TangentSpace I) α).baseSet
    exact Set.inter_self _
  rw [← hbase_eq]
  rw [← Bundle.Trivialization.contMDiffOn_section_baseSet_iff
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α)]
  rw [hbase_eq]
  exact hsection

private noncomputable def evalAtBasisLinearLocal (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [ContinuousMultilinearMap.add_apply]
  map_smul' c Φ := by
    funext φ
    simp [ContinuousMultilinearMap.smul_apply]

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma evalAtBasisLinearLocal_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisLinearLocal (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma evalAtBasisLinearLocal_injective (n : ℕ) :
    Function.Injective (evalAtBasisLinearLocal (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => chartModelBasis E) ?_
  intro v
  exact congr_fun h v

omit [NeZero (Module.finrank ℝ E)] in
private lemma finrank_tensor0SModel_local (n : ℕ) :
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

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma finrank_basis_pi_local (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

omit [NeZero (Module.finrank ℝ E)] in
private lemma evalAtBasisLinearLocal_bijective (n : ℕ) :
    Function.Bijective (evalAtBasisLinearLocal (E := E) n) := by
  have h_inj := evalAtBasisLinearLocal_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [finrank_tensor0SModel_local, finrank_basis_pi_local]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

private noncomputable def evalAtBasisCLELocal (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (LinearEquiv.ofBijective (evalAtBasisLinearLocal (E := E) n)
    (evalAtBasisLinearLocal_bijective (E := E) n)).toContinuousLinearEquiv

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma evalAtBasisCLELocal_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLELocal (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma contMDiffOn_into_tensor0SModel_of_eval_basis_local
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
        Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U := by
  have hpi : ContMDiffOn I 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun b : M => evalAtBasisCLELocal (E := E) n (Φ b)) U := by
    rw [contMDiffOn_pi_space]
    intro φ
    exact h φ
  have hsymm_smooth :
      ContMDiff 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ)
        𝓘(ℝ, Tensor0SModel n ℝ E) ∞
        (evalAtBasisCLELocal (E := E) n).symm :=
    (evalAtBasisCLELocal (E := E) n).symm.toContinuousLinearMap.contMDiff
  have hcomp := hsymm_smooth.comp_contMDiffOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((evalAtBasisCLELocal (E := E) n).symm_apply_apply (Φ b)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma loweredCompose_at_basis_tuple_local
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramMatrixInv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix (I := I) g α b)⁻¹ i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun b : M => (chartGramMatrix (I := I) g α b)⁻¹ i j)
        = (fun b : M => (chartGramMatrix (I := I) g α b).det⁻¹ *
              (chartGramMatrix (I := I) g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  intro b hb
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (chartGramMatrix (I := I) g α b).det :=
    chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (chartGramMatrix (I := I) g α b).det ≠ 0 := ne_of_gt hpos
  exact (ContMDiffWithinAt.inv₀ hdet hpos_ne).mul hadj

private noncomputable def separableFormBundleSectionLocal
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    M → TotalSpace (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) :=
  fun b => TotalSpace.mk' (Tensor0SModel r ℝ E)
    (E := fun y : M => Tensor0SSpace r I y) b
    (Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem trivializationAt_separableFormBundleSectionLocal_eval_basis
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) {b : M}
    (ψ : Fin r → Fin (Module.finrank ℝ E)) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α
        (separableFormBundleSectionLocal (I := I) (M := M) g r α φ_first b)).2
        (fun k : Fin r => (chartModelBasis E) (ψ k)) =
      ∏ k : Fin r,
        chartGramMatrix (I := I) g α b (φ_first k) (ψ k) := by
  unfold separableFormBundleSectionLocal
  change ((separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)).compContinuousLinearMap
        (fun _ : Fin r => (trivializationAt E (TangentSpace I) α).symmL ℝ b))
      (fun k : Fin r => (chartModelBasis E) (ψ k)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [chartGramMatrix_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma contMDiffOn_separableFormBundleSectionLocal
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (separableFormBundleSectionLocal (I := I) (M := M) g r α φ_first)
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
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local
    (I := I) (M := M) _ ?_
  intro ψ
  have h_prod_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ∏ k : Fin r,
        chartGramMatrix (I := I) g α b (φ_first k) (ψ k))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    refine contMDiffOn_finset_prod (fun k _ => ?_)
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (φ_first k) (ψ k)
  refine h_prod_smooth.congr (fun b _hb => ?_)
  exact trivializationAt_separableFormBundleSectionLocal_eval_basis
    (I := I) (M := M) g r α φ_first ψ

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma contMDiffOn_lower_chartCov_at_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E))
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lowerAllUpperIndices (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (fun j : Fin (r + s) =>
          chartBasisVecFiber (I := I) α (φ j) b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have h_sep_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (separableFormBundleSectionLocal (I := I) (M := M) g r α
          (fun k : Fin r => φ (Fin.castAdd s k)))
        x₀ :=
    (contMDiffOn_separableFormBundleSectionLocal (I := I) (M := M) g r α
      (fun k : Fin r => φ (Fin.castAdd s k))).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_S_smooth_on := tensorCovDeriv_chartBasis_contMDiffOn
    (I := I) (M := M) g r s S α i
  have h_S_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) b
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))) x₀ :=
    h_S_smooth_on.contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_applied : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel s ℝ E)
          (E := fun y : M => Tensor0SSpace s I y) b
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))
            (Tensor0SSpace.ofModel
              (separableFormAt (I := I) (M := M) g b r
                (fun k : Fin r =>
                  chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b))))) x₀ :=
    ContMDiffAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel r ℝ E) (F₂ := Tensor0SModel s ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (IM := I) (IB := I)
      (b := id)
      (ϕ := fun b : M =>
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
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
    exact (chartBasisVec_contMDiffOn (I := I) α (φ (Fin.natAdd r j))).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have h_eval := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := M)
    (T := fun b : M =>
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))
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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma contMDiffOn_loweredCompose_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local
    (I := I) (M := M) _ ?_
  intro φ
  refine ContMDiffOn.congr ?_ (fun b _ =>
    (loweredCompose_at_basis_tuple_local
      (I := I) (M := M) g r s α b
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α i b))) φ).symm)
  exact contMDiffOn_lower_chartCov_at_basis (I := I) (M := M) g r s S α i φ

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuousOn_loweredCompose_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
  (contMDiffOn_loweredCompose_chartCov (I := I) (M := M) g r s S α i).continuousOn

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuousOn_tensorInnerPointwise_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b))))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hSα := continuousOn_loweredCompose_chartCov (I := I) (M := M) g r s S α i
  have hTα := continuousOn_loweredCompose_chartCov (I := I) (M := M) g r s T α j
  have hchart :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_continuousOn
      (I := I) (M := M) g α r s
      (fun b : M => TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α i b)))
      (fun b : M => TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s T b
          (chartBasisVecFiber (I := I) α j b)))
      hSα hTα
  refine ContinuousOn.congr hchart ?_
  intro b hb
  exact tensorInnerPointwise_bridge_identity
    (I := I) (M := M) g α r s hb
    (TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)))
    (TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s T b
        (chartBasisVecFiber (I := I) α j b)))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTensorCovDerivPointwiseInner_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (chartTensorCovDerivPointwiseInner (I := I) (M := M) g α r s S T)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  unfold chartTensorCovDerivPointwiseInner
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · exact (chartGramMatrixInv_entry_contMDiffOn (I := I) (M := M) g α i j).continuousOn
  · exact continuousOn_tensorInnerPointwise_chartCov (I := I) (M := M) g r s S T α i j

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have h_chart_cont := chartTensorCovDerivPointwiseInner_continuousOn
    (I := I) (M := M) g r s S T x
  have h_cong : ∀ b ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b =
        chartTensorCovDerivPointwiseInner (I := I) (M := M) g x r s S T b := by
    intro b hb
    exact (chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
      (I := I) (M := M) g x r s S T hb).symm
  have h_local : ContinuousOn
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    h_chart_cont.congr h_cong
  exact h_local.continuousAt (hOpen.mem_nhds hx_base)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    MeasureTheory.Integrable
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (tensorCovDerivPointwiseInner_continuous
      (I := I) (M := M) g r s S T).integrable_of_hasCompactSupport
    (tensorCovDerivPointwiseInner_hasCompactSupport
      (I := I) (M := M) g r s S T)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
