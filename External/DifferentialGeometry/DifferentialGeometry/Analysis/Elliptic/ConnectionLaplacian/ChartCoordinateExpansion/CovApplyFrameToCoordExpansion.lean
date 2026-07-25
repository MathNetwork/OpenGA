import DifferentialGeometry.Geometry.Connection.ChartFrameNormGlobalSmoothCoordBasisExpansion
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter NormedSpace
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def chartModelBasisProj (k : Fin (Module.finrank ℝ E)) :
    E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj k).comp ((chartModelBasis E).equivFun.toLinearMap)) :
      E →ₗ[ℝ] ℝ)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma chartModelBasisProj_apply (k : Fin (Module.finrank ℝ E))
    (v : E) :
    chartModelBasisProj (E := E) k v =
      ((chartModelBasis E).repr v) k := by
  classical
  unfold chartModelBasisProj
  change ((LinearMap.proj k).comp ((chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

omit [I.Boundaryless] [BoundarylessManifold I M] in
private lemma chartFrameNormGlobalSmoothCoordMatrix_eq_clmAt_proj
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b =
      chartModelBasisProj (E := E) k
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) := by
  classical
  unfold chartFrameNormGlobalSmoothCoordMatrix
  rw [dif_pos hb]
  unfold chartBasisFamily
  rw [Module.Basis.map_repr]
  simp only [LinearEquiv.trans_apply]
  rw [chartModelBasisProj_apply]
  congr 2
  have h := Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ)
    (e := trivializationAt E (TangentSpace I) α) (b := b) hb
  exact congrArg (fun (f : TangentSpace I b → E) => f
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) h

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
lemma chartFrameNormGlobalSmoothCoordMatrix_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hB_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) :=
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff
  have h_triv :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun b : M =>
          ((trivializationAt E (TangentSpace I) α)
            ⟨b, (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b⟩).2)
        (trivializationAt E (TangentSpace I) α).baseSet := by
    have hiff := (trivializationAt E (TangentSpace I) α).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun b : M =>
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
    exact hiff.mp hB_smooth.contMDiffOn
  have h_eq_baseSet :
      Set.EqOn (fun b : M =>
          ((trivializationAt E (TangentSpace I) α)
            ⟨b, (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b⟩).2)
        (fun b : M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro b hb
    change ((trivializationAt E (TangentSpace I) α) ⟨b,
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b⟩).2 =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
    have h₁ : ((trivializationAt E (TangentSpace I) α) ⟨b,
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b⟩).2 =
        ((trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ b hb)
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) := by
      have hp := Trivialization.apply_eq_prod_continuousLinearEquivAt
        (R := ℝ) (e := trivializationAt E (TangentSpace I) α) (b := b) hb
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
      have hsnd := congrArg Prod.snd hp
      simp only at hsnd
      exact hsnd
    rw [h₁]
    have hclm := Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ)
      (e := trivializationAt E (TangentSpace I) α) (b := b) hb
    exact congrArg (fun (f : TangentSpace I b → E) => f
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) hclm
  have h_triv' :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun b : M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
    refine h_triv.congr ?_
    intro y hy
    exact (h_eq_baseSet hy).symm
  have h_clm_smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (chartModelBasisProj (E := E) k : E → ℝ) :=
    (chartModelBasisProj (E := E) k).contMDiff
  have h_comp :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        ((chartModelBasisProj (E := E) k : E → ℝ) ∘
          (fun b : M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    h_clm_smooth.contMDiffOn.comp (t := Set.univ) h_triv' (Set.subset_preimage_univ)
  refine h_comp.congr ?_
  intro b hb
  exact chartFrameNormGlobalSmoothCoordMatrix_eq_clmAt_proj
    (I := I) (M := M) g α i k hb

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
private lemma chartFrameNormGlobalSmoothCoordMatrix_mdiffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M =>
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b) b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have h_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have h_contMDiffOn :=
    chartFrameNormGlobalSmoothCoordMatrix_contMDiffOn (I := I) (M := M) g α i k
  have h_contMDiffAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b) b :=
    (h_contMDiffOn b hb_base).contMDiffAt (h_open.mem_nhds hb_base)
  exact h_contMDiffAt.mdifferentiableAt (by simp)

omit [I.Boundaryless] in
private lemma covApply_frameVec_eq_coord_sum_on_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (i : Fin (Module.finrank ℝ E))
    {y : M}
    (hy : y ∈ chartLeviCivitaGoodSet (I := I) α) :
    covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g))
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
        (fun z : M => T₀.toSection z) y =
      ∑ k : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k y •
          covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (fun z : M => chartBasisVecFiber (I := I) α k z)
            (fun z : M => T₀.toSection z) y := by
  classical
  change (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun (fun z : M => T₀.toSection z) y
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun y) =
    ∑ k : Fin (Module.finrank ℝ E),
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k y •
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun (fun z : M => T₀.toSection z) y
            (chartBasisVecFiber (I := I) α k y)
  have hExpand :
      (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun y =
        ∑ k : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k y •
            chartBasisVecFiber (I := I) α k y := by
    have h := chartFrameNormGlobalSmooth_eq_coordMatrix_sum
      (I := I) (M := M) g α i (b := y) hy
    have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
          Π b : M, TangentSpace I b) y)
        = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun y := rfl
    rw [hcoerce] at h
    exact h
  rw [hExpand]
  set L : TangentSpace I y →L[ℝ] TensorRSSpace r s I y :=
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun (fun z : M => T₀.toSection z) y
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [L.map_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartBasisVecFiber_mdiffAt
    (α : M) (k : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
        (chartBasisVecFiber (I := I) α k z)) b := by
  classical
  have h_contMDiffOn := chartBasisVec_contMDiffOn (I := I) α k
  have h_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have h_contMDiffAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) α k) b :=
    (h_contMDiffOn b hb).contMDiffAt (h_open.mem_nhds hb)
  exact h_contMDiffAt.mdifferentiableAt (by simp)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covApply_chartBasisVecFiber_T₀_mdiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (k : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (fun w : M => chartBasisVecFiber (I := I) α k w)
          (fun w : M => T₀.toSection w) z)) b := by
  classical
  have hcov_RS_smooth :
      CovariantDerivative.ContMDiffCovariantDerivative
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) ∞ := inferInstance
  have hT₀_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (T₀.toSection z)) :=
    T₀.toSection.contMDiff
  have hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
        (chartBasisVecFiber (I := I) α k z)) b :=
    chartBasisVecFiber_mdiffAt (I := I) (M := M) α k (b := b) hb
  have hHomSec_on :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
        (fun z : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
          (E := fun w : M => TangentSpace I w →L[ℝ] TensorRSSpace r s I w) z
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun (fun w : M => T₀.toSection w) z))
        Set.univ :=
    hcov_RS_smooth.contMDiff.contMDiff hT₀_smooth.contMDiffOn
  have hHomSec_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
          (E := fun w : M => TangentSpace I w →L[ℝ] TensorRSSpace r s I w) z
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun (fun w : M => T₀.toSection w) z)) b :=
    ((hHomSec_on.contMDiffAt (Filter.univ_mem))).mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (b := id) hHomSec_at hX_at

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma finsum_smul_section_mdiffAt
    {ι : Type*} (s_finset : Finset ι)
    (r s : ℕ) (f : ι → M → ℝ)
    (σ : ι → Π z : M, TensorRSSpace r s I z)
    {b : M}
    (hf : ∀ i ∈ s_finset, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) b)
    (hσ : ∀ i ∈ s_finset, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (σ i z)) b) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (∑ i ∈ s_finset, f i z • σ i z)) b := by
  classical
  induction s_finset using Finset.induction_on with
  | empty =>
    have h0 : (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (∑ i ∈ (∅ : Finset ι), f i z • σ i z)) =
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (0 : TensorRSSpace r s I z)) := by
      funext z; simp
    rw [h0]
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ)
      (E := fun z : M => TensorRSSpace r s I z) (F := TensorRSModel r s ℝ E)
  | @insert k₀ t hk₀t ih =>
    have hf_k₀ : MDifferentiableAt I 𝓘(ℝ, ℝ) (f k₀) b :=
      hf k₀ (Finset.mem_insert_self k₀ t)
    have hσ_k₀ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (σ k₀ z)) b :=
      hσ k₀ (Finset.mem_insert_self k₀ t)
    have hf_rest : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) b := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hσ_rest : ∀ i ∈ t, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (σ i z)) b :=
      fun i hi => hσ i (Finset.mem_insert_of_mem hi)
    have hrest := ih hf_rest hσ_rest
    have hsplit : (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (∑ i ∈ insert k₀ t, f i z • σ i z)) =
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        ((fun w : M => f k₀ w • σ k₀ w) z + (fun w : M => ∑ i ∈ t, f i w • σ i w) z)) := by
      funext z
      congr 1
      rw [Finset.sum_insert hk₀t]
    rw [hsplit]
    have hf_k₀_σ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          ((fun w : M => f k₀ w • σ k₀ w) z)) b := by
      have := MDifferentiableAt.smul_section (𝕜 := ℝ)
        (E := fun z : M => TensorRSSpace r s I z) (F := TensorRSModel r s ℝ E)
        (f := f k₀) (s := σ k₀) (x₀ := b) hf_k₀ hσ_k₀
      exact this
    exact mdifferentiableAt_add_section hf_k₀_σ hrest

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cov_RS_finsum_smul_section_leibniz_apply
    {ι : Type*} (s_finset : Finset ι)
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : ι → M → ℝ) (σ : ι → Π z : M, TensorRSSpace r s I z)
    {b : M}
    (hf : ∀ i ∈ s_finset, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) b)
    (hσ : ∀ i ∈ s_finset, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (σ i z)) b)
    (v : TangentSpace I b) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
        (fun z : M => ∑ i ∈ s_finset, f i z • σ i z) b v =
      ∑ i ∈ s_finset,
        (f i b • (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun (σ i) b v +
          extDerivFun (f i) b v • σ i b) := by
  classical
  induction s_finset using Finset.induction_on with
  | empty =>
    have h0 : (fun z : M => (∑ i ∈ (∅ : Finset ι), f i z • σ i z :
        TensorRSSpace r s I z)) = (fun _ : M => 0) := by
      funext z; simp
    rw [h0]
    have hZero : (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
        (fun _ : M => (0 : TensorRSSpace r s I _)) b = 0 := by
      exact (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.zero (hx := Set.mem_univ b)
    rw [hZero]
    simp
  | @insert k t hkt ih =>
    have hf_k : MDifferentiableAt I 𝓘(ℝ, ℝ) (f k) b :=
      hf k (Finset.mem_insert_self k t)
    have hσ_k : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (σ k z)) b :=
      hσ k (Finset.mem_insert_self k t)
    have hf_rest : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) b := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hσ_rest : ∀ i ∈ t, MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (σ i z)) b :=
      fun i hi => hσ i (Finset.mem_insert_of_mem hi)
    have hsum_apply : ∀ z : M, (∑ i ∈ insert k t, f i z • σ i z :
        TensorRSSpace r s I z) =
        f k z • σ k z + ∑ i ∈ t, f i z • σ i z := by
      intro z; rw [Finset.sum_insert hkt]
    have h_fkσk_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (f k z • σ k z)) b :=
      MDifferentiableAt.smul_section (𝕜 := ℝ)
        (E := fun z : M => TensorRSSpace r s I z) (F := TensorRSModel r s ℝ E)
        (f := f k) (s := σ k) (x₀ := b) hf_k hσ_k
    have h_sum_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z (∑ i ∈ t, f i z • σ i z)) b :=
      finsum_smul_section_mdiffAt (I := I) (M := M)
        (s_finset := t) r s f σ (b := b) hf_rest hσ_rest
    have hfun_eq :
        (fun z : M => ∑ i ∈ insert k t, f i z • σ i z) =
        ((fun z : M => f k z • σ k z) + (fun z : M => ∑ i ∈ t, f i z • σ i z)) := by
      funext z
      change ∑ i ∈ insert k t, f i z • σ i z =
        (fun z : M => f k z • σ k z) z + (fun z : M => ∑ i ∈ t, f i z • σ i z) z
      rw [hsum_apply z]
    rw [hfun_eq]
    rw [(TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.add
      (σ := fun z : M => f k z • σ k z)
      (σ' := fun z : M => ∑ i ∈ t, f i z • σ i z)
      (x := b) h_fkσk_mdiff h_sum_mdiff]
    have h_leib_k := (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.leibniz
      (σ := σ k) (g := f k) (x := b) hσ_k hf_k
    have h_smul_form : (fun z : M => f k z • σ k z) = (f k • σ k :
        Π z : M, TensorRSSpace r s I z) := rfl
    rw [h_smul_form]
    rw [h_leib_k]
    have h_ih := ih hf_rest hσ_rest
    rw [ContinuousLinearMap.add_apply]
    rw [h_ih]
    rw [Finset.sum_insert hkt]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]

omit [I.Boundaryless] in
theorem cov_RS_covApply_frameVec_eq_coord_expansion
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∀ l : Fin (Module.finrank ℝ E),
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
            (fun z : M => T₀.toSection z)) b
          (chartBasisVecFiber (I := I) α l b) =
        (∑ k : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b •
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (fun z : M => chartBasisVecFiber (I := I) α k z)
                  (fun z : M => T₀.toSection z)) b
                (chartBasisVecFiber (I := I) α l b)) +
        (∑ k : Fin (Module.finrank ℝ E),
          extDerivFun (fun z : M =>
              chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z)
              b (chartBasisVecFiber (I := I) α l b) •
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (fun z : M => chartBasisVecFiber (I := I) α k z)
              (fun z : M => T₀.toSection z) b) := by
  intro l
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hC_mdiff : ∀ k : Fin (Module.finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z : M =>
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z) b :=
    fun k => chartFrameNormGlobalSmoothCoordMatrix_mdiffAt
      (I := I) (M := M) g α i k (b := b) hb
  have hσ_mdiff : ∀ k : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (fun w : M => chartBasisVecFiber (I := I) α k w)
            (fun w : M => T₀.toSection w) z)) b := fun k =>
    covApply_chartBasisVecFiber_T₀_mdiffAt
      (I := I) (M := M) g r s α T₀ k (b := b) hb_base
  have hOrig_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
          (fun w : M => T₀.toSection w) z)) b := by
    have hcov_RS_smooth :
        CovariantDerivative.ContMDiffCovariantDerivative
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) ∞ := inferInstance
    have hT₀_smooth :
        ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun w : M => TensorRSSpace r s I w) z (T₀.toSection z)) :=
      T₀.toSection.contMDiff
    have hHomSec_on :
        ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
          (fun z : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
            (E := fun w : M => TangentSpace I w →L[ℝ] TensorRSSpace r s I w) z
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun (fun w : M => T₀.toSection w) z))
          Set.univ :=
      hcov_RS_smooth.contMDiff.contMDiff hT₀_smooth.contMDiffOn
    have hHomSec_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
          (fun z : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
            (E := fun w : M => TangentSpace I w →L[ℝ] TensorRSSpace r s I w) z
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun (fun w : M => T₀.toSection w) z)) b :=
      ((hHomSec_on.contMDiffAt (Filter.univ_mem))).mdifferentiableAt (by simp)
    have hB_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun z : M => TotalSpace.mk' E (E := TangentSpace I) z
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun z)) b :=
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).contMDiff.contMDiffAt).mdifferentiableAt
        (by simp)
    exact MDifferentiableAt.clm_bundle_apply (b := id) hHomSec_at hB_at
  have hSum_mdiff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z
        (∑ k : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z •
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (fun w : M => chartBasisVecFiber (I := I) α k w)
              (fun w : M => T₀.toSection w) z)) b :=
    finsum_smul_section_mdiffAt (I := I) (M := M)
      (s_finset := Finset.univ) r s
      (fun k => fun z =>
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z)
      (fun k => fun z =>
        covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (fun w : M => chartBasisVecFiber (I := I) α k w)
          (fun w : M => T₀.toSection w) z)
      (b := b)
      (fun k _ => hC_mdiff k) (fun k _ => hσ_mdiff k)
  have hGoodOpen : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hGood_nhds : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 b :=
    hGoodOpen.mem_nhds hb
  have hEvent :
      ∀ᶠ z in 𝓝 b,
        covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
          (fun w : M => T₀.toSection w) z =
        (∑ k : Fin (Module.finrank ℝ E),
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z •
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (fun w : M => chartBasisVecFiber (I := I) α k w)
              (fun w : M => T₀.toSection w) z) := by
    filter_upwards [hGood_nhds] with z hz
    exact covApply_frameVec_eq_coord_sum_on_goodSet
      (I := I) (M := M) g r s α T₀ i (y := z) hz
  set cov_RS := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_RS_def
  have hCovRSReplace :
      cov_RS.toFun
          (fun z : M =>
            covApply cov_RS
              (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
              (fun w : M => T₀.toSection w) z) b =
      cov_RS.toFun
          (fun z : M => ∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z •
              covApply cov_RS (fun w : M => chartBasisVecFiber (I := I) α k w)
                (fun w : M => T₀.toSection w) z) b :=
    cov_RS.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hOrig_mdiff hSum_mdiff (Filter.univ_mem) hEvent
  have hLeibniz := cov_RS_finsum_smul_section_leibniz_apply
    (ι := Fin (Module.finrank ℝ E))
    (s_finset := Finset.univ) (g := g) (r := r) (s := s)
    (f := fun k : Fin (Module.finrank ℝ E) => fun z : M =>
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z)
    (σ := fun k : Fin (Module.finrank ℝ E) => fun z : M =>
      covApply cov_RS (fun w : M => chartBasisVecFiber (I := I) α k w)
        (fun w : M => T₀.toSection w) z)
    (b := b)
    (hf := fun k _ => hC_mdiff k)
    (hσ := fun k _ => hσ_mdiff k)
    (v := chartBasisVecFiber (I := I) α l b)
  change cov_RS.toFun
        (covApply cov_RS
          (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
          (fun z : M => T₀.toSection z)) b
        (chartBasisVecFiber (I := I) α l b) = _
  have hLHS_replace :
      cov_RS.toFun
          (covApply cov_RS
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
            (fun z : M => T₀.toSection z)) b
          (chartBasisVecFiber (I := I) α l b) =
      cov_RS.toFun
          (fun z : M => ∑ k : Fin (Module.finrank ℝ E),
            chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k z •
              covApply cov_RS (fun w : M => chartBasisVecFiber (I := I) α k w)
                (fun w : M => T₀.toSection w) z) b
          (chartBasisVecFiber (I := I) α l b) :=
    congrArg (fun (T : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) =>
      T (chartBasisVecFiber (I := I) α l b)) hCovRSReplace
  rw [hLHS_replace]
  rw [hLeibniz]
  rw [Finset.sum_add_distrib]

end Connection
end Integral
end DifferentialGeometry

end
