import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.ChartProjectionSecondCovDerivViaSkExt
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentEuclidSkExtExpansion


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

private def secondCovDerivChartGlobalGradCorrectionCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (if m = l then
      secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y
     else 0) +
    (if m = k then
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx I' Jdx J' y
     else 0)

private def secondCovDerivChartGlobalValueCorrectionCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α k l Idx I' Jdx J' y +
    ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α k p.1 I' p.2 J' y

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma GlobalCorr_eu_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (secondCovDerivChartGlobalGradCorrectionCoeff (I := I) (M := M) g r s α k l Idx Jdx I' J' m)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold secondCovDerivChartGlobalGradCorrectionCoeff
  have h1 : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        if m = l then
          secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y
        else 0)
      (chartTargetEuclid (I := I) (M := M) α) := by
    by_cases h : m = l
    · simp only [h, if_true]
      exact secondCovDerivLO_gradCoeff_contDiffOn
        (I := I) (M := M) g r s α k Idx I' Jdx J'
    · simp only [h, if_false]
      exact contDiffOn_const
  have h2 : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        if m = k then
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx I' Jdx J' y
        else 0)
      (chartTargetEuclid (I := I) (M := M) α) := by
    by_cases h : m = k
    · simp only [h, if_true]
      exact covDerivLowerOrderCoeff_contDiffOn
        (I := I) (M := M) g r s α l Idx I' Jdx J'
    · simp only [h, if_false]
      exact contDiffOn_const
  exact h1.add h2

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma GlobalCorr0_eu_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (secondCovDerivChartGlobalValueCorrectionCoeff (I := I) (M := M) g r s α k l Idx Jdx I' J')
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold secondCovDerivChartGlobalValueCorrectionCoeff
  have h1 : ContDiffOn ℝ ∞
      (secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α k l Idx I' Jdx J')
      (chartTargetEuclid (I := I) (M := M) α) :=
    secondCovDerivLO_valueCoeff_contDiffOn
      (I := I) (M := M) g r s α k l Idx I' Jdx J'
  have h2 : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α k p.1 I' p.2 J' y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine ContDiffOn.sum (fun p _ => ?_)
    exact (covDerivLowerOrderCoeff_contDiffOn
        (I := I) (M := M) g r s α l Idx p.1 Jdx p.2).mul
      (covDerivLowerOrderCoeff_contDiffOn
        (I := I) (M := M) g r s α k p.1 I' p.2 J')
  exact h1.add h2

private def packageAsCcG
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                fun b : M => TensorRSSpace r s I b⟯) :
    SmoothCcTensor g r s where
  toSection := S
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma packageAsCcG_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                fun b : M => TensorRSSpace r s I b⟯) :
    (packageAsCcG (I := I) (M := M) g r s S).toSection = S := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRaw_S_k_packed_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯,
    ∃ V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      IsOpen V ∧
      V ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      (toEuclidean (E := E)) ((extChartAt I α) b₀) ∈ V ∧
      (∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        Set.EqOn
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s
              (packageAsCcG (I := I) (M := M) g r s S_k_ext) α Idx Jdx))
          (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx) V) ∧
      ((TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (chartBasisVecFiber (I := I) α k) T₀.toSection) b₀ =
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (fun y : M =>
          (packageAsCcG (I := I) (M := M) g r s S_k_ext).toSection y) b₀) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  obtain ⟨S_k_ext, U, hU_open, hb₀_U, hU_sub_good, hU_eq⟩ :=
    covApply_covRS_chartBasis_globalSmoothExtension
      (I := I) (M := M) g r s α T₀ k (b₀ := b₀) hb₀
  set V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) α ∩
      {y | (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ U} with hV_def
  have hchartT_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hcont_te : Continuous
      ((toEuclidean (E := E)).symm :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E) :=
    (toEuclidean (E := E)).symm.continuous
  have hcont_extsymm :
      ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  have hmap_target : MapsTo
      ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨z, hz_target, hz_eq⟩
    have hyz : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; exact (toEuclidean (E := E)).symm_apply_apply _
    rw [hyz]; exact hz_target
  have hcont_comp :
      ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
    hcont_extsymm.comp hcont_te.continuousOn hmap_target
  have hV_open : IsOpen V := hcont_comp.isOpen_inter_preimage hchartT_open hU_open
  have hV_sub : V ⊆ chartTargetEuclid (I := I) (M := M) α := fun y hy => hy.1
  have hb₀_good : b₀ ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb₀_U
  have hb₀_src : b₀ ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb₀_good
  have hb₀_tgt : (extChartAt I α) b₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb₀_src
  have hb₀_V : (toEuclidean (E := E)) ((extChartAt I α) b₀) ∈ V := by
    refine ⟨⟨(extChartAt I α) b₀, hb₀_tgt, rfl⟩, ?_⟩
    change (extChartAt I α).symm
        ((toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) ((extChartAt I α) b₀))) ∈ U
    rw [(toEuclidean (E := E)).symm_apply_apply, (extChartAt I α).left_inv hb₀_src]
    exact hb₀_U
  refine ⟨S_k_ext, V, hV_open, hV_sub, hb₀_V, ?_, ?_⟩
  · intro Idx Jdx y hy
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hy.1
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
    have hb_U : b ∈ U := hy.2
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb_U
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
    rw [tensorChartComponentRaw_def]
    rw [covDerivComponentEuclid_def]
    have htriv_eq :
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((packageAsCcG (I := I) (M := M) g r s S_k_ext).toSection b) =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α T₀.toSection
            (chartBasisVecFiber (I := I) α k) b) := by
      congr 1
      rw [packageAsCcG_toSection]
      have hStep_BTCi :
          (S_k_ext : Π b' : M, TensorRSSpace r s I b') b =
          covApply
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (chartBasisVecFiber (I := I) α k) T₀.toSection b := hU_eq b hb_U
      change (S_k_ext : Π b' : M, TensorRSSpace r s I b') b =
        chartTensorRSCovariantDerivative (I := I) r s g α T₀.toSection
          (chartBasisVecFiber (I := I) α k) b
      rw [hStep_BTCi, covApply_apply]
      have hCovDerivAt :
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T₀.toSection b
            (chartBasisVecFiber (I := I) α k b) =
          tensorCovDerivAt (I := I) (M := M) g r s T₀ b
            (chartBasisVecFiber (I := I) α k b) := by
        rw [tensorCovDerivAt_def]
      rw [hCovDerivAt]
      exact tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
        (I := I) (M := M) g r s T₀ α k (b := b) hb_good
    change tensorChartComponentProjection (E := E) r s Idx Jdx
        (tensorTrivProj (I := I) (M := M) g r s
          (packageAsCcG (I := I) (M := M) g r s S_k_ext) α b) =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α T₀.toSection
            (chartBasisVecFiber (I := I) α k) b))
    change tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((packageAsCcG (I := I) (M := M) g r s S_k_ext).toSection b)) =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α T₀.toSection
            (chartBasisVecFiber (I := I) α k) b))
    rw [htriv_eq]
  · set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcov_def
    set σ : Π y : M, TensorRSSpace r s I y :=
      covApply cov (chartBasisVecFiber (I := I) α k) T₀.toSection with hσ_def
    set σ' : Π y : M, TensorRSSpace r s I y :=
      fun y : M => (S_k_ext : Π y' : M, TensorRSSpace r s I y') y with hσ'_def
    have hagree : ∀ᶠ y in 𝓝 b₀, σ y = σ' y := by
      refine Filter.eventually_of_mem (hU_open.mem_nhds hb₀_U) (fun y hy_U => ?_)
      have hSk_y :
          (S_k_ext : Π y' : M, TensorRSSpace r s I y') y =
            covApply cov (chartBasisVecFiber (I := I) α k) T₀.toSection y :=
        hU_eq y hy_U
      change covApply cov (chartBasisVecFiber (I := I) α k) T₀.toSection y =
          (S_k_ext : Π y' : M, TensorRSSpace r s I y') y
      exact hSk_y.symm
    have hσ'_total_smooth :
        ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) y (σ' y)) :=
      S_k_ext.contMDiff
    have hσ'_total_mdiff :
        MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
          (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) y (σ' y)) b₀ :=
      (hσ'_total_smooth b₀).mdifferentiableAt (by simp)
    have htotal_agree :
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) y (σ y)) =ᶠ[𝓝 b₀]
          (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) y (σ' y)) := by
      refine hagree.mono (fun y hy => ?_)
      change TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ y) =
        TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ' y)
      rw [hy]
    have hσ_total_mdiff :
        MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
          (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) y (σ y)) b₀ :=
      (htotal_agree.mdifferentiableAt_iff (𝕜 := ℝ) (I := I)
        (I' := I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))).mpr hσ'_total_mdiff
    have hcov_loc : cov.toFun σ b₀ = cov.toFun σ' b₀ :=
      tensorRSCovariantDerivative_congr_of_eventuallyEq
        (I := I) (M := M) g r s
        (σ := σ) (σ' := σ') (x := b₀) hagree hσ_total_mdiff hσ'_total_mdiff
    have hσ'_eq_packed :
        σ' = (fun y : M => (packageAsCcG (I := I) (M := M) g r s S_k_ext).toSection y) := by
      funext y
      simp [hσ'_def, packageAsCcG_toSection]
    rw [hσ'_eq_packed] at hcov_loc
    exact hcov_loc

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma LHS_eq_covDerivComponentEuclid_S_k_packed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (k l : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                     fun b : M => TensorRSSpace r s I b⟯)
    {b : M} (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (hcov_agree :
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g))
        (chartBasisVecFiber (I := I) α k) T₀.toSection) b =
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (fun y : M =>
        (packageAsCcG (I := I) (M := M) g r s S_k_ext).toSection y) b) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (chartBasisVecFiber (I := I) α k) T₀.toSection) b
            (chartBasisVecFiber (I := I) α l b))) =
      covDerivComponentEuclid (I := I) (M := M) g r s α
          (packageAsCcG (I := I) (M := M) g r s S_k_ext) l Idx Jdx
          ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  set S_k_packed : SmoothCcTensor g r s :=
    packageAsCcG (I := I) (M := M) g r s S_k_ext with hS_k_packed_def
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  have hcov_loc_at_v :
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (chartBasisVecFiber (I := I) α k) T₀.toSection) b
        (chartBasisVecFiber (I := I) α l b) =
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (fun y : M => S_k_packed.toSection y) b
        (chartBasisVecFiber (I := I) α l b) := by
    rw [hcov_agree]
  rw [hcov_loc_at_v]
  have hcov_tensor :
      (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)).toFun
        (fun y : M => S_k_packed.toSection y) b
        (chartBasisVecFiber (I := I) α l b) =
      tensorCovDerivAt (I := I) (M := M) g r s S_k_packed b
        (chartBasisVecFiber (I := I) α l b) := by
    rw [tensorCovDerivAt_def]
  rw [hcov_tensor]
  have hcov_chart :
      tensorCovDerivAt (I := I) (M := M) g r s S_k_packed b
        (chartBasisVecFiber (I := I) α l b) =
      chartTensorRSCovariantDerivative (I := I) r s g α S_k_packed.toSection
        (chartBasisVecFiber (I := I) α l) b :=
    tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
      (I := I) (M := M) g r s S_k_packed α l (b := b) hb_good
  rw [hcov_chart]
  rw [covDerivComponentEuclid_def]
  have hsymm_te :
      (toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
        (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  rw [hsymm_te, hleft_inv]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_eqOn_of_eqOn_openG
    (V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (hV_open : IsOpen V)
    (u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (huv : Set.EqOn u v V)
    (n : Fin (Module.finrank ℝ E)) :
    Set.EqOn (euclidPartial (E := E) n u) (euclidPartial (E := E) n v) V := by
  classical
  intro y hy
  have hVeq : u =ᶠ[𝓝 y] v := huv.eventuallyEq_of_mem (hV_open.mem_nhds hy)
  have hfderiv : fderiv ℝ u y = fderiv ℝ v y :=
    Filter.EventuallyEq.fderiv_eq hVeq
  rw [euclidPartial_def, euclidPartial_def, hfderiv]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E)) :
    ∃ (GlobalCorr : (Fin r → Fin (Module.finrank ℝ E)) →
                     (Fin s → Fin (Module.finrank ℝ E)) →
                     Fin (Module.finrank ℝ E) →
                     EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (GlobalCorr0 : (Fin r → Fin (Module.finrank ℝ E)) →
                      (Fin s → Fin (Module.finrank ℝ E)) →
                      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ I' J' m, ContDiffOn ℝ ∞ (GlobalCorr I' J' m)
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (GlobalCorr0 I' J')
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
        tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartBasisVecFiber (I := I) α k) T₀.toSection) b
                (chartBasisVecFiber (I := I) α l b))) =
          euclidPartial (E := E) l
            (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
            ((toEuclidean (E := E)) ((extChartAt I α) b)) +
          (∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
            GlobalCorr I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
              euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                ((toEuclidean (E := E)) ((extChartAt I α) b))) +
          (∑ I' : Fin r → Fin (Module.finrank ℝ E),
            ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            GlobalCorr0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
              chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  refine ⟨secondCovDerivChartGlobalGradCorrectionCoeff (I := I) (M := M) g r s α k l Idx Jdx,
          secondCovDerivChartGlobalValueCorrectionCoeff (I := I) (M := M) g r s α k l Idx Jdx,
          ?_, ?_, ?_⟩
  · intro I' J' m
    exact GlobalCorr_eu_contDiffOn (I := I) (M := M) g r s α k l Idx Jdx I' J' m
  · intro I' J'
    exact GlobalCorr0_eu_contDiffOn (I := I) (M := M) g r s α k l Idx Jdx I' J'
  · intro T₀ b hb_good
    set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
    have hb_src : b ∈ (extChartAt I α).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
    have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hb_src
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α :=
      ⟨(extChartAt I α) b, hb_tgt, rfl⟩
    obtain ⟨S_k_ext, V, hV_open, hV_sub, hb_V, hVeqOn, hcov_agree⟩ :=
      chartPushedRaw_S_k_packed_eqOn (I := I) (M := M) g r s α T₀ k
        (b₀ := b) hb_good
    set S_k_packed : SmoothCcTensor g r s :=
      packageAsCcG (I := I) (M := M) g r s S_k_ext with hS_k_packed_def
    have hy_V : y ∈ V := hb_V
    have hStep2 :
        tensorChartComponentProjection (E := E) r s Idx Jdx
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartBasisVecFiber (I := I) α k) T₀.toSection) b
                (chartBasisVecFiber (I := I) α l b))) =
          covDerivComponentEuclid (I := I) (M := M) g r s α S_k_packed l Idx Jdx y :=
      LHS_eq_covDerivComponentEuclid_S_k_packed
        (I := I) (M := M) g r s α T₀ k l Idx Jdx S_k_ext hb_good hcov_agree
    rw [hStep2]
    have hStep3 :
        covDerivComponentEuclid (I := I) (M := M) g r s α S_k_packed l Idx Jdx y =
          euclidPartial (E := E) l
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α Idx Jdx)) y +
            covDerivLowerOrderTerm (I := I) (M := M) g r s S_k_packed α l Idx Jdx y :=
      covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α S_k_packed l Idx Jdx
        hy_target
    rw [hStep3]
    have hChart_S_k_packed_eq :
        Set.EqOn
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α Idx Jdx))
          (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx) V :=
      hVeqOn Idx Jdx
    have hPartial_S_k_packed_eq :
        euclidPartial (E := E) l
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α Idx Jdx)) y =
          euclidPartial (E := E) l
            (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx) y :=
      euclidPartial_eqOn_of_eqOn_openG (E := E) V hV_open _ _
        hChart_S_k_packed_eq l hy_V
    rw [hPartial_S_k_packed_eq]
    have hStep5 :
        euclidPartial (E := E) l
            (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx) y =
          euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y
            + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E)),
                secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α k l
                    Idx p.1 Jdx p.2 y *
                  rawComponentEuclid (I := I) (M := M) g r s α T₀ p.1 p.2 y)
            + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E)),
                secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k
                    Idx p.1 Jdx p.2 y *
                  euclidPartial (E := E) l
                    (rawComponentEuclid (I := I) (M := M) g r s α T₀ p.1 p.2) y) :=
      covDerivComponent_second_eq_iteratedFDeriv_add_lowerOrder
        (I := I) (M := M) g r s α T₀ k l Idx Jdx hy_target
    rw [hStep5]
    have hLOterm_expand :
        covDerivLowerOrderTerm (I := I) (M := M) g r s S_k_packed α l Idx Jdx y =
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
              (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)) y
                + covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k p.1 p.2 y) := by
      rw [covDerivLowerOrderTerm_def]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      have hpush_S :
          tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α p.1 p.2
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α p.1 p.2) y :=
        (chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S_k_packed α p.1 p.2)
          hy_target).symm
      rw [hpush_S]
      have hS_eq_T₀ := hVeqOn p.1 p.2 hy_V
      rw [hS_eq_T₀]
      rw [covDerivComponentEuclid_eqOn (I := I) (M := M) g r s α T₀ k p.1 p.2 hy_target]
    rw [hLOterm_expand]
    have hExpand :
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
            (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)) y
              + covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k p.1 p.2 y) =
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)) y)
          + (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
                covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k p.1 p.2 y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
    rw [hExpand]
    have hInnerLO :
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
            covDerivLowerOrderTerm (I := I) (M := M) g r s T₀ α k p.1 p.2 y =
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
              (covDerivLowerOrderCoeff (I := I) (M := M) g r s α k p.1 q.1 p.2 q.2 y *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2) y) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [covDerivLowerOrderTerm_def, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      have hpush_T :
          tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2) y :=
        (chartPushedRaw_apply_of_mem (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2)
          hy_target).symm
      rw [hpush_T]
    rw [hInnerLO]
    have hraw_eq : ∀ (p : (Fin r → Fin (Module.finrank ℝ E)) ×
                          (Fin s → Fin (Module.finrank ℝ E))),
        rawComponentEuclid (I := I) (M := M) g r s α T₀ p.1 p.2 y =
          chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) y := by
      intro p
      exact rawComponentEuclid_eqOn_chartPushed
        (I := I) (M := M) g r s α T₀ p.1 p.2 hy_target
    have hraw_partial_eq : ∀ (p : (Fin r → Fin (Module.finrank ℝ E)) ×
                                  (Fin s → Fin (Module.finrank ℝ E))),
        euclidPartial (E := E) l
            (rawComponentEuclid (I := I) (M := M) g r s α T₀ p.1 p.2) y =
          euclidPartial (E := E) l
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)) y := by
      intro p
      exact euclidPartial_rawComponentEuclid_eqOn
        (I := I) (M := M) g r s α T₀ l p.1 p.2 hy_target
    have hSecVal_rewrite :
        (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
          secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α k l
              Idx p.1 Jdx p.2 y *
            rawComponentEuclid (I := I) (M := M) g r s α T₀ p.1 p.2 y) =
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α k l
              Idx p.1 Jdx p.2 y *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2) y := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [hraw_eq p]
    have hSecGrad_rewrite :
        (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
          secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k
              Idx p.1 Jdx p.2 y *
            euclidPartial (E := E) l
              (rawComponentEuclid (I := I) (M := M) g r s α T₀ p.1 p.2) y) =
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k
              Idx p.1 Jdx p.2 y *
            euclidPartial (E := E) l
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)) y := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [hraw_partial_eq p]
    rw [hSecVal_rewrite, hSecGrad_rewrite]
    have hMSum : ∀ (I' : Fin r → Fin (Module.finrank ℝ E))
                  (J' : Fin s → Fin (Module.finrank ℝ E)),
        (∑ m : Fin (Module.finrank ℝ E),
          secondCovDerivChartGlobalGradCorrectionCoeff (I := I) (M := M) g r s α k l Idx Jdx I' J' m y *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y) =
          secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y *
            euclidPartial (E := E) l
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y +
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx I' Jdx J' y *
            euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y := by
      intro I' J'
      have hunfold : ∀ m,
          secondCovDerivChartGlobalGradCorrectionCoeff (I := I) (M := M) g r s α k l Idx Jdx I' J' m y *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y =
          (if m = l then
            secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y
          else 0) *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y
          + (if m = k then
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx I' Jdx J' y
          else 0) *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y := by
        intro m
        unfold secondCovDerivChartGlobalGradCorrectionCoeff
        ring
      rw [Finset.sum_congr rfl (fun m _ => hunfold m)]
      rw [Finset.sum_add_distrib]
      have hFirstSum :
          (∑ m : Fin (Module.finrank ℝ E),
            (if m = l then
              secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y
            else 0) *
              euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y) =
          secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y *
            euclidPartial (E := E) l
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y := by
        rw [Finset.sum_eq_single (l : Fin (Module.finrank ℝ E))]
        · simp
        · intro m _ hml
          simp [hml]
        · intro h
          exact absurd (Finset.mem_univ l) h
      have hSecondSum :
          (∑ m : Fin (Module.finrank ℝ E),
            (if m = k then
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx I' Jdx J' y
            else 0) *
              euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y) =
          covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx I' Jdx J' y *
            euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y := by
        rw [Finset.sum_eq_single (k : Fin (Module.finrank ℝ E))]
        · simp
        · intro m _ hmk
          simp [hmk]
        · intro h
          exact absurd (Finset.mem_univ k) h
      rw [hFirstSum, hSecondSum]
    have hMSum_total :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ m : Fin (Module.finrank ℝ E),
          secondCovDerivChartGlobalGradCorrectionCoeff (I := I) (M := M) g r s α k l Idx Jdx I' J' m y *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y) =
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          (secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y *
              euclidPartial (E := E) l
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y +
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx I' Jdx J' y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y)) := by
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      exact hMSum I' J'
    rw [hMSum_total]
    have hDoubleSum_to_pair :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          (secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx I' Jdx J' y *
              euclidPartial (E := E) l
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y +
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx I' Jdx J' y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y)) =
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          (secondCovDerivLO_gradCoeff (I := I) (M := M) g r s α k Idx p.1 Jdx p.2 y *
              euclidPartial (E := E) l
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)) y +
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α p.1 p.2)) y) := by
      rw [← Finset.sum_product']
      rfl
    rw [hDoubleSum_to_pair]
    rw [Finset.sum_add_distrib]
    have hGC0_total :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          secondCovDerivChartGlobalValueCorrectionCoeff (I := I) (M := M) g r s α k l Idx Jdx I' J' y *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y) =
        ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          (secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α k l Idx q.1 Jdx q.2 y +
            ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α k p.1 q.1 p.2 q.2 y) *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2) y := by
      rw [← Finset.sum_product']
      refine Finset.sum_congr rfl (fun q _ => ?_)
      unfold secondCovDerivChartGlobalValueCorrectionCoeff
      rfl
    rw [hGC0_total]
    have hGC0_split :
        ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          (secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α k l Idx q.1 Jdx q.2 y +
            ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α k p.1 q.1 p.2 q.2 y) *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2) y =
        (∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          secondCovDerivLO_valueCoeff (I := I) (M := M) g r s α k l Idx q.1 Jdx q.2 y *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2) y)
        + ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α k p.1 q.1 p.2 q.2 y) *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2) y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      ring
    rw [hGC0_split]
    have hInnerLO_reindex :
        ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            (∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
                covDerivLowerOrderCoeff (I := I) (M := M) g r s α k p.1 q.1 p.2 q.2 y) *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2) y =
        ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            covDerivLowerOrderCoeff (I := I) (M := M) g r s α l Idx p.1 Jdx p.2 y *
              (covDerivLowerOrderCoeff (I := I) (M := M) g r s α k p.1 q.1 p.2 q.2 y *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α q.1 q.2) y) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      ring
    rw [hInnerLO_reindex]
    ring

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
