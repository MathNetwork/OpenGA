import DifferentialGeometry.Geometry.Connection.CovApplyCovRSChartBasisExtension
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSCovariantDerivativeCongrLocally
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SkExtChartComponentEqCovDerivEuclid


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

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

private def packageAsCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                fun b : M => TensorRSSpace r s I b⟯) :
    SmoothCcTensor g r s where
  toSection := S
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma packageAsCc_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                fun b : M => TensorRSSpace r s I b⟯) :
    (packageAsCc (I := I) (M := M) g r s S).toSection = S := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartα_proj_secondCovDeriv_eq_chartCoord_first_deriv_of_Sk_ext
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (k l : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯,
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧ U ⊆ chartLeviCivitaGoodSet (I := I) α ∧
      ∀ b ∈ U,
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
          (packageAsCc (I := I) (M := M) g r s S_k_ext) l Idx Jdx
          ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
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
  refine ⟨S_k_ext, U, hU_open, hb₀_U, hU_sub_good, ?_⟩
  intro b hb_U
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb_U
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g) with hcov_def
  set σ : Π y : M, TensorRSSpace r s I y :=
    covApply cov (chartBasisVecFiber (I := I) α k) T₀.toSection with hσ_def
  set σ' : Π y : M, TensorRSSpace r s I y :=
    fun y : M => (S_k_ext : Π y' : M, TensorRSSpace r s I y') y with hσ'_def
  set S_k_packed : SmoothCcTensor g r s :=
    packageAsCc (I := I) (M := M) g r s S_k_ext with hS_k_packed_def
  have hσ'_eq_packed :
      σ' = (fun y : M => S_k_packed.toSection y) := by
    funext y
    simp [hσ'_def, hS_k_packed_def, packageAsCc_toSection]
  have hagree_σ_σ' : ∀ᶠ y in 𝓝 b, σ y = σ' y := by
    have hU_nhds : U ∈ 𝓝 b := hU_open.mem_nhds hb_U
    refine Filter.eventually_of_mem hU_nhds (fun y hy_U => ?_)
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
          (E := fun z : M => TensorRSSpace r s I z) y (σ' y)) b :=
    (hσ'_total_smooth b).mdifferentiableAt (by simp)
  have htotal_agree :
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ y)) =ᶠ[𝓝 b]
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ' y)) := by
    refine hagree_σ_σ'.mono (fun y hy => ?_)
    change TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (σ y) =
      TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (σ' y)
    rw [hy]
  have hσ_total_mdiff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (σ y)) b :=
    (htotal_agree.mdifferentiableAt_iff (𝕜 := ℝ) (I := I)
      (I' := I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))).mpr hσ'_total_mdiff
  have hcov_loc : cov.toFun σ b = cov.toFun σ' b :=
    tensorRSCovariantDerivative_congr_of_eventuallyEq
      (I := I) (M := M) g r s
      (σ := σ) (σ' := σ') (x := b) hagree_σ_σ' hσ_total_mdiff hσ'_total_mdiff
  have hcov_loc_at_v :
      cov.toFun σ b (chartBasisVecFiber (I := I) α l b) =
      cov.toFun σ' b (chartBasisVecFiber (I := I) α l b) := by
    rw [hcov_loc]
  have hcov_σ'_eq_packed :
      cov.toFun σ' b (chartBasisVecFiber (I := I) α l b) =
      cov.toFun (fun y : M => S_k_packed.toSection y) b
        (chartBasisVecFiber (I := I) α l b) := by
    rw [hσ'_eq_packed]
  have hcov_tensor :
      cov.toFun (fun y : M => S_k_packed.toSection y) b
        (chartBasisVecFiber (I := I) α l b) =
      tensorCovDerivAt (I := I) (M := M) g r s S_k_packed b
        (chartBasisVecFiber (I := I) α l b) := by
    rw [tensorCovDerivAt_def]
  have hcov_chart :
      tensorCovDerivAt (I := I) (M := M) g r s S_k_packed b
        (chartBasisVecFiber (I := I) α l b) =
      chartTensorRSCovariantDerivative (I := I) r s g α S_k_packed.toSection
        (chartBasisVecFiber (I := I) α l) b :=
    tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
      (I := I) (M := M) g r s S_k_packed α l (b := b) hb_good
  have hinner :
      cov.toFun σ b (chartBasisVecFiber (I := I) α l b) =
      chartTensorRSCovariantDerivative (I := I) r s g α S_k_packed.toSection
        (chartBasisVecFiber (I := I) α l) b := by
    rw [hcov_loc_at_v, hcov_σ'_eq_packed, hcov_tensor, hcov_chart]
  rw [hinner]
  rw [covDerivComponentEuclid_def]
  have hsymm_te :
      (toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
        (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  rw [hsymm_te, hleft_inv]

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
