import DifferentialGeometry.Geometry.Connection.CovApplyCovRSChartBasisExtension
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentSecondFormula
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartForm


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

private def euclidNeighbourhood (α : M) (U : Set M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  chartTargetEuclid (I := I) (M := M) α ∩
    {y | (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ U}

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidNeighbourhood_mem_iff (α : M) (U : Set M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} :
    y ∈ euclidNeighbourhood (I := I) (M := M) α U ↔
      y ∈ chartTargetEuclid (I := I) (M := M) α ∧
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ U := Iff.rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidNeighbourhood_subset_chartTargetEuclid
    (α : M) (U : Set M) :
    euclidNeighbourhood (I := I) (M := M) α U ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  intro y hy; exact hy.1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidNeighbourhood_isOpen
    (α : M) {U : Set M} (hU_open : IsOpen U) :
    IsOpen (euclidNeighbourhood (I := I) (M := M) α U) := by
  classical
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
    rw [hyz]
    exact hz_target
  have hcont_comp :
      ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
    hcont_extsymm.comp hcont_te.continuousOn hmap_target
  have hset_eq :
      euclidNeighbourhood (I := I) (M := M) α U =
        chartTargetEuclid (I := I) (M := M) α ∩
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
              (extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ⁻¹' U := rfl
  rw [hset_eq]
  exact hcont_comp.isOpen_inter_preimage hchartT_open hU_open

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma toEuclidean_extChartAt_mem_euclidNeighbourhood
    (α : M) {U : Set M} (hU_sub_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    {b₀ : M} (hb₀_U : b₀ ∈ U) :
    toEuclidean ((extChartAt I α) b₀) ∈
      euclidNeighbourhood (I := I) (M := M) α U := by
  classical
  have hb₀_good : b₀ ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb₀_U
  have hb₀_src : b₀ ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb₀_good
  have hb₀_tgt : (extChartAt I α) b₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb₀_src
  refine ⟨?_, ?_⟩
  · exact ⟨(extChartAt I α) b₀, hb₀_tgt, rfl⟩
  · change (extChartAt I α).symm
        ((toEuclidean (E := E)).symm (toEuclidean ((extChartAt I α) b₀))) ∈ U
    have hsymm_te : (toEuclidean (E := E)).symm
        (toEuclidean ((extChartAt I α) b₀)) =
        (extChartAt I α) b₀ :=
      (toEuclidean (E := E)).symm_apply_apply _
    rw [hsymm_te]
    have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b₀) = b₀ :=
      (extChartAt I α).left_inv hb₀_src
    rw [hleft_inv]
    exact hb₀_U

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedRaw_tensorChartComponentRaw_S_k_ext_eqOn_covDerivComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∃ S_k_ext : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
                       fun b : M => TensorRSSpace r s I b⟯,
    ∃ V : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      IsOpen V ∧
      toEuclidean ((extChartAt I α) b₀) ∈ V ∧
      Set.EqOn
        (chartPushedRaw I α
          (fun b : M =>
            tensorChartComponentProjection r s Idx Jdx
              ((trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ
                b (S_k_ext.toFun b))))
        (covDerivComponentEuclid (I := I) (M := M) g r s α T₀ k Idx Jdx)
        V := by
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
    euclidNeighbourhood (I := I) (M := M) α U with hV_def
  have hV_open : IsOpen V :=
    euclidNeighbourhood_isOpen (I := I) (M := M) α hU_open
  have hb₀_V : toEuclidean ((extChartAt I α) b₀) ∈ V :=
    toEuclidean_extChartAt_mem_euclidNeighbourhood
      (I := I) (M := M) α hU_sub_good hb₀_U
  refine ⟨S_k_ext, V, hV_open, hb₀_V, ?_⟩
  intro y hy
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hy.1
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_U : b ∈ U := hy.2
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hU_sub_good hb_U
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
  rw [covDerivComponentEuclid_def]
  congr 1
  congr 1
  have hStep_BTCi : (S_k_ext : Π b' : M, TensorRSSpace r s I b') b =
      covApply
        (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
        (chartBasisVecFiber (I := I) α k) T₀.toSection b := hU_eq b hb_U
  have hSk_unfold :
      S_k_ext.toFun b = (S_k_ext : Π b' : M, TensorRSSpace r s I b') b := rfl
  rw [hSk_unfold, hStep_BTCi]
  rw [covApply_apply]
  have hCovDerivAt : (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun T₀.toSection b
        (chartBasisVecFiber (I := I) α k b) =
      tensorCovDerivAt (I := I) (M := M) g r s T₀ b
        (chartBasisVecFiber (I := I) α k b) := by
    rw [tensorCovDerivAt_def]
  rw [hCovDerivAt]
  exact tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
    (I := I) (M := M) g r s T₀ α k (b := b) hb_good

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
