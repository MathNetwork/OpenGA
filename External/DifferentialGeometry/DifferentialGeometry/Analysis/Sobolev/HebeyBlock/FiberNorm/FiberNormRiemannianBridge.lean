import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberToModelOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberFromModelOpNorm
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.TensorRSBundleLocalityIdentities


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem triv_eq_toModel_at_chartCenter
    (r s : ℕ) (b₀ : M) (T : TensorRSSpace r s I b₀) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b₀ T =
      TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T := by
  ext D_α
  have h_loc :=
    tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
      (I := I) (M := M) r s b₀
      (h_chart := rfl) (h_src := mem_chart_source H b₀) T D_α
  simp only [TensorRSSpace.toModel, tensorRSSpace_continuousLinearEquiv]
  rw [h_loc]
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem symmL_toModel_eq_self_at_chartCenter
    (r s : ℕ) (b₀ : M) (T : TensorRSSpace r s I b₀) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).symmL ℝ b₀
          (TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T) = T := by
  have h_mem : b₀ ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).baseSet :=
    ⟨mem_baseSet_trivializationAt _ _ b₀, mem_baseSet_trivializationAt _ _ b₀⟩
  rw [← triv_eq_toModel_at_chartCenter (I := I) r s b₀ T]
  exact Trivialization.symmL_continuousLinearMapAt
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀) h_mem T

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem modelNorm_le_gNorm_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧ ∀ T : TensorRSSpace r s I x₀,
      ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ ≤ C * ‖T‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s x₀ isCompact_singleton
      (Set.singleton_subset_iff.mpr (mem_chart_source H x₀))
  refine ⟨C₀, hC₀_pos, fun T => ?_⟩
  have h_triv := hC₀_bound x₀ (Set.mem_singleton x₀) T
  rw [triv_eq_toModel_at_chartCenter (I := I) r s x₀ T] at h_triv
  exact h_triv

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gNorm_le_modelNorm_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ D : ℝ, 0 < D ∧ ∀ T : TensorRSSpace r s I x₀,
      ‖T‖ ≤ D * ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨D₀, hD₀_pos, hD₀_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s x₀ isCompact_singleton
      (Set.singleton_subset_iff.mpr (mem_chart_source H x₀))
  refine ⟨D₀, hD₀_pos, fun T => ?_⟩
  have h_inv := hD₀_bound x₀ (Set.mem_singleton x₀)
    (TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T)
  rw [symmL_toModel_eq_self_at_chartCenter (I := I) r s x₀ T] at h_inv
  exact h_inv

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
