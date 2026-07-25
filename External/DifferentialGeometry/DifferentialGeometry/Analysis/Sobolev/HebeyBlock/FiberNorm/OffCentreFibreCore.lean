import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberFromModelOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Set IsManifold ContinuousLinearMap Filter Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem tensorFiberNorm_sq_le_chartAlphaComponents_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s), ∀ x ∈ K,
        ‖T.toSection x‖ ^ 2 ≤
          C *
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2 := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK hKsub
  set B : ℝ :=
    midxPairCard (E := E) r s *
      (tensorChartBasisNormConstant (E := E) r s) ^ 2 with hB_def
  have hB_nn : 0 ≤ B := by
    rw [hB_def]
    exact mul_nonneg (midxPairCard_nonneg (E := E) r s)
      (sq_nonneg _)
  refine ⟨C₀ ^ 2 * B + 1, by positivity, ?_⟩
  intro T x hxK
  have hx_src : x ∈ (chartAt H α).source := hKsub hxK
  have hx_tan_α : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]; exact hx_src
  have hx_α_RS : x ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := ⟨hx_tan_α, hx_tan_α⟩
  set v : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s T α x with hv_def
  have hv_eq :
      v = (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
            (T.toSection x) := rfl
  have h_recover :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ x v =
        T.toSection x := by
    rw [hv_eq]
    exact Trivialization.symmL_continuousLinearMapAt
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α) hx_α_RS (T.toSection x)
  have h_opnorm : ‖T.toSection x‖ ≤ C₀ * ‖v‖ := by
    have h := hC₀_bound x hxK v
    rwa [h_recover] at h
  have h_alg :
      ‖v‖ ^ 2 ≤
        B *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2 := by
    have h_base :=
      tensorRSModel_norm_sq_le_sum_projection_sq (E := E) r s v
    have h_proj_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComponentProjection (E := E) r s Idx Jdx v =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x := by
      intro Idx Jdx
      rw [tensorChartComponentRaw_def, hv_def]
    calc ‖v‖ ^ 2
        ≤ midxPairCard (E := E) r s *
            (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                (tensorChartComponentProjection (E := E) r s Idx Jdx v) ^ 2 := h_base
      _ = B *
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2 := by
          simp only [hB_def, h_proj_eq]
  set RawSq : ℝ :=
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2
    with hRawSq_def
  have hRawSq_nn : 0 ≤ RawSq := by
    rw [hRawSq_def]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h_sec_nn : 0 ≤ ‖T.toSection x‖ := norm_nonneg _
  have hC₀_nn : 0 ≤ C₀ := le_of_lt hC₀_pos
  have h_sq_op : ‖T.toSection x‖ ^ 2 ≤ (C₀ * ‖v‖) ^ 2 := by
    have hCv_nn : 0 ≤ C₀ * ‖v‖ := mul_nonneg hC₀_nn (norm_nonneg _)
    have := mul_le_mul h_opnorm h_opnorm h_sec_nn hCv_nn
    simpa [sq] using this
  have h_chain : ‖T.toSection x‖ ^ 2 ≤ C₀ ^ 2 * B * RawSq := by
    calc ‖T.toSection x‖ ^ 2
        ≤ (C₀ * ‖v‖) ^ 2 := h_sq_op
      _ = C₀ ^ 2 * ‖v‖ ^ 2 := by ring
      _ ≤ C₀ ^ 2 * (B * RawSq) := by
          have h_alg' : ‖v‖ ^ 2 ≤ B * RawSq := by rw [hRawSq_def]; exact h_alg
          exact mul_le_mul_of_nonneg_left h_alg' (sq_nonneg C₀)
      _ = C₀ ^ 2 * B * RawSq := by ring
  have h_slack : C₀ ^ 2 * B * RawSq ≤ (C₀ ^ 2 * B + 1) * RawSq := by
    have h1 : C₀ ^ 2 * B * RawSq + 0 ≤ C₀ ^ 2 * B * RawSq + 1 * RawSq := by
      have : (0 : ℝ) ≤ 1 * RawSq := by simpa using hRawSq_nn
      linarith
    calc C₀ ^ 2 * B * RawSq
        = C₀ ^ 2 * B * RawSq + 0 := by ring
      _ ≤ C₀ ^ 2 * B * RawSq + 1 * RawSq := h1
      _ = (C₀ ^ 2 * B + 1) * RawSq := by ring
  exact h_chain.trans h_slack

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
