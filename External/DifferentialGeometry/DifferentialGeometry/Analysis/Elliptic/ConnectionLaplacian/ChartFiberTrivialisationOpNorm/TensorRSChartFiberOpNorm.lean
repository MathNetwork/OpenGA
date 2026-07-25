import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.TensorRSBundleLocalityIdentities
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma tensorRSSpace_norm_eq (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    ‖T‖ = ‖tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b T‖ :=
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma tensorRS_trivAt_clmAt_eq_CLE_on_locality
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source) :
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b :
        TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E) =
      ((tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s
        b).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro T
  apply ContinuousLinearMap.ext
  intro D_α
  have h_subB := tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (I := I) (M := M) (r := r) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src) (T := T) (D_α := D_α)
  change (((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T)
        D_α : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b T) D_α
  rw [h_subB]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma chartFiberFromModel_norm_le_coordChangeL_norm_on_locality
    (r s : ℕ) (α : M) {b₀ b : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀)
    (D : TensorRSModel r s ℝ E) :
    ‖tensorRSChartFiberFromModel (I := I) r s α b D‖ ≤
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀) b
            : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) D‖ := by
  have hb_tan_α : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]; exact hb_α
  have hb_tan_b₀ : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]; exact hb_b₀
  have hb_α' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := ⟨hb_tan_α, hb_tan_α⟩
  have hb_b₀' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).baseSet := ⟨hb_tan_b₀, hb_tan_b₀⟩
  have h_apply :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀) b
            : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) D =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D) := by
    change ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀) b) D =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_α', hb_b₀'⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_b₀',
        Bundle.Trivialization.symmL_apply]
  have h_locality_clm := tensorRS_trivAt_clmAt_eq_CLE_on_locality (I := I)
    (M := M) (r := r) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := hb_b₀)
  have h_appl :
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D) =
        (tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b)
          ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D) := by
    have := congrArg (fun (f : TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E) =>
        f ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b D))
      h_locality_clm
    simpa using this
  have h_norm_eq := tensorRSSpace_norm_eq (I := I) (M := M) r s b
    (tensorRSChartFiberFromModel (I := I) r s α b D)
  rw [h_norm_eq, h_apply, h_appl]
  exact le_refl _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma continuousOn_RS_coordChangeL_α_b₀ (r s : ℕ) (α b₀ : M) :
    ContinuousOn
      (fun b : M => ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) b₀) b
              : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
      ((chartAt H α).source ∩ (chartAt H b₀).source) := by
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) ∞
        (fun b : M => ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).coordChangeL ℝ
            (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) b₀) b
                : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet ∩
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I)
      (F := TensorRSModel r s ℝ E)
      (E := fun y : M => TensorRSSpace r s I y)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀)
  have h_base_α : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [inter_self, TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
  have h_base_b₀ : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).baseSet =
      (chartAt H b₀).source := by
    change (trivializationAt E (TangentSpace I) b₀).baseSet ∩
        (trivializationAt E (TangentSpace I) b₀).baseSet = (chartAt H b₀).source
    rw [inter_self, TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
  rw [h_base_α, h_base_b₀] at h_smooth
  exact h_smooth.continuousOn

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma exists_opNorm_bound_on_compact_of_continuousOn
    {r s : ℕ} (f : M → TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
    {K : Set M} (hK : IsCompact K) (h_cont : ContinuousOn f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ‖f b‖ ≤ C := by
  by_cases h_empty : K = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb; rw [h_empty] at hb; exact absurd hb (Set.notMem_empty _)
  have h_norm_cont : ContinuousOn (fun b : M => ‖f b‖) K :=
    continuous_norm.comp_continuousOn h_cont
  have h_bdd : BddAbove ((fun b : M => ‖f b‖) '' K) :=
    hK.bddAbove_image h_norm_cont
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  exact (hC ⟨b, hb, rfl⟩).trans (le_max_left _ _)

end Connection
end Integral
end DifferentialGeometry

end
