import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

omit [T2Space M] in
private lemma achart_eq_of_chartAt_eq {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀) :
    achart H b = achart H b₀ :=
  Subtype.ext h_chart

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma trivb₀_symmL_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).symmL ℝ b = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := I)
    (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma trivb₀_clmAt_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma continuousOn_coordChangeL_b₀_α (b₀ α : M) :
    ContinuousOn
      (fun b : M => ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E))
      ((chartAt H b₀).source ∩ (chartAt H α).source) := by
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun b : M => ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E))
        ((trivializationAt E (TangentSpace I) b₀).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I) (F := E)
      (E := (TangentSpace I : M → Type _))
      (trivializationAt E (TangentSpace I) b₀)
      (trivializationAt E (TangentSpace I) α)
  have h_base_b₀ : (trivializationAt E (TangentSpace I) b₀).baseSet =
      (chartAt H b₀).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀
  have h_base_α : (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
  rw [h_base_b₀, h_base_α] at h_smooth
  exact h_smooth.continuousOn

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma coordChangeL_eq_chartJ_of_locality
    (α : M) {b b₀ : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀) :
    ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E) =
      chartTrivializationLinearMap (I := I) (M := M) α b := by
  ext v
  have hb_b₀' : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact hb_b₀
  have hb_α' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hb_α
  have h_apply :
      ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E) v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b v) := by
    change ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b) v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b v)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_b₀', hb_α'⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_α',
        Bundle.Trivialization.symmL_apply]
  rw [h_apply]
  have h_symmL_id := trivb₀_symmL_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart hb_b₀
  have h_eq : (trivializationAt E (TangentSpace I) b₀).symmL ℝ b v = v := by
    have := congrArg (fun (f : E →L[ℝ] E) => f v) h_symmL_id
    simpa using this
  rw [h_eq]
  rfl

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma coordChangeL_eq_chartJinv_of_locality
    (α : M) {b b₀ : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀) :
    ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E) =
      chartTrivializationLinearMapSymm (I := I) (M := M) α b := by
  ext v
  have hb_b₀' : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact hb_b₀
  have hb_α' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hb_α
  have h_apply :
      ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E) v =
      (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) := by
    change ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b₀) b) v =
      (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_α', hb_b₀'⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_b₀',
        Bundle.Trivialization.symmL_apply]
  rw [h_apply]
  have h_clmAt_id := trivb₀_clmAt_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart hb_b₀
  have h_eq :
      (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) =
        (trivializationAt E (TangentSpace I) α).symmL ℝ b v := by
    have := congrArg
      (fun (f : E →L[ℝ] E) =>
        f ((trivializationAt E (TangentSpace I) α).symmL ℝ b v)) h_clmAt_id
    simpa using this
  rw [h_eq]
  rfl

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma chartJ_continuousOn_loc
    (α b₀ : M)
    {U : Set M}
    (hU_sub_b₀ : U ⊆ (chartAt H b₀).source)
    (hU_sub_α : U ⊆ (chartAt H α).source)
    (hU_const : ∀ b ∈ U, chartAt H b = chartAt H b₀) :
    ContinuousOn (fun b : M => chartTrivializationLinearMap (I := I) (M := M) α b) U := by
  have h_coord_cont :
      ContinuousOn
        (fun b : M => ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E)) U := by
    refine (continuousOn_coordChangeL_b₀_α (I := I) b₀ α).mono ?_
    intro b hb
    exact ⟨hU_sub_b₀ hb, hU_sub_α hb⟩
  have h_eq : EqOn
      (fun b : M => chartTrivializationLinearMap (I := I) (M := M) α b)
      (fun b : M => ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E)) U := by
    intro b hb
    exact (coordChangeL_eq_chartJ_of_locality (I := I) (M := M) α
      (hU_sub_α hb) (hU_sub_b₀ hb) (hU_const b hb)).symm
  exact h_coord_cont.congr h_eq

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma chartJinv_continuousOn_loc
    (α b₀ : M)
    {U : Set M}
    (hU_sub_b₀ : U ⊆ (chartAt H b₀).source)
    (hU_sub_α : U ⊆ (chartAt H α).source)
    (hU_const : ∀ b ∈ U, chartAt H b = chartAt H b₀) :
    ContinuousOn (fun b : M => chartTrivializationLinearMapSymm (I := I) (M := M) α b) U := by
  have h_coord_cont :
      ContinuousOn
        (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E)) U := by
    have h := continuousOn_coordChangeL_b₀_α (I := I) α b₀
    refine h.mono ?_
    intro b hb
    exact ⟨hU_sub_α hb, hU_sub_b₀ hb⟩
  have h_eq : EqOn
      (fun b : M => chartTrivializationLinearMapSymm (I := I) (M := M) α b)
      (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E)) U := by
    intro b hb
    exact (coordChangeL_eq_chartJinv_of_locality (I := I) (M := M) α
      (hU_sub_α hb) (hU_sub_b₀ hb) (hU_const b hb)).symm
  exact h_coord_cont.congr h_eq

omit [Module.Finite ℝ E] [InnerProductSpace ℝ E] [T2Space M] in
private lemma exists_opNorm_bound_on_compact_of_continuousOn
    (f : M → E →L[ℝ] E)
    {K : Set M} (hK : IsCompact K) (h_cont : ContinuousOn f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ‖f b‖ ≤ C := by
  by_cases h_empty : K = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    rw [h_empty] at hb
    exact absurd hb (Set.notMem_empty _)
  have h_norm_cont : ContinuousOn (fun b : M => ‖f b‖) K :=
    continuous_norm.comp_continuousOn h_cont
  have h_bdd : BddAbove ((fun b : M => ‖f b‖) '' K) :=
    hK.bddAbove_image h_norm_cont
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  exact (hC ⟨b, hb, rfl⟩).trans (le_max_left _ _)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
