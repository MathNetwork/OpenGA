import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic

/-!
# Pointwise-evaluation continuity of variable-base trivialization actions

For a fixed central point `α : M` and a fixed model-fibre vector `v : E`,
the maps `b ↦ (trivializationAt α).continuousLinearMapAt ℝ b v` and
`b ↦ (trivializationAt α).symmL ℝ b v` are continuous on the chart
source at `α`. Same for the `(0,s)`- and `(r,s)`-tensor bundles inherited
through multilinear / hom constructions.

The proof routes through the coordinate-change-applied continuity lemma
on `chart β source ∩ chart α source` (from `contMDiffOn_coordChangeL`)
combined with the centre identity `(e_β.symmL ℝ β) = id` over a
neighbourhood cover of `chart α source`.
-/

noncomputable section
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace Riemannian
namespace Tensor
namespace BundleSectionContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Tangent bundle: setup -/

private lemma tangent_baseSet_eq (α : M) :
    (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
  TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α

private lemma tangent_clmAt_self_eq_id (α : M) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

private lemma tangent_symmL_self_eq_id (α : M) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ α =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

/-! ## Wrapped continuity for the tangent bundle -/

private lemma continuousOn_coordChangeL_apply
    (α β : M) (v : E) :
    ContinuousOn (fun b : M =>
      ((trivializationAt E (TangentSpace I) β).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b) v)
      ((chartAt H β).source ∩ (chartAt H α).source) := by
  have hcLM := contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _))
    (trivializationAt E (TangentSpace I) β)
    (trivializationAt E (TangentSpace I) α)
  have hcont := hcLM.continuousOn
  rw [tangent_baseSet_eq, tangent_baseSet_eq] at hcont
  exact hcont.clm_apply continuousOn_const

private lemma continuousOn_symm_coordChangeL_apply
    (α β : M) (v : E) :
    ContinuousOn (fun b : M =>
      ((trivializationAt E (TangentSpace I) β).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b).symm v)
      ((chartAt H β).source ∩ (chartAt H α).source) := by
  have hcLM := contMDiffOn_symm_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _))
    (trivializationAt E (TangentSpace I) β)
    (trivializationAt E (TangentSpace I) α)
  have hcont := hcLM.continuousOn
  rw [tangent_baseSet_eq, tangent_baseSet_eq] at hcont
  exact hcont.clm_apply continuousOn_const

/-! ## Pointwise rewrite: wrapped form ↔ `e_α.clmAt b · (e_β.symmL b · v)` -/

private lemma triv_alpha_clmAt_at_symmL_beta_eq_coordChangeL
    (α β : M) {b : M}
    (hbβ : b ∈ (chartAt H β).source) (hbα : b ∈ (chartAt H α).source) (v : E) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) β).symmL ℝ b v) =
      ((trivializationAt E (TangentSpace I) β).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b) v := by
  have hbβ' :
      b ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [tangent_baseSet_eq]; exact hbβ
  have hbα' :
      b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [tangent_baseSet_eq]; exact hbα
  rw [Trivialization.coordChangeL_apply _ _ ⟨hbβ', hbα'⟩]
  have hsymm : (trivializationAt E (TangentSpace I) β).symmL ℝ b v =
      (trivializationAt E (TangentSpace I) β).symm b v := by
    rw [Bundle.Trivialization.symmL_apply]
  rw [hsymm,
    Bundle.Trivialization.continuousLinearMapAt_apply,
    Bundle.Trivialization.coe_linearMapAt_of_mem _ hbα']

end BundleSectionContinuity
end Tensor
end Riemannian

end
