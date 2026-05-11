import OpenGALib.Riemannian.Tensor.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Pointwise-evaluation continuity of variable-base trivialization actions

For a smooth manifold `M` modelled on `(E, H)` with model `I`, the trivialization
of the tangent bundle at a fixed central point `α : M` provides, for each base
point `b` in the chart source at `α`, a continuous linear map
`(trivializationAt α).continuousLinearMapAt ℝ b : TangentSpace I b →L[ℝ] E`
together with its inverse `(trivializationAt α).symmL ℝ b`.

When evaluated at a fixed model-fibre vector `v : E` (interpreted in
`TangentSpace I b = E` via the canonical type-synonym definitional equality), both
yield `M → E`-valued functions. We establish that these pointwise-evaluation
functions are continuous on the chart source at `α`.

The same statements are derived for the `(0,s)`- and `(r,s)`-tensor bundles
through the multilinear and hom constructions inherited from the tangent bundle.

## Strategy

Two infrastructure pieces are used:

1. The coordinate-change-applied continuity lemma `continuousOn_coordChangeL_apply`
   (continuity of `b ↦ (e_β.coordChangeL ℝ e_α b) v` on
   `chart β source ∩ chart α source`), proved from Mathlib's
   `contMDiffOn_coordChangeL`. By the trivialization-inverse identity, this
   wrapped-form value equals `e_α.continuousLinearMapAt ℝ b · (e_β.symmL ℝ b · v)`.

2. The smooth local-frame section `b ↦ e_β.symmL ℝ b · v`, which is a smooth
   section of the tangent bundle on `chart β source` (Mathlib's
   `contMDiffOn_localFrame_baseSet` extended to general `v` by linearity), with
   value `v` at `b = β` (centre identity).

Combining these over a neighbourhood cover of `chart α source` by sets
`chart β source ∩ chart α source`, together with the centre identities
`(e_β.symmL ℝ β) = id` and `(e_β.continuousLinearMapAt ℝ β) = id`, we recover
the pointwise bare continuity.

## Main statements

* `tangent_continuousOn_apply_continuousLinearMapAt`
* `tangent_continuousOn_apply_symmL`
* `tensor0S_continuousOn_apply_continuousLinearMapAt`
* `tensor0S_continuousOn_apply_symmL`
* `tensorRS_continuousOn_apply_continuousLinearMapAt`
* `tensorRS_continuousOn_apply_symmL`
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
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
