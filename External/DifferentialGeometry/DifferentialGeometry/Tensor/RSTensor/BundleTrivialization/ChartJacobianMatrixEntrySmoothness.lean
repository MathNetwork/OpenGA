import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.ChartJacobianClmSmoothness
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace DifferentialGeometry
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
private lemma tangent_baseSet_eq (α : M) :
    (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
  TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α

omit [Module.Finite ℝ E] in
private lemma tangent_symmL_self_eq_one (α : M) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ α = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

omit [Module.Finite ℝ E] in
private lemma tangent_clmAt_self_eq_one (α : M) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

omit [Module.Finite ℝ E] in
private lemma contMDiffOn_coordChangeL_tangent (α β : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  have h := contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _))
    (trivializationAt E (TangentSpace I) α)
    (trivializationAt E (TangentSpace I) β)
  rw [tangent_baseSet_eq, tangent_baseSet_eq] at h
  exact h

omit [Module.Finite ℝ E] in
private lemma coordChangeL_apply_eq_clmAt_symmL
    (α β : M) {b : M}
    (hbα : b ∈ (chartAt H α).source) (hbβ : b ∈ (chartAt H β).source) (v : E) :
    ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E) v =
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) := by
  have hbα' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [tangent_baseSet_eq]; exact hbα
  have hbβ' : b ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [tangent_baseSet_eq]; exact hbβ
  change ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) β) b) v =
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
      ((trivializationAt E (TangentSpace I) α).symmL ℝ b v)
  rw [Trivialization.coordChangeL_apply _ _ ⟨hbα', hbβ'⟩]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hbβ',
      Bundle.Trivialization.symmL_apply]

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_contMDiffOn
    (α β : M) (φ : E →L[ℝ] ℝ) (w : E) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b w)))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  have hcoord := contMDiffOn_coordChangeL_tangent (I := I) α β
  have hcoord_app : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E) w)
      ((chartAt H α).source ∩ (chartAt H β).source) :=
    hcoord.clm_apply contMDiffOn_const
  have hcoordj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ := φ.contMDiff
  have hwrapped : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        (((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E) w))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
    intro b hb
    exact (hcoordj _).contMDiffWithinAt.comp _ (hcoord_app _ hb) (mapsTo_univ _ _)
  refine hwrapped.congr ?_
  intro b ⟨hbα, hbβ⟩
  exact (congrArg φ
    (coordChangeL_apply_eq_clmAt_symmL (I := I) α β hbα hbβ w)).symm

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_contMDiffOn_swap
    (α β : M) (φ : E →L[ℝ] ℝ) (w : E) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) β).symmL ℝ b w)))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  have h := tangentCoordChangeL_entry_contMDiffOn (I := I) β α φ w
  rw [Set.inter_comm] at h
  exact h

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_contMDiffAt
    (α : M) (φ : E →L[ℝ] ℝ) (w : E)
    {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b w)))
      b₀ := by
  have hwrapped := tangentCoordChangeL_entry_contMDiffOn (I := I) α b₀ φ w
  have hOpen : IsOpen ((chartAt H α).source ∩ (chartAt H b₀).source) :=
    (chartAt H α).open_source.inter (chartAt H b₀).open_source
  have hb₀mem : b₀ ∈ (chartAt H α).source ∩ (chartAt H b₀).source :=
    ⟨hb₀, mem_chart_source H b₀⟩
  exact (hwrapped _ hb₀mem).contMDiffAt (hOpen.mem_nhds hb₀mem)

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_eq_symmL_entry_self
    (α : M) (φ : E →L[ℝ] ℝ) (w : E)
    {b₀ : M} (_hb₀ : b₀ ∈ (chartAt H α).source) :
    φ
      ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b₀
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b₀ w)) =
    φ
      ((trivializationAt E (TangentSpace I) α).symmL ℝ b₀ w) := by
  have h := tangent_clmAt_self_eq_one (I := I) b₀
  rw [h]
  rfl

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_contMDiffAt_swap
    (α : M) (φ : E →L[ℝ] ℝ) (w : E)
    {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => φ
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b w)))
      b₀ := by
  have hwrapped := tangentCoordChangeL_entry_contMDiffOn_swap (I := I) α b₀ φ w
  have hOpen : IsOpen ((chartAt H α).source ∩ (chartAt H b₀).source) :=
    (chartAt H α).open_source.inter (chartAt H b₀).open_source
  have hb₀mem : b₀ ∈ (chartAt H α).source ∩ (chartAt H b₀).source :=
    ⟨hb₀, mem_chart_source H b₀⟩
  exact (hwrapped _ hb₀mem).contMDiffAt (hOpen.mem_nhds hb₀mem)

omit [Module.Finite ℝ E] in
theorem tangentCoordChangeL_entry_eq_continuousLinearMapAt_entry_self
    (α : M) (φ : E →L[ℝ] ℝ) (w : E)
    {b₀ : M} (_hb₀ : b₀ ∈ (chartAt H α).source) :
    φ
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀
        ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b₀ w)) =
    φ
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀ w) := by
  have h := tangent_symmL_self_eq_one (I := I) b₀
  rw [h]
  rfl

end Tensor
end DifferentialGeometry

end
