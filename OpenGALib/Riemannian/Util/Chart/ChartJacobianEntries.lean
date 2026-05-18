import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Smoothness of chart-Jacobian matrix entries

For a smooth manifold `M` and base point `α : M`, the trivialisation of
the tangent bundle at `α` gives fibrewise continuous linear maps `(triv α).symmL ℝ b` and
`(triv α).continuousLinearMapAt ℝ b`. Scalar matrix entries are obtained
by applying these continuous linear maps to a model-basis vector and projecting onto a
model-basis coordinate.

This file proves smoothness of the **wrapped** form (a second
trivialisation centred at a reference point `β` corrects the
chart-at-`b`-variable issue) on `(chart α).source ∩ (chart β).source`.
At `β = b₀ ∈ (chart α).source`, the wrapped form agrees with the bare
form at `b = b₀`, which is enough for downstream pointwise matrix-entry
smoothness.

The proof identifies the wrapped composition with Mathlib's
`(triv α).coordChangeL ℝ (triv β) b`, smooth via `contMDiffOn_coordChangeL`.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Setup: chart base set identifications and centre identities -/

private lemma tangent_baseSet_eq (α : M) :
    (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
  TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α

private lemma tangent_symmL_self_eq_one (α : M) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ α = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

private lemma tangent_clmAt_self_eq_one (α : M) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := α) (b := α) (mem_chart_source H α)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H α) v

/-! ## Wrapped continuous linear map smoothness via `contMDiffOn_coordChangeL` -/

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

/-- **Eng.** The action of `coordChangeL` on `v` equals
`(triv β).clmAt ℝ b ((triv α).symmL ℝ b v)`. -/
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

/-! ## Matrix-entry scalar function and its smoothness -/

/-- **Eng.** The model-basis-coordinate linear functional, viewed as a continuous linear map `E →L[ℝ] ℝ`. -/
private noncomputable def basisCoordContinuousLinearMap (j : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  ((Module.finBasis ℝ E).coord j).toContinuousLinearMap

@[simp] private lemma basisCoordContinuousLinearMap_apply (j : Fin (Module.finrank ℝ E)) (v : E) :
    basisCoordContinuousLinearMap (E := E) j v = (Module.finBasis ℝ E).coord j v := rfl

/-! ### Smoothness of the wrapped scalar matrix entry -/

/-- **Eng.** Smoothness of the wrapped chart-Jacobian-inverse matrix entry on
`(chart α).source ∩ (chart β).source`. The entry is

```
(basis.coord j) ((triv β).clmAt ℝ b ((triv α).symmL ℝ b ((basis i))))
```

which is the `(j, i)` matrix entry of the trivialisation coord change
`(triv α).coordChangeL ℝ (triv β) b` in the model basis. The smoothness
follows from `contMDiffOn_coordChangeL` applied to the tangent bundle's
`ContMDiffVectorBundle ∞` instance. -/
theorem chartJinvMatrix_wrapped_entry_contMDiffOn
    (α β : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (Module.finBasis ℝ E).coord j
        ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b
            ((Module.finBasis ℝ E) i))))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  -- Express the wrapped scalar via `coordChangeL` smoothness.
  have hcoord := contMDiffOn_coordChangeL_tangent (I := I) α β
  have hcoord_app : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E)
          ((Module.finBasis ℝ E) i))
      ((chartAt H α).source ∩ (chartAt H β).source) :=
    hcoord.clm_apply contMDiffOn_const
  have hcoordj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (basisCoordContinuousLinearMap (E := E) j) :=
    (basisCoordContinuousLinearMap (E := E) j).contMDiff
  have hwrapped : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (basisCoordContinuousLinearMap (E := E) j)
        (((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) β) b : E →L[ℝ] E)
            ((Module.finBasis ℝ E) i)))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
    intro b hb
    exact (hcoordj _).contMDiffWithinAt.comp _ (hcoord_app _ hb) (mapsTo_univ _ _)
  refine hwrapped.congr ?_
  intro b ⟨hbα, hbβ⟩
  rw [basisCoordContinuousLinearMap_apply]
  exact (congrArg ((Module.finBasis ℝ E).coord j)
    (coordChangeL_apply_eq_clmAt_symmL (I := I) α β hbα hbβ
      ((Module.finBasis ℝ E) i))).symm

/-- **Eng.** Smoothness of the wrapped chart-Jacobian-forward matrix entry on
`(chart α).source ∩ (chart β).source`. The entry is

```
(basis.coord j) ((triv α).clmAt ℝ b ((triv β).symmL ℝ b ((basis i))))
```

The proof uses `chartJinvMatrix_wrapped_entry_contMDiffOn` with the roles of
`α` and `β` swapped. -/
theorem chartJMatrix_wrapped_entry_contMDiffOn
    (α β : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (Module.finBasis ℝ E).coord j
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) β).symmL ℝ b
            ((Module.finBasis ℝ E) i))))
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  -- Reduce to the inverse case via index swap.
  have h := chartJinvMatrix_wrapped_entry_contMDiffOn (I := I) β α i j
  -- The set is symmetric in α, β so we rewrite by inter_comm.
  rw [Set.inter_comm] at h
  exact h

/-! ### Smoothness of the bare scalar matrix entry — chart-Jacobian inverse

The bare matrix entry `(basis.coord j) ((triv α).symmL ℝ b ((basis i)))` is
the `(j, i)` entry of the matrix of `(triv α).symmL ℝ b`, viewed as
`E →L[ℝ] E` via the canonical type-synonym definitional equality
`TangentSpace I b = E`. We show it is smooth on `(chart α).source` by
combining:

* the smoothness of the wrapped continuous linear map `(triv b₀).clmAt ℝ b ∘L (triv α).symmL ℝ b`
  at `b = b₀` (provided by `chartJinv_pre_clm_contMDiffAt`);
* the centre identity `(triv b₀).clmAt ℝ b₀ = (1 : E →L[ℝ] E)`, which makes
  the wrapped continuous linear map evaluated at `b = b₀` equal `(triv α).symmL ℝ b₀`.

The smoothness at `b₀` of the bare matrix entry follows from the smoothness of
the wrapped continuous linear map at `b₀`, applied to `(basis i)` and projected via
`basisCoordContinuousLinearMap j`. -/

/-- **Eng.** Pointwise smoothness of the bare chart-Jacobian-inverse matrix entry,
recovered from the wrapped form at `b₀ ∈ (chart α).source`. -/
theorem chartJinvMatrix_entry_contMDiffAt_via_wrapped
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (Module.finBasis ℝ E).coord j
        ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b
            ((Module.finBasis ℝ E) i))))
      b₀ := by
  have hwrapped := chartJinvMatrix_wrapped_entry_contMDiffOn (I := I) α b₀ i j
  have hOpen : IsOpen ((chartAt H α).source ∩ (chartAt H b₀).source) :=
    (chartAt H α).open_source.inter (chartAt H b₀).open_source
  have hb₀mem : b₀ ∈ (chartAt H α).source ∩ (chartAt H b₀).source :=
    ⟨hb₀, mem_chart_source H b₀⟩
  exact (hwrapped _ hb₀mem).contMDiffAt (hOpen.mem_nhds hb₀mem)

/-- **Eng.** At the centre `b = b₀`, the wrapped chart-Jacobian-inverse
matrix entry equals the bare one. -/
theorem chartJinvMatrix_entry_wrapped_at_centre
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {b₀ : M} (_hb₀ : b₀ ∈ (chartAt H α).source) :
    (Module.finBasis ℝ E).coord j
      ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b₀
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b₀
          ((Module.finBasis ℝ E) i))) =
    (Module.finBasis ℝ E).coord j
      ((trivializationAt E (TangentSpace I) α).symmL ℝ b₀
        ((Module.finBasis ℝ E) i)) := by
  have h := tangent_clmAt_self_eq_one (I := I) b₀
  rw [h]
  rfl

/-- **Eng.** Pointwise smoothness of the bare chart-Jacobian-forward matrix entry,
recovered from the wrapped form at `b₀ ∈ (chart α).source`. -/
theorem chartJMatrix_entry_contMDiffAt_via_wrapped
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun b : M => (Module.finBasis ℝ E).coord j
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
          ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b
            ((Module.finBasis ℝ E) i))))
      b₀ := by
  have hwrapped := chartJMatrix_wrapped_entry_contMDiffOn (I := I) α b₀ i j
  have hOpen : IsOpen ((chartAt H α).source ∩ (chartAt H b₀).source) :=
    (chartAt H α).open_source.inter (chartAt H b₀).open_source
  have hb₀mem : b₀ ∈ (chartAt H α).source ∩ (chartAt H b₀).source :=
    ⟨hb₀, mem_chart_source H b₀⟩
  exact (hwrapped _ hb₀mem).contMDiffAt (hOpen.mem_nhds hb₀mem)

/-- **Eng.** At the centre `b = b₀`, the wrapped chart-Jacobian-forward
matrix entry equals the bare one. -/
theorem chartJMatrix_entry_wrapped_at_centre
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {b₀ : M} (_hb₀ : b₀ ∈ (chartAt H α).source) :
    (Module.finBasis ℝ E).coord j
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀
        ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b₀
          ((Module.finBasis ℝ E) i))) =
    (Module.finBasis ℝ E).coord j
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀
        ((Module.finBasis ℝ E) i)) := by
  have h := tangent_symmL_self_eq_one (I := I) b₀
  rw [h]
  rfl

end Tensor
end Riemannian

end
