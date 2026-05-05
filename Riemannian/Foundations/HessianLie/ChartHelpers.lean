import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Riemannian.TangentBundle.Smoothness

/-!
# Chart-bridge helpers for `mfderiv` ↔ `fderivWithin`

Three helpers that bridge manifold `mfderiv` to flat `fderivWithin` on
`range I` at the chart's base point. Used by `Manifold.lean` to lift
the flat scalar Hessian–Lie identity to the manifold via chart pullback.

## Helpers

* **`mfderiv_extChartAt_eq_id_eventually`** (Helper #1) —
  `mfderiv (extChartAt I x)` is the identity in a chart-coherent nbhd
  of `x`. Provided by `IsLocallyConstantChartedSpace H M`.

* **`mfderiv_chart_compose_apply`** (Helper #2) —
  for flat `g : E_M → F` differentiable within `range I` at `phi x`,
  the manifold derivative of `g ∘ extChartAt I x` at `x` equals
  `fderivWithin g (range I) (phi x)`. The chart-pullback chain rule
  at the chart's own base point.

* **`mfderivWithin_extChartAt_symm_eq_id_eventually`** (Helper #3) —
  the inverse of Helper #1: `mfderivWithin (extChartAt I x).symm (range I)`
  is the identity in a chart-target nbhd. Derived from Helper #1 plus
  `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`.

## Common technique

All three reduce to `tangentBundleCore.coordChange_self` once chart
selection is shown to be locally constant (via
`IsLocallyConstantChartedSpace`). Helper #3 also uses continuity of
`extChartAt I x` at the chart base for filter pull-back.
-/

open VectorField
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {H : Type*} [TopologicalSpace H]
  {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace ℝ E_M]
  {I : ModelWithCorners ℝ E_M H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section Helper1

variable [IsLocallyConstantChartedSpace H M]

/-- **Helper #1**: `mfderiv (extChartAt I x)` is the identity in a
chart-coherent neighbourhood of `x`. -/
theorem mfderiv_extChartAt_eq_id_eventually
    [IsManifold I 1 M] (x : M) :
    ∀ᶠ y in 𝓝 x, mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) y
                = ContinuousLinearMap.id ℝ E_M := by
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_chart_eq, h_chart_src] with y hy_eq hy_src
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hy_src,
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src,
      show achart H y = achart H x from Subtype.ext hy_eq]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H x) y
    (by simpa [tangentBundleCore_baseSet] using hy_src) v

/-- **Helper #3 (base point)**: `mfderivWithin (extChartAt I x).symm (range I)`
is the identity at `extChartAt I x x`. -/
theorem mfderivWithin_extChartAt_symm_eq_id_at_base
    [IsManifold I 1 M] (x : M) :
    mfderivWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm (Set.range I) (extChartAt I x x)
    = ContinuousLinearMap.id ℝ E_M := by
  have h_comp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := I) (M := M) (x := x) (mem_extChartAt_target x)
  have h_id : mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) x = ContinuousLinearMap.id ℝ E_M :=
    (mfderiv_extChartAt_eq_id_eventually (I := I) (M := M) x).self_of_nhds
  have h_symm_eq_x : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  rw [h_symm_eq_x] at h_comp
  rw [h_id] at h_comp
  simpa using h_comp

/-- **Helper #3**: `mfderivWithin (extChartAt I x).symm (range I)` is the
identity in a chart-target neighbourhood of `extChartAt I x x`. -/
theorem mfderivWithin_extChartAt_symm_eq_id_eventually
    [IsManifold I 1 M] (x : M) :
    ∀ᶠ e in 𝓝[Set.range I] (extChartAt I x x),
      mfderivWithin 𝓘(ℝ, E_M) I (extChartAt I x).symm (Set.range I) e
      = ContinuousLinearMap.id ℝ E_M := by
  have h_target : (extChartAt I x).target ∈ 𝓝[Set.range I] (extChartAt I x x) :=
    extChartAt_target_mem_nhdsWithin x
  -- Pull back chart-coherent nbhd via continuity of `extChartAt I x.symm`.
  have h_symm_tendsto : Filter.Tendsto (extChartAt I x).symm
      (𝓝[Set.range I] (extChartAt I x x)) (𝓝 x) := by
    have h_cont : ContinuousWithinAt (extChartAt I x).symm
        (extChartAt I x).target (extChartAt I x x) :=
      (continuousOn_extChartAt_symm x) _ (mem_extChartAt_target x)
    have h_symm_at_x : (extChartAt I x).symm (extChartAt I x x) = x :=
      (extChartAt I x).left_inv (mem_extChartAt_source x)
    have h_tendsto : Filter.Tendsto (extChartAt I x).symm
        (𝓝[(extChartAt I x).target] (extChartAt I x x)) (𝓝 x) := by
      have := h_cont.tendsto
      rwa [h_symm_at_x] at this
    refine h_tendsto.mono_left ?_
    rw [nhdsWithin]
    exact le_inf inf_le_left (Filter.le_principal_iff.mpr h_target)
  have h_chart_eq_e : ∀ᶠ e in 𝓝[Set.range I] (extChartAt I x x),
      chartAt H ((extChartAt I x).symm e) = chartAt H x :=
    h_symm_tendsto (chartAt_eventually_eq_of_locallyConstant x)
  filter_upwards [h_target, h_chart_eq_e] with e he_target hy_eq
  -- At point e, chart-coherence at `phi.symm e` gives `mfderiv (extChartAt I x) (phi.symm e) = id`,
  -- and the comp-identity then gives `mfderivWithin phi.symm e = id`.
  have h_symm_e_src : (extChartAt I x).symm e ∈ (chartAt H x).source := by
    have := (extChartAt I x).map_target he_target
    rwa [extChartAt_source] at this
  have h_comp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    (I := I) (M := M) (x := x) he_target
  have h_id_at_symm : mfderiv I 𝓘(ℝ, E_M) (extChartAt I x) ((extChartAt I x).symm e)
                    = ContinuousLinearMap.id ℝ E_M := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt h_symm_e_src,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core h_symm_e_src,
        show achart H ((extChartAt I x).symm e) = achart H x from Subtype.ext hy_eq]
    ext v
    exact (tangentBundleCore I M).coordChange_self (achart H x) ((extChartAt I x).symm e)
      (by simpa [tangentBundleCore_baseSet] using h_symm_e_src) v
  rw [h_id_at_symm] at h_comp
  simpa using h_comp

end Helper1

/-- **Helper #2**: chart-compose `mfderiv` at the chart base point reduces
to flat `fderivWithin`. For a flat function `g : E_M → F` differentiable
within `range I` at `extChartAt I x x`,

  `mfderiv (g ∘ extChartAt I x) x v = fderivWithin g (range I) (phi x) v`.

This is the chain-rule bridge from manifold mfderiv to flat fderivWithin. -/
theorem mfderiv_chart_compose_apply
    [IsManifold I 1 M] (x : M)
    (g : E_M → F)
    (hg : DifferentiableWithinAt ℝ g (Set.range I) (extChartAt I x x))
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, F) (fun y => g (extChartAt I x y)) x v
    = fderivWithin ℝ g (Set.range I) (extChartAt I x x) v := by
  -- Composition is MDifferentiableAt at x (within chart source, then promoted).
  have h_maps : Set.MapsTo (extChartAt I x) (chartAt H x).source (Set.range I) := by
    intro y _
    rw [extChartAt_coe]
    exact Set.mem_range_self _
  have h_comp : MDifferentiableAt I 𝓘(ℝ, F)
      (fun y => g (extChartAt I x y)) x :=
    (hg.comp_mdifferentiableWithinAt
      (mdifferentiableAt_extChartAt (mem_chart_source H x)).mdifferentiableWithinAt
      h_maps).mdifferentiableAt
        ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  rw [h_comp.mfderiv]
  -- writtenInExtChartAt simplifies to g on chart target; fderivWithin is congruent.
  have h_eqOn : (extChartAt I x).target.EqOn
      (writtenInExtChartAt I 𝓘(ℝ, F) x (fun y => g (extChartAt I x y))) g := by
    intro e he
    show (extChartAt 𝓘(ℝ, F) (g (extChartAt I x x)))
         (g (extChartAt I x ((extChartAt I x).symm e))) = g e
    rw [(extChartAt I x).right_inv he]; rfl
  have h_eventually :
      (writtenInExtChartAt I 𝓘(ℝ, F) x (fun y => g (extChartAt I x y)))
      =ᶠ[𝓝[Set.range I] (extChartAt I x x)] g := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with e he
    exact h_eqOn he
  rw [h_eventually.fderivWithin_eq (h_eqOn (mem_extChartAt_target x))]
  rfl

end Riemannian
