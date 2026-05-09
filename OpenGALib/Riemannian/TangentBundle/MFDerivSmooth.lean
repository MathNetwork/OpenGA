import OpenGALib.Riemannian.TangentBundle.Smoothness
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# `mfderiv` smoothness for chart-frame-constant directions

For a globally smooth scalar function $f : M \to \mathbb{R}$ and any
chart-frame-constant direction $v : E$, the function $y \mapsto df_y(v)$ is
smooth at every $x$.

Boundary-agnostic: works on manifolds with corners. The chart-pullback
identification uses `MDifferentiableAt.mfderiv` formula
($df = \mathrm{fderivWithin}_{\mathrm{range}\, I}(f \circ \mathrm{chart.symm})$),
combined with `IsLocallyConstantChartedSpace` to keep `extChartAt I y =
extChartAt I x` constant in a neighborhood. Smoothness of the chart-side
`fderivWithin` lifts to `M` via `comp_of_preimage_mem_nhdsWithin`. -/

open scoped ContDiff Manifold Topology

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of `mfderiv f y v` in `y`** for chart-frame-constant `v : E`.

Under `IsLocallyConstantChartedSpace`, in a neighborhood of `x` the chart
`extChartAt I y = extChartAt I x` is constant. Combined with
`MDifferentiableAt.mfderiv` (chart-pullback formula), we have on a nhd of `x`:
$$df_y(v) = \mathrm{fderivWithin}_{\mathrm{range}\,I}(f \circ \mathrm{chart.symm})(\mathrm{chart}\,y)(v).$$
Smoothness of the RHS follows from `ContDiffWithinAt.fderivWithin_right`
+ chart smoothness on `M`, bridged via
`MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin`. -/
theorem mfderiv_const_dir_smoothAt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : E) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => mfderiv I 𝓘(ℝ, ℝ) f y v) x := by
  -- Step 1: f ∘ chart.symm is ContDiffWithinAt within range I at chart x.
  have h_symm_within : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
      (Set.range I) (extChartAt I x x) :=
    contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x)
  have h_eqx : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have h_comp_within : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x) :=
    (hf x).comp_contMDiffWithinAt_of_eq h_symm_within h_eqx
  have h_f_hat : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I x).symm) (Set.range I)
      (extChartAt I x x) :=
    h_comp_within.contDiffWithinAt
  -- Step 2: fderivWithin (range I) f̂ smooth within range I at chart x.
  have h_unique : UniqueDiffOn ℝ (Set.range (I : H → E)) := I.uniqueDiffOn
  have h_mem : extChartAt I x x ∈ Set.range (I : H → E) := Set.mem_range_self _
  have h_fderiv_within : ContDiffWithinAt ℝ ∞
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_f_hat.fderivWithin_right h_unique (le_refl _) h_mem
  -- Apply at constant v: still ContDiffWithinAt within range I.
  have h_fderiv_apply_within : ContDiffWithinAt ℝ ∞
      (fun e₀ : E => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) e₀ v)
      (Set.range I) (extChartAt I x x) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.contDiffWithinAt.comp
      (extChartAt I x x) h_fderiv_within (Set.mapsTo_univ _ _)
  -- Convert to MDifferentiableWithinAt (normed source/target).
  have h_fderiv_mdiff_within : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun e₀ : E => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) e₀ v)
      (Set.range I) (extChartAt I x x) :=
    h_fderiv_apply_within.contMDiffWithinAt.mdifferentiableWithinAt (by decide)
  -- Step 3: bridge to M-side at x via comp_of_preimage_mem_nhdsWithin.
  have h_chart_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x : M → E) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E)
      (extChartAt I x) Set.univ x :=
    h_chart_mdiff.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_fderiv_compose_within : MDifferentiableWithinAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) v)
      Set.univ x :=
    h_fderiv_mdiff_within.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_fderiv_at : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) v) x :=
    mdifferentiableWithinAt_univ.mp h_fderiv_compose_within
  -- Step 4: bridge to mfderiv f y v on a chart-source nhd of x via
  -- MDifferentiableAt.mfderiv (chart-pullback formula) +
  -- IsLocallyConstantChartedSpace (chart locally constant ⇒ extChartAt I y = extChartAt I x).
  apply h_fderiv_at.congr_of_eventuallyEq
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have h_top_ne : (∞ : ℕ∞ω) ≠ 0 := by decide
  filter_upwards [h_chart_eq, h_chart_src] with y hy_chart hy_src
  have hf_at_y : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt h_top_ne
  -- Use MDifferentiableAt.mfderiv at y, with extChartAt I y = extChartAt I x by hy_chart.
  have h_extChart_eq : extChartAt I y = extChartAt I x := by
    show (chartAt H y).extend I = (chartAt H x).extend I
    rw [hy_chart]
  show mfderiv I 𝓘(ℝ, ℝ) f y v
      = fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) y) v
  rw [hf_at_y.mfderiv]
  -- Identify writtenInExtChartAt I 𝓘(ℝ, ℝ) y f with f ∘ chart_x.symm.
  -- For ℝ-self target, extChartAt 𝓘(ℝ, ℝ) z = identity, and chart_y = chart_x.
  have h_written :
      writtenInExtChartAt I 𝓘(ℝ, ℝ) y f = f ∘ (extChartAt I x).symm := by
    funext z
    show (extChartAt 𝓘(ℝ, ℝ) (f y)) (f ((extChartAt I y).symm z))
        = f ((extChartAt I x).symm z)
    rw [h_extChart_eq]
    rfl
  rw [h_written, h_extChart_eq]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of `mfderiv f y (V y)` in `y`** for smoothly varying direction
`V : M → E`. Generalization of `mfderiv_const_dir_smoothAt` via `clm_apply` of
the chart-pullback `fderivWithin` with smooth `V`. -/
theorem mfderiv_smoothDir_smoothAt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    {V : M → E} (hV : ContMDiffAt I 𝓘(ℝ, E) ∞ V x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ) f y (V y)) x := by
  -- Step 1: f ∘ chart.symm ContDiffWithinAt within range I.
  have h_symm_within : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
      (Set.range I) (extChartAt I x x) :=
    contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x)
  have h_eqx : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have h_comp_within : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x) :=
    (hf x).comp_contMDiffWithinAt_of_eq h_symm_within h_eqx
  have h_f_hat : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I x).symm) (Set.range I)
      (extChartAt I x x) :=
    h_comp_within.contDiffWithinAt
  -- Step 2: fderivWithin (range I) f̂ smooth as CLM-valued within range I.
  have h_unique : UniqueDiffOn ℝ (Set.range (I : H → E)) := I.uniqueDiffOn
  have h_mem : extChartAt I x x ∈ Set.range (I : H → E) := Set.mem_range_self _
  have h_fderiv_within : ContDiffWithinAt ℝ ∞
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_f_hat.fderivWithin_right h_unique (le_refl _) h_mem
  have h_fderiv_mdiff_within : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℝ)
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_fderiv_within.contMDiffWithinAt.mdifferentiableWithinAt (by decide)
  -- Step 3: bridge to M-side at x.
  have h_chart_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x : M → E) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E)
      (extChartAt I x) Set.univ x :=
    h_chart_mdiff.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_fderiv_compose_within : MDifferentiableWithinAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y))
      Set.univ x :=
    h_fderiv_mdiff_within.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_fderiv_at : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y)) x :=
    mdifferentiableWithinAt_univ.mp h_fderiv_compose_within
  -- Step 4: clm_apply with smooth V.
  have hV_mdiff : MDifferentiableAt I 𝓘(ℝ, E) V x :=
    hV.mdifferentiableAt (by decide)
  have h_compose : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) (V y)) x :=
    h_fderiv_at.clm_apply hV_mdiff
  -- Step 5: equate with mfderiv f y (V y) on chart source nhd.
  apply h_compose.congr_of_eventuallyEq
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have h_top_ne : (∞ : ℕ∞ω) ≠ 0 := by decide
  filter_upwards [h_chart_eq, h_chart_src] with y hy_chart hy_src
  have hf_at_y : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt h_top_ne
  have h_extChart_eq : extChartAt I y = extChartAt I x := by
    show (chartAt H y).extend I = (chartAt H x).extend I
    rw [hy_chart]
  show mfderiv I 𝓘(ℝ, ℝ) f y (V y)
      = fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) y) (V y)
  rw [hf_at_y.mfderiv]
  have h_written :
      writtenInExtChartAt I 𝓘(ℝ, ℝ) y f = f ∘ (extChartAt I x).symm := by
    funext z
    show (extChartAt 𝓘(ℝ, ℝ) (f y)) (f ((extChartAt I y).symm z))
        = f ((extChartAt I x).symm z)
    rw [h_extChart_eq]
    rfl
  rw [h_written, h_extChart_eq]
  rfl

end OpenGALib
