import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Tangent bundle — flat-codomain inverse trivialization + smoothness

Framework-owned **flat-codomain** form of `Trivialization.symmL` for the
tangent bundle, hiding the dependent codomain `E →L[ℝ] TangentSpace I y`
behind the `TangentSpace I y = E` def-eq. User-facing API takes flat
types; `cast` is internal implementation detail.

## API

  * `TangentBundle.symmLFlat x y : E →L[ℝ] E` — flat-type inverse
    trivialization at fiber `y`, basepoint `x`. Internally
    `(trivializationAt E (TangentSpace I) x).symmL ℝ y`, retyped via
    the `TangentSpace I y = E` def-eq.
  * `TangentBundle.symmLFlat_mdifferentiableAt` — smoothness of
    `y ↦ symmLFlat x y` at `x` as a function `M → (E →L[ℝ] E)`.
    Sorry'd body, statement clean (no cast / no `h_TS_E_eq`).

## Internal proof structure

Two flat-typed framework wrappers + one filter-level bridge:

  * **Wrapper** `symmLFlat` — flat form of `Trivialization.symmL`.
  * **Wrapper** `mfderivWithinFlat` (private) — flat form of
    `mfderivWithin (range I) (extChartAt I x).symm`.
  * **Helper 1** `mfderivWithinFlat_mdifferentiableAt` (private) —
    parametric smoothness of the chart-inverse-mfderiv.
    Substantive open content. Adapted from
    `Mathlib/VectorField/Pullback.lean` lines 280-322. **Sorry'd body**.
  * **Helper 2** `symmLFlat_eventuallyEq_mfderivWithinFlat` (private) —
    pointwise rewrite via `TangentBundle.symmL_trivializationAt` lifted
    to filter level. Closed.
  * **Main** `symmLFlat_mdifferentiableAt` — composes Helper 1 with
    `mdifferentiableAt_extChartAt`, bridges via Helper 2 with
    `MDifferentiableAt.congr_of_eventuallyEq`. Real proof, no `sorry`
    modulo Helper 1.

## Mathlib upstream candidacy

  * Helper 1 is a self-contained Mathlib upstream PR candidate
    (parametric smoothness of `mfderivWithin` for chart inverses).
    Generalisation: `[NontriviallyNormedField 𝕜]`, target
    `Mathlib/Geometry/Manifold/MFDeriv/Atlas.lean`.
  * `symmLFlat` / `mfderivWithinFlat` are framework-internal flat-API
    wrappers — Mathlib favors dependent codomain by design.

Proof technique acknowledgment: adapted from `VectorField/Pullback.lean`.

## Used by

  * `OpenGALib.MDifferentiableAt.metricInner_smoothAt`
    (`Riemannian/Metric/Smooth.lean`).

**Ground truth**: standard for tangent bundles — chart-derivatives are
smooth, hence so are their inverses.
-/

open scoped ContDiff Manifold Topology

namespace TangentBundle

set_option backward.isDefEq.respectTransparency false in
/-- **Flat-codomain inverse trivialization** of the tangent bundle.

The underlying value at fiber `y` is
`(trivializationAt E (TangentSpace I) x).symmL ℝ y`, retyped as
`E →L[ℝ] E` via the `TangentSpace I y = E` def-eq (made transparent by
`backward.isDefEq.respectTransparency false`). Hides the dependent
codomain so user-facing API speaks of `M → (E →L[ℝ] E)` directly. -/
noncomputable def symmLFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x).symmL ℝ y

set_option backward.isDefEq.respectTransparency false in
/-- **Flat-codomain chart-inverse-mfderiv** wrapper. The underlying
value at `e₀ ∈ E` is
`mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) e₀`, retyped
as `E →L[ℝ] E` via `TangentSpace I _ = E` def-eq. -/
private noncomputable def mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (e₀ : E) : E →L[ℝ] E :=
  mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) e₀

/-! ## Infrastructure: trivialization `continuousLinearMapAt` smoothness

Mathlib gives `Trivialization.contMDiffOn` (trivialization is smooth as a
fiber-bundle iso) and `ContMDiffVectorBundle.contMDiffOn_coordChangeL`
(coord change between two trivializations is smooth as `B → F →L F`).
Neither directly gives smoothness of one trivialization's
`continuousLinearMapAt` as a model-fiber-valued function `B → (F →L F)`.

For the tangent bundle, where `TangentSpace I y = E` def-equally, this
bridge IS achievable. The infrastructure lemma below converts
trivialization fiber-iso smoothness into model-fiber-valued CLM
smoothness via the def-eq + finite-dimensional component extraction. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Flat-codomain forward chart mfderiv** wrapper. Underlying value
at `y ∈ M` is `(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y`,
retyped from `TangentSpace I y →L[ℝ] E` to `E →L[ℝ] E` via the
`TangentSpace I y = E` def-eq.

By `TangentBundle.continuousLinearMapAt_trivializationAt`, equals
`mfderiv (extChartAt I x₀) y` on chart source. -/
noncomputable def continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y

/-- **Forward chart mfderiv smoothness as model-fiber-valued CLM**
(infrastructure / Mathlib upstream PR candidate).

The chart's mfderiv as a function of basepoint is smooth `M → (E →L E)`,
on chart base set. This is the natural mathematical statement
("a smooth chart's derivative is a smooth function of basepoint")
and the **fundamental** smoothness fact for tangent-bundle infrastructure.

The backward-direction (chart-inverse-mfderiv) corollary
`contMDiffOn_mfderivWithinFlat` follows via `inverse` composition + the
chain identity `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`.

**Sorry status**: PRE-PAPER. Closure path:
* `Trivialization.contMDiffOn` gives smoothness of `e : TotalSpace → M × E`
  on its source.
* For each `v : E`, the constant section `b ↦ ⟨b, v⟩` (treating v as
  fiber via `TangentSpace I b = E` def-eq) is smooth bundle-section.
* Apply trivialization to the constant section: `b ↦ e ⟨b, v⟩`. By bundle
  iso smoothness, this is smooth.
* The second component is `b ↦ (e ⟨b, v⟩).2 = e.continuousLinearMapAt R b v`,
  smooth as `M → E` for fixed v.
* Use `[FiniteDimensional ℝ E]` to lift pointwise-in-v smoothness to
  CLM-valued smoothness via basis decomposition. -/
theorem contMDiffOn_continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  -- TODO: build via `Trivialization.contMDiffOn` + finite-dim component
  -- extraction. See docstring above.
  sorry

/-- **Backward chart-inverse-mfderiv smoothness on chart target**
(corollary of `contMDiffOn_continuousLinearMapAtFlat` via inverse).

Derived from forward chart smoothness via:
* `inverse : (E →L E) → (E →L E)` smooth at invertible CLMs (CompleteSpace E)
* Chain identity: `mfderivWithin (.symm) (range I) e₀ = inverse(mfderiv (extChartAt I x) ((.symm) e₀))`
* `(extChartAt I x).symm : E → M` smooth on chart target -/
theorem contMDiffOn_mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x).target := by
  -- Step 1: forward chart smooth on chart source (baseSet of trivAt x).
  have h_fwd : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) x)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    contMDiffOn_continuousLinearMapAtFlat x
  -- Step 2: chart inverse smooth on chart target into chart source.
  have h_symm : ContMDiffOn 𝓘(ℝ, E) I ∞
      (extChartAt I x).symm (extChartAt I x).target :=
    contMDiffOn_extChartAt_symm x
  have h_maps_to : Set.MapsTo (extChartAt I x).symm
      (extChartAt I x).target
      (trivializationAt E (TangentSpace I) x).baseSet := by
    intro e₀ he₀
    -- (.symm) e₀ ∈ chart source ⊆ baseSet
    have h_src : (extChartAt I x).symm e₀ ∈ (extChartAt I x).source :=
      PartialEquiv.map_target _ he₀
    rwa [extChartAt_source] at h_src
  -- Step 3: composition gives smoothness of `e₀ ↦ continuousLinearMapAtFlat x ((.symm) e₀)`
  -- on chart target.
  have h_compose : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun e₀ => continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀))
      (extChartAt I x).target :=
    h_fwd.comp h_symm h_maps_to
  -- Step 4: each value `continuousLinearMapAtFlat x ((.symm) e₀)` is invertible
  -- on chart target (forward chart is local diffeomorphism).
  have h_invertible : ∀ e₀ ∈ (extChartAt I x).target,
      (continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀)).IsInvertible := by
    intro e₀ he₀
    have h_src : (extChartAt I x).symm e₀ ∈ (extChartAt I x).source :=
      PartialEquiv.map_target _ he₀
    -- continuousLinearMapAtFlat x y = mfderiv (extChartAt I x) y for y in chart source
    have h_chart_src : (extChartAt I x).symm e₀ ∈ (chartAt H x).source := by
      rwa [extChartAt_source] at h_src
    -- Convert via TangentBundle.continuousLinearMapAt_trivializationAt
    show ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ
      ((extChartAt I x).symm e₀)).IsInvertible
    rw [TangentBundle.continuousLinearMapAt_trivializationAt h_chart_src]
    exact isInvertible_mfderiv_extChartAt h_src
  -- Step 5: compose with `ContinuousLinearMap.inverse` (smooth at invertible).
  have h_inverse_comp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun e₀ => ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat (I := I) (M := M) x
          ((extChartAt I x).symm e₀)))
      (extChartAt I x).target := by
    intro e₀ he₀
    have h_inv_at : (continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀)).IsInvertible :=
      h_invertible e₀ he₀
    have h_cd : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat x ((extChartAt I x).symm e₀)) :=
      ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse h_inv_at
    exact h_cd.contMDiffAt.contMDiffWithinAt.comp e₀ (h_compose e₀ he₀) (Set.mapsTo_univ _ _)
  -- Step 6: identify `mfderivWithinFlat x e₀` with the inverse via chain identity.
  apply h_inverse_comp.congr
  intro e₀ he₀
  -- Goal: `mfderivWithinFlat x e₀ = inverse(continuousLinearMapAtFlat x ((.symm) e₀))`
  show mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) e₀
    = ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat (I := I) (M := M) x ((extChartAt I x).symm e₀))
  have h_chart_src : (extChartAt I x).symm e₀ ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact PartialEquiv.map_target _ he₀
  -- Convert continuousLinearMapAtFlat to mfderiv (forward chart) via Mathlib lemma.
  have h_eq_mfderiv :
      continuousLinearMapAtFlat (I := I) (M := M) x ((extChartAt I x).symm e₀)
        = mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm e₀) := by
    show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ
        ((extChartAt I x).symm e₀)
      = mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm e₀)
    exact TangentBundle.continuousLinearMapAt_trivializationAt h_chart_src
  rw [h_eq_mfderiv]
  -- Chain identities give: inverse(forward-mfderiv) = backward-mfderivWithin
  have h_chain := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x) he₀
  have h_chain' := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x) he₀
  exact (ContinuousLinearMap.inverse_eq h_chain h_chain').symm

/-! ## Helper 1 — single-point version (corollary of `contMDiffOn_mfderivWithinFlat`)

Bridge from on-set smoothness (`contMDiffOn_mfderivWithinFlat`, on chart
target) to single-point `MDifferentiableWithinAt` at the basepoint within
`range I`. Used by the main theorem `symmLFlat_mdifferentiableAt`. -/

/-- `MDifferentiableWithinAt` form of `mfderivWithinFlat x` at the
basepoint `extChartAt I x x` within `Set.range I`. -/
private theorem mfderivWithinFlat_mdifferentiableWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (Set.range I) (extChartAt I x x) := by
  -- Derived from on-set form `contMDiffOn_mfderivWithinFlat`:
  -- (1) `ContMDiffOn ... mfderivWithinFlat target` → `MDifferentiableOn ... target`
  -- (2) Apply at basepoint `extChartAt I x x ∈ target` → `MDifferentiableWithinAt ... target`
  -- (3) Convert within-target → within-range-I via `mono_of_mem_nhdsWithin` (since
  --     target ⊆ range I, `range I ∈ 𝓝[target] (extChartAt I x x)` trivially).
  have h_top_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have h_on : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x).target :=
    (contMDiffOn_mfderivWithinFlat x).mdifferentiableOn h_top_ne_zero
  have h_at_target : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat x) (extChartAt I x).target (extChartAt I x x) :=
    h_on _ (mem_extChartAt_target x)
  exact h_at_target.mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x)

/-! ## Helper 2 — eventually-equal rewrite (closed)

Lifts `TangentBundle.symmL_trivializationAt` (Mathlib pointwise identity
on chart source) to filter-level eventually-equal, expressed against
`symmLFlat` and `mfderivWithinFlat`. -/

set_option backward.isDefEq.respectTransparency false in
/-- For `y` in chart-source nbhd of `x`, `symmLFlat x y` equals
`mfderivWithinFlat x (extChartAt I x y)`. Lifted to `=ᶠ[𝓝 x]`. -/
private theorem symmLFlat_eventuallyEq_mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    (fun y : M => symmLFlat (I := I) (M := M) x y)
      =ᶠ[𝓝 x]
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y)) := by
  have h_chart_nhds : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_chart_nhds] with y hy
  show (trivializationAt E (TangentSpace I) x).symmL ℝ y =
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) (extChartAt I x y)
  exact TangentBundle.symmL_trivializationAt hy

/-! ## Main theorem — clean flat-type API, no cast in signature -/

/-- **Smoothness of `symmLFlat`** — the framework's flat-codomain inverse
trivialization is `MDifferentiableAt` at `x` as a map `M → (E →L[ℝ] E)`.

No `cast`, no `h_TS_E_eq` parameter in user-facing signature. The
`TangentSpace I y = E` def-eq is hidden inside `symmLFlat`'s definition.

Proof: composition of `extChartAt I x` (smooth, `mdifferentiableAt_extChartAt`)
with `mfderivWithinFlat x` (smooth, Helper 1), bridged to `symmLFlat` via
Helper 2's eventually-equal identity. -/
theorem symmLFlat_mdifferentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => symmLFlat (I := I) (M := M) x y) x := by
  have h_chart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_inv := mfderivWithinFlat_mdifferentiableWithinAt (I := I) (M := M) x
  -- Compose: `mfderivWithinFlat x ∘ extChartAt I x` is at-form smooth on M.
  -- The chart `extChartAt I x` maps a neighborhood of `x` into `range I` (no
  -- boundary assumption needed): on `(chartAt H x).source`, `extChartAt I x y
  -- = I (chartAt H x y) ∈ range I`.
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E) (extChartAt I x) Set.univ x :=
    h_chart.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_within : MDifferentiableWithinAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y))
      Set.univ x :=
    h_inv.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_comp : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y)) x :=
    mdifferentiableWithinAt_univ.mp h_within
  exact h_comp.congr_of_eventuallyEq
    (symmLFlat_eventuallyEq_mfderivWithinFlat (I := I) (M := M) x)

end TangentBundle
