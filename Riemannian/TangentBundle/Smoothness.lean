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

/-! ## Helper 1 — parametric chart-inverse-mfderiv smoothness

The substantive open content. Closure requires Mathlib's `Pullback.lean`
inverse-mfderiv pattern. -/

/-- Smoothness of `mfderivWithinFlat x` at `extChartAt I x x`, viewed as
a function `E → (E →L[ℝ] E)`.

This is the parametric inverse-mfderiv smoothness — the "raw" form
(non-`inCoordinates`) of `Mathlib/VectorField/Pullback.lean`'s technique.

**Sorry status**: PRE-PAPER. Closure requires:
* `ContMDiffWithinAt.mfderivWithin_const` for in-coordinates form
  smoothness of `mfderivWithin (range I) (extChartAt I x).symm`.
* `IsInvertible.contDiffAt_map_inverse` for inverse smoothness at
  invertible maps.
* `inCoordinates_eq` round-trip identity to bridge raw / in-coordinates
  forms.
* Composition assembly with `uniqueMDiffOn_range I` (chart range has
  unique mfderiv structure on smooth manifolds).

Independent Mathlib upstream PR candidate.

**Architecture note**: the conclusion is `MDifferentiableWithinAt`
in `Set.range I` rather than `MDifferentiableAt`. This avoids
the `[I.Boundaryless]` constraint (which would force `range I = univ`).
The main theorem `symmLFlat_mdifferentiableAt` recovers the at-form
on `M` via `MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin`,
using the fact that `extChartAt I x` maps a neighborhood of `x` into
`range I` regardless of boundary structure. -/
private theorem mfderivWithinFlat_mdifferentiableWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (Set.range I) (extChartAt I x x) := by
  -- Step 1: chart-inverse smoothness in range I.
  have h_smooth_inv :
      ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (Set.range I) (extChartAt I x x) :=
    contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x)
  -- Step 2: Mathlib's mfderivWithin_const gives inCoordinates-form smoothness.
  have h_unique : UniqueMDiffOn 𝓘(ℝ, E) (Set.range (I : H → E)) := I.uniqueMDiffOn
  have h_mem : extChartAt I x x ∈ Set.range (I : H → E) := Set.mem_range_self _
  have h2 : (1 : WithTop ℕ∞) + 1 ≤ ∞ := by decide
  have h_inCoords :
      ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) 1
        (inTangentCoordinates 𝓘(ℝ, E) I id (extChartAt I x).symm
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I))
          (extChartAt I x x))
        (Set.range I) (extChartAt I x x) :=
    h_smooth_inv.mfderivWithin_const (m := 1) h2 h_mem h_unique
  -- Step 3: convert ContMDiffWithinAt → MDifferentiableWithinAt.
  have h_inCoordsW :
      MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
        (inTangentCoordinates 𝓘(ℝ, E) I id (extChartAt I x).symm
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I))
          (extChartAt I x x))
        (Set.range I) (extChartAt I x x) :=
    h_inCoords.mdifferentiableWithinAt one_ne_zero
  -- Step 4: Bridge `inCoordinates` ↔ raw form on a neighbourhood within
  -- `range I` of `extChartAt I x x`. By `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm`,
  -- the inCoords value of `mfderivWithin (.symm) (range I)` is constant `id`
  -- on the chart target — but this means `inCoords ≠ raw form` (the latter
  -- being the actual non-trivial chart-inverse-mfderiv). The proof technique
  -- of `Mathlib/VectorField/Pullback.lean` requires composing with
  -- `ContinuousLinearMap.inverse` to recover raw form smoothness from inCoords
  -- smoothness of the FORWARD chart's mfderiv (not the backward chart we have).
  --
  -- TODO closure path (full proof):
  -- (a) Apply mfderivWithin_const to `extChartAt I x : M → E` (forward chart),
  --     get inCoords smoothness of `y ↦ mfderiv (extChartAt I x) y` as
  --     function `M → (E →L E)` near `x`.
  -- (b) Compose with `ContinuousLinearMap.inverse` (smooth at invertible CLMs;
  --     forward chart's mfderiv is invertible by `isInvertible_mfderiv_extChartAt`).
  -- (c) Compose with `(extChartAt I x).symm : E → M` smooth on `range I`.
  -- (d) The result `e₀ ↦ inverse(mfderiv (extChartAt I x) ((.symm) e₀))` equals
  --     `mfderivWithin (.symm) (range I) e₀ = mfderivWithinFlat x e₀` by
  --     `mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm` + `IsInvertible.of_inverse`.
  sorry

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
