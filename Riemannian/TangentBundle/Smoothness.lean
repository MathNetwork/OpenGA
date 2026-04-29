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

Independent Mathlib upstream PR candidate. -/
private theorem mfderivWithinFlat_mdifferentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x x) := by
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
  have h_inv := mfderivWithinFlat_mdifferentiableAt (I := I) (M := M) x
  have h_comp : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y)) x :=
    h_inv.comp x h_chart
  exact h_comp.congr_of_eventuallyEq
    (symmLFlat_eventuallyEq_mfderivWithinFlat (I := I) (M := M) x)

end TangentBundle
