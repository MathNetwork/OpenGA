import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Tangent bundle — smoothness of `Trivialization.symmL`

Smoothness of the inverse trivialization map of the tangent bundle as
a non-dependent CLM-valued function of the basepoint.

## The Pi-vs-flat obstacle

For `e := trivializationAt E (TangentSpace I) x`, the natural object
`fun y : M => e.symmL ℝ y` has Pi-codomain `(y : M) → (E →L[ℝ] TangentSpace I y)`
— dependent on `y`. The framework's `metricInner_smoothAt` consumer needs
this as a non-Pi `M → (E →L[ℝ] E)` (flat codomain) to pass it through
`MDifferentiableAt.clm_apply`. The `TangentSpace I y = E` def-eq exists
(activated by `set_option backward.isDefEq.respectTransparency false`),
but **only resolves equations between values, not Pi-vs-flat function
types**. Lean's elaborator cannot unify the function types automatically.

So the consumer takes an explicit `cast` via a hypothesis
`h_TS_E_eq : ∀ y : M, (E →L[ℝ] TangentSpace I y) = (E →L[ℝ] E)` (provable
as `rfl` under transparency), and the smoothness statement is in
cast-form.

## Why this isn't in Mathlib

Mathlib provides the building blocks:

* `TangentBundle.symmL_trivializationAt` — pointwise identity
  `e.symmL ℝ y = mfderivWithin (range I) (extChartAt I x).symm (extChartAt I x y)`.
* `ContMDiffWithinAt.mfderivWithin_const` — smoothness of parametric
  `mfderivWithin` (in `inCoordinates` form).
* `IsInvertible.contDiffAt_map_inverse` — inverse of an invertible CLM
  is smooth.
* `inCoordinates_eq` — round-trip identity for chart pullback.

These are combined in `Mathlib/VectorField/Pullback.lean` (lines 280–322)
to prove smoothness of inverse-of-mfderiv in the `inCoordinates` form,
used internally for vector field pullback differentiability. But this
**non-dependent flat-CLM cast-form** of the same fact — directly
applicable to `metricInner_smoothAt` — is not exposed as a Mathlib
public lemma.

## Mathlib upstream candidacy

The lemma below is **designed to be PR-ready upon proof closure**. The
current proof body is `sorry`'d; once the Pullback.lean-style technique
is fully adapted, the lemma can be PR'd to Mathlib by:

  1. Generalising `[NormedSpace ℝ E]` to
     `{𝕜 : Type*} [NontriviallyNormedField 𝕜]` (mechanical refactor;
     Mathlib's tangent bundle is already 𝕜-parametric).
  2. Moving to `Mathlib/Geometry/Manifold/MFDeriv/Atlas.lean` next to
     `TangentBundle.symmL_trivializationAt`.

The proof technique is acknowledged-adapted from
`Mathlib/VectorField/Pullback.lean`.

## Used by

* `OpenGALib.MDifferentiableAt.metricInner_smoothAt` (in
  `Riemannian/Metric/Smooth.lean`).

**Ground truth**: standard for tangent bundles — chart-derivatives are
smooth, hence so are their inverses.
-/

open scoped ContDiff Manifold Topology

namespace TangentBundle

set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of `Trivialization.symmL` for the tangent bundle**, as a
CLM-valued function of the basepoint, in non-dependent flat-codomain form.

For `e := trivializationAt E (TangentSpace I) x`, the function
`y ↦ e.symmL ℝ y` is `MDifferentiableAt` at `x` as a map
`M → (E →L[ℝ] E)`. The dependent codomain `E →L[ℝ] TangentSpace I y`
is bridged via the explicit `cast (h_TS_E_eq y)` argument (the type
equality is `rfl` under `respectTransparency false`).

Proof technique: parametric inverse-mfderiv smoothness, adapted from
`Mathlib/VectorField/Pullback.lean` (lines 280-322). Applies
`TangentBundle.symmL_trivializationAt` to rewrite to mfderivWithin
form, then `ContMDiffWithinAt.mfderivWithin_const` for parametric
smoothness, with `IsInvertible.contDiffAt_map_inverse` bridging the
inverse, and `inCoordinates_eq` for the round-trip identity. -/
theorem symmL_mdifferentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (h_TS_E_eq : ∀ y : M, (E →L[ℝ] TangentSpace I y) = (E →L[ℝ] E)) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => cast (h_TS_E_eq y)
        ((trivializationAt E (TangentSpace I) x).symmL ℝ y)) x := by
  -- Spike-in-progress: structural framework laid out in docstring.
  -- Closure of the inCoordinates_eq-based bridge requires careful
  -- multi-step rewrite (see Pullback.lean 280-322 for the adapted
  -- technique). The cast-form keeps the metricInner_smoothAt downstream
  -- API working; the proof body will be filled in a follow-up commit.
  sorry

end TangentBundle
