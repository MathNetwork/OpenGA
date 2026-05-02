import Riemannian.Connection.LeviCivita
import Riemannian.TangentBundle.SmoothVectorField

/-!
# `covDeriv` smoothness lemmas

Smoothness of `covDeriv (const v) (const w) y` in `y` for chart-frame
constant tangent sections — the form arising in
`Riemannian.Curvature.ricciTraceMap` (additivity / smul slots) and
`Riemannian.Curvature.ricciFormAt` (bilinear form linearity slots).

## Form

`covDeriv X Y y = leviCivitaConnection.toFun Y y (X y)`. Smoothness in
`y` requires:

* Smoothness of the bundle CLM section
  `y ↦ leviCivitaConnection.toFun Y y` (a section of `End(TM)`); and
* Smoothness of `X y` (trivially `MDifferentiableAt` of a smooth section).

For the chart-frame constants `(fun _ : M => v)` and `(fun _ : M => w)`,
both `mfderiv (fun _ => v) = 0` and `mfderiv (fun _ => w) = 0`, so the
Lie brackets in the Koszul formula vanish:
$$K(\text{const } v, \text{const } w; Z)(y) = X(\langle w, Z \rangle)
+ Y(\langle Z, v\rangle) - Z(\langle v, w\rangle)$$
(only the 3 directional-derivative terms survive). The covariant
derivative is then determined via Riesz extraction by smooth scalar
functions, and standard chart-pullback shows smoothness of the result
in `y`.

## PRE-PAPER status

`covDeriv_const_smoothVF_smoothAt` is a **PRE-PAPER sorry** (NOT an
axiom — Phase 1.6 invariant "zero existence axioms in Riemannian package"
is preserved). The lemma is used 10× in `Riemannian.Curvature`
(`ricciTraceMap` linearity smoothness witnesses, `ricciFormAt` bilinearity
smoothness witnesses).

Closure path is **bridge investment** (multi-file framework refactor):

1. **Strengthen `koszulLeviCivita_exists`** existential clause with a
   smoothness conjunct: `∀ Y v x, TangentSmoothAt (fun y ↦ cov.toFun Y y v) x`.
   The constructed `cov.toFun` is `TensorialAt.mkHom (koszulCovDerivAux Y x hY)`,
   so smoothness reduces to smoothness of the bundle `mkHom` evaluated at v.
2. **Prove the smoothness clause** via either:
   * Mathlib's `ContMDiffCovariantDerivativeOn` API (instance for
     `leviCivitaConnection.toFun` on `Set.univ`), composed with
     `MDifferentiableAt.clm_apply` for the constant-vector evaluation.
   * Direct chain: `koszulCovDeriv` smoothness (Riesz extraction of a smooth
     functional, using bundle-CLM-inverse smoothness of `metricToDual`).
3. **Propagate** through `leviCivitaConnection_exists` (1 line — extra `∧`
   conjunct). Then `covDeriv_const_smoothVF_smoothAt` is a one-line
   `Classical.choose_spec`-style projection.

Estimated effort: 100-200 LOC of new framework primitives, comparable to
Phase 4.7's `koszulLeviCivita_exists` upgrade from axiom to
`TensorialAt.mkHom` proof. The lemma is **narrow** (chart-frame constants
only, smoothness only) — no paper-level mathematical content.

**Ground truth**: Lee, *Smooth Manifolds*, Prop. 4.26 (covariant
derivative of smooth sections is smooth on smooth manifolds).
-/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [RiemannianMetric I M]

/-- **Smoothness of `covDeriv` along a chart-frame constant direction
against a smooth vector field.**

For any `v : E` (treated as a constant tangent vector field via
`SmoothVectorField.const`) and any `SmoothVectorField` `Y`, the
covariant-derivative section
`y ↦ ∇_(const v) Y y = leviCivitaConnection.toFun Y y v` is smooth at
every point `x : M`.

PRE-PAPER sorry (NOT an axiom). Closure plan: see module docstring above
("PRE-PAPER status" section). The lemma is **narrow**: only constant
direction `(fun _ => v)`, only smooth `Y` (encoded via
`SmoothVectorField` to bundle the global smoothness witness). No
paper-level mathematical content.

**Ground truth**: Lee, *Smooth Manifolds*, Prop. 4.26. -/
theorem covDeriv_const_smoothVF_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    OpenGALib.TangentSmoothAt
      (fun y : M => covDeriv (fun _ : M => v) Y.toFun y) x := by
  -- `covDeriv X Y y = leviCivitaConnection.toFun Y y (X y)` by def. With
  -- X = (fun _ => v), this reduces to leviCivitaConnection.toFun Y.toFun y v.
  -- Smoothness comes from the strengthened `leviCivitaConnection_exists`
  -- existential's 3rd conjunct (PRE-PAPER sorry at the connection-existence
  -- level — see `LeviCivita.lean`), exposed as
  -- `leviCivitaConnection_smoothAt_const_dir`.
  exact Riemannian.leviCivitaConnection_smoothAt_const_dir Y v x

end Riemannian
