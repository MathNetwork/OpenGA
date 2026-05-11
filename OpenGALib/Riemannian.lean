import OpenGALib.Riemannian.BumpFunction
import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.Curvature
import OpenGALib.Util.Notation
import OpenGALib.Util.Tactic
import OpenGALib.Riemannian.Gradient
import OpenGALib.Riemannian.Metric
import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.SecondFundamentalForm
import OpenGALib.Riemannian.Tensor.BundleSectionContinuity
import OpenGALib.Riemannian.Tensor.ChartJacobianSmooth
import OpenGALib.Riemannian.Tensor.ChartJacobianSmoothness
import OpenGALib.Riemannian.Tensor.Defs
import OpenGALib.Riemannian.TangentBundle
import OpenGALib.Riemannian.Instances.EuclideanSpace

/-!
# Riemannian

Riemannian-geometry primitives layered above Mathlib's covariant-derivative
infrastructure: framework-owned `RiemannianMetric` typeclass, Levi-Civita
connection (Koszul + Riesz construction), Riemann / Ricci / scalar curvature,
codim-1 second fundamental form + mean curvature, manifold gradient via
Riesz duality, and bump-function infrastructure.

This package is independent of paper-domain concerns and is a future
spin-out candidate as a standalone Lean lib (Mathlib upstream / community
use).

## Layering

```
Mathlib                      ← upstream
       ↑
Riemannian                   ← THIS package
       ↑
GeometricMeasureTheory       ← consumer (Variation/, Stable.lean)
       ↑
Regularity                   ← consumer
```

## Files

  * `Metric.lean` — `Riemannian.RiemannianMetric` typeclass + `metricInner` /
    `metricRiesz` operations + framework-owned NACG / IPS bridges
   .
  * `Connection.lean` — Levi-Civita connection via Koszul functional +
    Riesz extraction; covariant derivative `covDeriv`.
  * `Curvature.lean`  — Riemann curvature tensor, Ricci, scalar curvature.
  * `SecondFundamentalForm.lean` — codim-1 second fundamental form scalar,
    $|A|^2$, mean curvature.
  * `Gradient.lean`   — manifold gradient via Riesz duality, gradient norm
    squared.
  * `BumpFunction.lean` — scalar / radial / manifold bumps + tangent
    vector field extension (`Riemannian.BumpFunction`).
  * `Operators/` — second-order differential operators: `Hessian` (vector-field
    bilinear form via `covDeriv` + `manifoldGradient` + `metricInner`,
    plus Frobenius / trace Cauchy-Schwarz inequality), `Laplacian` (trace of
    Hessian).
  * `Tensor/` — `(0,s)` and `(r,s)` tensor bundle types over the tangent
    bundle, plus chart-Jacobian smoothness lemmas. Sub-namespace consumes
    `OpenGALib.Tensor.Multilinear` (in particular `Multilinear/Curry`).
    Phase B audit: not yet integrated with `Curvature.riemannCurvature`
    (which uses vector-field-input form, not tensor sections); see
    `docs/AUDIT_PHASE_B.md` Plan 1.

## Concrete instances

  * `Instances/EuclideanSpace.lean` — standard `RiemannianMetric` instance
    on any finite-dim real inner product space `E`, viewed as a manifold
    over itself with model `𝓘(ℝ, E)`. Specialises to
    `EuclideanSpace ℝ (Fin n)` and to `ℝ`.

## Public API

The names below form the stable public API surface of `Riemannian`.
Identifiers not listed here (e.g., private helpers, `koszulFunctional_*`
intermediate identities) are internal and may change without notice.

**Metric / inner product** (`Metric.lean`):
  * `Riemannian.RiemannianMetric` (typeclass)
  * `Riemannian.metricInner`, `Riemannian.metricRiesz`
  * `Riemannian.metricInner_comm`, `metricInner_self_pos`,
    `metricInner_self_nonneg`, `metricInner_add_left/right`,
    `metricInner_smul_left/right`, `metricInner_neg_left/right`,
    `metricInner_sub_left/right`, `metricInner_zero_left/right`
  * `Riemannian.metricRiesz_inner`, `metricRiesz_unique`
  * `Riemannian.metricInner_eq_iff_eq`

**Connection** (`Connection.lean`):
  * `Riemannian.leviCivitaConnection` — torsion-free, metric-compatible
  * `Riemannian.covDeriv` — convenience wrapper $\nabla_X Y$
  * `Riemannian.koszulFunctional`, `Riemannian.koszulCovDeriv`
  * `Riemannian.koszul_*` algebraic identities (anti-symm, metric-compat,
    add / smul in left / right / middle arg)
  * `Riemannian.leviCivitaConnection_torsion_zero`,
    `leviCivitaConnection_metric_compatible`

**Curvature** (`Curvature.lean`):
  * `Riemannian.riemannCurvature`
  * `Riemannian.riemannCurvature_antisymm`
  * `Riemannian.ricci`
  * `Riemannian.scalarCurvature`

**Second fundamental form** (`SecondFundamentalForm.lean`):
  * `Riemannian.secondFundamentalFormScalar`
  * `Riemannian.secondFundamentalFormSqNorm`
  * `Riemannian.meanCurvature`

**Gradient** (`Gradient.lean`):
  * `Riemannian.manifoldGradient`
  * `Riemannian.manifoldGradient_inner_eq`

**Bump functions** (`BumpFunction.lean`):
  * `Riemannian.BumpFunction.expDamping`
  * `Riemannian.BumpFunction.smoothStep`
  * `Riemannian.BumpFunction.radialBump`
  * `Riemannian.BumpFunction.manifoldBump`
  * `Riemannian.BumpFunction.extendVectorField`

**Smoothness infrastructure** (`TangentBundle/`, `Metric.lean`):
  * `Riemannian.TangentSmoothAt` — bundle-section smoothness predicate
  * `Riemannian.TangentSmoothAt.{mk, zero, add, neg, sub, smul,
    coordSmoothAt, iff_coord, toBundleSection}`
  * `TangentBundle.symmLFlat`,
    `TangentBundle.symmLFlat_mdifferentiableAt`
  * `Riemannian.MDifferentiableAt.metricInner_smoothAt`

**Util — engineering layer** (`Util/`, no mathematical content):
  * `Util/Notation.lean` — textbook notation: `⟪V, W⟫_g`,
    `‖V‖²_g`, `∇[X] Y`, `Riem(X, Y) Z` (scoped to `OpenGALib` /
    `Riemannian` scopes; `open scoped` to enable).
  * `Util/Attributes.lean` — `metric_simp` simp set declaration.
  * `Util/Tactic.lean` — user-facing entry point for tactic
    infrastructure.

Stability tier: pre-`v0.1.0` everything is **experimental**. The
Riemannian package carries **zero existence axioms**: all 9 primitives
(Riemann curvature, Ricci, scalar curvature, second fundamental form
+ sq norm, mean curvature, manifold gradient + sq norm, Levi-Civita
connection) are real Lean definitions. Remaining PRE-PAPER sorry'd
property-level statements (`ricci_symm`, `curvatureEndo.map_add'/_smul'`,
`tangentBundle_symmL_smoothAt`) are tracked in `docs/SORRY_CATALOG.md`
with explicit repair plans.

Performance: heavy framework proofs (`koszulLeviCivita_exists`,
`leviCivitaConnection_exists`, `koszul_*_middle`) profile at 200–400ms
typeclass-inference + 50–80ms elaboration per theorem. The strategic
`set_option backward.isDefEq.respectTransparency false` overrides on
the `TangentSpace`-fiber instance bridges (`Metric.lean`) and
chart trivialization helpers (`TangentBundle.lean`) keep the
typeclass diamond resolved without deep unfolding. No proof is on a
heartbeat-limit hot edge; future expansion has comfortable headroom.
-/
