import Riemannian.BumpFunction
import Riemannian.Connection
import Riemannian.Curvature
import Riemannian.Gradient
import Riemannian.Metric
import Riemannian.SecondFundamentalForm
import Riemannian.Instances.EuclideanSpace

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
MinMax / Regularity          ← consumers
       ↑
AltRegularity                ← consumer
```

## Files

  * `Metric.lean` — `OpenGALib.RiemannianMetric` typeclass + `metricInner` /
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
    vector field extension (`OpenGALib.BumpFunction`).

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
  * `OpenGALib.RiemannianMetric` (typeclass)
  * `OpenGALib.metricInner`, `OpenGALib.metricRiesz`
  * `OpenGALib.metricInner_comm`, `metricInner_self_pos`,
    `metricInner_self_nonneg`, `metricInner_add_left/right`,
    `metricInner_smul_left/right`, `metricInner_neg_left/right`,
    `metricInner_sub_left/right`, `metricInner_zero_left/right`
  * `OpenGALib.metricRiesz_inner`, `metricRiesz_unique`
  * `OpenGALib.metricInner_eq_iff_eq`

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
  * `Riemannian.ricci`
  * `Riemannian.scalarCurvature`

**Second fundamental form** (`SecondFundamentalForm.lean`):
  * `Riemannian.secondFundamentalFormScalar`
  * `Riemannian.secondFundamentalFormSqNorm`
  * `Riemannian.meanCurvature`

**Gradient** (`Gradient.lean`):
  * `Riemannian.manifoldGradient`
  * `Riemannian.manifoldGradientNormSq`
  * `Riemannian.manifoldGradient_riesz`

**Bump functions** (`BumpFunction.lean`):
  * `OpenGALib.BumpFunction.expDamping`
  * `OpenGALib.BumpFunction.smoothStep`
  * `OpenGALib.BumpFunction.radialBump`
  * `OpenGALib.BumpFunction.manifoldBump`
  * `OpenGALib.BumpFunction.extendVectorField`

Stability tier: pre-`v0.1.0` everything is **experimental**. PRE-PAPER
sorry'd statements (`ricci_symm`, `ricciTraceMap.map_*`) and structural
axioms (`tangentBundle_symmL_smoothAt`, `koszulLeviCivita_exists`) are
tracked in `docs/AXIOM_STATUS.md` with explicit repair
plans.
-/
