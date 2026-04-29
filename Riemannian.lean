import Riemannian.BumpFunction
import Riemannian.Connection
import Riemannian.Curvature
import Riemannian.Foundations.Notation
import Riemannian.Foundations.Tactic
import Riemannian.Gradient
import Riemannian.Metric
import Riemannian.SecondFundamentalForm
import Riemannian.TangentBundle.Smoothness
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

**Foundations** (`Foundations/`):
  * `Foundations/Notation.lean` — textbook notation: `⟪V, W⟫_g`,
    `‖V‖²_g`, `∇[X] Y`, `Riem(X, Y) Z` (scoped to `OpenGALib` /
    `Riemannian` scopes; `open scoped` to enable).
  * `Foundations/Attributes.lean` — `metric_simp` simp set declaration.
  * `Foundations/Tactic.lean` — user-facing entry point for tactic
    infrastructure.

Stability tier: pre-`v0.1.0` everything is **experimental**. PRE-PAPER
sorry'd statements (`ricci_symm`, `ricciTraceMap.map_*`) and structural
axioms (`tangentBundle_symmL_smoothAt`, `koszulLeviCivita_exists`) are
tracked in `docs/AXIOM_STATUS.md` with explicit repair
plans.
-/

/-! ## UXTest — Foundations layer

Verifies that the notation + `metric_simp` tactic infrastructure resolve
end-to-end. Regression guard against signature drift in the notation
elaboration. -/

section UXTestFoundations

open OpenGALib
open scoped OpenGALib Riemannian

/-- The `⟪V, W⟫_g` notation elaborates to `metricInner _ V W` with the
basepoint inferred from the type of `V`, `W`. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (V W : TangentSpace I x) :
    ⟪V, W⟫_g = metricInner x V W :=
  rfl

/-- The `‖V‖²_g` notation gives the squared norm. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (V : TangentSpace I x) :
    ‖V‖²_g = metricInner x V V :=
  rfl

/-- The `metric_simp` simp set discharges routine inner-product
algebra in one line. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (W : TangentSpace I x) :
    ⟪0, W⟫_g = 0 := by
  simp only [metric_simp]

/-- The `metric_simp` simp set composes with general `simp` to close
nontrivial algebraic goals. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (V W : TangentSpace I x) :
    ⟪V - 0, -W + W⟫_g = 0 := by
  simp [metric_simp]

end UXTestFoundations
