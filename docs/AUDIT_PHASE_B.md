# Phase B Audit (post-port)

Recorded: 2026-05-09. Snapshot after Phase A (external port) close-out,
before Phase C (substantive consolidation).

## Scope

Audit of the relationship between Phase A ported content and pre-port lib
core (Algebraic / Riemannian / GeometricMeasureTheory).

## Method

For each ported file, scan the entire pre-port lib for:

1. `import` of the ported module.
2. Reference to any public identifier defined in the ported module.

A pre-port file is identified as a "consumer" if either holds.

## Finding 1 — All ported content is isolated

**Zero pre-port files import or reference any ported public identifier.**

Tested identifiers include `compContinuousLinearMapL_diag`,
`MultilinearSection`, `ContinuousAlternatingMap.tensorProductMap`, `Wedge`,
`DifferentialForm`, `hessian`, `laplacian`, `TensorProduct.mapL`,
`Tensor0SBundle`, `TensorRSSpace`, `multiKroneckerDelta`,
`shuffleLeftRestrict`. All return zero matches.

The ported content forms a self-contained algebraic layer detached from the
analytical core (`GMT/Variation`, `GMT/Stable`, `GMT/Stationary`,
`GMT/FlatDistance`, `Riemannian/Connection`, `Riemannian/Curvature`,
`Riemannian/Gradient`, `Riemannian/Operators` — none consume the new content).

## Finding 2 — Architectural silos

* `DifferentialForm` is in `NormedSpace ℝ E` layer (normed-space differential
  forms). **Not yet on manifold**. The transition to manifold-valued forms is
  a planned bridge.
* `Operators/Hessian.hessian` is well-formed (composes `covDeriv` +
  `manifoldGradient` + `metricInner`) but has no caller.
* `Operators/Hessian.Bilin` is an abstract carrier — no concrete
  client constructs a `B : Bilin` from chart-Christoffel.
* `Riemannian/Tensor/Defs` provides `(0,s)` and `(r,s)` tensor bundle types.
  Not consumed by `Riemannian.riemannCurvature` / `Riemannian.ricci` (they
  use vector-field-input form, not tensor sections).

## Finding 3 — Naming inconsistencies

Style mismatches between definitions / theorems within the same namespace
(e.g. `continuousMultilinearMap_basis` mixing snake-case-with-camelcase in
ported code). Resolved during Phase C tier 2 by `docs/NAMING_CONVENTION.md`
(camelCase for definitions, `_`-separated theorem suffixes per Mathlib).
Files refactored so far: `Riemannian/Curvature.lean`, `Riemannian/Gradient.lean`,
`Riemannian/Operators/{Hessian, Laplacian}.lean`.

Namespace structure: `OpenGALib.Tensor.Multilinear.X` parallels
`OpenGALib.Riemannian.Tensor.X`. Decide whether `Tensor` should always
be top-level or always nested (deferred).

## Finding 4 — Silver lining: Mathlib upstream candidates

The 100% isolation of ported content **is a feature, not a bug** for
upstream PR purposes. Each sub-module (`Tensor/Multilinear`,
`Tensor/Alternating`, `Tensor/Product`, `Tensor/DifferentialForm`,
`Algebraic/Auxiliary/{Fin, Perm, MultiKronecker, Shuffle*}`) is:

* Mathematically self-contained.
* Conforming to Mathlib naming / docstring conventions (broadly).
* Free of paper-domain or framework-specific machinery.

This means the ported layer is **naturally PR-able** without untangling
dependencies. We do not currently target upstream PR (per
`feedback_no_mathlib_pr.md`), but the optionality is preserved.

## Repair plans

### Plan 1 — Bridge `Riemannian.Curvature` to `Riemannian/Tensor/Defs`

**Trigger**: `riemannCurvature` users want tensor-section view.

**Mechanism**: Show `riemannCurvature` is `C^∞(M)`-linear in each argument
(the tensoriality theorem; do Carmo §4 Proposition 2.6); package as a
section of the `(1,3)`-tensor bundle from `Riemannian/Tensor/Defs`.

**Cost**: Substantive — tensoriality proof requires Levi-Civita linearity
+ bracket identities. Multi-week.

### Plan 2 — Bridge `Operators/Hessian` to `HessianLie`

**Trigger**: `hessian` symmetry needed by a downstream consumer.

**Mechanism**: Use `mfderiv_iterate_sub_eq_mlieBracket_apply`
(`HessianLie.lean`) to derive `hessian f X Y = hessian f Y X`
when `X, Y` are smooth vector fields and `f` is `C^2`.

**Cost**: Single-file work. Defer until consumer surfaces.

### Plan 3 — Manifold-valued `DifferentialForm`

**Trigger**: Stokes' theorem / de Rham work needs forms on a manifold.

**Mechanism**: Lift `DifferentialForm n E F` (normed-space layer) to
sections of `Bundle.continuousAlternatingMap 𝕜 (Fin n) F (TangentSpace I)
F (Bundle.Trivial M F)`.

**Cost**: Substantive but mostly mechanical (the Alternating bundle is
already ported; this is glue).

## Phase C tier proposal

* **Tier 1** (current commit): documentation + facade + audit notation.
  Low risk, preparation for v0.1-style stable lib.
* **Tier 2**: naming consolidation + `@[simp]` / `@[ext]` audit. Medium risk
  — every signature change is a churn point.
* **Tier 3**: substantive bridges (Plans 1, 2, 3). Requires consumer
  pull. High value when triggered, otherwise speculative.

We default to Tier 1 + selective Tier 2 work; Tier 3 is consumer-driven.
