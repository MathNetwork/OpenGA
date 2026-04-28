import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# OpenGALib.RiemannianMetric — Framework-Owned Riemannian Metric Typeclass

This file provides `OpenGALib.RiemannianMetric I M`, a framework-owned
typeclass capturing a Riemannian metric on the manifold $M$ with model
$I : \text{ModelWithCorners}\ \mathbb{R}\ E\ H$.

## Why this typeclass exists

Phase 4.7's architectural redesign (per `docs/PHASE_4_7_REDESIGN_PLAN.md`)
introduces this typeclass as the framework's **single canonical path** for
inner product structure on `TangentSpace I x`, replacing the lean4#13063
typeclass diamond between Mathlib's `Bundle.RiemannianBundle`-derived
`InnerProductSpace ℝ (TangentSpace I y)` and the direct
`[NormedAddCommGroup E]` path via `TangentSpace I x = E` defeq.

Mathlib's own `Topology/VectorBundle/Riemannian.lean:439-440` explicitly
references lean4#13063, deliberately ordering its instance parameters to
work around the loop. The framework's redesign sidesteps the Mathlib
synthesis path entirely by providing the metric via this **explicit
operation-based typeclass** rather than via `Inner ℝ (TangentSpace I y)`
synthesis.

## Design

The typeclass holds:
* `metricTensor : (x : M) → E →L[ℝ] E →L[ℝ] ℝ` — the metric tensor at each
  point as a continuous bilinear form on the model space $E$. By
  definitional equality `TangentSpace I x = E`, this acts on tangent vectors.
* `symm` — the metric is symmetric: $g_x(v, w) = g_x(w, v)$.
* `posdef` — the metric is positive-definite: $g_x(v, v) > 0$ for $v \ne 0$.
* `smoothMetric` — the metric tensor is a smooth section of the bundle
  $\text{Hom}(TM \otimes TM, \mathbb{R})$, viewed as a smooth map
  $M \to (E \to_L^{\mathbb{R}} E \to_L^{\mathbb{R}} \mathbb{R})$.

Downstream operations (`metricInner`, `metricRiesz`, `metricInner_*`
algebra lemmas) build on these axioms to provide the framework's complete
inner product API on tangent spaces, replacing
`MDifferentiableAt.inner_bundle` and `InnerProductSpace.toDual.symm` with
framework-owned analogs that use the single canonical path.

## Phase ordering

* **Phase 4.7.1** (this file): typeclass declaration + axioms.
* **Phase 4.7.2**: `metricInner` operation + algebra properties
  (symm, posdef, bilinear).
* **Phase 4.7.3**: `metricRiesz` — framework-owned Riesz isomorphism
  `(T_xM →L[ℝ] ℝ) → T_xM` using metric tensor's positive-definiteness.
* **Phase 4.7.4–4.7.7**: refactor `Connection.lean`, downstream Riemannian,
  GMT, Regularity, AltRegularity to use this typeclass.
* **Phase 4.7.8**: close `koszulLinearFunctional_exists` +
  `leviCivitaConnection_exists` axioms.
* **Phase 4.7.9**: cleanup — sunset `InnerProductBridge.lean`.

**Ground truth**: do Carmo 1992 §1.2 (Riemannian metric definition);
Lee *Smooth Manifolds* Ch. 13 (Riemannian metrics as smooth bilinear sections).
-/

open scoped ContDiff Manifold

namespace OpenGALib

/-- **Framework-owned Riemannian metric typeclass.**

A `RiemannianMetric I M` instance equips the manifold $M$ (with model
$I : \text{ModelWithCorners}\ \mathbb{R}\ E\ H$) with a smooth, symmetric,
positive-definite metric tensor.

By design, this typeclass does **not** synthesize
`InnerProductSpace ℝ (TangentSpace I x)` as a derived instance — the
metric is accessed via the explicit `metricTensor` field, avoiding the
lean4#13063 typeclass diamond. The fiber's `NormedAddCommGroup` /
`InnerProductSpace` structure (when needed downstream) goes through the
single canonical direct $E$-path via `TangentSpace I x = E` defeq. -/
class RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  /-- The metric tensor at each point: a continuous bilinear form
  $g_x : E \times E \to \mathbb{R}$. By `TangentSpace I x = E` defeq,
  this acts on tangent vectors. -/
  metricTensor : (x : M) → E →L[ℝ] E →L[ℝ] ℝ
  /-- The metric tensor is symmetric: $g_x(v, w) = g_x(w, v)$. -/
  symm : ∀ (x : M) (v w : E), metricTensor x v w = metricTensor x w v
  /-- The metric tensor is positive-definite: $g_x(v, v) > 0$ for $v \ne 0$. -/
  posdef : ∀ (x : M) (v : E), v ≠ 0 → 0 < metricTensor x v v
  /-- The metric tensor is a smooth section, i.e., a smooth map
  $M \to (E \to_L^{\mathbb{R}} E \to_L^{\mathbb{R}} \mathbb{R})$. -/
  smoothMetric : ContMDiff I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ metricTensor

namespace RiemannianMetric

/-- Convenience accessor: the metric inner product as a `(x : M) → E → E → ℝ`
function. The framework's downstream `metricInner` (Phase 4.7.2) provides
the typed-on-tangent-space wrapper. -/
noncomputable def metricInnerRaw {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v w : E) : ℝ :=
  g.metricTensor x v w

end RiemannianMetric

end OpenGALib

/-! ## Phase 4.7.1 self-test: typeclass synthesizes + accessors resolve -/

section SelfTest

open OpenGALib

/-- Self-test: typeclass instance argument is accepted and `metricTensor`
field is accessible. Verifies typeclass declaration parses cleanly. -/
noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v : E) :
    ℝ := g.metricTensor x v v

/-- Self-test: `symm` axiom usable. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v w : E) :
    g.metricTensor x v w = g.metricTensor x w v :=
  g.symm x v w

/-- Self-test: `posdef` axiom usable. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v : E) (hv : v ≠ 0) :
    0 < g.metricTensor x v v :=
  g.posdef x v hv

/-- Self-test: `metricInnerRaw` accessor resolves with explicit instance threading. -/
noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianMetric I M] (x : M) (v w : E) :
    ℝ := RiemannianMetric.metricInnerRaw (I := I) x v w

/-- Self-test: `smoothMetric` field is accessible. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ g.metricTensor :=
  g.smoothMetric

end SelfTest
