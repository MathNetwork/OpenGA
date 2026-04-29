import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
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

open scoped ContDiff Manifold Topology

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
the typed-on-tangent-space wrapper.

**Stability**: experimental. Likely to be `@[deprecated]` in v0.2 in
favour of `metricInner` (which uses the typed-on-tangent-space form).
Prefer `metricInner` in new code. -/
noncomputable def metricInnerRaw {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v w : E) : ℝ :=
  g.metricTensor x v w

end RiemannianMetric

/-! ## Phase 4.7.2 — metricInner + algebra lemmas

The `metricInner` operation is the typed-on-tangent-space wrapper around
`RiemannianMetric.metricTensor`. Algebra lemmas (bilinearity, sub, neg, zero,
comm) are derived from the metric tensor's continuous-bilinear-form structure
and the `symm` axiom.

These lemmas replace `inner_add_left/right`, `inner_smul_left/right`,
`real_inner_comm`, etc. (the Mathlib `inner ℝ`-based API) for use in the
framework's Phase 4.7.4+ refactor of koszul identities and downstream
Riemannian/GMT code. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [g : RiemannianMetric I M]

/-- The **metric inner product** at point $x \in M$, treating
$\text{TangentSpace}\ I\ x = E$ via definitional equality.

This is the framework's primary inner product operation on tangent vectors.
Replaces `inner ℝ V W` for `V, W : TangentSpace I x` to bypass the
lean4#13063 typeclass diamond. -/
noncomputable def metricInner (x : M) (V W : TangentSpace I x) : ℝ :=
  g.metricTensor x V W

/-- **Symmetry**: $\langle V, W\rangle_g = \langle W, V\rangle_g$.

Direct from `RiemannianMetric.symm` axiom. -/
theorem metricInner_comm (x : M) (V W : TangentSpace I x) :
    metricInner x V W = metricInner x W V :=
  g.symm x V W

/-- **Positive-definite**: $\langle V, V\rangle_g > 0$ for $V \ne 0$.

Direct from `RiemannianMetric.posdef` axiom. -/
theorem metricInner_self_pos (x : M) (V : TangentSpace I x) (hV : V ≠ 0) :
    0 < metricInner x V V :=
  g.posdef x V hV

/-- **Additivity in left argument**:
$\langle V_1 + V_2, W\rangle_g = \langle V_1, W\rangle_g + \langle V_2, W\rangle_g$.

Proof via `flip` to align outer-CLM bilinear form with `map_add`. -/
theorem metricInner_add_left (x : M) (V₁ V₂ W : TangentSpace I x) :
    metricInner x (V₁ + V₂) W = metricInner x V₁ W + metricInner x V₂ W :=
  ((g.metricTensor x).flip W).map_add V₁ V₂

/-- **Additivity in right argument**:
$\langle V, W_1 + W_2\rangle_g = \langle V, W_1\rangle_g + \langle V, W_2\rangle_g$. -/
theorem metricInner_add_right (x : M) (V W₁ W₂ : TangentSpace I x) :
    metricInner x V (W₁ + W₂) = metricInner x V W₁ + metricInner x V W₂ :=
  (g.metricTensor x V).map_add W₁ W₂

/-- **Scalar mult in left argument**:
$\langle c \cdot V, W\rangle_g = c \cdot \langle V, W\rangle_g$. -/
theorem metricInner_smul_left (x : M) (c : ℝ) (V W : TangentSpace I x) :
    metricInner x (c • V) W = c * metricInner x V W :=
  ((g.metricTensor x).flip W).map_smul c V

/-- **Scalar mult in right argument**:
$\langle V, c \cdot W\rangle_g = c \cdot \langle V, W\rangle_g$. -/
theorem metricInner_smul_right (x : M) (c : ℝ) (V W : TangentSpace I x) :
    metricInner x V (c • W) = c * metricInner x V W :=
  (g.metricTensor x V).map_smul c W

/-- **Zero in left argument**: $\langle 0, W\rangle_g = 0$. -/
@[simp]
theorem metricInner_zero_left (x : M) (W : TangentSpace I x) :
    metricInner x 0 W = 0 :=
  ((g.metricTensor x).flip W).map_zero

/-- **Zero in right argument**: $\langle V, 0\rangle_g = 0$. -/
@[simp]
theorem metricInner_zero_right (x : M) (V : TangentSpace I x) :
    metricInner x V 0 = 0 :=
  (g.metricTensor x V).map_zero

/-- **Negation in left argument**: $\langle -V, W\rangle_g = -\langle V, W\rangle_g$. -/
@[simp]
theorem metricInner_neg_left (x : M) (V W : TangentSpace I x) :
    metricInner x (-V) W = -metricInner x V W :=
  ((g.metricTensor x).flip W).map_neg V

/-- **Negation in right argument**: $\langle V, -W\rangle_g = -\langle V, W\rangle_g$. -/
@[simp]
theorem metricInner_neg_right (x : M) (V W : TangentSpace I x) :
    metricInner x V (-W) = -metricInner x V W :=
  (g.metricTensor x V).map_neg W

/-- **Subtraction in left argument**:
$\langle V_1 - V_2, W\rangle_g = \langle V_1, W\rangle_g - \langle V_2, W\rangle_g$. -/
@[simp]
theorem metricInner_sub_left (x : M) (V₁ V₂ W : TangentSpace I x) :
    metricInner x (V₁ - V₂) W = metricInner x V₁ W - metricInner x V₂ W := by
  rw [sub_eq_add_neg, metricInner_add_left, metricInner_neg_left, sub_eq_add_neg]

/-- **Subtraction in right argument**:
$\langle V, W_1 - W_2\rangle_g = \langle V, W_1\rangle_g - \langle V, W_2\rangle_g$. -/
@[simp]
theorem metricInner_sub_right (x : M) (V W₁ W₂ : TangentSpace I x) :
    metricInner x V (W₁ - W₂) = metricInner x V W₁ - metricInner x V W₂ := by
  rw [sub_eq_add_neg, metricInner_add_right, metricInner_neg_right, sub_eq_add_neg]

/-- **Non-negativity of self-inner**: $\langle V, V\rangle_g \ge 0$.

Combines `metricInner_self_pos` (for $V \ne 0$) with `metricInner_zero_left`
(for $V = 0$). Used by downstream squared-norm primitives
(`manifoldGradientNormSq_nonneg`, `secondFundamentalFormSqNorm_nonneg`). -/
@[simp]
theorem metricInner_self_nonneg (x : M) (V : TangentSpace I x) :
    0 ≤ metricInner x V V := by
  rcases eq_or_ne V 0 with hV | hV
  · rw [hV, metricInner_zero_left]
  · exact le_of_lt (metricInner_self_pos x V hV)

end OpenGALib

/-! ## Phase 4.7.9 — Framework-owned NACG / InnerProductSpace bridges on `TangentSpace`

The framework's analog of Mathlib's bundle-based scoped instances
(`Topology/VectorBundle/Riemannian.lean` lines ~431, 453), provided
**directly from the model space `[NormedAddCommGroup E]` /
`[InnerProductSpace ℝ E]`** rather than going through
`[Bundle.RiemannianBundle ...]` — sidesteps the lean4#13063 typeclass
diamond by using only the single canonical direct-`E` path.

After Phase 4.7.9, the entire framework cascade can drop
`[Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]` — the
`[OpenGALib.RiemannianMetric I M]` typeclass + these bridges suffice
for all downstream `Norm (TangentSpace I x)` /
`InnerProductSpace ℝ (TangentSpace I x)` synthesis.

Mathlib's `TangentSpace` is declared non-reducible (line 1037 of
`IsManifold/Basic.lean`: "not reducible so that type class inference
does not pick wrong instances"), so we use
`set_option backward.isDefEq.respectTransparency false` to make
typeclass synthesis see through the `TangentSpace I x = E` defeq —
matching Mathlib's own pattern (e.g.,
`Topology/VectorBundle/Riemannian.lean` line ~98 for the trivial
bundle Riemannian instance). -/

namespace OpenGALib

section NACGBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
/-- **Framework-owned NACG bridge** on `TangentSpace I x`, directly
from `[NormedAddCommGroup E]`. Replaces
`Riemannian.InnerProductBridge.instNormedAddCommGroupTangentSpace`
(Phase 1.6, RiemannianBundle-based) with a framework-self-built path
that doesn't require `[Bundle.RiemannianBundle ...]`. -/
instance instNormedAddCommGroupTangent (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

end NACGBridge

section InnerProductBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
/-- **Framework-owned InnerProductSpace bridge** on `TangentSpace I x`,
directly from `[InnerProductSpace ℝ E]`. Replaces
`Riemannian.InnerProductBridge.instInnerProductSpaceTangentSpace`
(Phase 1.6, RiemannianBundle-based). -/
instance instInnerProductSpaceTangent (x : M) :
    InnerProductSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (InnerProductSpace ℝ E)

end InnerProductBridge

section FiniteDimensionalBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
/-- **Framework-owned FiniteDimensional bridge** on `TangentSpace I x`,
directly from `[FiniteDimensional ℝ E]`. Replaces
`Riemannian.InnerProductBridge.instFiniteDimensionalTangentSpace`. -/
instance instFiniteDimensionalTangent [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

set_option backward.isDefEq.respectTransparency false in
/-- **Framework-owned CompleteSpace bridge** on `TangentSpace I x`,
directly from `[CompleteSpace E]`. Replaces
`Riemannian.InnerProductBridge.instCompleteSpaceTangentSpace`. -/
instance instCompleteSpaceTangent [CompleteSpace E] (x : M) :
    CompleteSpace (TangentSpace I x) :=
  inferInstanceAs (CompleteSpace E)

end FiniteDimensionalBridge

end OpenGALib

/-! ## Phase 4.7.8.A — `metricInner` smoothness helper (`MDifferentiableAt`)

The framework's analog of Mathlib's `MDifferentiableAt.inner_bundle`
(`Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`), but using
the framework-owned `metricInner` (Phase 4.7.2) rather than going
through `[IsContMDiffRiemannianBundle]` — sidesteps the lean4#13063
typeclass diamond per the Phase 4.7 redesign.

Used by Phase 4.7.8.A to derive the scalar smoothness hypotheses of
`koszul_smul_right` and `koszul_add_right` (`Riemannian.Connection`,
`hYZ`, `hZX`, `h_YZ₁`, `h_YZ₂`, `h_Z₁X`, `h_Z₂X`) from vector-field
bundle-section smoothness — required for the `TensorialAt` instance on
`Z ↦ koszulFunctional X Y Z x` that closes the
`koszulLinearFunctional_exists` body.

**Mathematical content**: $y \mapsto g_y(Y(y), Z(y))$ is $C^\infty$ at
$x$ when $g$ (the metric tensor) is $C^\infty$ in $y$ (Phase 4.7.1
axiom `RiemannianMetric.smoothMetric`) and $Y, Z$ are smooth bundle
sections. Proof structure: chart-bridge via the trivialization
`e := trivializationAt E (TangentSpace I) x`, with the round-trip
identity `e.symmL ℝ y (e.continuousLinearMapAt ℝ y v) = v` for
$y \in e.\mathrm{baseSet}$. Steps 1-3 close (mdifferentiableAt_totalSpace
extracts plain `M → E` smoothness of `(e ⟨y, Y y⟩).2`,
`g.smoothMetric.mdifferentiableAt` provides metric tensor smoothness).

**Sorry status (Step 4)**: PRE-PAPER, structural blocker. The remaining
piece is `MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E) (fun y => e.symmL ℝ y) x`,
i.e., smoothness of the trivialization inverse as a CLM-valued function
of the basepoint. Mathlib provides:
* `TangentBundle.symmL_trivializationAt` — `e.symmL ℝ y =
  mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)` for y in
  chart source (decorated with `set_option backward.isDefEq.respectTransparency
  false` to bridge `E →L[ℝ] TangentSpace I y` vs `E →L[ℝ] E`).
* `ContMDiffVectorBundle.contMDiffOn_coordChangeL` — smoothness of CLM
  changes between two trivializations (flat codomain `F →L F`).
* `ContMDiffAt.mfderiv_const` — smoothness of the in-coordinates
  pullback of `mfderiv f`, again with flat codomain via `inCoordinates`.

The blocker: `e.symmL ℝ y` has dependent codomain `E →L[ℝ] TangentSpace I y`,
incompatible with the `MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)` model
(non-dependent codomain `E →L[ℝ] E`). Even with
`set_option backward.isDefEq.respectTransparency false` in scope, the
higher-order Pi-vs-flat unification problem `(y : M) → (E →L[ℝ] T y)`
vs `M → (E →L[ℝ] E)` (where `T y = E` def-eq) is not resolved
automatically by Lean's elaborator — the `→L[ℝ]` constructor demands
syntactic equality of the codomain type.

**Repair plan** (Phase 4.8 architectural follow-up):
1. **Option A** (recommended): change the typeclass field
   `RiemannianMetric.smoothMetric` from plain `M → CLM(E,E,ℝ)`
   smoothness to bundle-section smoothness in the Hom-bundle of
   `TangentSpace I`, matching Mathlib's `ContMDiffRiemannianMetric.contMDiff`.
   Then `clm_bundle_apply₂` directly closes this lemma. Requires
   updating users of `g.smoothMetric` (currently used only by this
   helper).
2. **Option B**: add a Mathlib-upstream lemma giving non-dependent
   smoothness of `Trivialization.symmL` for tangent bundles via
   `inCoordinates` form. This may already exist as
   `MDifferentiableAt.clm_apply_of_inCoordinates` composition; framework
   self-build of the helper is ~80 LOC.
3. **Option C**: change `Y, Z` hypothesis form throughout the framework
   from bundle-section to plain `M → E` smoothness (via def-eq abuse).
   Requires propagating refactor through `koszul_*` identities + their
   callers in `koszulFunctional_tensorialAt` / `koszulLinearFunctional_exists`.

Phase 4.7.5.C (this file) commits the proof structure with Step 4
extracted as the narrow structural axiom `tangentBundle_symmL_smoothAt`
below. Closure of the axiom scheduled as Phase 4.8 strategic decision item. -/

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [g : RiemannianMetric I M]

/-- **Narrow structural axiom**: smoothness of the tangent bundle
trivialization inverse `Trivialization.symmL`, as a CLM-valued function
of the basepoint, viewed in non-dependent codomain via the
`TangentSpace I y = E` def-eq cast.

**Mathematical content**: for the tangent bundle's preferred trivialization
$e := \mathrm{trivializationAt}\,E\,(TangentSpace\,I)\,x$, the function
$y \mapsto e.\mathrm{symmL}\,\mathbb{R}\,y$ is $C^\infty$ at $x$ as a map
$M \to (E \to_L^{\mathbb{R}} E)$. This is mathematically the smoothness
of the inverse chart-derivative, equivalent (via Mathlib's
`TangentBundle.symmL_trivializationAt`) to smoothness of
$y \mapsto \mathrm{mfderivWithin}\,(\mathrm{range}\,I)\,(\mathrm{extChartAt}\,I\,x).\mathrm{symm}\,(\mathrm{extChartAt}\,I\,x\,y)$.

**Why an axiom**: the dependent codomain `E →L[ℝ] TangentSpace I y` of
`e.symmL ℝ y` is incompatible with the non-dependent
`MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)` model expected. Even with
`set_option backward.isDefEq.respectTransparency false`, Lean's
elaborator cannot resolve the higher-order Pi-vs-flat unification
problem. The proof requires either:
* Mathlib upstream addition of `Trivialization.symmL` smoothness in
  non-dependent flat-CLM form (`F →L F` via the trivialization's own
  baseSet), OR
* Framework typeclass redesign making `RiemannianMetric.smoothMetric`
  use bundle-section smoothness in the Hom-bundle (then
  `clm_bundle_apply₂` handles the chart-bridge internally).

**Repair plan**: Phase 4.8 architectural follow-up. The axiom will be
discharged either as a Mathlib upstream PR or via the framework's
typeclass redesign (the latter requires cascade of topology-instance
synthesis fixes for the Hom-bundle's TotalSpace, which is out of
Phase 4.7 scope).

**Ground truth**: standard for tangent bundles — chart-derivatives
and their inverses are smooth as part of the smooth-manifold structure.
The non-dependent CLM-valued formulation is the only barrier. -/
axiom tangentBundle_symmL_smoothAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (h_TS_E_eq : ∀ y : M, (E →L[ℝ] TangentSpace I y) = (E →L[ℝ] E)) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => cast (h_TS_E_eq y)
        ((trivializationAt E (TangentSpace I) x).symmL ℝ y)) x

/-- **Smoothness of the metric inner product** as a scalar function of
the basepoint, given smooth bundle sections.

For smooth tangent-bundle sections $Y, Z$ at $x$, the scalar function
$y \mapsto \langle Y(y), Z(y)\rangle_g$ is $C^\infty$ at $x$. -/
theorem MDifferentiableAt.metricInner_smoothAt
    {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Z y⟩ : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x := by
  -- Set up the trivialization at x.
  set e := trivializationAt E (TangentSpace I) x with he_def
  -- Step 1: Extract chart-pulled-back fiber smoothness from bundle smoothness.
  rw [mdifferentiableAt_totalSpace] at hY hZ
  have hY' : MDifferentiableAt I 𝓘(ℝ, E) (fun y => (e ⟨y, Y y⟩).2) x := hY.2
  have hZ' : MDifferentiableAt I 𝓘(ℝ, E) (fun y => (e ⟨y, Z y⟩).2) x := hZ.2
  -- Step 2: g.metricTensor smooth as M → CLM.
  have hg : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) g.metricTensor x :=
    (g.smoothMetric x).mdifferentiableAt (by decide)
  -- Step 3: e.symmL smoothness as a CLM-valued function of y.
  -- For tangent bundle, `e.symmL ℝ y = mfderivWithin (range I) (extChartAt I x).symm (extChartAt I x y)`
  -- via `TangentBundle.symmL_trivializationAt`. The mfderiv of a smooth chart inverse is smooth.
  have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have h_baseSet : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds hx_chart
  -- e.symmL is smooth M → (E →L[ℝ] E) (= E →L[ℝ] TangentSpace I _ via def-eq).
  -- Use set_option to make def-eq transparent.
  -- For tangent bundle: e.symmL ℝ y = mfderivWithin (range I) (extChartAt I x).symm
  -- (extChartAt I x y), the mfderiv of the smooth chart inverse — smooth in y.
  -- Cast via type-equality (provable as rfl under transparency).
  set_option backward.isDefEq.respectTransparency false in
  have h_TS_E_eq : ∀ y : M, (E →L[ℝ] TangentSpace I y) = (E →L[ℝ] E) :=
    fun _ => rfl
  -- Step 3 closure via narrow structural axiom `tangentBundle_symmL_smoothAt`
  -- (file-level, with detailed Phase 4.8 repair plan in its docstring).
  set_option backward.isDefEq.respectTransparency false in
  have h_symmL : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => cast (h_TS_E_eq y) (e.symmL ℝ y)) x :=
    tangentBundle_symmL_smoothAt x h_TS_E_eq
  -- Step 4: Build the composed smooth function.
  set_option backward.isDefEq.respectTransparency false in
  have h_compY : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => (e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Y y⟩).2)) x :=
    h_symmL.clm_apply hY'
  set_option backward.isDefEq.respectTransparency false in
  have h_compZ : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => (e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Z y⟩).2)) x :=
    h_symmL.clm_apply hZ'
  set_option backward.isDefEq.respectTransparency false in
  have h_smooth : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => g.metricTensor y
        ((e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Y y⟩).2))
        ((e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Z y⟩).2))) x :=
    (hg.clm_apply h_compY).clm_apply h_compZ
  -- Step 5: Bridge to goal via eventuallyEq on e.baseSet.
  apply h_smooth.congr_of_eventuallyEq
  have h_baseSet_e : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  filter_upwards [h_baseSet_e] with y hy
  set_option backward.isDefEq.respectTransparency false in
  have hY_inv : (e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Y y⟩).2) = (Y y : E) := by
    have h_round := Bundle.Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (e := e) hy (Y y)
    -- (e ⟨y, Y y⟩).2 = e.continuousLinearMapAt ℝ y (Y y) for y ∈ baseSet.
    have h_eq : (e ⟨y, Y y⟩).2 = e.continuousLinearMapAt ℝ y (Y y) := by
      have := Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ) e hy
      exact (congrFun this (Y y)).symm
    rw [h_eq]
    exact h_round
  set_option backward.isDefEq.respectTransparency false in
  have hZ_inv : (e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Z y⟩).2) = (Z y : E) := by
    have h_round := Bundle.Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (e := e) hy (Z y)
    have h_eq : (e ⟨y, Z y⟩).2 = e.continuousLinearMapAt ℝ y (Z y) := by
      have := Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ) e hy
      exact (congrFun this (Z y)).symm
    rw [h_eq]
    exact h_round
  -- Goal: metricInner y (Y y) (Z y) = g.metricTensor y (symmL_y Y') (symmL_y Z')
  -- After rewrite via .symm direction: replaces (Y y) with (symmL_y Y'), (Z y) with (symmL_y Z')
  -- in metricInner = g.metricTensor (def-eq), then rfl.
  set_option backward.isDefEq.respectTransparency false in
  show metricInner y (Y y) (Z y) =
      g.metricTensor y
        ((e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Y y⟩).2))
        ((e.symmL ℝ y : E →L[ℝ] E) ((e ⟨y, Z y⟩).2))
  rw [hY_inv, hZ_inv]
  rfl

end OpenGALib

/-! ## Phase 4.7.3 — Framework-owned Riesz extraction

Build out the Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)` via the metric
tensor's positive-definiteness + finite-dim invertibility, providing the
framework's replacement for Mathlib's `(InnerProductSpace.toDual ℝ _).symm`. -/

namespace OpenGALib

section RieszExtraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [g : RiemannianMetric I M]

/-- **Forward Riesz**: vector → linear functional via metric. -/
noncomputable def metricToDual (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.metricTensor x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricToDual_apply (x : M) (v w : TangentSpace I x) :
    metricToDual (g := g) x v w = metricInner x v w :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Injectivity of forward Riesz**: from positive-definiteness. -/
theorem metricToDual_injective (x : M) :
    Function.Injective (metricToDual (g := g) x) := by
  intro v₁ v₂ h
  by_contra hne
  have hsub : v₁ - v₂ ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < metricInner x (v₁ - v₂) (v₁ - v₂) :=
    metricInner_self_pos x _ hsub
  have key : ∀ w, metricInner x v₁ w = metricInner x v₂ w := by
    intro w
    exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) h
  have hzero : metricInner x (v₁ - v₂) (v₁ - v₂) = 0 := by
    rw [metricInner_sub_left, key (v₁ - v₂), sub_self]
  linarith

omit [FiniteDimensional ℝ E] in
/-- **Vector equality via inner-product equality** (non-degeneracy).

Two tangent vectors at $x$ are equal iff their inner products with all
test vectors agree. Direct corollary of `metricToDual_injective` —
the injectivity of the forward Riesz map turns "Riesz functionals
agree" into "vectors agree".

Used by Phase 4.7.8.B to reduce vector identities (e.g., torsion-free,
metric-compat formulas at the level of Levi-Civita output vectors) to
inner-product identities (which are then discharged via the koszul
identities + `koszulCovDeriv_inner_eq`). -/
theorem metricInner_eq_iff_eq (x : M) (v w : TangentSpace I x) :
    (∀ Z : TangentSpace I x, metricInner x v Z = metricInner x w Z) ↔ v = w := by
  refine ⟨fun h => ?_, fun h _ => by rw [h]⟩
  apply metricToDual_injective x
  ext Z
  simpa [metricToDual_apply] using h Z

omit g in
/-- finrank of `TangentSpace I x →L[ℝ] ℝ` equals finrank of `TangentSpace I x`. -/
private theorem finrank_clm_dual_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x →L[ℝ] ℝ) =
      Module.finrank ℝ (TangentSpace I x) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  rw [← LinearEquiv.finrank_eq
    (LinearMap.toContinuousLinearMap : (TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _)]
  exact Subspace.dual_finrank_eq

/-- **Bijectivity of forward Riesz**: injective + same `finrank` ⇒ bijective. -/
theorem metricToDual_bijective (x : M) :
    Function.Bijective (metricToDual (g := g) x) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  haveI : FiniteDimensional ℝ (TangentSpace I x →L[ℝ] ℝ) :=
    Module.Finite.equiv (LinearMap.toContinuousLinearMap :
      (TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ))
  refine ⟨metricToDual_injective x, ?_⟩
  have h_finrank := finrank_clm_dual_eq (I := I) (M := M) x
  have hiff := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (metricToDual (g := g) x).toLinearMap) h_finrank.symm
  exact hiff.mp (metricToDual_injective (g := g) x)

/-- The Riesz isomorphism as a `LinearEquiv`. -/
noncomputable def metricToDualEquiv (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.ofBijective (metricToDual (g := g) x).toLinearMap
    (metricToDual_bijective (g := g) x)

/-- **Inverse Riesz**: linear functional → vector via metric. -/
noncomputable def metricRiesz (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x :=
  (metricToDualEquiv (g := g) x).symm φ

/-- **Riesz defining property**: $\langle \text{metricRiesz}\,\varphi, V\rangle_g
= \varphi(V)$. -/
theorem metricRiesz_inner (x : M) (φ : TangentSpace I x →L[ℝ] ℝ)
    (V : TangentSpace I x) :
    metricInner x (metricRiesz (g := g) x φ) V = φ V := by
  show metricToDual (g := g) x (metricRiesz (g := g) x φ) V = φ V
  have heq : (metricToDual (g := g) x).toLinearMap
      ((metricToDualEquiv (g := g) x).symm φ) = φ :=
    (metricToDualEquiv (g := g) x).apply_symm_apply φ
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f V) heq

/-- **Riesz uniqueness**: if `v` represents `φ`, then `v = metricRiesz x φ`. -/
theorem metricRiesz_unique (x : M) (v : TangentSpace I x)
    (φ : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ w, metricInner x v w = φ w) :
    v = metricRiesz (g := g) x φ := by
  apply metricToDual_injective (g := g) x
  ext w
  rw [metricToDual_apply, h w]
  show φ w = metricToDual (g := g) x (metricRiesz (g := g) x φ) w
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w)
    ((metricToDualEquiv (g := g) x).apply_symm_apply φ).symm

end RieszExtraction

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

/-! ## Phase 4.7.2 self-tests: metricInner + algebra lemmas -/

/-- Combined linearity self-test: bilinearity of metricInner. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (a b : ℝ) (V₁ V₂ W : TangentSpace I x) :
    metricInner x (a • V₁ + b • V₂) W = a * metricInner x V₁ W + b * metricInner x V₂ W := by
  rw [metricInner_add_left, metricInner_smul_left, metricInner_smul_left]

/-- Self-test: combine `metricInner_comm` + `metricInner_add_right`. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (V W₁ W₂ : TangentSpace I x) :
    metricInner x (W₁ + W₂) V = metricInner x W₁ V + metricInner x W₂ V := by
  rw [metricInner_comm x (W₁ + W₂) V, metricInner_add_right,
      metricInner_comm x V W₁, metricInner_comm x V W₂]

/-- Self-test: subtraction lemma. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (V₁ V₂ W : TangentSpace I x) :
    metricInner x (V₁ - V₂) W = metricInner x V₁ W - metricInner x V₂ W :=
  metricInner_sub_left x V₁ V₂ W

/-! ## Phase 4.7.3 self-tests: metricRiesz construction -/

/-- Self-test: `metricToDual` injective. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) :
    Function.Injective (metricToDual (g := g) x) :=
  metricToDual_injective x

/-- Self-test: `metricRiesz` defining property. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (φ : TangentSpace I x →L[ℝ] ℝ)
    (V : TangentSpace I x) :
    metricInner x (metricRiesz (g := g) x φ) V = φ V :=
  metricRiesz_inner x φ V

/-- Self-test: `metricRiesz` uniqueness. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v : TangentSpace I x)
    (φ : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ w, metricInner x v w = φ w) :
    v = metricRiesz (g := g) x φ :=
  metricRiesz_unique x v φ h

end SelfTest
