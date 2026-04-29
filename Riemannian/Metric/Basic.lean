import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# RiemannianMetric — typeclass + inner product API + tangent-space bridges

Defines the `RiemannianMetric` typeclass (smooth, symmetric,
positive-definite metric tensor) along with its primary inner product
operation `metricInner` and the algebra lemmas that form the framework
analog of Mathlib's `inner_*` API.

Also provides `NormedAddCommGroup`, `InnerProductSpace ℝ`,
`FiniteDimensional ℝ`, and `CompleteSpace` instances on `TangentSpace I x`
directly from the model space's instances on `E` via the
`TangentSpace I x = E` def-eq, sidestepping the lean4#13063 typeclass
diamond.

**Ground truth**: do Carmo 1992 §1.2; Lee *Smooth Manifolds* Ch. 13.
-/

open scoped ContDiff Manifold Topology

namespace OpenGALib

/-- **Riemannian metric typeclass**: a smooth, symmetric,
positive-definite metric tensor on a manifold $M$ modeled on $E$.

The metric is accessed via the explicit `metricTensor` field. The
fiber's `NormedAddCommGroup` / `InnerProductSpace` structure (when needed
downstream) goes through the direct $E$-path via `TangentSpace I x = E`
def-eq. -/
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
function. Use `metricInner` (typed-on-tangent-space form) in new code;
this raw form is a `@[deprecated]` candidate for v0.2. -/
noncomputable def metricInnerRaw {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [g : RiemannianMetric I M] (x : M) (v w : E) : ℝ :=
  g.metricTensor x v w

end RiemannianMetric

/-! ## `metricInner` + algebra lemmas

The `metricInner` operation is the typed-on-tangent-space wrapper around
`RiemannianMetric.metricTensor`. Algebra lemmas (bilinearity, sub, neg, zero,
comm) are derived from the metric tensor's continuous-bilinear-form
structure and the `symm` axiom. These lemmas form the framework analog of
Mathlib's `inner_add_left/right`, `inner_smul_left/right`, `real_inner_comm`
for use on tangent vectors. -/

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

/-! ## NACG / InnerProductSpace bridges on `TangentSpace`

Provides `NormedAddCommGroup`, `InnerProductSpace ℝ`,
`FiniteDimensional ℝ`, and `CompleteSpace` instances on `TangentSpace I x`
directly from the model space's instances on `E`, via the
`TangentSpace I x = E` def-eq.

`set_option backward.isDefEq.respectTransparency false` makes typeclass
synthesis see through the def-eq (Mathlib's `TangentSpace` is
non-reducible to prevent wrong-instance selection); this matches
Mathlib's own pattern in `Topology/VectorBundle/Riemannian.lean`. -/

namespace OpenGALib

section NACGBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
/-- `NormedAddCommGroup` on `TangentSpace I x`, directly from
`[NormedAddCommGroup E]` via `TangentSpace I x = E` def-eq. -/
instance instNormedAddCommGroupTangent (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

end NACGBridge

section InnerProductBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
/-- `InnerProductSpace ℝ` on `TangentSpace I x`, directly from
`[InnerProductSpace ℝ E]` via `TangentSpace I x = E` def-eq. -/
instance instInnerProductSpaceTangent (x : M) :
    InnerProductSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (InnerProductSpace ℝ E)

end InnerProductBridge

section FiniteDimensionalBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
/-- `FiniteDimensional ℝ` on `TangentSpace I x`, directly from
`[FiniteDimensional ℝ E]` via `TangentSpace I x = E` def-eq. -/
instance instFiniteDimensionalTangent [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

set_option backward.isDefEq.respectTransparency false in
/-- `CompleteSpace` on `TangentSpace I x`, directly from `[CompleteSpace E]`
via `TangentSpace I x = E` def-eq. -/
instance instCompleteSpaceTangent [CompleteSpace E] (x : M) :
    CompleteSpace (TangentSpace I x) :=
  inferInstanceAs (CompleteSpace E)

end FiniteDimensionalBridge

end OpenGALib
