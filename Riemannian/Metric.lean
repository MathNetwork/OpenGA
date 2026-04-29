import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# RiemannianMetric — framework-owned Riemannian metric typeclass

A Riemannian metric on a manifold $M$ modeled on $E$, given by a smooth,
symmetric, positive-definite tensor $g_x : E \times E \to \mathbb{R}$
acting on tangent vectors via `TangentSpace I x = E` def-eq.

This typeclass provides the metric via an explicit `metricTensor` field
rather than synthesising `Inner ℝ (TangentSpace I x)`, sidestepping the
lean4#13063 typeclass diamond between Mathlib's `Bundle.RiemannianBundle`
and the direct `[InnerProductSpace ℝ E]` path. Downstream operations
(`metricInner`, `metricRiesz`, algebra lemmas) provide the inner product
API on tangent vectors.

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

/-! ## `metricInner` smoothness helper

Framework analog of Mathlib's `MDifferentiableAt.inner_bundle`, using the
framework-owned `metricInner` instead of `[IsContMDiffRiemannianBundle]`.
Used by `koszul_smul_right` / `koszul_add_right` to derive scalar
smoothness of $\langle Y, Z \rangle_g$ from bundle-section smoothness of
$Y, Z$.

Proof: chart-bridge via the trivialization
`e := trivializationAt E (TangentSpace I) x`, using the round-trip
identity `e.symmL ℝ y (e.continuousLinearMapAt ℝ y v) = v` on
`e.baseSet`. The `e.symmL` smoothness step is extracted as the narrow
structural axiom `tangentBundle_symmL_smoothAt` (see `AXIOM_STATUS.md`
for repair plan). -/

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [g : RiemannianMetric I M]

/-- **Smoothness of the tangent-bundle trivialization inverse `symmL`**,
as a CLM-valued function of the basepoint, in non-dependent codomain via
the `TangentSpace I y = E` def-eq cast.

For `e := trivializationAt E (TangentSpace I) x`, the function
$y \mapsto e.\mathrm{symmL}\,\mathbb{R}\,y$ is $C^\infty$ at $x$ as a map
$M \to (E \to_L^{\mathbb{R}} E)$. Mathematically this is the smoothness
of the inverse chart-derivative, standard for tangent bundles.

This is an axiom because Mathlib's `Trivialization.symmL` has the
dependent codomain `E →L[ℝ] TangentSpace I y`, incompatible with
`MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)`'s non-dependent codomain. See
`AXIOM_STATUS.md` for the repair plan. -/
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
  -- Step 3 closure via narrow structural axiom `tangentBundle_symmL_smoothAt`.
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

/-! ## Framework-owned Riesz extraction

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
test vectors agree. Direct corollary of `metricToDual_injective`. -/
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

/-! ## Self-test: typeclass synthesises + accessors resolve -/

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

/-! ## Self-tests: metricInner + algebra lemmas -/

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

/-! ## Self-tests: metricRiesz construction -/

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
