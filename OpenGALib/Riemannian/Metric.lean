import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OpenGALib.Algebraic.BilinearForm.Basic
import OpenGALib.Algebraic.BilinearForm.Riesz
import OpenGALib.Riemannian.TangentBundle
import OpenGALib.Util.Attributes

/-!
# Riemannian metric

A **Riemannian metric** on a smooth manifold $M$ is a smooth, symmetric,
positive-definite tensor field $g$ assigning an inner product
$g_x : T_xM \times T_xM \to \mathbb{R}$ to each tangent space.

In OpenGALib, `RiemannianMetric I M` is an `abbrev` for Mathlib's
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` — that is,
the metric is *data* (an inhabitant of a structure), not a typeclass
attribute. Operators take a metric `g : RiemannianMetric I M` as an
explicit argument; multiple metrics on the same manifold coexist as
different inhabitants.

This file provides:

1. The `RiemannianMetric` abbreviation.
2. The metric inner product `g.metricInner` and its bilinear-form algebra.
3. Riesz duality `g.metricRiesz : (T_xM)^* \to T_xM`.
4. Smoothness of `g.metricInner` and of the Riesz section.
5. Bridge instances on `TangentSpace I x` (NACG, IPS, FiniteDim, Complete).

## Main definitions

* `RiemannianMetric I M` — alias for the Mathlib bundled metric.
* `g.metricInner x V W = g_x(V, W)` — the inner product.
* `g.metricRiesz x φ` — the unique vector $V$ with $g_x(V, \cdot) = \varphi$.

Reference: do Carmo, *Riemannian Geometry*, §1.2; Lee, *Smooth Manifolds*, Ch. 13.
Mathlib upstream: `Mathlib.Geometry.Manifold.VectorBundle.Riemannian`.
-/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace Riemannian

/-! ## The metric type -/

/-- A **Riemannian metric** on a smooth manifold $M$, modelled on
$(E, H, I)$. Defined as Mathlib's `Bundle.ContMDiffRiemannianMetric`
applied to the tangent bundle: the metric is data, not a typeclass
attribute. -/
abbrev RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

/-- **`[HasMetric I M]` typeclass**: a thin wrapper around
`RiemannianMetric I M` that makes the metric instance-bindable.

Path B's `abbrev RiemannianMetric` makes the metric *data*, which is
correct mathematically (multiple metrics on the same manifold coexist as
different inhabitants) but loses the `[g : RiemannianMetric I M]`
instance-binding form. Downstream code that binds `{I : ModelWithCorners
...}` independently from the manifold's bundled `modelI` needs an
instance-form of "this manifold has a metric on `I`". `HasMetric I M`
fills that gap: it's a single-field class whose `metric` field IS a
`RiemannianMetric I M`.

For typeclass-driven manifolds, `Manifold.lean` registers a bridge
`[RiemannianManifold M] → [HasMetric (SmoothManifold.modelI M) M]`.
For explicit-metric callers, declare `instance : HasMetric I M := ⟨g⟩`
once and the rest of the API (algebra, Riesz, smoothness) becomes
typeclass-resolvable. -/
class HasMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    where
  /-- The Riemannian metric on $(M, I)$. -/
  metric : RiemannianMetric I M

/-- **Bridge**: `[HasMetric I M]` induces a global `Bundle.RiemannianBundle
(TangentSpace I : M → Type _)`, which activates Mathlib's scoped
`NormedAddCommGroup` and `InnerProductSpace ℝ` instances on each fibre
`TangentSpace I x`. Single NACG/IPS source — see `Metric.lean` rationale. -/
noncomputable instance instRiemannianBundleOfHasMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [hm : HasMetric I M] :
    Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
  ⟨hm.metric.toRiemannianMetric⟩

end Riemannian

namespace Riemannian.RiemannianMetric


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Inner product -/

/-- The **metric inner product** $\langle V, W\rangle_g = g_x(V, W)$. -/
noncomputable def metricInner (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) : ℝ :=
  g.inner x V W

@[simp]
theorem metricInner_apply (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V W = g.inner x V W := rfl

/-- **Symmetry**: $\langle V, W\rangle_g = \langle W, V\rangle_g$. -/
theorem metricInner_comm (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V W = g.metricInner x W V :=
  g.symm x V W

/-- **Positive-definiteness**: $V \ne 0 \Rightarrow \langle V, V\rangle_g > 0$. -/
theorem metricInner_self_pos (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) (hV : V ≠ 0) :
    0 < g.metricInner x V V :=
  g.pos x V hV

@[metric_simp]
theorem metricInner_add_left (g : RiemannianMetric I M)
    (x : M) (V₁ V₂ W : TangentSpace I x) :
    g.metricInner x (V₁ + V₂) W = g.metricInner x V₁ W + g.metricInner x V₂ W := by
  show g.inner x (V₁ + V₂) W = g.inner x V₁ W + g.inner x V₂ W
  rw [(g.inner x).map_add]; rfl

@[metric_simp]
theorem metricInner_add_right (g : RiemannianMetric I M)
    (x : M) (V W₁ W₂ : TangentSpace I x) :
    g.metricInner x V (W₁ + W₂) = g.metricInner x V W₁ + g.metricInner x V W₂ :=
  (g.inner x V).map_add W₁ W₂

@[metric_simp]
theorem metricInner_smul_left (g : RiemannianMetric I M)
    (x : M) (c : ℝ) (V W : TangentSpace I x) :
    g.metricInner x (c • V) W = c * g.metricInner x V W := by
  show g.inner x (c • V) W = c * g.inner x V W
  rw [(g.inner x).map_smul]; rfl

@[metric_simp]
theorem metricInner_smul_right (g : RiemannianMetric I M)
    (x : M) (c : ℝ) (V W : TangentSpace I x) :
    g.metricInner x V (c • W) = c * g.metricInner x V W := by
  show g.inner x V (c • W) = c * g.inner x V W
  rw [(g.inner x V).map_smul]; rfl

@[simp, metric_simp]
theorem metricInner_zero_left (g : RiemannianMetric I M)
    (x : M) (W : TangentSpace I x) :
    g.metricInner x 0 W = 0 := by
  show g.inner x 0 W = 0
  rw [(g.inner x).map_zero]; rfl

@[simp, metric_simp]
theorem metricInner_zero_right (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) :
    g.metricInner x V 0 = 0 :=
  (g.inner x V).map_zero

@[simp, metric_simp]
theorem metricInner_neg_left (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x (-V) W = -g.metricInner x V W := by
  show g.inner x (-V) W = -g.inner x V W
  rw [(g.inner x).map_neg]; rfl

@[simp, metric_simp]
theorem metricInner_neg_right (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V (-W) = -g.metricInner x V W :=
  (g.inner x V).map_neg W

@[simp, metric_simp]
theorem metricInner_sub_left (g : RiemannianMetric I M)
    (x : M) (V₁ V₂ W : TangentSpace I x) :
    g.metricInner x (V₁ - V₂) W = g.metricInner x V₁ W - g.metricInner x V₂ W := by
  show g.inner x (V₁ - V₂) W = g.inner x V₁ W - g.inner x V₂ W
  rw [(g.inner x).map_sub]; rfl

@[simp, metric_simp]
theorem metricInner_sub_right (g : RiemannianMetric I M)
    (x : M) (V W₁ W₂ : TangentSpace I x) :
    g.metricInner x V (W₁ - W₂) = g.metricInner x V W₁ - g.metricInner x V W₂ :=
  (g.inner x V).map_sub W₁ W₂

/-- $\langle V, V\rangle_g \ge 0$ for any $V$. -/
@[simp, metric_simp]
theorem metricInner_self_nonneg (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) :
    0 ≤ g.metricInner x V V := by
  rcases eq_or_ne V 0 with hV | hV
  · rw [hV, g.metricInner_zero_left]
  · exact le_of_lt (g.metricInner_self_pos x V hV)

end Riemannian.RiemannianMetric

/-! ## TangentSpace fibre instances

`NormedAddCommGroup`, `NormedSpace`, and `InnerProductSpace` on each
fibre `TangentSpace I x` are *not* declared here. Instead, they are
supplied by Mathlib's scoped `Bundle.RiemannianBundle`-derived
instances, which become active once a `RiemannianBundle E` is in scope
(e.g., via the global instance on `[RiemannianManifold M]`, or via a
local `letI`). Routing through `RiemannianBundle` ensures that the
inner product the Mathlib `inner` projection lands on is *exactly*
`g.inner b · ·`, sidestepping the lean4#13063 NACG diamond.

The non-metric fibre instances `FiniteDimensional` and `CompleteSpace`
are orthogonal to the NACG/IPS chain and are transported here via the
`TangentSpace I x = E` def-eq. -/

namespace Riemannian

section TangentSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
instance instFiniteDimensionalTangent [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

end TangentSpaceInstances

end Riemannian

/-! ## Riesz duality

In a finite-dim inner product space $V$, every continuous linear functional
$\varphi : V \to \mathbb{R}$ is uniquely represented as $\langle V_\varphi, \cdot\rangle_g$. -/

namespace Riemannian.RiemannianMetric


section Riesz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Bridge from the metric's continuous bilinear form to the
algebraic-core `BilinearForm.Form ℝ E`. -/
private noncomputable def toBilinForm (g : RiemannianMetric I M) (x : M) :
    BilinearForm.Form ℝ E :=
  LinearMap.mk₂ ℝ
    (fun v w => g.inner x v w)
    (fun v₁ v₂ w => by
      simp only [show g.inner x (v₁ + v₂) = g.inner x v₁ + g.inner x v₂
        from (g.inner x).map_add v₁ v₂, ContinuousLinearMap.add_apply])
    (fun c v w => by
      simp only [show g.inner x (c • v) = c • g.inner x v
        from (g.inner x).map_smul c v, ContinuousLinearMap.smul_apply])
    (fun v w₁ w₂ => (g.inner x v).map_add w₁ w₂)
    (fun c v w => (g.inner x v).map_smul c w)

omit [FiniteDimensional ℝ E] in
private theorem toBilinForm_isPosDef (g : RiemannianMetric I M) (x : M) :
    BilinearForm.IsPosDef (g.toBilinForm x) := by
  intro v hv
  show 0 < g.inner x v v
  exact g.pos x v hv

/-- **Forward Riesz** $V \mapsto g_x(V, \cdot)$. -/
noncomputable def metricToDual (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.inner x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricToDual_apply (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.metricToDual x v w = g.metricInner x v w := rfl

omit [FiniteDimensional ℝ E] in
theorem metricToDual_injective (g : RiemannianMetric I M) (x : M) :
    Function.Injective (g.metricToDual x) := by
  intro v₁ v₂ h
  apply BilinearForm.toDual_injective (g.toBilinForm_isPosDef x)
  ext w
  show g.inner x v₁ w = g.inner x v₂ w
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) h

omit [FiniteDimensional ℝ E] in
/-- **Non-degeneracy**: vectors with equal inner-products against everything are equal. -/
theorem metricInner_eq_iff_eq (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (∀ Z : TangentSpace I x, g.metricInner x v Z = g.metricInner x w Z) ↔ v = w :=
  BilinearForm.inner_eq_iff_eq (g.toBilinForm_isPosDef x) v w

/-- **Inverse Riesz** $\varphi \mapsto V_\varphi$ such that $g_x(V_\varphi, W) = \varphi(W)$.

Constructed via the algebraic-core `BilinearForm.riesz` applied to the
`LinearMap` coercion of the continuous functional. -/
noncomputable def metricRiesz (g : RiemannianMetric I M) (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x :=
  BilinearForm.riesz (g.toBilinForm_isPosDef x)
    ((φ : TangentSpace I x →ₗ[ℝ] ℝ))

/-- **Defining property of Riesz**: $\langle \text{metricRiesz}\,\varphi, W\rangle_g = \varphi(W)$. -/
@[simp]
theorem metricRiesz_inner (g : RiemannianMetric I M) (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) (V : TangentSpace I x) :
    g.metricInner x (g.metricRiesz x φ) V = φ V :=
  BilinearForm.riesz_inner (g.toBilinForm_isPosDef x)
    ((φ : TangentSpace I x →ₗ[ℝ] ℝ)) V

/-- **Uniqueness**: if $g_x(V, \cdot) = \varphi$, then $V = \text{metricRiesz}\,\varphi$. -/
theorem metricRiesz_unique (g : RiemannianMetric I M) (x : M)
    (v : TangentSpace I x) (φ : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ w, g.metricInner x v w = φ w) :
    v = g.metricRiesz x φ :=
  BilinearForm.riesz_unique (g.toBilinForm_isPosDef x) v
    ((φ : TangentSpace I x →ₗ[ℝ] ℝ)) h

theorem metricToDual_bijective (g : RiemannianMetric I M) (x : M) :
    Function.Bijective (g.metricToDual x) := by
  refine ⟨g.metricToDual_injective x, ?_⟩
  intro φ
  refine ⟨g.metricRiesz x φ, ?_⟩
  ext v
  exact g.metricRiesz_inner x φ v

/-- The Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)`, built directly
from `metricToDual` and its bijectivity. The forward map is
`v ↦ g.inner x v` (the metric-induced continuous functional); the inverse
is `g.metricRiesz x`. -/
noncomputable def metricToDualEquiv (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.ofBijective (g.metricToDual x).toLinearMap (g.metricToDual_bijective x)

end Riesz

end Riemannian.RiemannianMetric

/-! ## Smoothness of the metric inner product

Given a Riemannian metric `g` on `M` and two smooth tangent-bundle
sections `Y, Z : ∀ y, TangentSpace I y`, the scalar function
`y ↦ g_y(Y y, Z y) : M → ℝ` is smooth. Below is the full 8-variant
parity API with Mathlib's `MDifferentiable*.inner_bundle` and
`ContMDiff*.inner_bundle` families:

* `metricInner_{mdifferentiable, mdifferentiableAt, mdifferentiableOn,
  mdifferentiableWithinAt}` — differentiability.
* `metricInner_{contMDiff, contMDiffAt, contMDiffOn, contMDiffWithinAt}`
  — smoothness of any order `n ≤ ∞`.

Each variant is parametric over the basepoint map `b : N → M` so the
sections may live over a general parameter space. All variants reduce
to Mathlib's `inner_bundle` after locally injecting a
`Bundle.RiemannianBundle (TangentSpace I)` from `g.toRiemannianMetric`. -/

namespace Riemannian.RiemannianMetric

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {v w : ∀ x : M, TangentSpace I x} {s : Set M} {x : M}

/-! ### `ContMDiff` family — smoothness order `n ≤ ∞` -/

variable {n : ℕ∞ω} [hLE : ENat.LEInfty n]

/-- $\langle v(\cdot), w(\cdot)\rangle_g$ is `ContMDiffWithinAt` whenever
the tangent-bundle sections `v`, `w` are. -/
theorem metricInner_contMDiffWithinAt
    (g : RiemannianMetric I M)
    (hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s x)
    (hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s x) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) n
      (fun y => g.metricInner y (v y) (w y)) s x := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ContMDiffWithinAt.inner_bundle (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _)) (b := fun y => y)
    (v := v) (w := w) (IM := I) hv hw

/-- Pointwise variant. -/
theorem metricInner_contMDiffAt
    (g : RiemannianMetric I M)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) x)
    (hw : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y => g.metricInner y (v y) (w y)) x :=
  g.metricInner_contMDiffWithinAt hv hw

/-- Set-form variant. -/
theorem metricInner_contMDiffOn
    (g : RiemannianMetric I M)
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s)
    (hw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s) :
    ContMDiffOn I 𝓘(ℝ, ℝ) n
      (fun y => g.metricInner y (v y) (w y)) s :=
  fun y hy => g.metricInner_contMDiffWithinAt (hv y hy) (hw y hy)

/-- Global variant. -/
theorem metricInner_contMDiff
    (g : RiemannianMetric I M)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M))) :
    ContMDiff I 𝓘(ℝ, ℝ) n
      (fun y => g.metricInner y (v y) (w y)) :=
  fun y => g.metricInner_contMDiffAt (hv y) (hw y)

/-! ### `MDifferentiable` family — first-order differentiability -/

/-- Differentiable-within-at variant. -/
theorem metricInner_mdifferentiableWithinAt
    (g : RiemannianMetric I M)
    (hv : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s x)
    (hw : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s x) :
    MDifferentiableWithinAt I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (v y) (w y)) s x := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact MDifferentiableWithinAt.inner_bundle (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _)) (b := fun y => y)
    (v := v) (w := w) (IM := I) hv hw

/-- Pointwise differentiability. -/
theorem metricInner_mdifferentiableAt
    (g : RiemannianMetric I M)
    (hv : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) x)
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (v y) (w y)) x :=
  g.metricInner_mdifferentiableWithinAt hv hw

/-- Set-form differentiability. -/
theorem metricInner_mdifferentiableOn
    (g : RiemannianMetric I M)
    (hv : MDifferentiableOn I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s)
    (hw : MDifferentiableOn I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s) :
    MDifferentiableOn I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (v y) (w y)) s :=
  fun y hy => g.metricInner_mdifferentiableWithinAt (hv y hy) (hw y hy)

/-- Global differentiability. -/
theorem metricInner_mdifferentiable
    (g : RiemannianMetric I M)
    (hv : MDifferentiable I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (hw : MDifferentiable I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M))) :
    MDifferentiable I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (v y) (w y)) :=
  fun y => g.metricInner_mdifferentiableAt (hv y) (hw y)

end Smoothness

end Riemannian.RiemannianMetric
