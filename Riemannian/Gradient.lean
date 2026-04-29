import Riemannian.Connection

/-!
# Riemannian.Gradient

Manifold gradient via Riesz duality on `TangentSpace I x`.

## Form

The manifold gradient $\nabla^M f : (x : M) \to T_xM$ of a smooth scalar
function $f : M \to \mathbb{R}$ is defined by Riesz duality:
$\langle \nabla^M f(x), v \rangle = (\mathrm{d}f)_x(v)$ for all
$v \in T_xM$.

The inner product on `TangentSpace I x` is the framework-owned
`metricInner` (Phase 4.7); the Riesz isomorphism is `metricRiesz`
(Phase 4.7.3 in `Riemannian.Metric`), which sidesteps the lean4#13063
typeclass diamond by using `OpenGALib.RiemannianMetric I M` as the
single canonical inner-product source on tangent vectors.

**Ground truth**: do Carmo 1992 §3 ex. 8 (manifold gradient).
-/

open Bundle OpenGALib
open scoped ContDiff Manifold Bundle

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianMetric I M]

/-- The **manifold gradient** $\nabla^M f : (x : M) \to T_xM$, defined
via **Riesz duality** on the tangent space.

Concretely: $\nabla^M f(x)$ is the unique $v \in T_xM$ such that
$\langle v, w \rangle_g = (\mathrm{d}f)_x(w)$ for all $w \in T_xM$,
where $\langle \cdot, \cdot \rangle_g$ is the framework-owned
`metricInner`. Implemented via `metricRiesz` (Phase 4.7.3) applied to
the manifold differential `mfderiv I 𝓘(ℝ, ℝ) f x`.

**Ground truth**: do Carmo 1992 §3 ex. 8.

Real `noncomputable def` (no `Classical.choose` over an existence
axiom) — Riesz duality is a constructive bijection via
`metricRiesz`, which is built from positive-definiteness and
finite-dim invertibility of the metric tensor. -/
noncomputable def manifoldGradient
    (f : M → ℝ) (x : M) : TangentSpace I x :=
  metricRiesz x (mfderiv I 𝓘(ℝ, ℝ) f x)

/-- **Riesz duality for the manifold gradient**:
$\langle \nabla^M f(x), v \rangle_g = (\mathrm{d}f)_x(v)$.

Holds by construction of `manifoldGradient` via `metricRiesz`. The
inner product is the framework-owned `metricInner`. -/
theorem manifoldGradient_riesz
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    metricInner x (manifoldGradient f x) v = (mfderiv I 𝓘(ℝ, ℝ) f x) v :=
  metricRiesz_inner x (mfderiv I 𝓘(ℝ, ℝ) f x) v

/-- The **squared gradient norm** $|\nabla^M f|^2 : M \to \mathbb{R}$,
defined as $\langle \nabla^M f(x), \nabla^M f(x)\rangle_g$ via the
framework-owned `metricInner` (Phase 4.7).

**Ground truth**: standard; used in Jacobi second-variation formula
(Simon 1983 §49).

Real `noncomputable def` (no `Classical.choose`) — direct constructive
form via `metricInner`. -/
noncomputable def manifoldGradientNormSq
    (I' : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I' ∞ M]
    [RiemannianMetric I' M]
    (f : M → ℝ) (x : M) : ℝ :=
  metricInner x (manifoldGradient (I := I') f x) (manifoldGradient (I := I') f x)

/-- **$|\nabla^M f|^2 \geq 0$**: gradient squared norm is non-negative.
Direct from `metricInner_self_nonneg` (Phase 4.7.5 extension). -/
@[simp]
theorem manifoldGradientNormSq_nonneg
    (I' : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I' ∞ M]
    [RiemannianMetric I' M]
    (f : M → ℝ) (x : M) :
    0 ≤ manifoldGradientNormSq I' f x :=
  metricInner_self_nonneg x _

end Riemannian

/-! ## UXTest

Self-tests verifying that the manifold gradient + gradient-norm-squared
primitives resolve their typeclass cascade. Regression guard against
signature drift in `RiemannianMetric` / `metricRiesz`. -/

section UXTest

open Riemannian OpenGALib
open scoped ContDiff Manifold

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (f : M → ℝ) (x : M) :
    TangentSpace I x := manifoldGradient f x

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    metricInner x (manifoldGradient f x) v = (mfderiv I 𝓘(ℝ, ℝ) f x) v :=
  manifoldGradient_riesz f x v

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (f : M → ℝ) (x : M) : ℝ := manifoldGradientNormSq I f x

end UXTest
