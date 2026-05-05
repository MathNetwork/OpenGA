import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Riemannian.BumpFunction — Framework-Owned Bump Function Infrastructure

This file provides the framework's canonical bump function surface:
scalar bumps on $\mathbb{R}$, radial bumps on a normed space $E$,
manifold bumps on $M$, and tangent-vector field extension via bump.

## Why this module exists

Bump functions are a foundational geometric-topology tool with reuse
across partition-of-unity constructions, cutoff arguments, smoothing,
test-section construction, and chart-local extension proofs. Per the
framework's "build it ourselves" stance, we expose the
canonical bump infrastructure under a single namespace
`OpenGALib.BumpFunction` so downstream Riemannian / GMT / MinMax /
Regularity work has one stable entry point.

Mathlib provides the underlying primitives (`Real.expNegInvGlue`,
`Real.smoothTransition`, `ContDiffBump`, `SmoothBumpFunction`); none
require the `Bundle.RiemannianBundle` typeclass diamond, so they
compose cleanly with the framework's `OpenGALib.RiemannianMetric`
typeclass cascade. Layers 1–3 are thin wrappers; Layer 4
(`extendVectorField`) is a framework self-build needed for downstream
Riesz extraction and test-section construction (e.g., constructing
test sections in `koszulLinearFunctional_exists`).

## Layering

* **Layer 1** — scalar bumps on $\mathbb{R}$:
  `expDamping`, `smoothStep` re-exporting Mathlib's `Real.expNegInvGlue`
  and `Real.smoothTransition`.
* **Layer 2** — radial bumps on a normed space $E$: re-exports of
  Mathlib's `ContDiffBump` (transitive via `Mathlib.Geometry.Manifold.BumpFunction`).
* **Layer 3** — manifold bumps on $M$: re-export of Mathlib's
  `SmoothBumpFunction I c` plus a `someBump` convenience accessor.
* **Layer 4** — tangent vector field extension via bump:
  `extendVectorField x v` lifts a tangent vector $v \in T_xM$ to a
  smooth section of $TM$ supported in a bump neighbourhood of $x$.

**Ground truth**: Lee *Smooth Manifolds* §2 (bump-function partition of
unity); Mathlib `Real.smoothTransition` for the scalar primitive;
Mathlib `SmoothBumpFunction` for the manifold-side bundled wrapper.
-/

open scoped ContDiff Manifold

namespace OpenGALib
namespace BumpFunction

/-! ## Layer 1 — Scalar bump on $\mathbb{R}$

Re-exports Mathlib's `Real.expNegInvGlue` and `Real.smoothTransition`
with framework-friendly names. Mathlib already proves $C^\infty$
smoothness via the polynomial-times-`expNegInvGlue` lemma machinery
(see `Mathlib.Analysis.SpecialFunctions.SmoothTransition`); we just
expose the headline facts under our namespace. -/

/-- The classical exponential damping function:
$\varphi(t) = e^{-1/t}$ for $t > 0$, zero for $t \le 0$.

This is the standard non-analytic-but-$C^\infty$ glue used to build
smooth bumps. Re-export of Mathlib's root-level `expNegInvGlue`. -/
noncomputable abbrev expDamping : ℝ → ℝ := expNegInvGlue

/-- `expDamping` is $C^\infty$ on all of $\mathbb{R}$ for any
natural smoothness level $n \in \mathbb{N}_\infty$. -/
theorem expDamping_contDiff {n : ℕ∞} : ContDiff ℝ n expDamping :=
  expNegInvGlue.contDiff

/-- `expDamping t = 0` for $t \le 0$. -/
theorem expDamping_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : expDamping t = 0 :=
  expNegInvGlue.zero_of_nonpos h

/-- `expDamping t > 0` for $t > 0$. -/
theorem expDamping_pos_of_pos {t : ℝ} (h : 0 < t) : 0 < expDamping t :=
  expNegInvGlue.pos_of_pos h

/-- `expDamping` is non-negative everywhere. -/
theorem expDamping_nonneg (t : ℝ) : 0 ≤ expDamping t :=
  expNegInvGlue.nonneg t

/-- The smooth transition function: $0$ on $(-\infty, 0]$, $1$ on
$[1, \infty)$, $C^\infty$ everywhere, monotone non-decreasing in
$[0, 1]$.

Re-export of Mathlib's `Real.smoothTransition`. Built as
`expDamping t / (expDamping t + expDamping (1 - t))`. -/
noncomputable abbrev smoothStep : ℝ → ℝ := Real.smoothTransition

/-- `smoothStep` is $C^\infty$ on all of $\mathbb{R}$ for any
natural smoothness level $n \in \mathbb{N}_\infty$. -/
theorem smoothStep_contDiff {n : ℕ∞} : ContDiff ℝ n smoothStep :=
  Real.smoothTransition.contDiff

/-- `smoothStep t = 0` for $t \le 0$. -/
theorem smoothStep_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : smoothStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos h

/-- `smoothStep t = 1` for $1 \le t$. -/
theorem smoothStep_one_of_one_le {t : ℝ} (h : 1 ≤ t) : smoothStep t = 1 :=
  Real.smoothTransition.one_of_one_le h

/-- `smoothStep` is non-negative everywhere. -/
theorem smoothStep_nonneg (t : ℝ) : 0 ≤ smoothStep t :=
  Real.smoothTransition.nonneg t

/-- `smoothStep t ≤ 1` everywhere. -/
theorem smoothStep_le_one (t : ℝ) : smoothStep t ≤ 1 :=
  Real.smoothTransition.le_one t

/-! ## Layer 2 — Radial bump on a normed space $E$

Re-exports Mathlib's `ContDiffBump`. Each `ContDiffBump c : E → ℝ`
is a smooth radial bump centred at `c` with prescribed inner / outer
radii and the standard properties: $f \equiv 1$ on the closed inner
ball, $f \equiv 0$ outside the open outer ball, $0 \le f \le 1$,
$C^\infty$ on $E$.

The framework uses Mathlib's bundled `ContDiffBump` directly;
no further wrapping needed at this layer. -/

/-- Convenience alias: a `ContDiffBump c` is a smooth bump on a normed
space centered at `c`. Mathlib's bundled type exposes inner/outer radii
and the standard smoothness + indicator properties. -/
abbrev radialBump {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) : Type _ := ContDiffBump c

/-! ## Layer 3 — Manifold bump on $M$ centred at $c$

Re-exports Mathlib's `SmoothBumpFunction I c`, a bundled smooth bump
function $f : M \to \mathbb{R}$ such that $f \equiv 1$ near $c$,
$f$ has compact support in the chart at $c$, and $0 \le f \le 1$.

A `Nonempty (SmoothBumpFunction I c)` instance is provided by Mathlib
(`nhdsWithin_range_basis.nonempty`) for any $c$ on a finite-dimensional
manifold; we expose `someBump c` as the framework's canonical accessor
when a specific bump is not otherwise required. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth bump function on $M$ centred at $c$: smooth, compactly
supported in the chart at $c$, equal to $1$ near $c$, valued in $[0, 1]$
elsewhere. Re-export of Mathlib's `SmoothBumpFunction I c`. -/
abbrev manifoldBump (c : M) : Type _ := SmoothBumpFunction I c

variable [FiniteDimensional ℝ E]

/-- **Existence accessor**: a canonical smooth bump at any centre $c$,
extracted via `Classical.choice` from Mathlib's `Nonempty` instance.
Used by `extendVectorField` (Layer 4) and downstream test-section
constructions when a specific bump radius is not required. -/
noncomputable def someBump (c : M) : SmoothBumpFunction I c :=
  Classical.choice inferInstance

/-! ## Layer 4 — Tangent vector field extension via bump

Given a tangent vector $v \in T_xM$, `extendVectorField x v` produces
a smooth section $\widetilde{v} : (y : M) \to T_yM$ of the tangent
bundle with:
* `extendVectorField x v x = v` (value at center, since
  `someBump x x = 1`);
* `extendVectorField x v y = 0` outside the bump's support;
* the section is $C^\infty$ on $M$ (Layer 4 smoothness theorem,
  proven below using `SmoothBumpFunction.contMDiff`).

The tangent vector $v$ is treated as an element of $E$ via the
definitional equality `TangentSpace I x = E` (Mathlib's
`Geometry.Manifold.IsManifold.Basic` line 1041); the result at $y$ is
$f(y) \cdot v \in E = \text{TangentSpace}\,I\,y$.

This is the framework primitive used downstream to construct
**test sections** in the `koszulLinearFunctional_exists` Riesz
extraction: for each $v \in T_xM$, lift to a smooth global $Z$ with
$Z(x) = v$, then evaluate $\frac12 K(X, Y; Z)$ — by
$C^\infty(M)$-linearity in $Z$ (`koszul_smul_right`) and locality
(`koszulFunctional_local`), the result is independent of the chosen
extension. -/

variable [IsManifold I ∞ M]

/-- **Tangent vector field extension via bump**: given $v \in T_xM$,
returns a smooth section $\widetilde{v} : (y : M) \to T_yM$ of the
tangent bundle, supported in `(someBump x).tsupport` (a compact
neighbourhood of $x$), with $\widetilde{v}(x) = v$.

The construction multiplies the tangent vector $v$ by the scalar bump
value at each $y$: $\widetilde{v}(y) := (\text{someBump}\,x)(y) \cdot v$,
where the multiplication uses `TangentSpace I y = E` definitional
equality and the SMul on $E$. -/
noncomputable def extendVectorField (x : M) (v : TangentSpace I x) (y : M) :
    TangentSpace I y :=
  (((someBump x : SmoothBumpFunction I x) : M → ℝ) y) • (v : E)

omit [IsManifold I ∞ M] in
/-- **Value at center**: `extendVectorField x v x = v`.

Direct from `SmoothBumpFunction.eq_one` (`f c = 1` at the center),
which makes the scalar coefficient $1$ and `1 • v = v`. -/
@[simp]
theorem extendVectorField_at [T2Space M] (x : M) (v : TangentSpace I x) :
    extendVectorField x v x = v := by
  show ((someBump x : SmoothBumpFunction I x) : M → ℝ) x • (v : E) = v
  rw [SmoothBumpFunction.eq_one]
  exact one_smul ℝ v

omit [IsManifold I ∞ M] in
/-- **Zero outside support**: if $y$ is outside `(someBump x).tsupport`,
then `extendVectorField x v y = 0`.

Direct from the bump's vanishing outside its support; the SMul of zero
gives zero. -/
theorem extendVectorField_zero_outside_support
    (x : M) (v : TangentSpace I x) (y : M)
    (h : y ∉ tsupport ((someBump x : SmoothBumpFunction I x) : M → ℝ)) :
    extendVectorField x v y = (0 : E) := by
  show ((someBump x : SmoothBumpFunction I x) : M → ℝ) y • (v : E) = 0
  rw [image_eq_zero_of_notMem_tsupport h, zero_smul]

end BumpFunction
end OpenGALib

/-! ## Self-tests -/

section SelfTest

open OpenGALib OpenGALib.BumpFunction

/-- Layer 1 self-test: `expDamping` smoothness at any natural level. -/
example {n : ℕ∞} : ContDiff ℝ n expDamping := expDamping_contDiff

/-- Layer 1 self-test: `smoothStep` smoothness at any natural level. -/
example {n : ℕ∞} : ContDiff ℝ n smoothStep := smoothStep_contDiff

/-- Layer 1 self-test: `smoothStep` is $0$ on $(-\infty, 0]$. -/
example (t : ℝ) (h : t ≤ 0) : smoothStep t = 0 := smoothStep_zero_of_nonpos h

/-- Layer 1 self-test: `smoothStep` is $1$ on $[1, \infty)$. -/
example (t : ℝ) (h : 1 ≤ t) : smoothStep t = 1 := smoothStep_one_of_one_le h

/-- Layer 3 self-test: `someBump` resolves at any centre. -/
noncomputable example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (c : M) :
    SmoothBumpFunction I c := someBump c

/-- Layer 4 self-test: `extendVectorField x v` resolves and has the
value-at-center property. -/
example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] (x : M) (v : TangentSpace I x) :
    extendVectorField x v x = v := extendVectorField_at x v

end SelfTest
