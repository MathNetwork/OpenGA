import Riemannian.Connection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Riemannian.SecondFundamentalForm

Codim-1 second fundamental form, $|A|^2$, and mean curvature.

## Form

The second fundamental form on a hypersurface (codim-1 submanifold) is
the bilinear form $A(X, Y) := \langle \nabla^M_X Y, \nu \rangle$, where
$\nu$ is the unit normal to the hypersurface in the ambient $M$.

For the codim-1 setting in our framework, the hypersurface is the
support of a `Varifold M`, and $\nu$ is supplied by the
`Varifold.HasNormal` typeclass (Phase 1.5 Commit B).

  * `secondFundamentalFormScalar` — real `noncomputable def` using
    `covDeriv` (Levi-Civita) + `metricInner` on `TangentSpace I x`
    (framework-owned, `Riemannian.Metric`).
  * `secondFundamentalFormSqNorm` — real `noncomputable def` via summation
    over Mathlib's `stdOrthonormalBasis ℝ (TangentSpace I x)` of
    $A(e_i, e_j)^2$ (Frobenius squared norm).
  * `meanCurvature` — real `noncomputable def` via summation of
    $A(e_i, e_i)$ over the same orthonormal basis.

The framework-owned `OpenGALib.RiemannianMetric` typeclass (Phase 4.7)
provides `metricInner` directly on tangent vectors via
`TangentSpace I x = E` def-eq, sidestepping the lean4#13063 typeclass
diamond on `Bundle.RiemannianBundle`.

**Ground truth**: do Carmo 1992 §6.2 (codim-1 case);
Simon 1983 §49 (use in second variation).
-/

open Bundle OpenGALib
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianMetric I M]

/-- The **second fundamental form (codim-1 scalar form)** $A$ at a point:
$$A(X, Y)(x) := \langle \nabla^M_X Y(x), \nu(x) \rangle.$$

Real `noncomputable def` using `covDeriv` (Levi-Civita) + `metricInner`
on `TangentSpace I x` (framework-owned, `Riemannian.Metric`).

**Ground truth**: do Carmo 1992 §6.2. -/
noncomputable def secondFundamentalFormScalar
    (ν X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  metricInner x (covDeriv X Y x) (ν x)

/-- $|A|^2 : M \to \mathbb{R}$, the squared norm of the second fundamental form,
defined as $\sum_{i, j} A(e_i, e_j)^2$ over the standard orthonormal
basis $\{e_i\}$ of `TangentSpace I x` (Mathlib `stdOrthonormalBasis`,
applicable via the `Riemannian.InnerProductBridge`).

The basis-dependent sum equals the basis-independent
$|A|^2 = \sum_{i, j} A_{ij}^2$ (Frobenius norm) when $\{e_i\}$ is
orthonormal — which `stdOrthonormalBasis` guarantees.

**Ground truth**: do Carmo 1992 §6.2; Simon 1983 §49 (Jacobi formula
uses this). -/
noncomputable def secondFundamentalFormSqNorm
    (ν : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, ∑ j, (secondFundamentalFormScalar (I := I) (M := M) ν
    (fun (_ : M) => (e i : TangentSpace I x))
    (fun (_ : M) => (e j : TangentSpace I x)) x) ^ 2

/-- **$|A|^2 \geq 0$**: squared norm is non-negative.
Direct from sum of squares. -/
@[simp]
theorem secondFundamentalFormSqNorm_nonneg
    (ν : Π x : M, TangentSpace I x) (x : M) :
    0 ≤ secondFundamentalFormSqNorm ν x := by
  unfold secondFundamentalFormSqNorm
  positivity

/-- The **mean curvature (codim-1 scalar form)** $H : M \to \mathbb{R}$
of the hypersurface oriented by unit normal $\nu$:
$$H(x) := \mathrm{tr}_g A(x) = \sum_i A(e_i, e_i)(x)$$
over an orthonormal basis $\{e_i\}$ of `TangentSpace I x`.

Real `noncomputable def` via `stdOrthonormalBasis ℝ (TangentSpace I x)`
+ basis-sum (basis-independent for orthonormal frame).

**Ground truth**: do Carmo 1992 §6.2; standard codim-1 specialization. -/
noncomputable def meanCurvature
    (ν : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, secondFundamentalFormScalar (I := I) (M := M) ν
    (fun (_ : M) => (e i : TangentSpace I x))
    (fun (_ : M) => (e i : TangentSpace I x)) x

end Riemannian

/-! ## UXTest

Self-tests verifying that the second-fundamental-form primitives resolve
their typeclass cascade. Regression guard against signature drift in
`RiemannianMetric` / `covDeriv`. -/

section UXTest

open Riemannian OpenGALib
open scoped ContDiff Manifold

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (ν X Y : Π x : M, TangentSpace I x) (x : M) :
    ℝ := secondFundamentalFormScalar ν X Y x

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (ν : Π x : M, TangentSpace I x) (x : M) :
    ℝ := secondFundamentalFormSqNorm ν x

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (ν : Π x : M, TangentSpace I x) (x : M) :
    ℝ := meanCurvature ν x

example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianMetric I M]
    (ν : Π x : M, TangentSpace I x) (x : M) :
    0 ≤ secondFundamentalFormSqNorm ν x :=
  secondFundamentalFormSqNorm_nonneg ν x

end UXTest
