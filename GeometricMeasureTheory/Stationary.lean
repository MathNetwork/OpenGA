import GeometricMeasureTheory.Varifold
import GeometricMeasureTheory.HasNormal
import GeometricMeasureTheory.Variation.FirstVariation
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# AltRegularity.GMT.Stationary

Stationary varifolds.

A varifold $V$ is stationary iff its first variation $\delta V$ vanishes
for every compactly supported smooth vector field on $M$. Stationarity
has two key consequences used throughout the paper:
  * the **monotonicity formula** (Proposition 2.10): the rescaled mass
    $r \mapsto \|V\|(B_r(p))/r^n$ is monotone non-decreasing in $r$, so
    the density $\Theta(\|V\|, p)$ exists pointwise.
  * the **rectifiability theorem** (Proposition 2.12, in
    `AltRegularity.GMT.Rectifiability`).

## Definition style

`IsStationary` is an explicit `def` — universally quantified over all
test vector fields — so the structure of "first variation vanishes on
every test field" is visible to the Lean kernel.

`TestVectorField` is a paper-faithful structure carrying a smooth
section of the tangent bundle with compact support (Layer B C-2).

`firstVariation` is grounded in the **ambient-divergence form**:
$\delta V(X) = \int_M \mathrm{div}_M X\, d\|V\|$. The computation uses
`fderiv`-of-chart-pullback + `LinearMap.trace` to realize the divergence,
mirroring Mathlib's `VectorField.lieBracket` chart-pullback pattern.

For the paper §4-6 codim-1 use, the GMT-paper formula
$\delta V(X) = \int \mathrm{div}_S X\, dV(x, S)$ differs from the
ambient form by a normal-direction correction
$\langle\nu, \nabla_\nu X\rangle$. Capturing this correction would
require upgrading `Varifold` to carry a unit normal field — a refinement
deferred to a future round. Chain proofs use `IsStationary V` as a
black-box hypothesis and do not inspect the specific value of
`firstVariation V X`, so the codim-1 gap does not propagate into the
chain.
-/

open scoped ContDiff Manifold
open VectorField

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

-- `TestVectorField` was moved to `HasNormal.lean` (Phase 1.7) to break the
-- import cycle with `Variation/FirstVariation.lean`. It remains available
-- via the open `GeometricMeasureTheory` namespace inherited via the
-- `HasNormal` import below.

namespace Varifold

/-- **Ambient divergence on a normed space**:
$\mathrm{div}\,V(y) := \mathrm{tr}(\mathrm{D}V(y))$
where $\mathrm{D}V(y) : E \to E$ is the Fréchet derivative of
$V : E \to E$. Implemented via `LinearMap.trace ℝ E ∘ fderiv ℝ V`.

Returns 0 if $V$ is not differentiable at $y$ (Mathlib convention),
or if $E$ is infinite-dimensional or has no finite basis (returns 0
from `LinearMap.trace`). For finite-dim ambients (paper §6 setting:
ambient $M^{n+1}$ is a closed Riemannian manifold), the def gives
the standard ambient divergence.

**Ground truth**: standard differential calculus (e.g., Simon §38). -/
noncomputable def divergenceFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E → E) (y : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ V y).toLinearMap

/-- **Ambient divergence of a vector field on the manifold** $M$ at $x$,
computed via chart pullback to the model space $E$.

Concretely: pull back $X$ from $M$ to $E$ via the inverse chart at $x$
(using `VectorField.mpullbackWithin`), then take the flat-space
divergence at the chart image of $x$.

For a flat ambient ($M$ open in a normed space), this equals the
standard divergence. For curved Riemannian ambient, it equals the
Riemannian divergence $\mathrm{div}_g X = \mathrm{tr}_g(\nabla X)$
only when the chart is isometric at $x$ (e.g., normal coordinates);
the chart-dependent value differs by Christoffel correction terms.
Mathlib does not yet expose `riemannianDivergence`, so this
chart-local form is the closest paper-faithful expression available.

**Used by**: `firstVariation`. -/
noncomputable def divergenceM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (X : Π (x : M), TangentSpace I x) (x : M) : ℝ :=
  divergenceFlat
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (Set.range I))
    ((extChartAt I x) x)

/-- The **first variation** $\delta V(X) \in \mathbb{R}$ of a varifold
$V$ along a test vector field $X$, in the **ambient-divergence form**:
$$\delta V(X) := \int_M \mathrm{div}_M X(x)\, d\|V\|(x).$$

The integrand `divergenceM I X.toFun x` is the chart-local ambient
divergence (see `divergenceM` docstring). Integration is against the
mass measure $\|V\|$.

**Codim-0 case**: when $V = \theta \cdot \mathrm{vol}_g$ for a density
$\theta : M \to \mathbb{R}_{\ge 0}$, this equals
$\int \mathrm{div}_S X(x)\, dV(x, S)$ verbatim
(every $S = T_x M$ is the full tangent space).

**Codim-1 case** (paper §4-6 setting): the GMT-paper formula has an
additional normal-direction correction $\langle\nu, \nabla_\nu X\rangle$,
not captured here because the mass-only `Varifold` carries no
tangent-plane data. Chain proofs treat `IsStationary V` as a black-box
hypothesis (`isStationary_of_minmaxLimit` is sorried, and downstream
consumers never inspect the value), so the codim-1 gap does not
propagate.

A future refinement upgrading `Varifold` to carry a unit normal field
$\nu$ would replace `divergenceM` with the codim-1 form
$\mathrm{div}_M X - \langle\nu, \nabla_\nu X\rangle$ for full
paper-faithfulness.

**Ground truth**: Pitts 1981 §38; Simon 1983 §38; Allard 1972 §4.1.

**Used by**: `Varifold.IsStationary` def (in this file). -/
noncomputable def firstVariation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    (V : Varifold M) (X : TestVectorField I M) : ℝ :=
  ∫ x, divergenceM I X.toFun x ∂V.massMeasure

/-- $V$ is **stationary** iff its first variation $\delta V(X)$ vanishes
on every smooth compactly supported test vector field $X$ on $M$.

Defined explicitly as a universally-quantified vanishing statement so
the structure "$\delta V = 0$ on every test field" is visible to the
Lean kernel.

**Phase 1.7 body migration** (post Phase 1.6 Bridge unblock): the body
now uses `Variation.firstVariationFull` (paper-faithful codim-1 form
with $\langle\nu, \nabla_\nu X\rangle$ correction) instead of the
ambient `firstVariation` (codim-1 caveat). The `[HasNormal I V]`
typeclass is universally quantified inside the `∀`, matching the
"for all smooth-manifold structures and for all unit-normal-field
choices" form. Framework's `HasNormal` instances for `ofBoundary` /
`tangentCone` (Phase 1.6 commit `bdc6d4f`) auto-resolve at chain
consumption sites where `V` comes from a concrete varifold construction.

Universally quantifies over the smooth-manifold structure on $M$ so the
predicate `IsStationary V` does not need to thread the
`ModelWithCorners` parameter through every callsite. The smooth-manifold
type parameters are restricted to `Type` (universe 0) to avoid the
universe-inference issue when `IsStationary V` is used as a structure
field; this matches the standard $\mathbb{R}$-finite-dim convention. -/
def IsStationary (V : Varifold M) : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    [Varifold.HasNormal I V]
    (X : TestVectorField I M), Variation.firstVariationFull I V X = 0

end Varifold

end GeometricMeasureTheory
