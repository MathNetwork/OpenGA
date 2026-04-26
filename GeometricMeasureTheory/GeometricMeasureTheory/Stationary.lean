import GeometricMeasureTheory.Varifold
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic

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

`TestVectorField` is now a paper-faithful structure carrying a smooth
section of the tangent bundle with compact support (Layer B C-2).
`firstVariation` remains an opaque leaf primitive pending Mathlib's
Riemannian-divergence operator (the integrand $\mathrm{div}_S X$
requires either Riemannian connection infrastructure for the manifold
divergence, or full Grassmann-bundle varifold data for the tangent-plane
divergence — neither is currently in Mathlib).
-/

open scoped ContDiff

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- A smooth, compactly supported vector field on a smooth manifold $M$.

A test vector field is a section of the tangent bundle $TM$ that is
$C^\infty$ as a map into the total space and supported on a compact set
in the base.

**Ground truth**: standard smooth-manifold concept; Simon 1983 §38
("smooth vector fields with compact support on $M$"); Allard 1972 §3.

**Encoding**: as a Mathlib `Π (x : M), TangentSpace I x` (the standard
section type used in `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`),
together with a smoothness predicate via `ContMDiff I I.tangent ∞`
on the lifted bundle map, and a compact-support predicate.

**Used by**: `Varifold.IsStationary` def (in this file). -/
structure TestVectorField
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The vector field as a section of the tangent bundle. -/
  toFun : Π (x : M), TangentSpace I x
  /-- The lifted bundle map $x \mapsto (x, X(x))$ is $C^\infty$. -/
  contMDiff : ContMDiff I I.tangent ∞ (fun x : M => (toFun x : TangentBundle I M))
  /-- The vector field has compact support: the closure of the
  non-vanishing set is compact. -/
  isCompactSupport : IsCompact (closure {x : M | toFun x ≠ 0})

namespace Varifold

/-- The **first variation** $\delta V(X) \in \mathbb{R}$ of a varifold
$V$ along a test vector field $X$:
$\delta V(X) := \int \mathrm{div}_S X(x)\, dV(x, S)$,
where $\mathrm{div}_S X = \sum_{i=1}^n \langle e_i, \nabla_{e_i} X \rangle$
for an orthonormal basis $\{e_i\}$ of $S$.

For a smooth varifold supported on a hypersurface $\Sigma$ this equals
$-\int_\Sigma X \cdot \vec{H}_\Sigma \, d\mathcal{H}^n$, where
$\vec{H}_\Sigma$ is the mean curvature vector.

**Ground truth**: Simon 1983 §38, equations (38.1)–(38.3); Allard 1972
§4.1; Pitts 1981 §3.6.

**Why opaque** (Layer B C-2 retreat):

Two paths to a real def, both currently blocked at the Mathlib level:

  * **Riemannian-divergence path**: integrand
    $\mathrm{div}_g X = \mathrm{tr}_g(\nabla X)$ requires the
    Riemannian connection $\nabla$ on $M$. Mathlib's
    `Mathlib/Geometry/Manifold/Riemannian/` has the metric tensor and
    geodesic basics but no divergence operator at the time of this
    grounding round (auditor checked: 0 results for
    `^def divergence` / `^def Divergence` /
    `riemannianDivergence` in `Mathlib/`).
  * **Grassmann-bundle path**: integrand
    $\mathrm{div}_S X = \mathrm{tr}_S(\mathrm{d}X)$ requires the
    varifold to carry a measure on the Grassmann bundle
    $G_n(M)$. The framework's `Varifold` is currently mass-only
    (deferred refinement, see `Varifold.lean`); paper §6
    only uses mass-measure data.

Once either Mathlib gains a Riemannian divergence operator OR the
framework upgrades `Varifold` to carry Grassmann data, this opaque
will be replaced by an explicit integral.

**Used by**: `Varifold.IsStationary` def (in this file). -/
opaque firstVariation
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    [ChartedSpace H M] [IsManifold I ∞ M] :
    Varifold M → TestVectorField I M → ℝ

/-- $V$ is **stationary** iff its first variation $\delta V(X)$ vanishes
on every smooth compactly supported test vector field $X$ on $M$.

Defined explicitly as a universally-quantified vanishing statement so
the structure "$\delta V = 0$ on every test field" is visible to the
Lean kernel.

Universally quantifies over the smooth-manifold structure on $M$ so the
predicate `IsStationary V` does not need to thread the
`ModelWithCorners` parameter through every callsite (callers without a
distinguished `I` simply universally use this form). The smooth-manifold
type parameters are restricted to `Type` (universe 0) to avoid the
universe-inference issue when `IsStationary V` is used as a structure
field; this matches the standard `𝕜 ∈ {ℝ, ℂ}` convention. -/
def IsStationary (V : Varifold M) : Prop :=
  ∀ {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    [ChartedSpace H M] [IsManifold I ∞ M]
    (X : TestVectorField I M), firstVariation V X = 0

end Varifold

end GeometricMeasureTheory
