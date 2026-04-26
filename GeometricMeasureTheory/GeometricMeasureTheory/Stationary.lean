import GeometricMeasureTheory.Varifold

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
every test field" is visible to the Lean kernel rather than hidden in
an opaque predicate. The two leaf primitives `TestVectorField` (the
space of smooth compactly supported vector fields on $M$) and
`firstVariation` (the pairing $\delta V(X) \in \mathbb{R}$) remain
opaque pending Mathlib-level manifold infrastructure.
-/

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- A smooth, compactly supported vector field on $M$.

**Ground truth**: standard smooth-manifold concept; Simon 1983 §38
("vector fields with compact support on $M$"). Pending Mathlib's
smooth-manifold-with-corners infrastructure for $M$, this type is
left opaque; concrete inhabitants (zero field, bump-times-coord fields)
will become available once the manifold structure is threaded through.

**Used by**: `Varifold.IsStationary` def (`GMT/Stationary.lean`). -/
opaque TestVectorField (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] : Type

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

**Used by**: `Varifold.IsStationary` def (`GMT/Stationary.lean`). -/
opaque firstVariation : Varifold M → TestVectorField M → ℝ

/-- $V$ is **stationary** iff its first variation $\delta V(X)$ vanishes
on every smooth compactly supported test vector field $X$ on $M$.

Defined explicitly as a universally-quantified vanishing statement so
the structure "$\delta V = 0$ on every test field" is visible to the
Lean kernel. -/
def IsStationary (V : Varifold M) : Prop :=
  ∀ X : TestVectorField M, firstVariation V X = 0

end Varifold

end GeometricMeasureTheory
