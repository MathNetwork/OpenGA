import GeometricMeasureTheory.Varifold

/-!
# AltRegularity.GMT.TangentCone

Tangent cones of varifolds and the junction-cone configuration excluded
by the $\alpha$-structural hypothesis.

For a stationary integral varifold $V$ and a singular point $Z \in
\mathrm{sing}\,V$, any **tangent cone** $C := \lim_{r \to 0}
\eta_{Z, r \#} V$ is a stationary integral cone in $T_Z M \cong
\mathbb{R}^{n+1}$. By [Wickramasekera 2014, Sheeting Theorem +
Minimum Distance Theorem; cf. paper Remark 3.5(ii)], the
$\alpha$-structural hypothesis ($\mathcal{S}3$) is equivalent to: no
tangent cone at any singular point is a **junction cone** — a union of
$N \ge 3$ half-hyperplanes meeting along a common $(n-1)$-dimensional
edge with stationary balance condition.

The two GMT primitives `tangentCone` (the cone at a point) and
`IsJunctionCone` (the junction-configuration predicate) are leaf
primitives pending Mathlib's tangent-measure / blow-up infrastructure.
-/

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- The **tangent cone** of $V$ at $Z$: the blow-up limit of $V$ under
rescaling at $Z$, a stationary integral cone in the tangent space.

**Ground truth**: Simon 1983 §42 (varifold tangents, blow-up procedure
for stationary integral varifolds); Allard 1972 §3.4–§3.6.

**Why opaque** (Layer B Item 3 retreat):

A paper-faithful definition requires the rescaling map
$\eta_{Z, r}(x) := (x - Z) / r$ and the push-forward measure
$\eta_{Z, r \#} V$, then the weak limit as $r \to 0^+$. Three options
explored:

  * **(A) Full geometric blow-up**: requires affine/vector-space
    structure on $M$ (e.g., `[NormedAddCommGroup M]`), which would
    cascade through ~27 framework files and conflicts with $M$ being a
    Riemannian manifold rather than a normed space at the typeclass
    level.
  * **(B/C) `Classical.choice` over `IsTangentConeAt` predicate**:
    introduce sub-primitive `opaque IsTangentConeAt : Varifold M → M →
    Varifold M → Prop` and pick any cone via choice. Net opaque count
    unchanged (1 → 1); semantics degenerate to the zero varifold
    via `instNonempty` since existence proof itself is paper-
    mathematical (Simon §42).
  * **(D) Mathlib normed-space form**: same blocker as (A).

The chain only uses `tangentCone V Z` as black-box input to
`Varifold.HasJunction V Z := IsJunctionCone (tangentCone V Z)`; the
computed value is never inspected by chain proofs. Retreat preserves
structural information without losing chain-checked correctness.

**Used by**: `Varifold.HasJunction` def
(`Regularity/AlphaStructuralVerification.lean`). -/
noncomputable opaque tangentCone : Varifold M → M → Varifold M

/-- $C$ is a **junction cone**: a stationary integral cone supported on
$N \ge 3$ distinct half-hyperplanes $P_1^+, \ldots, P_N^+$ meeting along
a common $(n-1)$-dimensional edge $L$, with the stationary balance
condition $\sum_{j=1}^N m_j \nu_j = 0$ on the outward conormals.

**Ground truth**: Simon 1983 §42 (regularity of stationary integral
cones, classification of tangent cones); Wickramasekera 2014 §3
(Sheeting Theorem and Minimum Distance Theorem give the equivalence
with the $\alpha$-structural hypothesis).

Encoded as an opaque leaf primitive pending Mathlib's
half-hyperplane / cone infrastructure.

**Used by**: `Varifold.HasJunction` def. -/
opaque IsJunctionCone : Varifold M → Prop

end Varifold

end GeometricMeasureTheory
