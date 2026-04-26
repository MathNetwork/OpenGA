import AltRegularity.GMT.Varifold

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

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- The **tangent cone** of $V$ at $Z$: the blow-up limit of $V$ under
rescaling at $Z$, a stationary integral cone in the tangent space.

Encoded as an opaque leaf primitive pending Mathlib's tangent-measure
infrastructure. -/
noncomputable opaque tangentCone : Varifold M → M → Varifold M

/-- $C$ is a **junction cone**: a stationary integral cone supported on
$N \ge 3$ distinct half-hyperplanes $P_1^+, \ldots, P_N^+$ meeting along
a common $(n-1)$-dimensional edge $L$, with the stationary balance
condition $\sum_{j=1}^N m_j \nu_j = 0$ on the outward conormals.

Encoded as an opaque leaf primitive pending Mathlib's
half-hyperplane / cone infrastructure. -/
opaque IsJunctionCone : Varifold M → Prop

end Varifold

end AltRegularity
