import AltRegularity.GMT.Stationary

/-!
# AltRegularity.GMT.Rectifiability

Rectifiability of stationary varifolds with positive density
(Proposition 2.12 of the paper).

A stationary $n$-varifold whose density is positive at $\|V\|$-a.e. point
of its support is rectifiable: the support is $\mathcal{H}^n$-rectifiable
and $V$ equals $\theta\, \mathcal{H}^n$ on its support, with
$\theta(p) = \Theta(\|V\|, p) > 0$ for $\mathcal{H}^n$-a.e. $p$.

Reference: Allard 1972, Theorem 5.5(1); Simon 1984, Theorem 42.4.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- $V$ is rectifiable: there exists an $\mathcal{H}^n$-rectifiable subset
$\Sigma \subseteq \mathrm{spt}\|V\|$ and a non-negative function
$\theta\colon \Sigma \to \mathbb{R}$ representing $\|V\|$ as
$\theta\, \mathcal{H}^n \mres \Sigma$. -/
opaque IsRectifiable : Varifold M → Prop

/-- **Rectifiability theorem (Proposition 2.12).**
A stationary varifold with positive density $\|V\|$-a.e. on its support
is rectifiable. -/
theorem isRectifiable_of_isStationary_of_density_pos
    {V : Varifold M} (hstat : IsStationary V)
    (hpos : ∀ p ∈ support V, 0 < density V p) :
    IsRectifiable V := by sorry

end Varifold

end AltRegularity
