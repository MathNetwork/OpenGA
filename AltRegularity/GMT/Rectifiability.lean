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

## Definition style

`IsRectifiable` is an explicit `def` — there exists an $\mathcal{H}^n$-rectifiable
subset $\Sigma$ supporting $\|V\|$ — built on top of the leaf primitive
`IsHRectifiable` (countable union of Lipschitz images of $\mathbb{R}^n$).
The leaf primitive remains opaque pending Mathlib-level GMT infrastructure.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- A subset $S \subseteq M$ is **$\mathcal{H}^n$-rectifiable** iff it
is the countable union of Lipschitz images of bounded subsets of
$\mathbb{R}^n$, modulo an $\mathcal{H}^n$-null set.

Pending Mathlib's rectifiable-set infrastructure, this predicate is
left opaque. -/
opaque IsHRectifiable : Set M → ℕ → Prop

namespace Varifold

/-- $V$ is **rectifiable** iff its mass measure $\|V\|$ is concentrated
on an $\mathcal{H}^n$-rectifiable subset of $M$ for some $n$.

Defined explicitly as an existential over a rectifiable carrier $S$
with $\|V\|(S^c) = 0$. The dimension $n$ is left existentially
quantified pending a varifold-dimension parameter on `Varifold` itself. -/
def IsRectifiable (V : Varifold M) : Prop :=
  ∃ (n : ℕ) (S : Set M), IsHRectifiable S n ∧ V.massMeasure Sᶜ = 0

/-- **Rectifiability theorem (Proposition 2.12).**
A stationary varifold with positive density $\|V\|$-a.e. on its support
is rectifiable. -/
theorem isRectifiable_of_isStationary_of_density_pos
    {V : Varifold M} (hstat : IsStationary V)
    (hpos : ∀ p ∈ support V, 0 < density V p) :
    IsRectifiable V := by sorry

end Varifold

end AltRegularity
