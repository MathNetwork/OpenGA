import GeometricMeasureTheory.Stationary
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.EMetricSpace.Lipschitz

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

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- A subset $S \subseteq M$ is **$\mathcal{H}^n$-rectifiable** iff
$$ S \subseteq \left( \bigcup_{i \in \mathbb{N}} f_i(A_i) \right) \cup N $$
where each $A_i \subseteq \mathbb{R}^n$ is bounded, each $f_i : \mathbb{R}^n
\to M$ is Lipschitz on $A_i$, and $\mathcal{H}^n(N) = 0$.

This is the standard Simon §11 / Federer §3.2.14 characterization
expressed with Mathlib's `LipschitzOnWith` and `hausdorffMeasure`.

**Ground truth**: Simon 1983 §11, Theorem 11.1 (Lipschitz-image
characterization); Federer 1969 §3.2.14.

**Used by**: `Varifold.IsRectifiable` def (in this file). -/
def IsHRectifiable (S : Set M) (n : ℕ) : Prop :=
  ∃ (A : ℕ → Set (Fin n → ℝ)) (f : ℕ → (Fin n → ℝ) → M)
    (K : ℕ → NNReal),
    (∀ i, Bornology.IsBounded (A i)) ∧
    (∀ i, LipschitzOnWith (K i) (f i) (A i)) ∧
    MeasureTheory.Measure.hausdorffMeasure (n : ℝ) (S \ ⋃ i, f i '' A i) = 0

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

end GeometricMeasureTheory
