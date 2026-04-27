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
on an $\mathcal{H}^{V.dim}$-rectifiable subset of $M$.

Defined explicitly as an existential over a rectifiable carrier $S$
with $\|V\|(S^c) = 0$, using the varifold's intrinsic dimension
`V.dim`. -/
def IsRectifiable (V : Varifold M) : Prop :=
  ∃ S : Set M, IsHRectifiable S V.dim ∧ V.massMeasure Sᶜ = 0

/-- **Rectifiability theorem** ([Allard 1972, Theorem 5.5(1)];
[Simon 1984, Theorem 42.4]; reproduced as paper §2 Proposition
`prop:allard-rectifiability`).

Verbatim paper §2 statement (`paper/chapters/part2/2-preliminaries.tex:96`):
> Let $V$ be a stationary $n$-varifold in $(M^{n+1}, g)$ with
> $\Theta(\|V\|, p) > 0$ for $\|V\|$-a.e. $p$. Then $V$ is rectifiable:
> $V = \underline{v}(\Sigma, \theta)$ where $\Sigma \subset \spt\|V\|$
> is $\mathcal{H}^n$-rectifiable and
> $\theta(p) = \Theta(\|V\|, p) > 0$ for $\mathcal{H}^n$-a.e. $p \in \Sigma$.

The Lean signature uses the **a.e.-density-positive** hypothesis
(`∀ᵐ p ∂V.massMeasure, 0 < density V p`), matching paper §2 verbatim.
The conclusion `IsRectifiable V` packages the existence of a
$\mathcal{H}^n$-rectifiable carrier $\Sigma$ with $V$-mass concentrated
on it; the explicit multiplicity $\theta = \Theta(\|V\|, \cdot)$ is
recoverable from the carrier via the density (definition of
multiplicity for integer-rectifiable varifolds, Simon §38).

**Used by**: `integrality_with_cancellation` (paper §6.1 Theorem 6.3
case (b), via positive-density hypothesis from
`positiveDensity_of_sweepoutWideReplacement`). -/
theorem isRectifiable_of_isStationary_of_density_pos
    {V : Varifold M} (hstat : IsStationary V)
    (hpos : ∀ᵐ p ∂V.massMeasure, 0 < density V p) :
    IsRectifiable V := by sorry

end Varifold

end GeometricMeasureTheory
