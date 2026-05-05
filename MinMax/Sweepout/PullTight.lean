import MinMax.Sweepout.MinMaxLimit
import GeometricMeasureTheory.Stationary

open GeometricMeasureTheory
open MinMax

namespace MinMax.Sweepout

/-!
# AltRegularity.Sweepout.PullTight

The pull-tight argument of Colding–De Lellis (Proposition 3.7 in the
paper; Proposition 1.4 in CL03):

Along any min-max sequence $t_i \to t_0 \in \mathfrak{m}(\Phi)$, the
varifold limit $V = \lim_i |\partial^*\Omega_{t_i}|$ is a **stationary**
$n$-varifold with total mass equal to the width $W(\Phi)$.
-/



variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]


/-- **Pull-tight gives stationarity** — stationarity component of
paper §3 Proposition `thm:CLS-stationary` ([CL03, Proposition 1.4]).

Verbatim paper §3 statement (`paper/chapters/part2/3-sweepouts.tex:236-237`):
> Let $(M^{n+1},g)$ be a closed Riemannian manifold with $n \geq 2$,
> and let $\Phi$ be an optimal sweepout with $\sup_x \mathbf{M}(\Phi(x)) = W$.
> Then there exists a **stationary** $n$-varifold $V$ in $M$ with
> $\mathbf{M}(V) = W$.

Paper §3 Prop 3.7 has two outputs: existence of $V$ (with critical
parameter, mass = W) and stationarity of $V$. Lean factors these:

  * Existence + mass: `exists_minmaxLimit` (Round 5 Item 5).
  * **Stationarity**: this theorem.

The factoring matches the chain proof's structure
(`main_theorem_no_cancellation` step 1 calls `isStationary_of_minmaxLimit hlim`
on the V from `exists_minmaxLimit`).

The hypothesis is just `MinMaxLimit Φ t₀ V` — the optimal-sweepout
context is already captured in `MinMaxLimit`'s convergence requirement
(V is built from a min-max sequence along $\Phi$, which carries the
optimality information through the `Critical` parameter at $t_0$).
Paper §3 line 240 explicitly notes: "The non-excessive condition is
not used here" — pull-tight stationarity does not require
non-excessiveness, only that V is a varifold limit along a min-max
sequence.

This is a black-box wrapper for the CL03 pull-tight argument. -/
theorem isStationary_of_minmaxLimit
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : MinMaxLimit Φ t₀ V) : Varifold.IsStationary V := by sorry



end MinMax.Sweepout
