import MinMax.Sweepout.MassCancellation
import Regularity.AlphaStructural
import GeometricMeasureTheory
import MinMax
import Regularity

/-!
# AltRegularity.Integrality.PerimeterConvergence

The De Lellis–Tasnady varifold-vs-Caccioppoli convergence criterion
(Proposition 6.1 of the paper, citing De Lellis–Tasnady 2013
Proposition A.1), together with the boundary-varifold operation
`Varifold.ofBoundary` and its integrality.

These three primitives are the inputs needed to formalize Theorem 6.3
(Integrality without mass cancellation): given the convergence
hypotheses (a) weak distributional, (b) perimeter, the criterion
identifies the varifold limit as the boundary varifold of the limit
slice, which is integral by definition.
-/

namespace AltRegularity

open GeometricMeasureTheory GeometricMeasureTheory.Varifold GeometricMeasureTheory.FinitePerimeter Regularity Regularity.Varifold MinMax.Sweepout MinMax.Sweepout.Varifold
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- **(e) of paper §6.1 Theorem 6.3: $|\partial^*\Omega|$ is integral.**
The boundary varifold of any finite-perimeter set has integer
multiplicity (multiplicity 1 on the reduced boundary). -/
theorem isIntegral_ofBoundary (Ω : FinitePerimeter M) :
    IsIntegral (ofBoundary Ω) := by sorry

end Varifold

/-- **DLT13 Prop A.1 + uniqueness, applied form** ([DLT13, Prop A.1];
reproduced verbatim as paper §5 Proposition `prop:p2-DLT-integrality`).

DLT13 Prop A.1 verbatim (paper §5 line 8-15):
> Let $\{\Omega^k\}$ be a sequence of Caccioppoli sets and $U$ an open
> subset of $M$. Assume that
> (i) $D\chi_{\Omega^k} \to D\chi_\Omega$ in the sense of measures in $U$;
> (ii) $\mathrm{Per}(\Omega^k, U) \to \mathrm{Per}(\Omega, U)$
> for some Caccioppoli set $\Omega$. Then the varifolds
> $|\partial^*\Omega^k|$ converge to $|\partial^*\Omega|$ in the sense
> of varifolds.

The Lean statement combines DLT13 Prop A.1 with **uniqueness of weak
varifold limits**: given `hlim` (the min-max sequence converges to V)
and (i)+(ii), DLT13 gives a second weak limit $|\partial^*\Omega(t_0)|$;
uniqueness of weak limits identifies $V = |\partial^*\Omega(t_0)|$.
This is the combined form paper §5 uses in the proof of Theorem
`thm:integrality(a)`: "Both conditions of Proposition A.1 are satisfied,
so $V$ is the integral varifold induced by the Caccioppoli boundary
$\partial^*\Omega(x_0)$."

Signature-level paper-faithful: matches paper §5 USAGE pattern in the
integrality-theorem proof. The DLT13 verbatim form (convergence-only)
is recoverable by stripping `hlim` and recasting via `VarifoldConverge`,
but is not separately exposed since the chain only consumes the
equality form.

**Used by**: `integrality_no_cancellation` (chain proof step (d) of
paper §6.1 Theorem 6.3 / paper §5 Theorem `thm:integrality(a)`). -/
theorem dlt_criterion
    {Φ : MinMax.Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : MinMax.Sweepout.MinMaxLimit Φ t₀ V)
    (hWeak : MinMax.Sweepout.DChiWeakConverge Φ t₀)
    (hPer : MinMax.Sweepout.PerimeterConverge Φ t₀) :
    V = Varifold.ofBoundary (Φ.slice t₀) := by sorry

end AltRegularity
