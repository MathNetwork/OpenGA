import AltRegularity.Sweepout.MassCancellation
import AltRegularity.Regularity.AlphaStructural

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

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- The **boundary varifold** $|\partial^*\Omega|$ associated to a
finite-perimeter set: the rectifiable $n$-varifold supported on the
reduced boundary $\partial^*\Omega$ with multiplicity 1. -/
noncomputable opaque ofBoundary : FinitePerimeter M → Varifold M

/-- **(e) of paper §6.1 Theorem 6.3: $|\partial^*\Omega|$ is integral.**
The boundary varifold of any finite-perimeter set has integer
multiplicity (multiplicity 1 on the reduced boundary). -/
theorem isIntegral_ofBoundary (Ω : FinitePerimeter M) :
    IsIntegral (ofBoundary Ω) := by sorry

end Varifold

/-- **(d) of paper §6.1 Theorem 6.3: the De Lellis–Tasnady criterion
(Proposition 6.1).**

If a min-max sequence has weak measure convergence of distributional
derivatives (`DChiWeakConverge`) and perimeter convergence
(`PerimeterConverge`), the limit varifold $V$ equals the boundary
varifold of the limit slice $\Omega(t_0)$.

This is the precise content of Proposition A.1 in De Lellis–Tasnady
2013, packaged for the paper's min-max setup. -/
theorem dlt_criterion
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : Sweepout.MinMaxLimit Φ t₀ V)
    (hWeak : Sweepout.DChiWeakConverge Φ t₀)
    (hPer : Sweepout.PerimeterConverge Φ t₀) :
    V = Varifold.ofBoundary (Φ.slice t₀) := by sorry

end AltRegularity
