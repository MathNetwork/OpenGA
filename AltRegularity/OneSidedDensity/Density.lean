import AltRegularity.OneSidedDensity.AlmostMinimizer
import AltRegularity.GMT.Varifold

/-!
# AltRegularity.OneSidedDensity.Density

Density from one-sided almost minimality (Lemma 5.8 in the paper).

If a sequence of sets of finite perimeter $\Omega_i$ is uniformly one-sided
$\varepsilon$-almost area-minimizing on a ball $B_R(p)$ for $\varepsilon$
sufficiently small, and the boundaries $|\partial^* \Omega_i|$ converge
as varifolds to $V$, then the limit varifold has positive density at $p$.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- **Density from one-sided almost minimality (Lemma 5.8).**
Given $|\partial^*\Omega_i| \to V$ with each $\Omega_i$ uniformly one-sided
$\varepsilon$-almost minimizing in $B_R(p)$ for sufficiently small $\varepsilon$,
the limit varifold has $\Theta(\|V\|, p) > 0$. -/
theorem density_pos_of_oneSided_AM
    {V : Varifold M} {p : M} (hp : p ∈ Varifold.support V) :
    -- Hypothesis on a sequence Ω_i is deferred to the precise statement.
    0 < Varifold.density V p := by sorry

end AltRegularity
