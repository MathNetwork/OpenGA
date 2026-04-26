import AltRegularity.GMT.Varifold

/-!
# AltRegularity.GMT.Stationary

Stationary varifolds.

A varifold $V$ is stationary if its first variation $\delta V$ vanishes for
every compactly supported smooth vector field. Stationarity has two key
consequences used throughout the paper:
  * the **monotonicity formula** (Proposition 2.10): the rescaled mass
    $r \mapsto \|V\|(B_r(p))/r^n$ is monotone non-decreasing in $r$, so
    the density $\Theta(\|V\|, p)$ exists pointwise. The precise form
    requires a dimension parameter on `Varifold`, which is not yet
    threaded through the formalization.
  * the **rectifiability theorem** (Proposition 2.12, in
    `AltRegularity.GMT.Rectifiability`).
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- $V$ has vanishing first variation on every test vector field, i.e. $V$
is stationary. -/
opaque IsStationary : Varifold M → Prop

end Varifold

end AltRegularity
