import Sweepout.MinMaxLimit
import GeometricMeasureTheory.Stationary

open GeometricMeasureTheory

namespace Sweepout

/-!
# AltRegularity.Sweepout.PullTight

The pull-tight argument of Colding–De Lellis (Proposition 3.7 in the
paper; Proposition 1.4 in CL03):

Along any min-max sequence $t_i \to t_0 \in \mathfrak{m}(\Phi)$, the
varifold limit $V = \lim_i |\partial^*\Omega_{t_i}|$ is a **stationary**
$n$-varifold with total mass equal to the width $W(\Phi)$.
-/



variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]


/-- **Pull-tight gives stationarity.** The min-max limit varifold along a
non-excessive ONVP sweepout is stationary. -/
theorem isStationary_of_minmaxLimit
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : MinMaxLimit Φ t₀ V) : Varifold.IsStationary V := by sorry



end Sweepout
