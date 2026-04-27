import MinMax.Sweepout.MinMaxLimit
import GeometricMeasureTheory
import MinMax
import Regularity

/-!
# AltRegularity.Integrality.ReducedBoundary

Density lower bound on the reduced boundary of the limit slice.

This is Lemma 6.4 in the paper: at a point $p$ of
$\partial^*\Omega_{t_0} \cap \mathrm{spt}\|V\|$ that is the varifold limit
of slice boundaries along a min-max sequence $t_i \nearrow t_0$, the
varifold density satisfies $\Theta(\|V\|, p) \ge 1$.

The proof in the paper uses lower semicontinuity of total variation and
the fact that $|D\chi_{\Omega_{t_0}}| \le \|V\|$ as Radon measures. The
formalization is deferred.
-/

namespace AltRegularity

open GeometricMeasureTheory GeometricMeasureTheory.Varifold GeometricMeasureTheory.FinitePerimeter Regularity Regularity.Varifold MinMax.Sweepout MinMax.Sweepout.Varifold
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- **Density lower bound on the reduced boundary (Lemma 6.4).**
At a point of $\partial^*\Omega_{t_0} \cap \mathrm{spt}\|V\|$ that is the
varifold limit of slice boundaries along a min-max sequence $t_i \nearrow t_0$,
the varifold density is $\ge 1$. -/
theorem density_lower_bound_rbdy
    {V : Varifold M} {p : M} {Φ : MinMax.Sweepout M} {t₀ : ℝ}
    (hp : p ∈ Varifold.support V) (hbdy : p ∈ FinitePerimeter.rbdy (Φ.slice t₀))
    (hlim : MinMax.Sweepout.MinMaxLimit Φ t₀ V) :
    1 ≤ Varifold.density V p := by sorry

end AltRegularity
