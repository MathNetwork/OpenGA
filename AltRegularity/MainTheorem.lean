import AltRegularity.Integrality.Theorem
import MinMax.Sweepout.PullTight
import Regularity.SmoothRegularity
import AltRegularity.Regularity.AlphaStructuralVerification
import AltRegularity.Regularity.StabilityVerification
import AltRegularity.PositiveDensity
import GeometricMeasureTheory
import MinMax
import Regularity

/-!
# AltRegularity.MainTheorem

The main regularity theorem of the paper (Theorem 1.1).

**Theorem.** Let $(M^{n+1}, g)$ be a closed Riemannian manifold with
$n \ge 2$. Let $\Phi$ be a non-excessive ONVP sweepout, and let $V$ be
the varifold limit of a min-max sequence $t_i \to t_0$. Then $V$ is a
stationary $n$-varifold with $\|V\|(M) = W$.

  * **(a) No mass cancellation.** If $\mathrm{Per}(\Omega_{t_0}) = W$,
    then $V$ is integral and (for $2 \le n \le 6$) $\mathrm{spt}\|V\|$ is
    a smooth, closed, embedded minimal hypersurface.

  * **(b) Mass cancellation, conditional.** If $\mathrm{Per}(\Omega_{t_0}) < W$,
    then $V$ has the same regularity conclusion provided the cancelled
    mass is integral. This reduces (via the rectifiability theorem and
    the sheet decomposition) to `PositiveDensityOnSupport` on the
    cancellation locus, equivalently `SweepoutWideReplacement` (still
    open at the level of the sweepout-wide construction).

## Proof structure

Both cases share the same chain
`Stationary + Integral + Stable + AlphaStructural ⟹ InClassSAlpha ⟹
SmoothMinimalHypersurface`. The two cases differ only in how integrality
is obtained:

  * (a) directly from `integrality_no_cancellation`
        (DLT perimeter-convergence criterion);
  * (b) from `integrality_with_cancellation` after positive density on
        the support is supplied by `positiveDensity_of_sweepoutWideReplacement`.

Stability and the $\alpha$-structural hypothesis come from
non-excessiveness via Section 7 of the paper, recorded as the two private
bridges below.
-/

namespace AltRegularity

open GeometricMeasureTheory GeometricMeasureTheory.Varifold GeometricMeasureTheory.FinitePerimeter Regularity Regularity.Varifold MinMax.Sweepout MinMax.Sweepout.Varifold
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

-- Both Section 7 bridges are provided by chain-proof modules:
--   * `isStable_of_nonExcessive_minmax`
--     in `AltRegularity.Regularity.StabilityVerification` (paper §7.1)
--   * `alphaStructural_of_nonExcessive_minmax`
--     in `AltRegularity.Regularity.AlphaStructuralVerification` (paper §7.2)
-- The main theorems below consume them as black-box inputs.

/-! ## Theorem 1.1 -/

/-- **Theorem 1.1(a) — Main theorem, no-mass-cancellation case.**

Paper Theorem 1.1's "$2 \le n \le 6$" hypothesis on the codimension-1
ambient dimension is now threaded explicitly via `(n : ℕ) (hn : 2 ≤ n)
(hn6 : n ≤ 6)`, so paper §4 Theorem~\ref{thm:wickramasekera} (cited
verbatim) can be invoked through its "in particular" corollary.

Proof: chain stationarity (pull-tight), integrality (Theorem 6.1(a)),
stability and $\alpha$-structural (Section 7), then apply the smooth
regularity theorem for the class $\mathcal{S}_\alpha$ in the
$2 \le n \le 6$ case. -/
theorem main_theorem_no_cancellation
    {Φ : MinMax.Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6)
    (hne : MinMax.Sweepout.NonExcessive Φ) (honvp : MinMax.Sweepout.ONVP Φ)
    (hcrit : MinMax.Sweepout.Critical Φ t₀) (hlim : MinMax.Sweepout.MinMaxLimit Φ t₀ V)
    (hno : MinMax.Sweepout.NoMassCancellation Φ t₀) :
    Varifold.IsSmoothMinimalHypersurface V := by
  -- (1) Stationarity from pull-tight (CL03 / Proposition 3.7).
  have hstat : Varifold.IsStationary V :=
    MinMax.Sweepout.isStationary_of_minmaxLimit hlim
  -- (2) Integrality from Theorem 6.1(a) (DLT perimeter-convergence criterion).
  have hint : Varifold.IsIntegral V :=
    integrality_no_cancellation hlim hno
  -- (3) Stability from non-excessiveness (Section 7).
  have hstable : Varifold.IsStable V :=
    isStable_of_nonExcessive_minmax hne honvp hcrit hlim
  -- (4) α-structural hypothesis from non-excessiveness (Section 7).
  obtain ⟨α, hα0, hα1, hα⟩ :=
    alphaStructural_of_nonExcessive_minmax hne honvp hcrit hlim
  -- (5) Bundle into the class 𝒮_α.
  have hclass : Varifold.InClassSAlpha V α :=
    { stationary := hstat
      integral := hint
      stable := hstable
      alphaStructural := hα }
  -- (6) Apply the smooth regularity theorem for 𝒮_α at 2 ≤ n ≤ 6
  -- (paper §4 Theorem 4.4 "in particular" clause).
  exact Varifold.isSmoothMinimalHypersurface_of_inClassSAlpha
    ⟨hα0, hα1⟩ hn hn6 hclass

/-- **Theorem 1.1(b) — Main theorem, mass-cancellation case (conditional
on the sweepout-wide replacement).**

Paper Theorem 1.1's "$2 \le n \le 6$" hypothesis is threaded explicitly
via `(n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6)`.

Proof: identical chain to (a), except that integrality is obtained from
Theorem 6.1(b) after positive density on the support is supplied
pointwise by `positiveDensity_of_sweepoutWideReplacement`. -/
theorem main_theorem_with_cancellation
    {Φ : MinMax.Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6)
    (hne : MinMax.Sweepout.NonExcessive Φ) (honvp : MinMax.Sweepout.ONVP Φ)
    (hcrit : MinMax.Sweepout.Critical Φ t₀) (hlim : MinMax.Sweepout.MinMaxLimit Φ t₀ V)
    (hcanc : MinMax.Sweepout.MassCancellation Φ t₀)
    (hReplacement : ∀ p, SweepoutWideReplacement Φ t₀ V p) :
    Varifold.IsSmoothMinimalHypersurface V := by
  -- (1) Stationarity.
  have hstat : Varifold.IsStationary V :=
    MinMax.Sweepout.isStationary_of_minmaxLimit hlim
  -- (2a) Positive density on the support, pointwise from the formal
  -- proof in `AltRegularity.PositiveDensity`.
  have hposDensity : ∀ p ∈ Varifold.support V, 0 < Varifold.density V p :=
    fun p hp => positiveDensity_of_sweepoutWideReplacement
      hne honvp hcrit hlim (hReplacement p) hp
  -- (2b) Integrality from Theorem 6.1(b).
  have hint : Varifold.IsIntegral V :=
    integrality_with_cancellation hlim hcanc hposDensity
  -- (3) Stability from non-excessiveness.
  have hstable : Varifold.IsStable V :=
    isStable_of_nonExcessive_minmax hne honvp hcrit hlim
  -- (4) α-structural hypothesis from non-excessiveness.
  obtain ⟨α, hα0, hα1, hα⟩ :=
    alphaStructural_of_nonExcessive_minmax hne honvp hcrit hlim
  -- (5) Bundle into 𝒮_α.
  have hclass : Varifold.InClassSAlpha V α :=
    { stationary := hstat
      integral := hint
      stable := hstable
      alphaStructural := hα }
  -- (6) Apply the smooth regularity theorem at 2 ≤ n ≤ 6.
  exact Varifold.isSmoothMinimalHypersurface_of_inClassSAlpha
    ⟨hα0, hα1⟩ hn hn6 hclass

end AltRegularity
