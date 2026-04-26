import AltRegularity.GMT.Stationary

/-!
# AltRegularity.Regularity.AlphaStructural

The $\alpha$-structural hypothesis and the class $\mathcal{S}_\alpha$
(Section 4.1 in the paper, following Wickramasekera 2014).

A stable codimension-1 integral varifold $V$ on an open subset $U$ of a
Riemannian manifold belongs to $\mathcal{S}_\alpha$ if it satisfies:

  (S1) **Stationarity:** $\delta V = 0$.
  (S2) **Stability:** the second variation is non-negative on the
       regular part for normal deformations supported in
       $\Omega \setminus \mathrm{sing}\,V$.
  (S3) **$\alpha$-structural hypothesis:** at each singular point $Z$,
       no neighborhood of $Z$ in $\mathrm{spt}\|V\|$ equals a finite
       union of $C^{1,\alpha}$ hypersurfaces-with-boundary sharing a
       common boundary through $Z$.

These conditions are the input to the smooth regularity theorem
(`AltRegularity.Regularity.SmoothRegularity`).
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- The integral varifold has integer multiplicity. -/
opaque IsIntegral : Varifold M → Prop

/-- Stability condition (S2): the second variation is non-negative on the
regular part for normal deformations supported away from the singular set. -/
opaque IsStable : Varifold M → Prop

/-- The $\alpha$-structural hypothesis (S3): no singular point is a junction
of $C^{1,\alpha}$ hypersurfaces-with-boundary along a common boundary. -/
opaque AlphaStructural : Varifold M → ℝ → Prop

/-- The class $\mathcal{S}_\alpha$ from Wickramasekera 2014: integral,
stationary, stable, and satisfies the $\alpha$-structural hypothesis. -/
structure InClassSAlpha (V : Varifold M) (α : ℝ) : Prop where
  /-- (S1) The varifold is stationary: $\delta V = 0$. -/
  stationary : IsStationary V
  /-- The varifold has integer multiplicity. -/
  integral : IsIntegral V
  /-- (S2) The second variation is non-negative on the regular part. -/
  stable : IsStable V
  /-- (S3) The $\alpha$-structural hypothesis at each singular point. -/
  alphaStructural : AlphaStructural V α

end Varifold

end AltRegularity
