import AltRegularity.Regularity.AlphaStructural
import AltRegularity.GMT.Rectifiability

/-!
# AltRegularity.Regularity.SmoothRegularity

Smooth regularity for stable codimension-1 integral varifolds in the class
$\mathcal{S}_\alpha$ (paper Theorem 4.4, [Wickramasekera 2014, Theorem 3.1
/ Theorem 6.1]).

If $V \in \mathcal{S}_\alpha$ for some $\alpha \in (0, 1/2)$ on a smooth
Riemannian manifold of dimension $n+1 \ge 3$, with finite total mass,
then the singular set has small Hausdorff dimension:

  * $\mathrm{sing}\, V = \emptyset$ for $2 \le n \le 6$;
  * $\mathrm{sing}\, V$ is discrete for $n = 7$;
  * $\mathcal{H}^{n-7+\gamma}(\mathrm{sing}\, V) = 0$ for every $\gamma > 0$
    when $n \ge 8$.

In particular, for $2 \le n \le 6$, $\mathrm{spt}\|V\|$ is a smooth, closed,
embedded minimal hypersurface.

## Definition style

`IsSmoothMinimalHypersurface` is an explicit `structure` with the
defining conditions: rectifiable, integral, stationary, no singular
point. The structural content of "smooth embedded minimal hypersurface"
is visible to the Lean kernel.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- $V$ is a **smooth, closed, embedded minimal hypersurface** of $M$
(paper Theorem 4.4 conclusion, the $2 \le n \le 6$ case).

Encoded as a structure carrying the defining conditions:

  * **rectifiable** (Allard 1972) — $\|V\|$ is concentrated on an
    $n$-rectifiable subset;
  * **integral** — multiplicity is integer-valued $\|V\|$-a.e.;
  * **stationary** ($\delta V = 0$, i.e., minimal in the variational sense);
  * **no singular point** ($\mathrm{sing}\,V = \emptyset$, i.e., the
    support is locally a smooth embedded hypersurface).

Together these conditions encode "smooth closed embedded minimal
hypersurface" for $2 \le n \le 6$, the dimension regime of the paper. -/
structure IsSmoothMinimalHypersurface (V : Varifold M) : Prop where
  /-- $\|V\|$ is concentrated on an $n$-rectifiable subset of $M$. -/
  rectifiable : IsRectifiable V
  /-- The varifold has integer multiplicity. -/
  integral : IsIntegral V
  /-- The first variation vanishes (minimal in the variational sense). -/
  stationary : IsStationary V
  /-- The singular set is empty: the support is locally a smooth
  embedded hypersurface. -/
  noSingular : sing V = ∅

/-- **Regularity in the class $\mathcal{S}_\alpha$** (paper Theorem 4.4,
[Wickramasekera 2014, Theorem 3.1 / Theorem 6.1]).

For an integral stable varifold satisfying the $\alpha$-structural
hypothesis with $0 < \alpha < 1/2$, the singular set is empty when
$2 \le n \le 6$ and the support is a smooth embedded minimal
hypersurface. -/
theorem regularity_of_inClassSAlpha
    {V : Varifold M} {α : ℝ} (hα : 0 < α ∧ α < 1/2)
    (hclass : InClassSAlpha V α) :
    sing V = ∅ ∧ IsSmoothMinimalHypersurface V := by sorry

end Varifold

end AltRegularity
