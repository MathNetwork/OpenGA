import AltRegularity.Regularity.AlphaStructural

/-!
# AltRegularity.Regularity.SmoothRegularity

Smooth regularity for stable codimension-1 integral varifolds in the class
$\mathcal{S}_\alpha$ (Theorem 4.4 in the paper).

If $V \in \mathcal{S}_\alpha$ for some $\alpha \in (0, 1/2)$ on a smooth
Riemannian manifold of dimension $n+1 \ge 3$, with finite total mass,
then the singular set has small Hausdorff dimension:

  * $\mathrm{sing}\, V = \emptyset$ for $2 \le n \le 6$;
  * $\mathrm{sing}\, V$ is discrete for $n = 7$;
  * $\mathcal{H}^{n-7+\gamma}(\mathrm{sing}\, V) = 0$ for every $\gamma > 0$
    when $n \ge 8$.

In particular, for $2 \le n \le 6$, $\mathrm{spt}\|V\|$ is a smooth, closed,
embedded minimal hypersurface.

Reference: Wickramasekera 2014, Theorem 3.1; manifold version Theorem 6.1.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- Singular set of a varifold (the complement of the regular part where
$\mathrm{spt}\|V\|$ is locally a smooth embedded hypersurface). -/
opaque sing : Varifold M → Set M

/-- $\mathrm{spt}\|V\|$ is a smooth, closed, embedded minimal hypersurface
of $M$. -/
opaque IsSmoothMinimalHypersurface : Varifold M → Prop

/-- **Regularity in the class $\mathcal{S}_\alpha$ (Theorem 4.4).**
For an integral stable varifold satisfying the $\alpha$-structural
hypothesis with $0 < \alpha < 1/2$, the singular set is empty when
$2 \le n \le 6$ and the support is a smooth embedded minimal hypersurface. -/
theorem regularity_of_inClassSAlpha
    {V : Varifold M} {α : ℝ} (hα : 0 < α ∧ α < 1/2)
    (hclass : InClassSAlpha V α) :
    sing V = ∅ ∧ IsSmoothMinimalHypersurface V := by sorry

end Varifold

end AltRegularity
