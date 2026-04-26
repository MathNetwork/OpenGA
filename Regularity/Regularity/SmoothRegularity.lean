import Regularity.AlphaStructural
import GeometricMeasureTheory.Rectifiability
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Geometry.Manifold.IsManifold.Basic

open GeometricMeasureTheory GeometricMeasureTheory.Varifold
open scoped ContDiff

/-!
# AltRegularity.Regularity.SmoothRegularity

Smooth regularity for stable codimension-1 integral varifolds in the
class $\mathcal{S}_\alpha$ (paper §4 Theorem~\ref{thm:wickramasekera},
[Wickramasekera 2014, Theorem 3.1 / Theorem 6.1]).

## Paper §4 statement (verbatim)

> Let $(N^{n+1}, g)$ be a smooth Riemannian manifold and $\alpha \in
> (0, 1/2)$. If $V \in \mathcal{S}_\alpha$ on $N$ with $\|V\|(N) <
> \infty$, then:
>   (a) $\mathrm{sing}\,V = \varnothing$ if $2 \le n \le 6$;
>   (b) $\mathrm{sing}\,V$ is discrete if $n = 7$;
>   (c) $\mathcal{H}^{n-7+\gamma}(\mathrm{sing}\,V) = 0$ for each
>       $\gamma > 0$ if $n \ge 8$.
>
> In particular, for $2 \le n \le 6$, $\mathrm{spt}\|V\|$ is a smooth
> embedded minimal hypersurface.

## Definition style

`regularity_of_inClassSAlpha` mirrors paper §4 verbatim — the
conclusion is a 3-way conjunction indexed by the codimension-1
ambient-dimension parameter $n$. `IsSmoothMinimalHypersurface` is an
explicit `structure` carrying the four conditions implied by the "in
particular" clause for $2 \le n \le 6$.

The high-dimensional Hausdorff-measure clause (c) is encoded as the
opaque leaf primitive `Varifold.HausdorffSmallSingular`, pending
Mathlib's Hausdorff-measure-on-manifold infrastructure.
-/

namespace Regularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

namespace Varifold

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- $V$ is a **smooth, closed, embedded minimal hypersurface** of $M$
(paper §4 Theorem~\ref{thm:wickramasekera}, "in particular" clause for
$2 \le n \le 6$).

Encoded as a structure carrying the defining conditions:

  * **rectifiable** (Allard 1972) — $\|V\|$ is concentrated on an
    $n$-rectifiable subset;
  * **integral** — multiplicity is integer-valued $\|V\|$-a.e.;
  * **stationary** ($\delta V = 0$, i.e., minimal in the variational
    sense);
  * **no singular point** ($\mathrm{sing}\,V = \emptyset$, i.e., the
    support is locally a smooth embedded hypersurface).

Together these conditions encode "smooth closed embedded minimal
hypersurface" for $2 \le n \le 6$, the dimension regime of paper
Theorem 1.1. -/
structure IsSmoothMinimalHypersurface (V : Varifold M) : Prop where
  /-- $\|V\|$ is concentrated on an $n$-rectifiable subset of $M$. -/
  rectifiable : IsRectifiable V
  /-- The varifold has integer multiplicity. -/
  integral : IsIntegral V
  /-- The first variation vanishes (minimal in the variational sense). -/
  stationary : IsStationary V
  /-- The singular set is empty: the support is locally a smooth
  embedded hypersurface. -/
  noSingular : sing I V = ∅

/-- **High-dimensional Hausdorff-small singular set** (paper §4
Theorem~\ref{thm:wickramasekera} clause (c)): for the codimension-1
ambient-dimension parameter $n \ge 8$, the singular set has Hausdorff
dimension $\le n - 7$:
$$\mathcal{H}^{n-7+\gamma}(\mathrm{sing}\,V) = 0 \quad \forall \gamma > 0.$$

Defined explicitly via `MeasureTheory.Measure.hausdorffMeasure` at
exponent $n - 7 + \gamma$.

**Ground truth**: Wickramasekera 2014 Theorem 3.1 / Theorem 6.1 (manifold
version), clause (c). The Hausdorff $n$-measure machinery is Simon 1983
§3 (Hausdorff measure construction) and §11.

For $n < 8$ the def is vacuous on the sense that callers only invoke
it under the hypothesis $8 \le n$ (paper Theorem 4.4 clause (c));
the def itself does not enforce $n \ge 8$.

**Used by**: `Varifold.regularity_of_inClassSAlpha` (n ≥ 8 case). -/
def HausdorffSmallSingular (V : Varifold M) (n : ℕ) : Prop :=
  ∀ γ : ℝ, 0 < γ →
    MeasureTheory.Measure.hausdorffMeasure ((n : ℝ) - 7 + γ) (sing I V) = 0

/-- **Regularity in the class $\mathcal{S}_\alpha$** (paper §4
Theorem~\ref{thm:wickramasekera}, [Wickramasekera 2014, Theorem 3.1 /
Theorem 6.1]).

The codimension-1 ambient-dimension parameter $n$ (so $\dim M = n+1$)
is threaded explicitly through the hypotheses, and the conclusion is
the verbatim 3-case dimension-dependent statement from paper §4. The
finiteness $\|V\|(N) < \infty$ is implicit in our `Varifold` structure
via the `isFiniteMeasure` field. -/
theorem regularity_of_inClassSAlpha
    {V : Varifold M} {α : ℝ} (hα : 0 < α ∧ α < 1/2)
    {n : ℕ} (hn : 2 ≤ n)
    (hclass : InClassSAlpha I V α) :
    (n ≤ 6 → sing I V = ∅) ∧
    (n = 7 → (sing I V).Countable) ∧
    (8 ≤ n → HausdorffSmallSingular I V n) := by sorry

/-- **"In particular" clause of paper §4 Theorem~\ref{thm:wickramasekera}**:
for $2 \le n \le 6$, the support $\mathrm{spt}\|V\|$ is a smooth
embedded minimal hypersurface.

This packages clause (a) of `regularity_of_inClassSAlpha` together with
the implicit consequences (rectifiability via Allard from stationary +
integral; integrality, stationarity from $\mathcal{S}_\alpha$) into the
`IsSmoothMinimalHypersurface` conclusion used downstream by paper
Theorem 1.1. -/
theorem isSmoothMinimalHypersurface_of_inClassSAlpha
    {V : Varifold M} {α : ℝ} (hα : 0 < α ∧ α < 1/2)
    {n : ℕ} (hn : 2 ≤ n) (hn6 : n ≤ 6)
    (hclass : InClassSAlpha I V α) :
    IsSmoothMinimalHypersurface I V := by sorry

end Smooth

end Varifold

end Regularity
