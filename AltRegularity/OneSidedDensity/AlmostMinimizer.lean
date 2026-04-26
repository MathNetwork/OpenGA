import AltRegularity.GMT.FinitePerimeter

/-!
# AltRegularity.OneSidedDensity.AlmostMinimizer

One-sided $\varepsilon$-almost minimizers (Definition 5.1 in the paper).

A set of finite perimeter $\Omega$ is **one-sided inner $\varepsilon$-almost area
minimizing** in an open $U \subseteq M$ if for every $q \in U$, every
$\rho > 0$ with $B_\rho(q) \Subset U$, and every $F \subset \Omega$ with
$F \mathbin{\triangle} \Omega \Subset B_\rho(q)$,
$$\mathrm{Per}(\Omega, B_\rho(q)) \le \mathrm{Per}(F, B_\rho(q))
    + \varepsilon \rho^n.$$
The **outer** version requires the inequality with $F \supset \Omega$.
When $\varepsilon = 0$, this recovers the locally one-sided area-minimizing
notion of CLS22 Definition 1.10.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace FinitePerimeter

/-- $\Omega$ is locally one-sided **inner** $\varepsilon$-almost area
minimizing in the open set $U$.

**Ground truth**: Pitts 1981 §3.7 (almost-minimizing varifolds, inner
side); paper §5.1 Definition 5.1; CLS22 Def 1.10 ($\varepsilon = 0$
case). -/
opaque IsInnerAlmostMinimizer : FinitePerimeter M → Set M → ℝ → Prop

/-- $\Omega$ is locally one-sided **outer** $\varepsilon$-almost area
minimizing in the open set $U$.

**Ground truth**: Pitts 1981 §3.7 (outer side); paper §5.1 Definition
5.1; CLS22 Def 1.10. -/
opaque IsOuterAlmostMinimizer : FinitePerimeter M → Set M → ℝ → Prop

end FinitePerimeter

end AltRegularity
