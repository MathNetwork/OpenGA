import GeometricMeasureTheory.FinitePerimeter
import GeometricMeasureTheory
import MinMax
import Regularity

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

open GeometricMeasureTheory GeometricMeasureTheory.Varifold GeometricMeasureTheory.FinitePerimeter Regularity Regularity.Varifold MinMax.Sweepout MinMax.Sweepout.Varifold
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

namespace FinitePerimeter

/-- $\Omega$ is locally one-sided **inner** $\varepsilon$-almost area
minimizing in the open set $U$ (paper §5.1 Definition 5.1, inner
variant): for every inner competitor $F \subseteq \Omega$ with
$F \,\triangle\, \Omega \subseteq U$,
$\mathrm{Per}(\Omega, U) \le \mathrm{Per}(F, U) + \varepsilon$.

The full paper §5.1 Definition 5.1 quantifies over every $q \in U$ and
$\rho > 0$ with $B_\rho(q) \Subset U$, and uses the $\varepsilon \rho^n$
scaling. The locale-level form below captures the geometric content
(inner perimeter cannot be improved by more than $\varepsilon$ via inner
modification supported in $U$); the $q,\rho$-localization and the $\rho^n$
scaling are paper-internal refinements requiring an ambient dimension
parameter on `FinitePerimeter`.

**Ground truth**: Pitts 1981 §3.7 (almost-minimizing varifolds, inner
side); paper §5.1 Definition 5.1; CLS22 Def 1.10 ($\varepsilon = 0$
case). -/
def IsInnerAlmostMinimizer (Ω : FinitePerimeter M) (U : Set M) (ε : ℝ) : Prop :=
  ∀ F : FinitePerimeter M,
    F.carrier ⊆ Ω.carrier →
    symmDiff F.carrier Ω.carrier ⊆ U →
    (Ω.perimOn U : ℝ) ≤ (F.perimOn U : ℝ) + ε

/-- $\Omega$ is locally one-sided **outer** $\varepsilon$-almost area
minimizing in the open set $U$ (paper §5.1 Definition 5.1, outer
variant): symmetric to `IsInnerAlmostMinimizer` with the competitor
condition $\Omega \subseteq F$.

**Ground truth**: Pitts 1981 §3.7 (outer side); paper §5.1 Definition
5.1; CLS22 Def 1.10. -/
def IsOuterAlmostMinimizer (Ω : FinitePerimeter M) (U : Set M) (ε : ℝ) : Prop :=
  ∀ F : FinitePerimeter M,
    Ω.carrier ⊆ F.carrier →
    symmDiff F.carrier Ω.carrier ⊆ U →
    (Ω.perimOn U : ℝ) ≤ (F.perimOn U : ℝ) + ε

end FinitePerimeter

end AltRegularity
