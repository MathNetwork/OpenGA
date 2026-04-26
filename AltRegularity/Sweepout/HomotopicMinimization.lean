import AltRegularity.Sweepout.NonExcessive
import AltRegularity.Sweepout.MinMaxLimit

/-!
# AltRegularity.Sweepout.HomotopicMinimization

One-sided homotopic minimization (paper Definition 3.7 / [CLS22, Def 1.4])
and the **set of non-homotopic-minimizing points** $\mathfrak{h}_{\mathrm{nm}}(V)$
(paper Definition 3.8 / [CLS22, Def 2.5]).

For a non-excessive ONVP sweepout, the slices at a critical parameter
$t_0$ have a homotopic-minimizer property: any one-sided ambient isotopy
of $\partial^*\Omega_{t_0}$ that does not increase $t$ beyond $t_0$ is
bounded below by the original perimeter. This property substitutes for
the classical almost-minimizing condition of Schoen–Simon (1981) and
provides the stability needed for the smooth regularity theorem.

## Definition style

`Varifold.OneSidedMinimizingAt` and `Sweepout.hnm` are explicit `def`s
over the leaf primitive `Varifold.IsOneSidedCompetitor`. The
sweepout-level `Sweepout.InnerHomotopicMinimizer` /
`OuterHomotopicMinimizer` predicates remain opaque pending a
formalization of the CLS22 sweepout-slice homotopic-minimizer property.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- $K$ is a **one-sided homotopic competitor** for $V$ at the point $P$
in radius $r$: $K$ is a finite-perimeter set obtained from $V$'s
support by a one-sided ambient isotopy supported in $B_r(P)$.

The two sides correspond to the inner ("$K \subseteq \mathrm{spt}\|V\|$
on $B_r$") and outer ("$K \supseteq \mathrm{spt}\|V\|$ on $B_r$")
versions; this single predicate quantifies over both. -/
opaque IsOneSidedCompetitor : Varifold M → FinitePerimeter M → M → ℝ → Prop

/-- $V$ is **one-sided homotopic minimizing** at $P$ in radius $r$
(paper Def 3.7 / [CLS22, Def 1.4]): for every one-sided homotopic
competitor $K$, the local mass of $V$ on $B_r(P)$ is bounded above by
$K$'s perimeter on $B_r(P)$.

Defined explicitly as a universally-quantified mass-perimeter
inequality, with the "one-sided ambient isotopy" content packaged into
the leaf primitive `IsOneSidedCompetitor`. -/
def OneSidedMinimizingAt (V : Varifold M) (P : M) (r : ℝ) : Prop :=
  ∀ K : FinitePerimeter M, IsOneSidedCompetitor V K P r →
    massOn V (Metric.ball P r) ≤ FinitePerimeter.perimOn K (Metric.ball P r)

end Varifold

namespace Sweepout

/-! ## Sweepout-level homotopic-minimizer property -/

/-- $\Phi$ at $t_0$ has the **one-sided homotopic-minimizer** property
on the inner side: the slice $\Omega_{t_0}$ is a homotopic perimeter
minimizer among ambient isotopies that do not enlarge it. -/
opaque InnerHomotopicMinimizer : Sweepout M → ℝ → Prop

/-- Outer homotopic-minimizer property (the symmetric version). -/
opaque OuterHomotopicMinimizer : Sweepout M → ℝ → Prop

/-- **Non-excessive ⟹ one-sided homotopic minimization.**
The non-excessive property at a critical $t_0$ implies the inner (and
outer) homotopic-minimizer property of the slice $\Omega_{t_0}$. -/
theorem innerHomotopicMinimizer_of_nonExcessive
    {Φ : Sweepout M} (h : NonExcessive Φ) (t₀ : ℝ) (hcrit : Critical Φ t₀) :
    InnerHomotopicMinimizer Φ t₀ := by sorry

/-- The outer companion of `innerHomotopicMinimizer_of_nonExcessive`. -/
theorem outerHomotopicMinimizer_of_nonExcessive
    {Φ : Sweepout M} (h : NonExcessive Φ) (t₀ : ℝ) (hcrit : Critical Φ t₀) :
    OuterHomotopicMinimizer Φ t₀ := by sorry

/-! ## Non-homotopic-minimizing points and their finiteness -/

/-- The **set of non-homotopic-minimizing points** $\mathfrak{h}_{\mathrm{nm}}(V)$
of the limit varifold $V$ (paper Def 3.8 / [CLS22, Def 2.5]): points
$P \in \mathrm{spt}\|V\|$ at which $V$ fails to be one-sided homotopic
minimizing in every neighborhood.

Defined explicitly via `Varifold.OneSidedMinimizingAt`, so the
"fails-at-every-radius" structure is visible to the Lean kernel. -/
def hnm (V : Varifold M) : Set M :=
  {P | P ∈ Varifold.support V ∧ ∀ r > 0, ¬ Varifold.OneSidedMinimizingAt V P r}

/-- **Finiteness of $\mathfrak{h}_{\mathrm{nm}}(V)$** ([CLS22, Proposition 3.1]).
For the limit varifold of a non-excessive ONVP sweepout, the set of
non-homotopic-minimizing points is finite. The finiteness uses both the
non-excessive property and the nestedness of the sweepout. -/
theorem hnm_finite_of_nonExcessive
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : NonExcessive Φ) (hcrit : Critical Φ t₀)
    (hlim : MinMaxLimit Φ t₀ V) :
    (hnm V).Finite := by sorry

end Sweepout

end AltRegularity
