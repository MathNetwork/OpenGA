import Sweepout.NonExcessive
import Sweepout.MinMaxLimit

open GeometricMeasureTheory

namespace Sweepout

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



variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- $K$ is a **one-sided competitor** for $V$ at the point $P$ in
radius $r$ (paper §3 Def 3.7 / [CLS22, Def 1.4], geometric content):

  * $K$ agrees with $\mathrm{spt}\|V\|$ outside $B_r(P)$, i.e.,
    $K \,\triangle\, \mathrm{spt}\|V\| \subseteq B_r(P)$;
  * $K$ is **one-sided** with respect to $\mathrm{spt}\|V\|$:
    either $K \subseteq \mathrm{spt}\|V\|$ (inner) or
    $\mathrm{spt}\|V\| \subseteq K$ (outer).

This captures the geometric inner/outer + symmetric-difference content
of paper §3 Def 3.7 verbatim. The third condition of paper Def 3.7
(connectedness via continuous family of Caccioppoli sets in $B_r(P)$)
is paper-internal homotopy data not encoded here; including it would
require a `Caccioppoli-homotopic` sub-predicate, which is left for a
future round when needed by chain proofs.

**Ground truth**: Pitts 1981 §3.7 (almost-minimizing competitor
surfaces); CLS22 §2 Def 1.4; paper §3 Def 3.7.

**Used by**: `Varifold.OneSidedMinimizingAt` def (in this file). -/
def IsOneSidedCompetitor (V : Varifold M) (K : FinitePerimeter M)
    (P : M) (r : ℝ) : Prop :=
  symmDiff K.carrier (Varifold.support V) ⊆ Metric.ball P r ∧
  (K.carrier ⊆ Varifold.support V ∨ Varifold.support V ⊆ K.carrier)

/-- $V$ is **one-sided homotopic minimizing** at $P$ in radius $r$
(paper Def 3.7 / [CLS22, Def 1.4]): for every one-sided homotopic
competitor $K$, the local mass of $V$ on $B_r(P)$ is bounded above by
$K$'s perimeter on $B_r(P)$.

Defined explicitly as a universally-quantified mass-perimeter
inequality, with the "one-sided ambient isotopy" content packaged into
the leaf primitive `IsOneSidedCompetitor`. -/
def OneSidedMinimizingAt (V : Varifold M) (P : M) (r : ℝ) : Prop :=
  ∀ K : FinitePerimeter M, IsOneSidedCompetitor V K P r →
    Varifold.massOn V (Metric.ball P r) ≤ FinitePerimeter.perimOn K (Metric.ball P r)

end Varifold


/-! ## Sweepout-level homotopic-minimizer property -/

/-- $\Phi$ at $t_0$ has the **inner homotopic-minimizer** property
(paper §3 Def 3.7 inner variant, sweepout-level lift): for every
varifold limit $V$ at $t_0$, every $P \in \mathrm{spt}\|V\|$ and every
radius $r > 0$, every inner one-sided competitor $K$ (with
$K \subseteq \mathrm{spt}\|V\|$) has perimeter at least the local mass
of $V$ on $B_r(P)$.

Defined explicitly via `Varifold.IsOneSidedCompetitor` (grounded), with
the inner specialization `K.carrier ⊆ V.support`.

**Ground truth**: paper §3 Def 3.7 inner variant; CLS22 §2 (Def 1.4);
Pitts 1981 §3.7. The Caccioppoli-homotopy condition omitted (matches
`IsOneSidedCompetitor`'s simplification). -/
def InnerHomotopicMinimizer (Φ : Sweepout M) (t₀ : ℝ) : Prop :=
  ∀ V : Varifold M, MinMaxLimit Φ t₀ V →
    ∀ P ∈ Varifold.support V, ∀ r > 0,
      ∀ K : FinitePerimeter M,
        Varifold.IsOneSidedCompetitor V K P r →
        K.carrier ⊆ Varifold.support V →
        Varifold.massOn V (Metric.ball P r) ≤
          FinitePerimeter.perimOn K (Metric.ball P r)

/-- $\Phi$ at $t_0$ has the **outer homotopic-minimizer** property
(paper §3 Def 3.7 outer variant): same as `InnerHomotopicMinimizer` but
with the outer specialization `V.support ⊆ K.carrier`.

**Ground truth**: paper §3 Def 3.7 outer variant; CLS22 §2 (Def 1.4);
Pitts 1981 §3.7. -/
def OuterHomotopicMinimizer (Φ : Sweepout M) (t₀ : ℝ) : Prop :=
  ∀ V : Varifold M, MinMaxLimit Φ t₀ V →
    ∀ P ∈ Varifold.support V, ∀ r > 0,
      ∀ K : FinitePerimeter M,
        Varifold.IsOneSidedCompetitor V K P r →
        Varifold.support V ⊆ K.carrier →
        Varifold.massOn V (Metric.ball P r) ≤
          FinitePerimeter.perimOn K (Metric.ball P r)

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

/-- **Finiteness of $\mathfrak{h}_{\mathrm{nm}}(V)$**
(paper §6.1 Proposition `prop:stability`, citing [CLS22] §3-§4
propositions: `p:pairs`, `p:def_thm` for the no-cancellation case,
`p:def-thm-cancel` for the cancellation case).

Paper §6.1 phrasing (verbatim, line 18):

> By [CLS22, Proposition 3.1], the set $\mathfrak{h}_{\mathrm{nm}}(V)$
> of non-homotopic-minimizing points is finite. ... We remark that the
> finiteness ... in [CLS22, Proposition 3.1] relies on both the
> non-excessive property **and the nestedness of the sweepout**: the
> proof constructs replacement families by "gluing in" one-sided
> homotopies, and nestedness ($\Omega(x_1) \subset \Omega(x_2)$)
> ensures that the parameter sets on which these replacements are
> defined are intervals.

CLS22 actual statements (combining no-cancellation and cancellation
cases in CLS22 §4):
  * **No cancellation** ([CLS22, Proposition `p:def_thm`(3)]):
    if $\mathfrak{h}_{\mathrm{nm}}(\Sigma)$ is non-empty, then
    $\mathcal{H}^0(\mathfrak{h}_{\mathrm{nm}}(\Sigma)) = 1$.
  * **Cancellation** ([CLS22, Proposition `p:def-thm-cancel`]):
    $\mathfrak{h}_{\mathrm{nm}}(V) = \emptyset$.

Paper §6.1 quotes only "finite"; framework follows paper. The stronger
"cardinality at most 1" CLS22 conclusion is documented here for future
tightening but not encoded in the Lean signature.

**Hypothesis on `NonExcessive` form**: the framework's `NonExcessive`
(forbid 2-sided `IReplacementExists`) is what the chain consumes; via
Option C bridge `nonExcessive_of_strict`, it is implied by the paper-
faithful `NonExcessiveStrict`. CLS22's actual hypothesis (e.g., in
`p:pairs` line 1396, "$x_0 \in \mathfrak{m}_L(\Phi)$" with "$\Phi$ is
not left excessive at $x_0$") is the separated form, equivalent via
the bridge.

**ONVP is required**: paper §6.1 explicitly notes the proof "relies on
both the non-excessive property and the nestedness of the sweepout";
adding `(honvp : ONVP Φ)` to the hypothesis is paper-faithful. -/
theorem hnm_finite_of_nonExcessive
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : NonExcessive Φ) (honvp : ONVP Φ) (hcrit : Critical Φ t₀)
    (hlim : MinMaxLimit Φ t₀ V) :
    (hnm V).Finite := by sorry



end Sweepout
