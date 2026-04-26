import AltRegularity.Sweepout.Defs
import AltRegularity.Sweepout.ONVP
import Mathlib.Topology.Order.LiminfLimsup

/-!
# AltRegularity.Sweepout.NonExcessive

The non-excessive condition on a sweepout (paper Definition 3.4,
[CLS22, Def 2.1] / [CLS22, Theorem 2.2]).

## Concepts (paper §3)

  * **Critical mass** $M(x) := \limsup_{r \to 0} \{\mathbf{M}(\Phi(y))
    : |y-x| < r\}$ (paper Def 3.3).
  * **Critical parameter** $x \in \mathfrak{m}(\Phi)$: $M(x) = W$ (paper
    Def 3.3).
  * **$I$-replacement family** on an interval $(a, b)$: a flat-continuous
    family of finite-perimeter sets matching $\Phi$ at the endpoints with
    mass strictly less than $W$ on the open interior (paper Def 3.4).
  * **Excessive at $x$**: there exists an excessive interval extending
    to either side of $x$ (paper Def 3.4).
  * **Non-excessive sweepout**: no critical parameter is excessive
    (paper Def 3.4 / Theorem 2.2).

## Definition style

Each concept is an explicit `def` or `structure` so the structural
content from paper §3 is visible to the Lean kernel rather than hidden
in opaque predicates. The bridges `non_excessive_def` and
`ireplacement_to_excessive` reduce to definitional unfolding.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Sweepout

/-! ## Critical parameters (paper Def 3.3) -/

/-- The **critical mass** $M(x) := \limsup_{r \to 0} \{\mathbf{M}(\Phi(y))
: |y-x| < r\}$ at parameter $x$ (paper Def 3.3, [CLS22, Def 1.5]).

Defined explicitly as the limsup of slice perimeters along the
neighborhood filter of $x$. -/
noncomputable def criticalMass (Φ : Sweepout M) (x : ℝ) : ℝ :=
  Filter.limsup (fun y => ((Φ.slice y).perim : ℝ)) (nhds x)

/-- $x \in \mathfrak{m}(\Phi)$: $x$ is a **critical parameter**, i.e.,
$M(x) = W$ (paper Def 3.3).

Defined explicitly as the equality of the critical mass with the
width. -/
def Critical (Φ : Sweepout M) (x : ℝ) : Prop :=
  Sweepout.criticalMass Φ x = Sweepout.width Φ

/-! ## I-replacement family and excessive intervals (paper Def 3.4) -/

/-- An **$I$-replacement family** for $\Phi$ on the open interval
$(a, b)$ (paper Def 3.4, [CLS22, Def 2.1]):

  * $\mathcal{F}$-continuous on $[a, b]$,
  * matches $\Phi$ at the endpoints $a$ and $b$,
  * limsup mass on every interior point is strictly less than $W$.

Encoded as a structure so each constituent is named and accessible. -/
structure IReplacementFamily (Φ : Sweepout M) (a b : ℝ) where
  /-- The replacement family $x \mapsto \Omega^I(x)$. -/
  family : ℝ → FinitePerimeter M
  /-- Flat continuity on $[a, b]$. -/
  isFContinuous : Sweepout.FContinuous family
  /-- Endpoint match: $\Omega^I(a) = \Omega(a)$. -/
  endpoint_left : family a = Φ.slice a
  /-- Endpoint match: $\Omega^I(b) = \Omega(b)$. -/
  endpoint_right : family b = Φ.slice b
  /-- $\limsup_{(a,b) \ni y \to x} \mathbf{M}(\Phi^I(y)) < W$ for all
  interior points $x \in (a, b)$. -/
  perim_lt_width : ∀ x ∈ Set.Ioo a b,
    Filter.limsup (fun y => ((family y).perim : ℝ))
      (nhdsWithin x (Set.Ioo a b)) < width Φ

/-- The interval $(a, b)$ is **excessive** for $\Phi$ if an
$I$-replacement family exists on it (paper Def 3.4). -/
def IsExcessiveInterval (Φ : Sweepout M) (a b : ℝ) : Prop :=
  Nonempty (IReplacementFamily Φ a b)

/-- $x$ is **left excessive** for $\Phi$: there is an excessive interval
$(a, b)$ extending strictly to the left of $x$ with $x \le b$ (paper
Def 3.4). -/
def LeftExcessiveAt (Φ : Sweepout M) (x : ℝ) : Prop :=
  ∃ a b : ℝ, a < x ∧ x ≤ b ∧ IsExcessiveInterval Φ a b

/-- $x$ is **right excessive** for $\Phi$: there is an excessive
interval $(a, b)$ extending strictly to the right of $x$ with $a \le x$
(paper Def 3.4). -/
def RightExcessiveAt (Φ : Sweepout M) (x : ℝ) : Prop :=
  ∃ a b : ℝ, a ≤ x ∧ x < b ∧ IsExcessiveInterval Φ a b

/-- $x$ is **excessive** for $\Phi$: left or right excessive (paper
Def 3.4). -/
def ExcessiveAt (Φ : Sweepout M) (x : ℝ) : Prop :=
  LeftExcessiveAt Φ x ∨ RightExcessiveAt Φ x

/-- An **$I$-replacement exists at $t_0$**: $t_0$ is excessive on at
least one side. -/
def IReplacementExists (Φ : Sweepout M) (t₀ : ℝ) : Prop :=
  ExcessiveAt Φ t₀

/-! ## Non-excessive (paper Def 3.4 / Theorem 2.2) -/

/-- $\Phi$ is **non-excessive** if no critical parameter is excessive
(paper Def 3.4 / [CLS22, Theorem 2.2]).

Defined explicitly as a universally-quantified non-excessivity
condition over critical parameters. -/
def NonExcessive (Φ : Sweepout M) : Prop :=
  ∀ t : ℝ, Critical Φ t → ¬ ExcessiveAt Φ t

/-- A non-excessive sweepout has no excessive critical point.
This is the definitional content of `NonExcessive` (paper Def 3.4). -/
theorem non_excessive_def {Φ : Sweepout M} (h : NonExcessive Φ) (t : ℝ)
    (hcrit : Critical Φ t) : ¬ ExcessiveAt Φ t :=
  h t hcrit

/-- An $I$-replacement at a critical parameter makes that parameter
excessive (definitional unfolding: $I$-replacement existence is exactly
excessivity). -/
theorem ireplacement_to_excessive {Φ : Sweepout M} {t₀ : ℝ}
    (h : IReplacementExists Φ t₀) (_hcrit : Critical Φ t₀) :
    ExcessiveAt Φ t₀ :=
  h

/-! ## CLS22 existence theorem -/

/-- **Existence of non-excessive ONVP sweepouts**
(paper §3 Theorem~\ref{thm:non-excessive-existence}, citing
[CLS22, Theorem~\ref{c:non-excessive_minmax}]).

Paper §3 phrasing (verbatim):

> Let $(M^{n+1},g)$ be a closed Riemannian manifold with $2 \le n \le 6$.
> There exists an (ONVP) sweepout $\Psi$ such that every
> $x \in \mathfrak{m}_L(\Psi)$ is not left excessive and every
> $x \in \mathfrak{m}_R(\Psi)$ is not right excessive.

CLS22 phrasing of the same theorem:

> There exists a (ONVP) sweepout $\Psi$ such that every
> $x \in \mathfrak{m}_L(\Psi)$ is not left excessive and every
> $x \in \mathfrak{m}_R(\Psi)$ is not right excessive.

(CLS22 omits the "$2 \le n \le 6$" hypothesis — paper §3 adds it because
downstream regularity arguments require it.)

The strictly positive width $W(\Phi) > 0$ in the conclusion is from
isoperimetric inequality [DLT13, Proposition 0.5], cited in paper §3
Definition~\ref{def:p2-sweepout}.

**Note on `NonExcessive` form**: this theorem returns the framework's
unified `NonExcessive Φ` (`∀ t, Critical → ¬ ExcessiveAt`), which is
strictly stronger than CLS22's left/right separated form
(`m_L not left-excessive ∧ m_R not right-excessive`). See
`references/cite_verification.md` Item 5 for tightening notes. -/
theorem exists_nonExcessive_ONVP (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    (n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6) :
    ∃ Φ : Sweepout M, NonExcessive Φ ∧ ONVP Φ ∧ 0 < width Φ := by sorry

end Sweepout

end AltRegularity
