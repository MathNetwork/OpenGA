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

/-- $x \in \mathfrak{m}_L(\Phi)$: $x$ is a **left-critical parameter**
(paper §3 Def 3.3 / [CLS22, Def 1.5]): there is a strictly increasing
sequence $x_i \nearrow x$ with $\mathbf{M}(\Phi(x_i)) \to W$. -/
def LeftCritical (Φ : Sweepout M) (x : ℝ) : Prop :=
  ∃ tᵢ : ℕ → ℝ, StrictMono tᵢ ∧
    Filter.Tendsto tᵢ Filter.atTop (nhds x) ∧
    Filter.Tendsto (fun i => ((Φ.slice (tᵢ i)).perim : ℝ))
      Filter.atTop (nhds (width Φ))

/-- $x \in \mathfrak{m}_R(\Phi)$: $x$ is a **right-critical parameter**
(paper §3 Def 3.3 / [CLS22, Def 1.5]): there is a strictly decreasing
sequence $x_i \searrow x$ with $\mathbf{M}(\Phi(x_i)) \to W$. -/
def RightCritical (Φ : Sweepout M) (x : ℝ) : Prop :=
  ∃ tᵢ : ℕ → ℝ, StrictAnti tᵢ ∧
    Filter.Tendsto tᵢ Filter.atTop (nhds x) ∧
    Filter.Tendsto (fun i => ((Φ.slice (tᵢ i)).perim : ℝ))
      Filter.atTop (nhds (width Φ))

/-- Paper §3 Def 3.3 last sentence: $\mathfrak{m}(\Phi) = \mathfrak{m}_L
(\Phi) \cup \mathfrak{m}_R(\Phi)$ — every critical parameter is either
left-critical or right-critical (and may be both). -/
theorem critical_iff_left_or_right (Φ : Sweepout M) (t : ℝ) :
    Critical Φ t ↔ LeftCritical Φ t ∨ RightCritical Φ t := by sorry

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

/-- An **$I$-replacement exists at $t_0$** (paper §6.2 chord-beats-arc /
§5.1 sweepout-wide replacement, both 2-sided constructions): the chord
construction and Federer-filling produce a flat-continuous family on
$(t_0 - \varepsilon, t_0 + \varepsilon)$ matching $\Phi$ at the
endpoints with strict perimeter drop on **both sides** simultaneously.
Hence $t_0$ is both left-excessive **and** right-excessive.

Encoded as a conjunction `LeftExcessiveAt ∧ RightExcessiveAt` to match
the paper's actual 2-sided construction (paper §6.2 Step 3 and §5.1).
The previous disjunctive form was a strict under-statement. -/
def IReplacementExists (Φ : Sweepout M) (t₀ : ℝ) : Prop :=
  LeftExcessiveAt Φ t₀ ∧ RightExcessiveAt Φ t₀

/-! ## Non-excessive (paper Def 3.4 / Theorem 2.2) -/

/-- $\Phi$ is **non-excessive (framework form)**: no critical parameter
admits a 2-sided $I$-replacement.

The forbidden configuration is `IReplacementExists Φ t` (the conjunction
`LeftExcessive ∧ RightExcessive`), which is what paper §6.2 chord-beats-arc
and paper §5.1 sweepout-wide replacement *actually* construct. This is
the form the chain proofs naturally consume.

The paper-faithful **strict** form is `NonExcessiveStrict` (paper §3
line 226 verbatim, separated by critical side); this framework form is
derived from the strict form via `nonExcessive_of_strict`. -/
def NonExcessive (Φ : Sweepout M) : Prop :=
  ∀ t : ℝ, Critical Φ t → ¬ IReplacementExists Φ t

/-- $\Phi$ is **non-excessive (strict / paper-faithful form)** —
verbatim paper §3 line 226 / [CLS22, Theorem `c:non-excessive_minmax`]:

> A sweepout is non-excessive if no critical point is excessive **on
> its critical side**.

That is:
  * every left-critical parameter is not left-excessive, and
  * every right-critical parameter is not right-excessive.

This is the form CLS22 actually establishes (`c:non-excessive_minmax`).
The framework's `NonExcessive` is derived from it via
`nonExcessive_of_strict`, exploiting the 2-sided structure of
`IReplacementExists` (paper §6.2 / §5.1). -/
def NonExcessiveStrict (Φ : Sweepout M) : Prop :=
  (∀ t, LeftCritical Φ t → ¬ LeftExcessiveAt Φ t) ∧
  (∀ t, RightCritical Φ t → ¬ RightExcessiveAt Φ t)

/-- A non-excessive sweepout has no critical point admitting a 2-sided
$I$-replacement. Definitional unfolding. -/
theorem non_excessive_def {Φ : Sweepout M} (h : NonExcessive Φ) (t : ℝ)
    (hcrit : Critical Φ t) : ¬ IReplacementExists Φ t :=
  h t hcrit

/-- **Bridge: paper-faithful strict form implies framework form.**

Argument:
  * `IReplacementExists Φ t = LeftExcessive Φ t ∧ RightExcessive Φ t`
    (paper §6.2 / §5.1 — 2-sided construction);
  * `Critical Φ t ↔ LeftCritical Φ t ∨ RightCritical Φ t`
    (paper §3 Def 3.3, $\mathfrak{m} = \mathfrak{m}_L \cup \mathfrak{m}_R$);
  * either disjunct of `LeftCritical ∨ RightCritical` contradicts the
    matching side of `LeftExcessive ∧ RightExcessive` via the strict
    form.

This bridge is the formal version of "the framework's unified
`NonExcessive` is what you actually get from the paper-faithful
separated form, given that I-replacements are 2-sided." -/
theorem nonExcessive_of_strict {Φ : Sweepout M}
    (h : NonExcessiveStrict Φ) : NonExcessive Φ := by
  intro t hcrit hIRep
  obtain ⟨hLeftExc, hRightExc⟩ := hIRep
  rcases (critical_iff_left_or_right Φ t).mp hcrit with hLCrit | hRCrit
  · exact h.1 t hLCrit hLeftExc
  · exact h.2 t hRCrit hRightExc

/-- An $I$-replacement at a critical parameter makes that parameter
excessive (in the paper Def 3.4 disjunctive sense). Direct from the
conjunctive form of `IReplacementExists`: `Left ∧ Right` projects to
`Left ∨ Right`. -/
theorem ireplacement_to_excessive {Φ : Sweepout M} {t₀ : ℝ}
    (h : IReplacementExists Φ t₀) (_hcrit : Critical Φ t₀) :
    ExcessiveAt Φ t₀ :=
  Or.inl h.1

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

**Paper-faithful return type**: this theorem returns
`NonExcessiveStrict Φ`, the separated form that CLS22 actually
establishes. Downstream chain consumers bridge to the framework's
`NonExcessive Φ` (which forbids 2-sided I-replacement at critical
points) via `nonExcessive_of_strict`. -/
theorem exists_nonExcessive_ONVP (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    (n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6) :
    ∃ Φ : Sweepout M, NonExcessiveStrict Φ ∧ ONVP Φ ∧ 0 < width Φ := by sorry

end Sweepout

end AltRegularity
