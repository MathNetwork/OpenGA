import AltRegularity.Sweepout.HomotopicMinimization
import AltRegularity.Regularity.AlphaStructural
import AltRegularity.Regularity.SmoothRegularity

/-!
# AltRegularity.Regularity.StabilityVerification

Stability of the min-max varifold of a non-excessive ONVP sweepout
(Section 7.1, Proposition 7.1 of the paper).

## Strategy

Mirror of `AltRegularity.Regularity.AlphaStructuralVerification`:
both proofs derive their conclusion from non-excessiveness via a
five-step chain. For stability, the chain is the verbatim translation
of paper §7.1's proof:

  1. **(a)** $\mathfrak{h}_{\mathrm{nm}}(V)$ is finite ([CLS22, Proposition 3.1]).
  2. **(b)** Off $\mathfrak{h}_{\mathrm{nm}}(V)$, $V$ is one-sided
     homotopic minimizing in some ball $B_r(P)$.
  3. **(c)** One-sided homotopic minimization implies non-negative
     second variation locally:
     $\delta^2 V(\varphi, \varphi) \ge 0$ for $\varphi$ supported
     in $B_r(P)$.
  4. **(d)** Finite sets are $\mathcal{H}^n$-null (general fact).
  5. **(e)** Local stability off an $\mathcal{H}^n$-null set, plus a
     partition-of-unity argument, gives global stability.

The five sorry'd inputs are CLS22 / GMT prerequisites; the chain
itself is fully formalized.

## Local-property primitives

`Varifold.LocallyStable` is an explicit `def` so the docstring semantics
from paper §6.1 (paper sec. "Stability") are encoded directly into Lean
types. The companion local-property predicate
`Varifold.OneSidedMinimizingAt` and its leaf primitive
`Varifold.IsOneSidedCompetitor` live upstream in
`AltRegularity.Sweepout.HomotopicMinimization` (used by `Sweepout.hnm`).

The leaf primitive `Varifold.secondVariation` (in
`AltRegularity.GMT.SecondVariation`) is shared between the consume side
(`InClassSAlpha.stable` via `IsStable`) and the produce side
(`isStable_of_nonExcessive_minmax` via `LocallyStable`), giving a single
kernel-verified semantics.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-! ## Local-property definitions -/

/-- $V$ is **locally stable** at the point $P$ in the ball $B_r(P)$
(paper §6.1, paragraph after Prop. on stability): the second variation
$\delta^2 V(\varphi, \varphi) \ge 0$ for every smooth scalar normal
deformation $\varphi$ compactly supported in
$B_r(P) \setminus \mathrm{sing}\,V$.

Defined explicitly as a universally-quantified statement so that the
structure of "δ² ≥ 0 for all test functions on the ball away from
singularities" is visible to the Lean kernel. -/
def LocallyStable (V : Varifold M) (P : M) (r : ℝ) : Prop :=
  ∀ φ : M → ℝ, Function.support φ ⊆ Metric.ball P r \ sing V →
    0 ≤ secondVariation V φ

/-! ## Section 6.1 input lemmas -/

/-- **(b) of paper §7.1:** away from $\mathfrak{h}_{\mathrm{nm}}(V)$,
the limit varifold is one-sided homotopic minimizing in some
neighborhood. -/
theorem oneSidedMinimizing_off_hnm
    {V : Varifold M} (hFinite : (Sweepout.hnm V).Finite) :
    ∀ P ∈ support V \ Sweepout.hnm V, ∃ r > 0, OneSidedMinimizingAt V P r := by
  sorry

/-- **(c) of paper §7.1:** one-sided homotopic minimization implies
local stability. The second variation is non-negative for compactly
supported normal deformations in $B_r(P)$. -/
theorem locallyStable_of_oneSidedMinimizing
    {V : Varifold M}
    (h : ∀ P ∈ support V \ Sweepout.hnm V, ∃ r > 0, OneSidedMinimizingAt V P r) :
    ∀ P ∈ support V \ Sweepout.hnm V, ∃ r > 0, LocallyStable V P r := by
  sorry

/-- **(e) of paper §7.1:** local stability away from an $\mathcal{H}^n$-null
set extends to global stability via a partition-of-unity argument. -/
theorem isStable_of_locallyStable_offNullSet
    {V : Varifold M} {N : Set M} (hNullN : N.Finite)
    (hLocal : ∀ P ∈ support V \ N, ∃ r > 0, LocallyStable V P r) :
    IsStable V := by
  sorry

end Varifold

/-! ## Main verification: paper §7.1 chain proof -/

/-- **Stability of the min-max varifold (paper §7.1, Proposition 7.1).**

Mirror of `alphaStructural_of_nonExcessive_minmax`: both proofs derive
a regularity-input property from non-excessiveness via a chain of
black-box CLS22 / GMT lemmas. The chain proof here is verbatim from
paper §7.1's three-line proof:

  > "By [CLS22, Proposition 3.1], $\mathfrak{h}_{\mathrm{nm}}(V)$ is
  > finite. Therefore $V$ is one-sided homotopic minimizing in $B_r(P)$
  > for every $P \in \mathrm{spt}\|V\| \setminus \mathfrak{h}_{\mathrm{nm}}(V)$
  > and some $r = r(P) > 0$. One-sided homotopic minimization implies
  > $\delta^2 V(\varphi, \varphi) \ge 0$ for normal $\varphi$ supported
  > in $B_r(P)$. Since the finitely many points form an
  > $\mathcal{H}^n$-null set, partition of unity extends stability
  > globally."

-/
theorem isStable_of_nonExcessive_minmax
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : Sweepout.NonExcessive Φ) (honvp : Sweepout.ONVP Φ)
    (hcrit : Sweepout.Critical Φ t₀)
    (hlim : Sweepout.MinMaxLimit Φ t₀ V) :
    Varifold.IsStable V := by
  -- (a) hnm(V) is finite, by paper §6.1 / CLS22 propositions.
  -- Paper §6.1 explicitly notes: finiteness needs both NonExcessive
  -- AND ONVP (nestedness).
  have hHnmFinite : (Sweepout.hnm V).Finite :=
    Sweepout.hnm_finite_of_nonExcessive hne honvp hcrit hlim
  -- (b) Off hnm(V), V is one-sided homotopic minimizing in some ball.
  have hOneSided := Varifold.oneSidedMinimizing_off_hnm hHnmFinite
  -- (c) One-sided homotopic minimization → local stability (δ²V ≥ 0).
  have hLocallyStable := Varifold.locallyStable_of_oneSidedMinimizing hOneSided
  -- (d) Finite ⟹ Hⁿ-null is implicit in `hHnmFinite`; (e) consumes it directly.
  -- (e) Local stability off the finite null set + partition of unity →
  -- global stability.
  exact Varifold.isStable_of_locallyStable_offNullSet hHnmFinite hLocallyStable

end AltRegularity
