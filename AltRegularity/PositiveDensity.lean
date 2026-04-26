import AltRegularity.Integrality.ReducedBoundary
import AltRegularity.Sweepout.NonExcessive

/-!
# AltRegularity.PositiveDensity

Positive density on the support of the min-max varifold limit, deduced
from the existence of a sweepout-wide replacement at every zero-density
point. This is the content of Section 5.1 of the paper.

The deduction uses three auxiliary facts (formalized in companion files):
  * `density_lower_bound_rbdy` (`AltRegularity.Integrality.ReducedBoundary`)
  * `FinitePerimeter.trichotomy`   (`AltRegularity.GMT.FinitePerimeter`)
  * `Sweepout.outside_closure_not_in_spt` (`AltRegularity.Sweepout.MinMaxLimit`)

Given these, the implication
`SweepoutWideReplacement ⟹ PositiveDensityOnSupport`
is a finite logical chain that Lean checks formally.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Sweepout-wide replacement (statement, open).**
Under the hypotheses of a non-excessive ONVP sweepout with a min-max limit
$V$, a point $p \in \mathrm{spt}\|V\|$ in the topological interior of the
limit slice $\Omega_{t_0}$ at zero density admits an $I$-replacement at $t_0$.

This statement packages the existence of a family $\{\Omega^*_t\}$
satisfying:
  (1) Locality outside $B_r(p)$;
  (2) $\mathrm{Per}(\Omega^*_t) \le \mathrm{Per}(\Omega_t)$ for every $t$;
  (3) Strict mass decrease in the limit on $B_r(p)$;
plus admissibility ($\mathcal{F}$-continuity, ONVP-nested), into the single
predicate `Sweepout.IReplacementExists Φ t₀`. -/
def SweepoutWideReplacement (Φ : Sweepout M) (t₀ : ℝ) (V : Varifold M) (p : M) : Prop :=
  Sweepout.NonExcessive Φ → Sweepout.ONVP Φ → Sweepout.Critical Φ t₀ →
    Sweepout.MinMaxLimit Φ t₀ V →
    p ∈ Varifold.support V → p ∈ (Φ.slice t₀).topInterior →
    Varifold.density V p = 0 →
    Sweepout.IReplacementExists Φ t₀

/-- **Positive density at every $p \in \mathrm{spt}\|V\|$.**
The published statement reads "$\|V\|$-a.e. $p$"; the everywhere version
(used here) follows from the monotonicity formula for stationary varifolds. -/
def PositiveDensityOnSupport (V : Varifold M) (p : M) : Prop :=
  p ∈ Varifold.support V → 0 < Varifold.density V p

/-- **Main implication: sweepout-wide replacement implies positive density on
the support.**

The proof mirrors the LaTeX argument in Section 5.1 of the paper:

1. By contradiction, assume $\Theta(\|V\|, p) \le 0$. With non-negativity of
   density, this forces $\Theta(\|V\|, p) = 0$.
2. Trichotomy on $p$ relative to the limit slice $\Omega_{t_0}$
   (`FinitePerimeter.trichotomy`):
     * Case 1: $p$ outside $\overline{\Omega_{t_0}}$. Then $p \notin \mathrm{spt}\|V\|$
       (`Sweepout.outside_closure_not_in_spt`), contradicting the hypothesis.
     * Case 2a: $p$ on $\partial^*\Omega_{t_0}$. The lower bound gives
       $\Theta \ge 1$ (`density_lower_bound_rbdy`), contradicting $\Theta = 0$.
     * Case 2b: $p$ in $\mathrm{int}(\Omega_{t_0})$. Apply
       `SweepoutWideReplacement` to obtain an $I$-replacement; this makes
       $t_0$ excessive (`Sweepout.ireplacement_to_excessive`), contradicting
       non-excessiveness (`Sweepout.non_excessive_def`). -/
theorem positiveDensity_of_sweepoutWideReplacement
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M} {p : M}
    (hne : Sweepout.NonExcessive Φ) (honvp : Sweepout.ONVP Φ)
    (hcrit : Sweepout.Critical Φ t₀) (hlim : Sweepout.MinMaxLimit Φ t₀ V)
    (hReplacement : SweepoutWideReplacement Φ t₀ V p) :
    PositiveDensityOnSupport V p := by
  intro hp_spt
  by_contra hΘ
  push Not at hΘ
  -- hΘ : density V p ≤ 0; with non-negativity, density V p = 0.
  have hΘ0 : Varifold.density V p = 0 :=
    le_antisymm hΘ (Varifold.density_nonneg V p)
  rcases (Φ.slice t₀).trichotomy p with hout | hb | hint
  · -- Case 1: p outside closure(Ω_{t₀}).
    exact Sweepout.outside_closure_not_in_spt honvp hlim hout hp_spt
  · -- Case 2a: p on ∂*Ω_{t₀} ⟹ density ≥ 1, contradiction.
    have h1 : 1 ≤ Varifold.density V p :=
      density_lower_bound_rbdy hp_spt hb hlim
    linarith
  · -- Case 2b: p in int(Ω_{t₀}) ⟹ apply the sweepout-wide replacement
    -- to obtain a 2-sided I-replacement at t₀ (paper §5.1 — `Left ∧ Right`),
    -- which contradicts non-excessiveness directly.
    have hIRep : Sweepout.IReplacementExists Φ t₀ :=
      hReplacement hne honvp hcrit hlim hp_spt hint hΘ0
    exact Sweepout.non_excessive_def hne t₀ hcrit hIRep

end AltRegularity
