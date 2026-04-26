import AltRegularity.Sweepout.Defs

/-!
# AltRegularity.Sweepout.NonExcessive

The non-excessive condition on a sweepout (Definition 3.4 in the paper):
no critical parameter admits an $I$-replacement family producing a strict
width drop on a neighborhood. The supporting machinery records:
  * `Critical Φ t` — $t \in \mathfrak{m}(\Phi)$;
  * `ExcessiveAt Φ t` — there is an excessive interval around $t$;
  * `IReplacementExists Φ t₀` — the existence of a sweepout-wide
    replacement at $t_0$ (Section 5.1 of the paper).

The two structural facts used downstream are:
  * `non_excessive_def`     — non-excessive forbids excessive critical points;
  * `ireplacement_to_excessive` — an $I$-replacement at a critical point
    makes that point excessive.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Sweepout

/-- $t \in \mathfrak{m}(\Phi)$: $t$ is a critical parameter, i.e., the
width is realized at a min-max sequence approaching $t$. -/
opaque Critical : Sweepout M → ℝ → Prop

/-- The critical parameter $t_0$ is excessive in $\Phi$: there is an open
interval $J \ni t_0$ on which a competitor sweepout has $\limsup$ mass
strictly below $W$. -/
opaque ExcessiveAt : Sweepout M → ℝ → Prop

/-- An $I$-replacement family for $\Phi$ exists at the critical parameter
$t_0$: a flat-continuous, ONVP-nested $\Phi^*$ that strictly lowers the
limit varifold mass on a fixed ball at $t_0$ while not increasing
$\mathrm{Per}$ globally. -/
opaque IReplacementExists : Sweepout M → ℝ → Prop

/-- $\Phi$ is non-excessive: no critical parameter admits an $I$-replacement
producing a strict width drop on a neighborhood. -/
opaque NonExcessive : Sweepout M → Prop

/-- A non-excessive sweepout has no excessive critical point.
This is the definitional content of `NonExcessive` (Definition 3.4). -/
theorem non_excessive_def {Φ : Sweepout M} (h : NonExcessive Φ) (t : ℝ)
    (hcrit : Critical Φ t) : ¬ ExcessiveAt Φ t := by sorry

/-- An $I$-replacement at a critical parameter makes that parameter excessive. -/
theorem ireplacement_to_excessive {Φ : Sweepout M} {t₀ : ℝ}
    (h : IReplacementExists Φ t₀) (hcrit : Critical Φ t₀) :
    ExcessiveAt Φ t₀ := by sorry

end Sweepout

end AltRegularity
