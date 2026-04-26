import AltRegularity.Sweepout.NonExcessive
import AltRegularity.Sweepout.MinMaxLimit
import AltRegularity.Regularity.AlphaStructural
import AltRegularity.Regularity.SmoothRegularity

/-!
# AltRegularity.Regularity.AlphaStructuralVerification

Verification of the $\alpha$-structural hypothesis for the min-max varifold
of a non-excessive ONVP sweepout (Section 7 of the paper).

## Strategy

The verification is by contradiction, mirroring the structure of
`AltRegularity.PositiveDensity`:

  * **Negation as junction.** If $V$ violates the $\alpha$-structural
    hypothesis, then some singular point $Z \in \mathrm{sing}\, V$ admits a
    "junction": $N \ge 3$ distinct half-hyperplanes meeting along a common
    $(n-1)$-dimensional edge through $Z$, satisfying the stationary
    balancing condition.
  * **Junction $\Rightarrow$ $I$-replacement (Section 7's chord-beats-arc).**
    From the junction configuration at $Z$, the chord-beats-arc construction
    produces a sweepout-wide modification $\tilde\Phi$ whose slice
    $\tilde\Omega(x)$ at $x \in (x_0 - \varepsilon, x_0 + \varepsilon)$
    satisfies
    $\mathrm{Per}(\tilde\Omega(x)) \le \mathrm{Per}(\Omega(x))
        - \tfrac{\delta(\theta_j)}{2}\,\rho(x)^n$,
    making the interval excessive.
  * **$I$-replacement $\Rightarrow$ excessive $\Rightarrow$ contradiction.**
    By `Sweepout.ireplacement_to_excessive` and `Sweepout.non_excessive_def`.

The two sorry'd inputs (the negation-as-junction equivalence and the
chord-beats-arc construction) are the substantive Section 7 content. The
chain itself is fully formalized.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Varifold

/-- The varifold $V$ has a **junction** at the point $Z$: the tangent cone
to $\|V\|$ at $Z$ is supported on $N \ge 3$ distinct half-hyperplanes
meeting along a common $(n-1)$-dimensional edge through $Z$, with the
stationary balancing condition $\sum \nu_j = 0$ on the conormals. This is
the configuration excluded by $(\mathcal{S}3)$. -/
opaque HasJunction (V : Varifold M) (Z : M) : Prop

/-- The $\alpha$-structural hypothesis fails iff some singular point of
$V$ is a junction.

Forward direction: $\neg (\mathcal{S}3)$ at some $Z$ exhibits an explicit
half-hyperplane configuration. Reverse direction: a junction at $Z$ is the
canonical witness to the negation of $(\mathcal{S}3)$. -/
theorem not_alphaStructural_iff_exists_junction (V : Varifold M) (α : ℝ) :
    ¬ AlphaStructural V α ↔ ∃ Z ∈ sing V, HasJunction V Z := by sorry

end Varifold

namespace Sweepout

/-- **Chord-beats-arc: a junction in the min-max varifold limit produces
an $I$-replacement.**

Section 7 of the paper. From a junction at $Z \in \mathrm{sing}\,V$ in the
min-max varifold $V$ of a non-excessive ONVP sweepout, the chord-beats-arc
construction yields a sweepout-wide modification of $\Phi$ on an open
interval $(x_0 - \varepsilon, x_0 + \varepsilon)$ along which every slice
has strictly smaller perimeter than the original. This is the precise
input for the contradiction with non-excessiveness.

The proof in the paper consists of four steps (Step 3a–3d in Section 7):
  * Step 3a: Pick a small ball $B_r(Z)$ and the chord surface $T_\rho$
    spanning two adjacent sheets.
  * Step 3b: Smooth cutoff $\eta$ ramping from $0$ to $1$.
  * Step 3c: Modified sweepout $\tilde\Phi$ with $\mathcal{F}$-continuity.
  * Step 3d: Strict perimeter drop
    $\mathrm{Per}(\tilde\Omega(x)) \le \mathrm{Per}(\Omega(x))
        - \tfrac{\delta(\theta_j)}{2}\,\rho(x)^n$
    on the open interval, yielding the $I$-replacement. -/
theorem ireplacement_of_junction
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : NonExcessive Φ) (honvp : ONVP Φ) (hcrit : Critical Φ t₀)
    (hlim : MinMaxLimit Φ t₀ V) {Z : M} (hZ : Z ∈ Varifold.sing V)
    (hjunc : Varifold.HasJunction V Z) :
    IReplacementExists Φ t₀ := by sorry

end Sweepout

/-! ## Main verification: Section 7 chain proof -/

/-- **$\alpha$-structural hypothesis from non-excessiveness.**

Mirror of `positiveDensity_of_sweepoutWideReplacement` (Section 5.1):
both proofs derive a contradiction with non-excessiveness from a "bad"
configuration, via the same five-step chain:
  1. Negate the conclusion (junction at some $Z$ here; zero density at $p$
     in Section 5.1).
  2. Apply the "Claim" producing an $I$-replacement
     (`ireplacement_of_junction` here; `SweepoutWideReplacement` there).
  3. Use `Sweepout.ireplacement_to_excessive` to make $t_0$ excessive.
  4. Use `Sweepout.non_excessive_def` to contradict non-excessiveness.

The constant $\alpha = 1/4$ is one of many choices in $(0, 1/2)$. -/
theorem alphaStructural_of_nonExcessive_minmax
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : Sweepout.NonExcessive Φ) (honvp : Sweepout.ONVP Φ)
    (hcrit : Sweepout.Critical Φ t₀) (hlim : Sweepout.MinMaxLimit Φ t₀ V) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 2 ∧ Varifold.AlphaStructural V α := by
  -- Pick α = 1/4 ∈ (0, 1/2). Any value in (0, 1/2) works.
  refine ⟨1 / 4, by norm_num, by norm_num, ?_⟩
  -- Prove `AlphaStructural V (1/4)` by contradiction.
  by_contra h_not
  -- Negation gives a junction at some singular point.
  rw [Varifold.not_alphaStructural_iff_exists_junction] at h_not
  obtain ⟨Z, hZ, hjunc⟩ := h_not
  -- Chord-beats-arc: junction yields an I-replacement at t₀.
  have hIRep : Sweepout.IReplacementExists Φ t₀ :=
    Sweepout.ireplacement_of_junction hne honvp hcrit hlim hZ hjunc
  -- I-replacement makes t₀ excessive.
  have hExc : Sweepout.ExcessiveAt Φ t₀ :=
    Sweepout.ireplacement_to_excessive hIRep hcrit
  -- t₀ excessive contradicts the non-excessive property of Φ.
  exact Sweepout.non_excessive_def hne t₀ hcrit hExc

end AltRegularity
