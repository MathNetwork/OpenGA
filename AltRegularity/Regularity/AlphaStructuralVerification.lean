import MinMax.Sweepout.NonExcessive
import MinMax.Sweepout.MinMaxLimit
import Regularity.AlphaStructural
import Regularity.SmoothRegularity
import GeometricMeasureTheory.TangentCone
import GeometricMeasureTheory
import MinMax
import Regularity
import Mathlib.Geometry.Manifold.IsManifold.Basic

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
    By `MinMax.Sweepout.ireplacement_to_excessive` and `MinMax.Sweepout.non_excessive_def`.

The two sorry'd inputs (the negation-as-junction equivalence and the
chord-beats-arc construction) are the substantive Section 7 content. The
chain itself is fully formalized.
-/

namespace AltRegularity

open GeometricMeasureTheory GeometricMeasureTheory.Varifold GeometricMeasureTheory.FinitePerimeter Regularity Regularity.Varifold MinMax.Sweepout MinMax.Sweepout.Varifold
open scoped ContDiff
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- The $\alpha$-structural hypothesis fails iff some singular point of
$V$ is a junction.

Forward direction: $\neg (\mathcal{S}3)$ at some $Z$ exhibits an explicit
half-hyperplane configuration. Reverse direction: a junction at $Z$ is the
canonical witness to the negation of $(\mathcal{S}3)$.

The lib-level concepts `HasJunction` and `IsJunctionCone` live in
`Regularity.AlphaStructural` (regularity-theory primitives, Wic14
Remark 3.5(ii)), not in `GeometricMeasureTheory`. -/
theorem not_alphaStructural_iff_exists_junction (V : Varifold M) (α : ℝ) :
    ¬ AlphaStructural I V α ↔ ∃ Z ∈ sing I V, HasJunction I V Z := by sorry

namespace MinMax.Sweepout

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
    {Φ : MinMax.Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : NonExcessive Φ) (honvp : ONVP Φ) (hcrit : Critical Φ t₀)
    (hlim : MinMaxLimit Φ t₀ V) {Z : M} (hZ : Z ∈ Varifold.sing I V)
    (hjunc : Varifold.HasJunction I V Z) :
    IReplacementExists Φ t₀ := by sorry

end MinMax.Sweepout

/-! ## Main verification: Section 7 chain proof -/

/-- **$\alpha$-structural hypothesis from non-excessiveness.**

Mirror of `positiveDensity_of_sweepoutWideReplacement` (Section 5.1):
both proofs derive a contradiction with non-excessiveness from a "bad"
configuration, via the same five-step chain:
  1. Negate the conclusion (junction at some $Z$ here; zero density at $p$
     in Section 5.1).
  2. Apply the "Claim" producing an $I$-replacement
     (`ireplacement_of_junction` here; `SweepoutWideReplacement` there).
  3. Use `MinMax.Sweepout.ireplacement_to_excessive` to make $t_0$ excessive.
  4. Use `MinMax.Sweepout.non_excessive_def` to contradict non-excessiveness.

The constant $\alpha = 1/4$ is one of many choices in $(0, 1/2)$. -/
theorem alphaStructural_of_nonExcessive_minmax
    {Φ : MinMax.Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : MinMax.Sweepout.NonExcessive Φ) (honvp : MinMax.Sweepout.ONVP Φ)
    (hcrit : MinMax.Sweepout.Critical Φ t₀) (hlim : MinMax.Sweepout.MinMaxLimit Φ t₀ V) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 2 ∧ Varifold.AlphaStructural I V α := by
  -- Pick α = 1/4 ∈ (0, 1/2). Any value in (0, 1/2) works.
  refine ⟨1 / 4, by norm_num, by norm_num, ?_⟩
  -- Prove `AlphaStructural I V (1/4)` by contradiction.
  by_contra h_not
  -- Negation gives a junction at some singular point.
  rw [AltRegularity.not_alphaStructural_iff_exists_junction] at h_not
  obtain ⟨Z, hZ, hjunc⟩ := h_not
  -- Chord-beats-arc: junction yields a 2-sided $I$-replacement at $t_0$
  -- (paper §6.2 Step 3 — `IReplacementExists` is `Left ∧ Right`).
  have hIRep : MinMax.Sweepout.IReplacementExists Φ t₀ :=
    MinMax.Sweepout.ireplacement_of_junction (I := I) hne honvp hcrit hlim hZ hjunc
  -- The 2-sided $I$-replacement at a critical point contradicts
  -- non-excessiveness directly (`NonExcessive` forbids
  -- `IReplacementExists` at every critical point).
  exact MinMax.Sweepout.non_excessive_def hne t₀ hcrit hIRep

end AltRegularity
