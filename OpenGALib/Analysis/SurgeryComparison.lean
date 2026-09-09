import OpenGALib.Analysis.ComparisonTrace
import OpenGALib.Analysis.SurgeryVolume
import OpenGALib.Analysis.FiniteEventPartition

/-!
# From surgery volume control to finite comparison traces

A potentially infinite set of event times carries scalar and width profiles
on event-free intervals. Radial volume control proves that the events are
finite, and a sorted partition then gives a `WidthComparisonTrace`.

This is a conditional analytic interface for Kleiner-Lott's nonaccumulation
argument (Section 3.5, p. 13) and the Colding-Minicozzi width argument. It does
not assert that these data have been constructed from a Riemannian manifold,
or supply the missing surgery, polar-integration, or sweepout geometry.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace OpenGA

/-- **Math.** An interval within a finite horizon whose interior contains
no event. Its endpoints may be event times. -/
def EventFreeInterval (events : Set ℝ) (T a b : ℝ) : Prop :=
  0 ≤ a ∧ a < b ∧ b ≤ T ∧ Disjoint events (Ioo a b)

/-- **Math.** Scalar/width comparison profiles and volume-loss control before
one knows that the event times are finite. Every geometric interpretation,
including the budget and radial density hypotheses, remains a separate input. -/
structure SurgeryComparisonProcess (initialWidth finalTime : ℝ) where
  volumeControl : RadialSurgeryVolumeBudget
  events_inside : volumeControl.events ⊆ Ioo 0 finalTime
  finalTime_pos : 0 < finalTime
  scalar : ℝ → ℝ → ℝ
  width : ℝ → ℝ → ℝ
  scalar_cont : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ContinuousOn (scalar a) (Icc a b)
  width_cont : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ContinuousOn (width a) (Icc a b)
  scalar_initial : -6 ≤ scalar 0 0
  width_initial : width 0 0 ≤ initialWidth
  width_nonneg : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ∀ t ∈ Icc a b, 0 ≤ width a t
  scalar_slope : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ∀ t ∈ Ico a b, ∀ q : ℝ, q < (2 / 3 : ℝ) * (scalar a t) ^ 2 →
      ∀ᶠ s in 𝓝[>] t, q < slope (scalar a) t s
  comparison : ∀ a b, EventFreeInterval volumeControl.events finalTime a b →
    ∀ t ∈ Ico a b, Nonempty (WidthComparisonData (width a) t (scalar a t))
  scalar_jump : ∀ a b c,
    EventFreeInterval volumeControl.events finalTime a b →
    EventFreeInterval volumeControl.events finalTime b c → scalar a b ≤ scalar b b
  width_jump : ∀ a b c,
    EventFreeInterval volumeControl.events finalTime a b →
    EventFreeInterval volumeControl.events finalTime b c → width b b ≤ width a b

/-- **Math.** Volume control removes the possibility of infinitely many
partition events, yielding the finite comparison trace used by the width
extinction reduction. -/
theorem nonempty_widthComparisonTrace_of_surgeryComparisonProcess {W T : ℝ}
    (P : SurgeryComparisonProcess W T) : Nonempty (WidthComparisonTrace W T) := by
  obtain ⟨n, hn, times, hfirst, hlast, hmem, hstrict, hfree⟩ :=
    exists_event_free_partition P.volumeControl.events_finite P.events_inside P.finalTime_pos
  have hgap (i : ℕ) (hi : i < n) :
      EventFreeInterval P.volumeControl.events T (times i) (times (i + 1)) :=
    ⟨(hmem i (by omega)).1, hstrict i hi, (hmem (i + 1) (by omega)).2, hfree i hi⟩
  refine ⟨{
    count := n
    count_pos := hn
    times := times
    first_time := hfirst
    last_time := hlast
    times_strict := hstrict
    scalar := fun i => P.scalar (times i)
    width := fun i => P.width (times i)
    scalar_cont := fun i hi => P.scalar_cont _ _ (hgap i hi)
    width_cont := fun i hi => P.width_cont _ _ (hgap i hi)
    scalar_initial := ?_
    width_initial := ?_
    width_nonneg := fun i hi => P.width_nonneg _ _ (hgap i hi)
    scalar_slope := fun i hi => P.scalar_slope _ _ (hgap i hi)
    comparison := fun i hi => P.comparison _ _ (hgap i hi)
    scalar_jump := fun i hi => P.scalar_jump _ _ _ (hgap i (by omega)) (hgap (i + 1) hi)
    width_jump := fun i hi => P.width_jump _ _ _ (hgap i (by omega)) (hgap (i + 1) hi)
  }⟩
  · simpa only [hfirst] using P.scalar_initial
  · simpa only [hfirst] using P.width_initial

end OpenGA
