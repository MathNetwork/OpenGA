import Definitions.Def_OpenGA_SurgeryComparisonProcess
import Definitions.Def_OpenGA_WidthComparisonTrace
import Theorems.Thm_OpenGA_RadialSurgeryVolumeBudget_events_finite
import Theorems.Thm_OpenGA_exists_event_free_partition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison


open OpenGA in
/-- **Math.** Volume control removes the possibility of infinitely many
partition events, yielding the finite comparison trace used by the width
extinction reduction. -/
theorem solution {W T : ℝ}
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
