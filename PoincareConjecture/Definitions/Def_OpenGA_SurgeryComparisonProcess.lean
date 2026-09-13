import Definitions.Def_OpenGA_RadialSurgeryVolumeBudget
import Definitions.Def_OpenGA_WidthComparisonData
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

end OpenGA
