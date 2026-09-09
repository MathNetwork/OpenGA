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

theorem OpenGA.exists_event_free_partition {events : Set ℝ} {T : ℝ}
    (hfinite : events.Finite) (hinside : events ⊆ Ioo 0 T) (hT : 0 < T) :
    ∃ n : ℕ, 0 < n ∧ ∃ times : ℕ → ℝ,
      times 0 = 0 ∧ times n = T ∧
      (∀ i ≤ n, times i ∈ Icc 0 T) ∧
      (∀ i < n, times i < times (i + 1)) ∧
      (∀ i < n, Disjoint events (Ioo (times i) (times (i + 1)))) := by sorry
