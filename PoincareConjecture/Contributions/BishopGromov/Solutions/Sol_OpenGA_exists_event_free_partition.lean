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


/-- **Math.** A finite set of interior event times gives a strictly ordered
partition whose open subintervals contain no event. -/
theorem solution {events : Set ℝ} {T : ℝ}
    (hfinite : events.Finite) (hinside : events ⊆ Ioo 0 T) (hT : 0 < T) :
    ∃ n : ℕ, 0 < n ∧ ∃ times : ℕ → ℝ,
      times 0 = 0 ∧ times n = T ∧
      (∀ i ≤ n, times i ∈ Icc 0 T) ∧
      (∀ i < n, times i < times (i + 1)) ∧
      (∀ i < n, Disjoint events (Ioo (times i) (times (i + 1)))) := by
  classical
  let cuts : Finset ℝ := insert 0 (insert T hfinite.toFinset)
  have hzero : 0 ∈ cuts := by simp [cuts]
  have hterminal : T ∈ cuts := by simp [cuts]
  have hcard : 1 < cuts.card := Finset.one_lt_card.mpr
    ⟨0, hzero, T, hterminal, hT.ne⟩
  have hmem (t : ℝ) (ht : t ∈ cuts) : t ∈ Icc 0 T := by
    simp only [cuts, Finset.mem_insert, Set.Finite.mem_toFinset] at ht
    rcases ht with rfl | rfl | ht
    · exact ⟨le_rfl, hT.le⟩
    · exact ⟨hT.le, le_rfl⟩
    · exact ⟨(hinside ht).1.le, (hinside ht).2.le⟩
  let e := cuts.orderIsoOfFin rfl
  let times : ℕ → ℝ := fun i => if h : i < cuts.card then (e ⟨i, h⟩).val else T
  have htimes (i : ℕ) (hi : i < cuts.card) : times i = (e ⟨i, hi⟩).val := by
    simp [times, hi]
  have he_mem (i : Fin cuts.card) : (e i).val ∈ Icc 0 T := hmem _ (e i).property
  have hfirst : times 0 = 0 := by
    rw [htimes 0 (by omega)]
    apply le_antisymm
    · have h : (e ⟨0, by omega⟩).val ≤ (e (e.symm ⟨0, hzero⟩)).val :=
        e.monotone (show (⟨0, by omega⟩ : Fin cuts.card) ≤ e.symm ⟨0, hzero⟩ from
          show 0 ≤ (e.symm ⟨0, hzero⟩).val from Nat.zero_le _)
      simpa only [OrderIso.apply_symm_apply] using h
    · exact (he_mem _).1
  have hlast : times (cuts.card - 1) = T := by
    rw [htimes _ (by omega)]
    apply le_antisymm (he_mem _).2
    have h : (e (e.symm ⟨T, hterminal⟩)).val ≤ (e ⟨cuts.card - 1, by omega⟩).val :=
      e.monotone (show e.symm ⟨T, hterminal⟩ ≤ (⟨cuts.card - 1, by omega⟩ : Fin cuts.card) by
      have := (e.symm ⟨T, hterminal⟩).isLt
      show (e.symm ⟨T, hterminal⟩).val ≤ cuts.card - 1
      omega)
    simpa only [OrderIso.apply_symm_apply] using h
  refine ⟨cuts.card - 1, by omega, times, hfirst, hlast, ?_, ?_, ?_⟩
  · intro i hi
    rw [htimes i (by omega)]
    exact he_mem _
  · intro i hi
    rw [htimes i (by omega), htimes (i + 1) (by omega)]
    exact e.strictMono (show (⟨i, by omega⟩ : Fin cuts.card) < ⟨i + 1, by omega⟩ by
      show i < i + 1
      omega)
  · intro i hi
    apply Set.disjoint_left.mpr
    intro t ht hinterval
    have htcut : t ∈ cuts := by simp [cuts, ht]
    let j : Fin cuts.card := e.symm ⟨t, htcut⟩
    have hej : (e j).val = t := by simp [j]
    rw [htimes i (by omega), htimes (i + 1) (by omega), ← hej] at hinterval
    have hlo : (⟨i, by omega⟩ : Fin cuts.card) < j := e.lt_iff_lt.mp hinterval.1
    have hhi : j < (⟨i + 1, by omega⟩ : Fin cuts.card) := e.lt_iff_lt.mp hinterval.2
    have hlo' : i < j.val := hlo
    have hhi' : j.val < i + 1 := hhi
    omega
