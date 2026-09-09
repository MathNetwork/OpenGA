import Theorems.Thm_PoincareFormalization_persistent_comparison_data_of_not_homeomorph_sphere
import Theorems.Thm_OpenGA_eventually_width_slope_lt_of_comparison

set_option autoImplicit false

open Set Filter
open scoped Topology

theorem solution
    (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (hnot : ¬ Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1))) :
    ∃ W₀ : ℝ, 0 ≤ W₀ ∧ ∀ T : ℝ, 0 < T → Nonempty (OpenGA.ScalarWidthTrace W₀ T) := by
  obtain ⟨initialWidth, hnonneg, hpersist⟩ :=
    PoincareFormalization.persistent_comparison_data_of_not_homeomorph_sphere M hnot
  refine ⟨initialWidth, hnonneg, ?_⟩
  intro finalTime hfinalTime
  obtain ⟨data⟩ := hpersist finalTime hfinalTime
  refine ⟨{
    count := data.count
    count_pos := data.count_pos
    times := data.times
    first_time := data.first_time
    last_time := data.last_time
    times_strict := data.times_strict
    scalar := data.scalar
    width := data.width
    scalar_cont := data.scalar_cont
    width_cont := data.width_cont
    scalar_initial := data.scalar_initial
    width_initial := data.width_initial
    width_nonneg := data.width_nonneg
    scalar_slope := data.scalar_slope
    width_slope := ?_
    scalar_jump := data.scalar_jump
    width_jump := data.width_jump
  }⟩
  intro i hi t ht q hq
  obtain ⟨comparison⟩ := data.comparison i hi t ht
  exact (OpenGA.eventually_width_slope_lt_of_comparison comparison q hq).frequently
