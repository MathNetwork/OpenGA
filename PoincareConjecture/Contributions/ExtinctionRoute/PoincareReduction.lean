import Theorems.Thm_OpenGA_scalar_lower_bound_across_upward_jumps
import Theorems.Thm_OpenGA_le_width_deadline_across_downward_jumps
import Theorems.Thm_PoincareFormalization_persistent_profiles_of_not_homeomorph_sphere

set_option autoImplicit false

open Set Filter
open scoped Topology

theorem solution (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)) := by
  classical
  by_contra hnot
  obtain ⟨W₀, _, hpersist⟩ :=
    PoincareFormalization.persistent_profiles_of_not_homeomorph_sphere M hnot
  let deadline : ℝ :=
    ((1 / 4 : ℝ) ^ ((1 : ℝ) / 4) +
      W₀ / (16 * Real.pi * (1 / 4 : ℝ) ^ ((3 : ℝ) / 4))) ^ (4 : ℕ) - 1 / 4
  let T : ℝ := max deadline 0 + 1
  have hT : 0 < T := by
    dsimp [T]
    linarith [le_max_right deadline 0]
  obtain ⟨F⟩ := hpersist T hT
  have hscalar := OpenGA.scalar_lower_bound_across_upward_jumps
    F.count F.count_pos F.times F.scalar F.first_time F.times_strict
    F.scalar_cont F.scalar_initial F.scalar_slope F.scalar_jump
  have hslope : ∀ i < F.count, ∀ x ∈ Ico (F.times i) (F.times (i + 1)), ∀ q : ℝ,
      -(4 * Real.pi) + 3 / (4 * (x + (1 / 4 : ℝ))) * F.width i x < q →
        ∃ᶠ s in 𝓝[>] x, slope (F.width i) x s < q := by
    intro i hi x hx q hq
    apply F.width_slope i hi x hx q
    have hs := hscalar i hi x (Ico_subset_Icc_self hx)
    have hw := F.width_nonneg i hi x (Ico_subset_Icc_self hx)
    have hm := mul_le_mul_of_nonneg_right hs hw
    have hid : (-(6 : ℝ) / (1 + 4 * x)) * F.width i x / 2 =
        -(3 / (4 * (x + (1 / 4 : ℝ))) * F.width i x) := by
      have hden : 1 + 4 * x = 4 * (x + (1 / 4 : ℝ)) := by ring
      rw [hden]
      ring
    nlinarith
  have hlast : F.count - 1 + 1 = F.count := by have := F.count_pos; omega
  have hfinal : 0 ≤ F.width (F.count - 1) (F.times F.count) := by
    apply F.width_nonneg (F.count - 1) (by have := F.count_pos; omega)
    constructor
    · simpa [hlast] using (F.times_strict (F.count - 1) (by have := F.count_pos; omega)).le
    · simp [hlast]
  have hbound := OpenGA.le_width_deadline_across_downward_jumps
    (C := (1 / 4 : ℝ)) (W₀ := W₀) (by norm_num)
    F.count F.count_pos F.times F.width F.first_time F.times_strict
    F.width_cont F.width_initial hfinal hslope F.width_jump
  rw [F.last_time] at hbound
  change T ≤ deadline at hbound
  dsimp [T] at hbound
  linarith [le_max_left deadline 0]
