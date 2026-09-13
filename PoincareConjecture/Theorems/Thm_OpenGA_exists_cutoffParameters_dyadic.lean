import Definitions.Def_OpenGA_CutoffSurgeryProcess
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false

open Set
open OpenGA

theorem OpenGA.exists_cutoffParameters_dyadic (eps : ℝ) (heps : 0 < eps) (rs ds : ℕ → ℝ)
    (hr : ∀ j : ℕ, 0 < rs j) (hd : ∀ j : ℕ, 0 < ds j)
    (hra : Antitone rs) (hda : Antitone ds) :
    ∃ p : CutoffParameters,
      (∀ t : ℝ, 0 ≤ t → t < eps → p.r t = rs 0 ∧ p.delta t = ds 0) ∧
      (∀ (j : ℕ) (t : ℝ), 2 ^ j * eps ≤ t → t < 2 ^ (j + 1) * eps →
        p.r t = rs j ∧ p.delta t = ds j) := by sorry
