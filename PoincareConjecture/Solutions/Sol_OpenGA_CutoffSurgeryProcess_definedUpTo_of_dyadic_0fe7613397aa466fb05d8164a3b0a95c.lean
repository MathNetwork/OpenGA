import Definitions.Def_OpenGA_CutoffSurgeryProcess
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

open Set
open OpenGA

theorem solution (P : CutoffSurgeryProcess) (eps : ℝ) (heps : 0 < eps)
    (h : ∀ i : ℕ, P.DefinedUpTo (2 ^ i * eps)) (T : ℝ) (hT : 0 ≤ T) : P.DefinedUpTo T := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, T / eps < 2 ^ i := pow_unbounded_of_one_lt _ one_lt_two
  have hle : T ≤ 2 ^ i * eps := by
    rw [div_lt_iff₀ heps] at hi
    linarith
  exact P.definedUpTo_mono hT hle (h i)
