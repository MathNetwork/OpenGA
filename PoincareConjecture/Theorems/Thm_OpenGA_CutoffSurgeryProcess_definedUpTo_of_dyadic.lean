import Definitions.Def_OpenGA_CutoffSurgeryProcess
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

open Set
open OpenGA

theorem OpenGA.CutoffSurgeryProcess.definedUpTo_of_dyadic (P : CutoffSurgeryProcess)
    (eps : ℝ) (heps : 0 < eps) (h : ∀ i : ℕ, P.DefinedUpTo (2 ^ i * eps))
    (T : ℝ) (hT : 0 ≤ T) : P.DefinedUpTo T := by sorry
