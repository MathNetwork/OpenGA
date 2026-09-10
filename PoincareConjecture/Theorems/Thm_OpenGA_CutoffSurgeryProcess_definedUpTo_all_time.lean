import Definitions.Def_OpenGA_CutoffSurgeryProcess

set_option autoImplicit false

open Set
open OpenGA

theorem OpenGA.CutoffSurgeryProcess.definedUpTo_all_time (P : CutoffSurgeryProcess)
    (T : ℝ) (hT : 0 ≤ T) : P.DefinedUpTo T := by sorry
