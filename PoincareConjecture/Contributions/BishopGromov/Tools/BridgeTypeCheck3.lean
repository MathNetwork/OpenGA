import Lean
import Theorems.Thm_OpenGA_nonempty_widthComparisonTrace_of_surgeryComparisonProcess
import Solutions.Sol_OpenGA_nonempty_widthComparisonTrace_of_surgeryComparisonProcess
open Lean in
run_meta do
  let a ← Lean.getConstInfo `OpenGA.nonempty_widthComparisonTrace_of_surgeryComparisonProcess
  let b ← Lean.getConstInfo `solution
  unless ← Lean.Meta.isDefEq a.type b.type do
    throwError "Solution type mismatch"
  Lean.logInfo "Exact target type checked"
