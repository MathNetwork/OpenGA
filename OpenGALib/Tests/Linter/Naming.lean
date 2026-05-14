import Lean.Elab.GuardMsgs
import OpenGALib.Util.Linter.Naming

/-!
# Tests for `NamingLinter`

Positive case: a fully expanded name passes. Three negative cases —
one per forbidden initialism (`CLM`, `NACG`, `IPS`) — verify the
linter fires and emits the correct expansion suggestion.
-/

namespace OpenGALib.Tests.Linter.Naming

/-- **Math.** Pass: fully expanded Mathlib-style name. -/
def continuousLinearMap_smul_example : Nat := 0

/--
warning: declaration name `someCLMthing` contains the forbidden initialism `CLM` — expand to `ContinuousLinearMap` (initialisms drop semantics and risk colliding with unrelated names; see CLAUDE.md naming test).

Note: This linter can be disabled with `set_option linter.openGA.naming false`
-/
#guard_msgs (warning) in
/-- **Math.** -/
def someCLMthing : Nat := 0

/--
warning: declaration name `NACG_helper` contains the forbidden initialism `NACG` — expand to `NormedAddCommGroup` (initialisms drop semantics and risk colliding with unrelated names; see CLAUDE.md naming test).

Note: This linter can be disabled with `set_option linter.openGA.naming false`
-/
#guard_msgs (warning) in
/-- **Math.** -/
def NACG_helper : Nat := 0

/--
warning: declaration name `IPS_bridge` contains the forbidden initialism `IPS` — expand to `InnerProductSpace` (initialisms drop semantics and risk colliding with unrelated names; see CLAUDE.md naming test).

Note: This linter can be disabled with `set_option linter.openGA.naming false`
-/
#guard_msgs (warning) in
/-- **Math.** -/
def IPS_bridge : Nat := 0

end OpenGALib.Tests.Linter.Naming
