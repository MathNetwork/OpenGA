import OpenGALib.Util.Linter.Naming

/-!
# Smoke test for `NamingLinter`

Three names exercising the linter, each silenced locally so the build
stays clean while documenting the trigger patterns.
-/

namespace OpenGALib.Linter.Naming.Test

/-- **Math.** Acceptable name (no forbidden initialism). -/
def continuousLinearMap_smul : Nat := 0

set_option linter.openGANaming false in
/-- **Math.** Deliberate `CLM` initialism (linter silenced). -/
def someCLMthing : Nat := 0

set_option linter.openGANaming false in
/-- **Math.** Deliberate `NACG` initialism (linter silenced). -/
def NACG_helper : Nat := 0

set_option linter.openGANaming false in
/-- **Math.** Deliberate `IPS` initialism (linter silenced). -/
def IPS_bridge : Nat := 0

end OpenGALib.Linter.Naming.Test
