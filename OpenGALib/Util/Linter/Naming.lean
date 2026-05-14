import Lean

/-!
# Naming-convention linter — forbidden initialisms

Enforces the OpenGALib rule against bare initialisms in declaration
names. Specifically forbids the substrings `CLM`, `NACG`, and `IPS` in
top-level declaration identifiers — they lose semantics and may collide
with unrelated names. Full Mathlib-style names are mandatory:

* `CLM`  → `ContinuousLinearMap`
* `NACG` → `NormedAddCommGroup`
* `IPS`  → `InnerProductSpace`

Activated via `set_option linter.openGANaming true` (default: `true`).

See CLAUDE.md "Code quality / Natural-language reading test" plus
memory entry `feedback_avoid_initialisms.md` for the convention.
-/

open Lean Elab Linter

namespace OpenGALib.Linter.Naming

/-- **Eng.** The OpenGALib naming-convention linter option. -/
register_option linter.openGANaming : Bool := {
  defValue := true
  descr := "Forbid bare initialisms (CLM, NACG, IPS) in declaration names."
}

/-- **Eng.** Initialisms that must be expanded into full names. -/
private def forbiddenInitialisms : List String := ["CLM", "NACG", "IPS"]

/-- **Eng.** Suggested expansion for each forbidden initialism. -/
private def expandSuggestion : String → String
  | "CLM"  => "ContinuousLinearMap"
  | "NACG" => "NormedAddCommGroup"
  | "IPS"  => "InnerProductSpace"
  | _      => "(no suggestion)"

private def stringContains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def findBadInitialism (name : String) : Option String :=
  forbiddenInitialisms.find? (stringContains name ·)

/-- **Eng.** Locate the first `Lean.Parser.Command.declId` node inside
`stx` (depth-first). Returns `none` if the declaration is anonymous
(e.g., `instance : Foo` without a name). -/
private partial def findDeclId? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Lean.Parser.Command.declId then some stx
  else stx.getArgs.findSome? findDeclId?

/-- **Eng.** The naming linter. For every top-level declaration with an
explicit name, warns if the name contains one of the forbidden
initialisms. -/
def namingLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.openGANaming (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  let some declId := findDeclId? stx[1] | return
  let nameStx := declId[0]
  unless nameStx.isIdent do return
  let name := nameStx.getId.toString
  if let some bad := findBadInitialism name then
    Linter.logLint linter.openGANaming nameStx
      m!"declaration name `{name}` contains the forbidden initialism `{bad}` — \
         expand to `{expandSuggestion bad}` (initialisms drop semantics and \
         risk colliding with unrelated names; see CLAUDE.md naming test)."

initialize addLinter namingLinter

end OpenGALib.Linter.Naming
