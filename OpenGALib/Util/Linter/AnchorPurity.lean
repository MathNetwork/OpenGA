import Lean

/-!
# Anchor-purity linter

Enforces the OpenGALib "anchor files expose only `**Math.**`-tagged
declarations" rule. Any top-level declaration whose docstring begins
with `**Eng.**` or `**Mixed.**` is forbidden unless the file lives
inside a `Util/` directory (the only allowed home for engineering /
mixed declarations).

Declarations without docstrings and `**Math.**` tagged ones are silently
accepted.

Activated via `set_option linter.openGAAnchorPurity true` (default: `true`).

See CLAUDE.md "Code quality / Engineering tax encapsulation" for the
convention itself.
-/

open Lean Elab Linter

namespace OpenGALib.Linter.AnchorPurity

/-- **Eng.** The OpenGALib anchor-purity linter option. -/
register_option linter.openGAAnchorPurity : Bool := {
  defValue := true
  descr := "Forbid **Eng.**/**Mixed.** docstring tags outside `Util/` folders."
}

/-- **Eng.** Forbidden tag prefixes in anchor files. -/
private def forbiddenInAnchor : List String := ["**Eng.**", "**Mixed.**"]

private def startsWithForbidden (s : String) : Option String :=
  let t := s.trimAsciiStart.toString
  forbiddenInAnchor.find? fun tag => t.startsWith tag

/-- **Eng.** True when `path` lies inside a `Util/` directory (top-level
`OpenGALib/Util/` or per-layer `OpenGALib/<Layer>/Util/`). Checked by
segmenting on `/` so accidental substrings like `Utilities` would not match. -/
private def isUtilPath (path : String) : Bool :=
  (path.splitOn "/").contains "Util"

/-- **Eng.** The anchor-purity linter. On a top-level declaration in a
non-`Util/` file, warns if the docstring is tagged `**Eng.**` or
`**Mixed.**` — those tags must move to a `Util/` sub-module. -/
def anchorPurityLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.openGAAnchorPurity (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  if isUtilPath (← getFileName) then return
  let docStx := stx[0][0][0]
  if docStx.isMissing then return
  let docString ← try getDocStringText ⟨docStx⟩ catch _ => return
  if let some bad := startsWithForbidden docString then
    Linter.logLint linter.openGAAnchorPurity docStx
      m!"`{bad}` declaration in an anchor file — move it to the layer's \
         `Util/` sub-module, or re-tag as `**Math.**` if it actually \
         describes a textbook concept."

initialize addLinter anchorPurityLinter

end OpenGALib.Linter.AnchorPurity
