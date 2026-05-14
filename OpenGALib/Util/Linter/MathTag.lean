import Lean

/-!
# `Math/Eng/Mixed` docstring-tag linter

Enforces the OpenGALib documentation convention: any declaration
(`def` / `theorem` / `lemma` / `abbrev` / `instance` / `class` / `structure`
/ `inductive` / ...) whose docstring is present must begin with one of
the tags `**Math.**`, `**Eng.**`, or `**Mixed.**`.

The linter does not require a docstring; it only checks the tag when one
is present. Declarations with no docstring are silently skipped.

Activated via `set_option linter.openGAMathTag true` (default: `true`).
To silence locally use `set_option linter.openGAMathTag false in <decl>`,
or fix the tag.

See CLAUDE.md "Code quality / Math-Eng-Mixed tagging" for the convention itself.
-/

open Lean Elab Linter

namespace OpenGALib.Linter.MathTag

/-- **Eng.** The OpenGALib Math/Eng/Mixed docstring-tag linter option. -/
register_option linter.openGAMathTag : Bool := {
  defValue := true
  descr := "Enforce **Math.**/**Eng.**/**Mixed.** docstring tag on declarations."
}

/-- **Eng.** Accepted tag prefixes for OpenGALib declarations. -/
private def acceptedTags : List String := ["**Math.**", "**Eng.**", "**Mixed.**"]

private def hasAcceptedTag (s : String) : Bool :=
  let t := s.trimAsciiStart.toString
  acceptedTags.any fun tag => t.startsWith tag

/-- **Eng.** The Math/Eng/Mixed-tag linter. Fires only on top-level
declaration commands (`def`, `theorem`, `lemma`, `abbrev`, `instance`,
`class`, `structure`, `inductive`, ...). Structure fields, class fields,
and other nested constructs are skipped — the tagging convention applies
to whole declarations, not internal slots. -/
def mathTagLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.openGAMathTag (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  let docStx := stx[0][0][0]
  if docStx.isMissing then return
  let docString ← try getDocStringText ⟨docStx⟩ catch _ => return
  unless hasAcceptedTag docString do
    let preview := (docString.trimAsciiStart.toString.take 40).replace "\n" " "
    Linter.logLint linter.openGAMathTag docStx
      m!"docstring should start with **Math.**, **Eng.**, or **Mixed.** \
         (got: \"{preview}…\")"

initialize addLinter mathTagLinter

end OpenGALib.Linter.MathTag
