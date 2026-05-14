import Lean

/-!
# Anchor-purity linter

Enforces the OpenGALib "anchor files expose only `**Math.**`-tagged
declarations" rule. Any top-level declaration whose docstring begins
with `**Eng.**` or `**Mixed.**` is forbidden unless the file lives
inside a `Util/` directory.

The rule applies to the anchor's **exposed math API**, not to file-internal
or framework-required plumbing. Two principled exemptions:

* **Typeclass `instance` declarations** — Lean's typeclass synthesis
  requires the instance to be visible wherever it is consumed; co-location
  with the type (rather than via a separate `Util/` import) is a real
  language constraint, not aesthetic choice. Same Mathlib convention.
* **`private` declarations** — invisible outside the file, so they do not
  participate in the anchor's exposed API. Their Eng/Mixed tag is internal
  documentation, not API drift.

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

/-- **Eng.** Inner declaration kinds the linter deliberately skips —
typeclass instances co-locate with their type by Lean synthesis
requirement. -/
private def exemptKinds : List Name :=
  [``Lean.Parser.Command.instance]

/-- **Eng.** Detect a `private` modifier inside `declModifiers` at
`declaration[0]`. The `private` token, when present, lives somewhere
in the modifiers' subtree as an atom literal `"private"`. -/
private partial def hasPrivateModifier (stx : Syntax) : Bool :=
  if stx.isAtom && stx.getAtomVal == "private" then true
  else stx.getArgs.any hasPrivateModifier

/-- **Eng.** The anchor-purity linter. On a top-level *exposed content*
declaration in a non-`Util/` file, warns if the docstring is tagged
`**Eng.**` or `**Mixed.**` — those tags must move to a `Util/` sub-module
or be retagged `**Math.**`. Skips `instance` declarations (typeclass
synthesis must co-locate) and `private` declarations (not part of the
anchor's exposed API). -/
def anchorPurityLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.openGAAnchorPurity (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  if exemptKinds.contains stx[1].getKind then return
  if hasPrivateModifier stx[0] then return
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
