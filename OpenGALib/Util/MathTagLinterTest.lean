import OpenGALib.Util.MathTagLinter

/-!
# Smoke test for `MathTagLinter`

* `goodMath` / `goodEng` / `goodMixed`  — correctly tagged → no warning.
* `badTag`                              — wrong prefix; the linter is
  locally disabled with `set_option linter.openGAMathTag false in` to
  keep this smoke-test build clean while still documenting the violation.
* `noDocstring`                         — no doc → silently skipped.

To verify the linter fires, comment out the `set_option` line on
`badTag` and `lake build` — a warning should appear at that line.
-/

namespace OpenGALib.Linter.MathTag.Test

/-- **Math.** A perfectly tagged theorem. -/
theorem goodMath : True := trivial

/-- **Eng.** An engineering helper. -/
def goodEng : Nat := 0

/-- **Mixed.** A mixed-flavour lemma. -/
theorem goodMixed : 1 + 1 = 2 := rfl

set_option linter.openGAMathTag false in
/-- This docstring forgot the tag entirely (deliberate; linter silenced). -/
theorem badTag : True := trivial

theorem noDocstring : True := trivial

end OpenGALib.Linter.MathTag.Test
