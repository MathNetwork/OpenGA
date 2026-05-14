import Lean.Elab.GuardMsgs
import OpenGALib.Util.Linter.MathTag

/-!
# Tests for `MathTagLinter`

Positive cases pass silently; the negative case is wrapped in
`#guard_msgs (warning) in` so the build fails if the linter ever stops
firing on the intended trigger (a docstring without the required tag).
-/

namespace OpenGALib.Tests.Linter.MathTag

/-- **Math.** Pass: correctly tagged with **Math.** -/
theorem pos_math : True := trivial

/-- **Eng.** Pass: correctly tagged with **Eng.** -/
def pos_eng : Nat := 0

/-- **Mixed.** Pass: correctly tagged with **Mixed.** -/
theorem pos_mixed : 1 + 1 = 2 := rfl

-- Pass: a declaration without a docstring is silently accepted.
theorem pos_no_doc : True := trivial

/--
warning: docstring should start with **Math.**, **Eng.**, or **Mixed.** (got: "this docstring forgot the tag entirely…")

Note: This linter can be disabled with `set_option linter.openGA.mathTag false`
-/
#guard_msgs (warning) in
/-- this docstring forgot the tag entirely -/
theorem neg_no_tag : True := trivial

end OpenGALib.Tests.Linter.MathTag
