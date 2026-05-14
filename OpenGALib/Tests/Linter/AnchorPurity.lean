import Lean.Elab.GuardMsgs
import OpenGALib.Util.Linter.AnchorPurity

/-!
# Tests for `AnchorPurityLinter`

This file lives at `OpenGALib/Tests/Linter/AnchorPurity.lean` — *outside*
`Util/` — so the path check inside the linter is *not* short-circuited.
Negative cases exercise both forbidden tags (`**Eng.**`, `**Mixed.**`);
exemption cases (`instance`, `private`) verify the two principled
carve-outs.
-/

namespace OpenGALib.Tests.Linter.AnchorPurity

/-- **Math.** Pass: Math-tagged content. -/
def pos_math : Nat := 0

/--
warning: `**Eng.**` declaration in an anchor file — move it to the layer's `Util/` sub-module, or re-tag as `**Math.**` if it actually describes a textbook concept.

Note: This linter can be disabled with `set_option linter.openGA.anchorPurity false`
-/
#guard_msgs (warning) in
/-- **Eng.** Should fire — Eng-tagged in non-Util anchor file. -/
def neg_eng : Nat := 0

/--
warning: `**Mixed.**` declaration in an anchor file — move it to the layer's `Util/` sub-module, or re-tag as `**Math.**` if it actually describes a textbook concept.

Note: This linter can be disabled with `set_option linter.openGA.anchorPurity false`
-/
#guard_msgs (warning) in
/-- **Mixed.** Should fire — Mixed-tagged in non-Util anchor file. -/
def neg_mixed : Nat := 0

-- Exemption 1: `instance` declarations co-locate with their type by
-- Lean synthesis requirement. Silent even when tagged **Eng.**.

class TestExemptionClass where val : Nat

/-- **Eng.** Exempt: typeclass instances may carry Eng/Mixed tags. -/
instance : TestExemptionClass := ⟨0⟩

-- Exemption 2: `private` declarations are not part of the anchor's
-- exposed API, so an Eng tag is internal documentation. Silent.

/-- **Eng.** Exempt: private declarations do not pollute exposed API. -/
private def pos_private_eng : Nat := 0

end OpenGALib.Tests.Linter.AnchorPurity
