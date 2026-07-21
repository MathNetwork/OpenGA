<!-- Reviewer checklist: .github/REVIEW.md -->

## What

<!-- One sentence: what this PR adds or changes. -->

## Checklist

- [ ] Builds green (`lake build`), **no new `sorry`**
- [ ] One concern per PR; bottom-up on the dependency cone
- [ ] Docstrings tagged (`**Math.**` / `**Eng.**` / `**Mixed.**`)
- [ ] Reuse checked — not already in Mathlib or OpenGALib
- [ ] Facade theorems: `#print axioms` clean — only `propext`, `Classical.choice`, `Quot.sound`

### Adoption PRs (porting from `feat/hopf-rinow`)

- [ ] Faithful port — matches the `feat/hopf-rinow` version, no silent edits
- [ ] Not a file flagged in #112 (§3.4 `Equation.lean`, §3.1 `HopfRinow.lean`), or its prerequisite fix is in

<!-- Adopted from feat/hopf-rinow? Credit original authors with `Co-authored-by:` trailers. -->
