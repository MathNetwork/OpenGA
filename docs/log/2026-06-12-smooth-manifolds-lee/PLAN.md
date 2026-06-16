# 2026-06-12 · SmoothManifoldsLee integration plan

**Event.** LehengChen pushed `import/smooth-manifolds-lee` (`a5f308c`): a Lean
formalization of Lee's *Introduction to Smooth Manifolds* Ch1–5 — 346 files /
62k lines, Mathlib-only deps, zero dependency on and zero overlap with
OpenGALib. Same-day full audit: **187 new / 95 Mathlib-dup / 57 partial-dup;
52 high-value files**. Per-file detail and the construction ledger are in
`WORKLIST.md` (same folder).

## Problem

This material is a **textbook-ordered formalization**: one file per numbered
item, an import graph coupled to chapter numbering, and infrastructure code
(chart operations, cutoff functions, instance packaging) scattered ad hoc under
each chapter's theorems. We want **reusable, maintainable, extensible
software**: declarations organized by mathematical object, infrastructure
settled into shared layers, upper layers importing the infrastructure without
knowing the textbook exists.

So the question to answer is: **how to turn a textbook-ordered formalization
into a software library, and make that conversion a repeatable process** — this
will not be the last time someone shows up with a whole book's worth of
formalization.

## Branches and process

```
import/<source>    frozen reference snapshot (read-only, never merged, staging/ stays out of trunk)
      ↓ manual/AI port, not a git merge
port/<item>        short-lived work branch, one item each, cut from develop
      ↓ PR + CI + review
develop → main     existing practice unchanged
```

- Import branches are never merged: foreign conventions stay out of history, and
  audit conclusions are valid only for the pinned snapshot commit. New upstream
  material goes to `import/<source>-v2`; diff the delta, re-audit only the delta,
  no force-push.
- Quality gates per port PR: house-style namespace, correct module placement,
  **zero sorry**, **full `lake build`** before pushing, a one-line provenance
  footer in the module docstring (`Provenance: <source> <commit> — <files>`), no
  new linter-baseline violations.
- Claiming an item updates its status in the `WORKLIST.md` ledger; the ledger
  change travels with the port PR. Don't touch an item someone else has marked
  in-progress.
- When all items are ported: tag the reference branch for archive, then delete
  it; the ledger remains as the provenance record.

## Automation pipeline (proposed, to be piloted)

The work items are isomorphic units; each runs the same loop, with automation
depth decided by pilot data:

```
claim → ① shared-layer check (AI emits a reuse/extend/new decision table, grep evidence required)
      → ② port (AI: house-style namespace, restructure, single **Math.** docstrings)
      → ③ machine gate (CI: full build, zero sorry, linters, naming + provenance checks)
      → ④ auto-open PR (with decision table and ledger diff)
      → ⑤ human review (two things only — see next section)
```

Two **standing constraints** are written into the AI task template, not relied
on as verbal reminders:

1. **Shared-layer-first**: no code until the question "does the trunk already
   have an equivalent facility?" is answered. The audit confirmed the need —
   both sides had written half of the same facilities (chart calculus, cutoff
   functions, bundled classes).
2. **Semantic faithfulness**: each declaration carries a single docstring tag.
   Anchor files (outside `Util/`) use `**Math.**` only — the `AnchorPurity`
   linter forbids `**Eng.**`/`**Mixed.**` there; engineering detail is dropped
   (the code is self-evident) or moved to a `Util/` submodule. Tag *presence* is
   linter-enforced; *faithfulness* is human-reviewed. (Note: an earlier draft of
   this plan called for "Math./Eng. dual docstrings" — that was a misreading of
   the house style, now corrected.)

The pipeline terminates at a PR, never at develop. A human is always the merge
gatekeeper.

## The human part: how review is allocated

Grounded in the minimal-trusted-base argument: the Lean kernel has checked every
proof, so **proofs need no human review**; but a wrong definition lets the
kernel happily certify thousands of lines of true theorems about the wrong
object. Human review collapses to **definitions and statements**, and within
that, a wrong definition kills the entire downstream dependency cone while a
wrong theorem statement only kills itself.

1. **Core-node list**: high in-degree `def`/`class`/`structure` declarations are
   selected (measured load-bearing walls: `IsEmbeddedSubmanifold` referenced 18×,
   `TopologicalManifold` 17×), plus hand-added semantically-subtle definitions;
   `theorem`s generally don't qualify.
2. **CODEOWNERS**: core-node files map to math experts; no merge without owner
   approval (enforced by GitHub).
3. **Experts review only two things**: whether the `**Math.**` docstring and the
   statement describe the same mathematical object; and whether the definition's
   instantiation test is non-vacuous (an example in `Tests/`, e.g. "the sphere is
   an `IsEmbeddedSubmanifold`", to block "hypotheses unsatisfiable, vacuously
   true").
4. Non-core nodes: AI review + spot checks.

In one line: the kernel eliminated proof review, the remaining burden concentrates
on the trusted base, and the load-bearing part of the trusted base is the
dependency-graph hubs — pin the hubs to experts via CODEOWNERS, buying global
correctness with the least expert time.

## For the team to decide

- [ ] Add three linters (docstring tag, namespace whitelist, provenance line) to
      `OpenGALib/Util/Linter/`?
- [ ] Core-node in-degree threshold (suggest ≥ 5; first list ships with item #1).
- [ ] CODEOWNERS mapping: manifold foundations / submanifolds & slices / boundary
      & geometric-measure-theory interface — who owns each.
- [ ] Auto-PR trigger: local script / GitHub Action / scheduled agent.
- [ ] Human-review SLA (suggest core-node PRs answered within three working days).

**Pilot**: item #1 runs the full loop semi-manually to calibrate the template and
linters; rework rate and human-review findings decide the automation depth for
#2–9.

---
Related: issue #61 · `import/smooth-manifolds-lee` (`a5f308c`)
