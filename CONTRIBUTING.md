# Contributing to OpenGA

Thanks for your interest. Conventions below are non-negotiable for
merged contributions but liberally relaxable for sketches / WIP / drafts.

## Design principles

* **Math object is primary; Lean is a UI.** API surface, ergonomics,
  and discoverability come first. Engineering noise (chart-pullback
  helpers, typeclass cascades, smoothness bridges) is `private` and
  hidden under sections inside the `.lean` file of the math object it
  serves.

* **Chain depth over breadth.** OpenGA targets proof depth on the
  Riemannian → GMT chain rather than broad parity with Mathlib's full
  differential geometry. If a theorem isn't on the chain, we don't
  pre-port it; pull when needed.

* **Self-build when Mathlib lacks a primitive.** When Mathlib has a
  gap blocking the chain (e.g., the framework-owned `RiemannianMetric`
  typeclass that sidesteps the lean4#13063 NACG diamond), we build
  the framework analog rather than wait for upstream.

## Where to start

1. **Read `docs/NAMING_CONVENTION.md`** before opening a PR. It's
   enforced by reviewers.
2. **Skim `docs/REFACTOR_PLAYBOOK.md`** if your change touches more
   than one file. The playbook describes the verifiable-object
   consolidation pattern, programmatic bulk-edit recipes, and the
   pitfalls we've encountered.
3. **Pick a sorry to close**, or open an issue first if your idea is
   architectural. Every `sorry` in the lib carries a closure plan in
   its docstring (`**Sorry status**:` / `Closure path:` / `Repair
   plan:`); start from one whose path you understand. Good first
   issues: closing low-dependency PRE-PAPER sorries in `Algebraic/`,
   `Tensor/`.
4. **External references** — `external/` (git-ignored) contains the
   `qinz1yang/differential-geometry` reference repo we draw from.
   We **re-implement** in our conventions — never copy.

## PR workflow

1. **Fork + branch** off `main`. One concern per PR — don't bundle
   rename + refactor + bug-fix.
2. **Local `lake build` must be clean** (warnings OK; no errors).
3. **Local CI checks**: `sorry` count and `axiom` count are CI-enforced
   (see `.github/workflows/ci.yml`). If your PR changes either:
   - Update the `EXPECTED` constant in the workflow.
   - Document the new `sorry` / `axiom` in the relevant module
     docstring with a closure plan.
4. **Commit messages** — short subject line, prose body explaining
   *why* (not just *what*); reference the issue if relevant. Don't
   add Co-Authored-By trailers for AI assistants (we strip them on
   release). The repo ships a `commit-msg` hook in `.githooks/` that
   strips Claude Code attribution automatically; activate per-clone
   with:
   ```
   git config core.hooksPath .githooks
   ```
5. **Open PR** against `main`. Reviewers will check naming + chain
   depth + docstring quality. Expect one round of feedback for
   non-trivial changes.

## Style

| Aspect | Where to look |
|---|---|
| Naming (defs, theorems, types) | `docs/NAMING_CONVENTION.md` §1-§3 |
| Docstring template | `docs/NAMING_CONVENTION.md` §5-§6 |
| File / namespace structure | `docs/NAMING_CONVENTION.md` §7-§9 |
| `@[simp]` / `@[ext]` policy | `docs/NAMING_CONVENTION.md` (Phase 5 deferred — apply conservatively) |
| Engineering hiding | `docs/NAMING_CONVENTION.md` §7 (`private`, `where`-aux) |
| Bulk codemods | `docs/REFACTOR_PLAYBOOK.md` + `scripts/` |

In short: **textbook-clean math API at the surface, engineering
hidden underneath**. If a reader of the API has to scroll past
`set_option backward.isDefEq.respectTransparency false` or
`coordChangeL_apply_of_mem_baseSet` to find the math, the file is
mis-organized.

## What we don't accept

* `Co-Authored-By` trailers for AI assistants in commit messages
  (we strip on release).
* `Inspired by <repo>` / `Adapted from <author>` attribution in
  source files — attribution belongs in commit history, not in
  code or docstrings.
* `paper §X` / project-specific cross-references in `Algebraic/`,
  `Tensor/`, `Riemannian/`, `GeometricMeasureTheory/` — these
  namespaces must be paper-agnostic; paper-specific work lives in
  downstream consumer repos.
* Self-tests / UX tests as `example` blocks at end of file — these
  are documentation pretending to be test; we keep the real math
  in the body and let LSP + `lake build` catch regressions.
* Adding `sorry` without updating `EXPECTED` in CI + adding a
  closure plan in docstring.

## Questions

Open an issue. Architectural / design questions are welcome there
before you write code.
