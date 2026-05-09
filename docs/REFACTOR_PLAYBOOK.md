# Refactor Playbook

Source of truth for OpenGALib refactor workflows. Sister to `scripts/`
(reusable codemods) and the project's CLAUDE.md (architectural stance).

The goal: **same operation never costs more than the first time**.

---

## Decision tree

```
What's the refactor about?
├─ Rename a single identifier (def, theorem, structure field)?
│   └─ VSCode F2 (Rename Symbol).
│      Lean LSP scans the import graph semantically.
│      Doesn't touch docstrings/comments. Safest possible.
│
├─ Rewrite an import path prefix across many files?
│   └─ scripts/rewrite-import.sh OLD_PREFIX NEW_PREFIX
│      Idempotent, refuses dirty working tree, prefix-match.
│
├─ Move file or directory?
│   └─ git mv first, then scripts/rewrite-import.sh.
│      git mv preserves rename detection in history.
│
├─ Introduce or migrate notation?
│   └─ Hand-write a 5-line example file FIRST. Verify parsing,
│      typeclass inference, simp interaction — before any sweep.
│      THEN bulk-migrate via perl/sed AND audit docstrings
│      (text replace catches them too — see Pitfalls #2).
│
├─ Change a typeclass cascade or generic signature?
│   └─ Manual. No bulk tool helps. Build incrementally.
│      Use git checkpoints between each step.
│
├─ Need an AST-aware operation (rename only in code, not in
│   docstrings; find all theorems referencing X; etc.)?
│   └─ Lake script. See "Lake script vs bash" below.
│
└─ Bulk delete dead content (e.g., a sub-package being removed)?
    └─ git rm -r + scripts/lean-grep.sh to find dangling refs +
       manual cleanup of those refs.
```

---

## Pre-flight checklist (always)

1. **`git status` clean.** No uncommitted changes. The bulk operation
   should be a single revertible step.
2. **Snapshot commit** of the current good state if there's any pending
   work: `git commit -am "snapshot before X refactor"`.
3. **One refactor concern per commit.** Don't bundle "rename + reorganize
   + add deprecation alias" into one diff. Three separate commits.
4. **`lake build` after each commit.** Catches silent breakage early
   when revert is still cheap.

If anything fails: `git reset --hard HEAD~1` and retry. The atomic-commit
discipline makes rollback one command.

---

## Lake script vs bash — when to use which

| Need | Tool | Reason |
|------|------|--------|
| File text replacement | bash + sed/perl | Milliseconds, well-understood |
| Import path rewrite | `scripts/rewrite-import.sh` | Already written |
| `grep` on Lean source only | `scripts/lean-grep.sh` | Excludes `.lake/`, `.git/` |
| Rename identifier in code only (skip docstrings) | Lake script | Needs Lean syntax tree |
| Find all theorems whose statement uses X | Lake script | Needs `Lean.Environment` API |
| Audit `@[simp]` lemma RHS shapes | Lake script | Needs elaborator |
| Generate a typeclass dependency graph | Lake script | Needs full elab info |
| One-off file munging | Inline shell command | Don't bother formalizing |

**Rule of thumb:** if the codemod would need to *understand* Lean
syntax or semantics, write it in Lean (Lake script). Otherwise bash is
faster to write and run.

### Lake script template

In `lakefile.lean`:

```lean
script myCodemod (args : List String) do
  match args with
  | [arg1, arg2] =>
    -- ... do work using IO + Lean APIs ...
    return 0
  | _ =>
    IO.eprintln "Usage: lake script run myCodemod ARG1 ARG2"
    return 1
```

Invoke: `lake script run myCodemod foo bar`.

For AST-level work, `import Lean` and use `Lean.Environment`,
`Lean.Syntax`, `Lean.Elab.*`. Mathlib's `scripts/` directory has good
examples.

---

## Pitfalls (encountered, in this lib's history)

1. **Text-level sed corrupts docstrings.** `sed 's/X/Y/g'` on `.lean`
   files matches `X` inside `/-- ... -/` blocks too. After bulk
   migration, search docstrings with `scripts/lean-grep.sh '<old form>'`
   and clean residual mentions. Or use VSCode F2 (semantic) when
   available.

2. **`open scoped X` requires the namespace to exist via imports.**
   Adding `open scoped X` to a file whose import graph doesn't reach a
   `namespace X` declaration produces "unknown namespace X" build
   error. After any sweep that adds scoped opens, verify with
   `scripts/lean-grep.sh 'open scoped'`.

3. **Notation prefix conflicts with built-in syntax.**
   - `T[x]` clashes with Lean's array indexing (`term[term]`)
   - `T x` (where `T` is an identifier) is parsed as function
     application, beating a `notation:max "T " x:max` pattern
   - Solutions that work: paren form (`Tan(x)`, like `Ric(X, Y)`),
     bracket form with non-identifier prefix (`∇[X]`, since `∇` is in
     Unicode category `Sm`, not `Lu`).

4. **Notation requires careful eta-reduction.** `fun x => f x`
   wrappers in notation RHS create lambdas that don't beta-reduce in
   simp's normal form, breaking pattern matches in subsequent rewrites.
   Always eta-reduce: `notation X => f` not `notation X => fun x => f x`.

5. **Typeclass inference can fail through `_` in notation.** A
   `notation:max "Tan(" x ")" => TangentSpace _ x` gets stuck when
   Lean can't pin the implicit `I : ModelWithCorners` from
   surrounding context. If this happens repeatedly, either:
   (a) keep the original verbose form `TangentSpace I x`, or
   (b) make `I` explicit in the notation.
   `abbrev`-based shorthands hit similar issues.

6. **Force-pushing to remove an oversight is partially effective.**
   `Co-Authored-By: ...` trailers, once pushed to a public repo,
   remain in GitHub's contributor cache even after the commit is
   force-pushed away. The orphan commit is still server-side. Lesson:
   **don't push to a public repo with a trailer you'd regret**.
   Memory `feedback_release_repo_attribution.md` enforces this for
   MathNetwork/OpenGA going forward.

---

## Adding to this playbook

When a refactor pattern is performed **3+ times** with the same
manual workaround, lift it into:

* a `scripts/` entry (if shell-tool-shaped), or
* a `lake script` entry (if AST-aware), and
* a row in the decision tree above + a Pitfall note if it has a known
  failure mode.

The playbook is dogfood. Trust accumulates over commits.
