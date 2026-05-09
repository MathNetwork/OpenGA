# `scripts/`

Reusable codemods + dev helpers for OpenGALib refactor workflows.
Sister to `docs/REFACTOR_PLAYBOOK.md` (which documents the decision
tree for *which* tool to reach for).

## Available scripts

* **`rewrite-import.sh OLD_PATH NEW_PATH`** — rewrite every
  `import OLD_PATH...` line to `import NEW_PATH...` across all `.lean`
  files. Prefix match, so paths nested under `OLD_PATH` come along
  automatically. Refuses to run on a dirty working tree.

* **`lean-grep.sh [grep_flags] PATTERN`** — `grep -r` restricted to
  `.lean` files, excluding `.lake/` and `.git/`. Use this instead of
  raw `grep` to avoid matching Mathlib source under `.lake/`.

## Convention for adding new scripts

1. Triggered by **3+** repetitions of the same manual command in past
   refactor sessions. One-off pain doesn't justify a script.
2. Self-contained shell scripts (no Python / Node deps). `bash` + standard
   Unix tools (`grep`, `sed`, `perl`, `find`).
3. **Refuse to run on dirty working tree** if the script makes bulk
   modifications. Bulk edits must be one revertible step.
4. Document inputs / examples in the script header.
5. Add an entry to this README's "Available scripts" list.

## Why scripts and not just inline commands?

Each script is a **frozen decision** about how to handle a recurring
operation safely. Inline `sed` / `find` commands accumulate
context-specific bugs (forget to exclude `.lake/`, miss a `git status`
check, etc.). Lifting them into named scripts gives:

* **Repeatability** — `scripts/rewrite-import.sh A B` always behaves the
  same way, no edge case rediscovered.
* **Documentation** — the script header is the spec.
* **Auditability** — `git log scripts/` shows how the workflow has
  evolved.
