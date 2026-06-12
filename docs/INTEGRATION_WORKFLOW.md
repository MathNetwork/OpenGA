# Integration Workflow

Source of truth for how content from reference branches reaches `main`. Sister to `REFACTOR_PLAYBOOK.md` (in-tree refactors) and the per-import worklist documents (e.g. `SMOOTH_MANIFOLDS_LEE_WORKLIST.md`). Goal: **external material enters the library only through our conventions, in reviewable units, with provenance intact**.

## Branch topology

```
import/<source-name>     frozen reference snapshot (read-only, never merged)
        |  manual porting, never `git merge`
        v
port/<work-item>         short-lived porting branch, one worklist item each
        |  pull request + CI + review
        v
develop                  integration trunk
        |  batched promotion pull requests
        v
main                     release grade
```

| Branch role | Rules |
|---|---|
| `import/*` | Holds an external project snapshot under `staging/`, pinned to one commit. Read-only: never merged, never rebased, never force-pushed. Content reaches the library by re-implementation only. `staging/` must never appear on `develop` or `main`. |
| `port/*` | Cut from `develop`. Scope = exactly one worklist item. Short-lived: open the pull request as soon as the item builds. If item B depends on unmerged item A, branch `port/B` from `port/A` — do not hand-copy unmerged content from `develop`. |
| `develop` | Integration trunk. Receives port pull requests. Must always build clean (zero `sorry` from ports). |
| `main` | Receives batched promotions from `develop` (existing practice). |

**Why imports are never merged.** A merge would (a) put foreign-convention source in our history, (b) break the independent-library stance, and (c) invalidate the audit: overlap classification is valid only for the audited snapshot commit. The import branch is a fixture the audit is anchored to, not a development line.

## Coordination ledger

Each import gets a worklist document in `docs/` produced by a full overlap audit (classification vs Mathlib and vs this library, value rating, target module). The worklist is the **coordination ledger**:

- Every item carries a status: `todo` / `in-progress @ port/<branch>` / `merged @ #<PR>` / `skipped (<dup reason>)`.
- Claim an item by setting it `in-progress` — the ledger change lands in the same pull request as the port itself.
- Nobody touches an item marked `in-progress` by someone else.
- Dependency order is recorded in the worklist's construction-order section; independent items may proceed in parallel.

## Quality gates per port pull request

1. **Conventions**: namespaces replaced (no foreign generic namespaces such as bare `Manifold`), files placed per the normalized module layout, names per `NAMING_CONVENTION.md`, no bare initialisms.
2. **Zero `sorry`**: a source file containing `sorry` is either completed during the port or excluded from the item.
3. **Full `lake build` locally before the pull request** — not language-server diagnostics only. Ports touch typeclass resolution paths; incremental builds miss downstream `@[simp] rfl` breakage (clean dependent `.olean` files when definition bodies change).
4. **Provenance line** in the module docstring: `Ported from <source> <path> (<commit>), restructured.` This is what makes future upstream diffs actionable.
5. **Linter baselines**: no new violations against the fitness functions in `OpenGALib/Util/Linter/`.
6. No `Co-Authored-By` trailers on this repository.

## Upstream updates

New material from the same source goes to a **new versioned branch** (`import/<source-name>-v2`), never a force-push of the old one. Then:

1. `git diff <old-commit>..<new-commit> -- staging/` to isolate changed files.
2. Re-audit the delta only; patch the ledger.
3. Old audit results for unchanged files remain valid.

## Retirement

When all high-value items of an import are ported or consciously skipped:

1. Tag the reference branch (`reference/<source-name>-<yyyy-mm>`).
2. Delete the `import/*` branch.
3. Mark the worklist document as closed (keep it — it is the provenance record).

## Current imports

| Import branch | Snapshot | Worklist | Status |
|---|---|---|---|
| `import/smooth-manifolds-lee` | `a5f308c` (2026-06-12) | `SMOOTH_MANIFOLDS_LEE_WORKLIST.md` | audit complete, porting not started |
