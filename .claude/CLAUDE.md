# CLAUDE.md

## Mission

OpenGALib is a reusable Lean 4 mathematical software library. Paper-specific formalization projects consume it via `require OpenGALib from ".."`. The Lean code is authoritative — when code and prose disagree, the code wins.

## Architecture

Single Lake package `OpenGALib`. Math layers (dependency order, `≺` reads "is depended on by"):

```
Algebraic ≺ Tensor ≺ Riemannian ≺ { Comparison, GeometricMeasureTheory }
                  MetricGeometry   (Layer-1 parallel; metric-only stack)
```

Infrastructure folders: `Util/` (engineering helpers, depended on by all, depends on none), `Bridges/` (one-directional adapters between OpenGA and Mathlib; currently `RiemannianToLength`), `Tests/` (linter `#guard_msgs` regression).

`OpenGALib` is a package name, never a namespace prefix. Use concept-level namespaces (`namespace Riemannian`, `namespace BilinearForm`); Mathlib-extension lemmas live in the Mathlib namespace they extend. Anchor files are content-named (`Connection/LeviCivita.lean`, `Curvature/RiemannCurvature.lean`) — never role-named (no `Basic.lean`, `Defs.lean`, `Foundation.lean`).

`Util/` is the only role-named folder. Two tiers: top-level `OpenGALib/Util/` for cross-layer engineering helpers; per-layer `OpenGALib/<Layer>/Util/` for layer-scoped helpers. Files inside `Util/` are content-named.

Mathlib primitives are used directly in proof bodies but wrapped at the API surface under OpenGA names; no re-export `def`s for renaming.

## Working stance

**Self-build, don't retreat.** When Mathlib lacks a primitive or surfaces an API in a non-applicable form, build the framework analog — self-built primitives are first-class library content, not workarounds. Mechanical build errors (unknown identifier, missing import, typeclass propagation) keep fixing; real blockers report and ask. Do not propose fallback, revert, or simplification mid-task; the user decides scope changes. Treat as a smell: "blocked by Mathlib upstream", "strategic decision needed", "exceeds atomic-commit scope", "specialized expertise required", or any time-/LOC-/session-budget framing.

**Atomic commits.** Commit once at task end, or fail-and-report without committing. Broken working directory mid-task is normal. No mid-refactor commits.

## Code quality

**Math / Eng / Mixed tagging.** Every declaration's docstring begins with one of:

```lean
/-- **Math.** Paper-side definition of [concept]. ... -/
/-- **Eng.** Type-theoretic glue, no paper analogue. ... -/
/-- **Mixed.** Math: [statement]. Eng: [glue in the proof]. ... -/
```

Math names must pass the natural-language reading test: `s/_/ /` reads as a clear mathematical statement.

**Anchor purity.** Anchor files expose only `**Math.**` declarations; `**Eng.**` and `**Mixed.**` live in `Util/` sub-modules. Exemptions: `instance` (synthesis needs co-location) and `private` (not exposed API).

**Hard migrations.** Rewrite all call sites in one atomic change. No bridge wrappers, no `@[deprecated]` aliases, no double APIs for the same concept.

**Multiple views.** An object's natural presentations (bundle / function / chart-pullback; matrix / digraph) are connected by bridge lemmas and stay first-class — don't force a canonical view.

**Signature reads as paper.** Headline lemmas are stable when the Lean signature reads as the textbook sentence with no engineering tax inline. UX polish (`@[simp]`, `@[ext]`, naming) applies only past this point.

## Discipline

**Sorries** are categorized (PRE-PAPER / CITED-BLACK-BOX / PAPER-INTERNAL / CONJECTURAL), each with a repair plan in its docstring. Substantive chain proofs stay 0-sorry, non-circular. Never silently weaken a statement to remove a sorry. CI baselines the count against `docs/SORRY_CATALOG.md`.

**Shake** (`lake exe shake OpenGALib --no-downstream`) catches unused imports; CI baselines the count, PRs hold or reduce, manual apply (`--fix` over-applies).

**Refactor protocol** — `docs/REFACTOR_PLAYBOOK.md`. Plan from first principles, atomic chunks, build-verify per commit.

All architectural rules baseline-enforced by linters in `OpenGALib/Util/Linter/`; adding a new linter → `OpenGALib/Util/Linter/README.md`.

## Role division

- **Moqian** (总指挥) — direction, scope, refactor triggers
- **Claude chat** (参谋) — translates direction into executable Claude Code prompts
- **Claude Code** (executor) — mechanical execution, build verification
