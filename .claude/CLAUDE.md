# CLAUDE.md

## Mission

OpenGALib is a reusable Lean 4 mathematical software library — Algebraic, Tensor, Riemannian, GeometricMeasureTheory. Paper-specific formalization projects consume it via `require OpenGALib from ".."`.

The Lean code is the primary artifact. When code and prose disagree, the code wins; refactoring code does not require co-editing prose.

## Architecture

Single Lake package `OpenGALib`, layered:

```
Algebraic ≺ Tensor ≺ Riemannian ≺ GeometricMeasureTheory
```

`OpenGALib` is a package name, never a namespace prefix. Use concept-level namespaces (`namespace Riemannian`, `namespace BilinearForm`). Mathlib-extension lemmas live in the Mathlib namespace they extend so dot-notation works.

Each math concept gets its own folder with **content-named** anchor files (`Connection/LeviCivita.lean`, `Curvature/RiemannCurvature.lean`) — never role-named (no `Basic.lean`, `Defs.lean`, `Foundation.lean`).

The only role-named folder is `Util/`. Two tiers: top-level `OpenGALib/Util/` for cross-layer engineering helpers; per-layer `OpenGALib/<Layer>/Util/` for layer-scoped helpers. Files inside `Util/` are content-named — the folder carries the role.

Layers must not reference paper-specific concepts. Each is a candidate for standalone spin-out.

Mathlib primitives are used directly inside proof bodies but wrapped at the API surface under OpenGA names. No re-export `def`s whose only purpose is renaming. Cross-codebase bridges live in `OpenGALib/Bridges/<X>To<Y>.lean`, one-directional.

## Working stance

**Self-build is the default.** When Mathlib lacks a primitive, exposes a non-firing scoped instance, or surfaces an API in a non-applicable form, build the framework analog. Self-built primitives are first-class library content, not workarounds. Do not wait on Mathlib's PR cycle.

**Continue, do not retreat.** Mechanical build errors (unknown identifier, missing import, typeclass propagation) — keep fixing. Real blockers — report state, ask. Do not propose fallback, revert, or simplification mid-task; the user decides scope changes.

Rejected framings (all wrong, treat as a smell): "blocked by Mathlib upstream", "strategic decision needed", "exceeds atomic-commit scope", "specialized expertise required", or any time-/LOC-/session-budget framing. The correct response is depth-audit + iterate.

**Atomic commits.** Commit once at task end, or fail-and-report without committing. Broken working directory mid-task is normal. No mid-refactor commits.

## Code quality

**Math / Eng / Mixed tagging.** Every declaration's docstring begins with one of:

```lean
/-- **Math.** Paper-side definition of [concept]. ... -/
/-- **Eng.** Type-theoretic glue, no paper analogue. ... -/
/-- **Mixed.** Math: [statement]. Eng: [glue in the proof]. ... -/
```

Linter-enforced (`OpenGALib/Util/Linter/MathTag.lean`). Math names must pass the natural-language reading test: `s/_/ /` reads as a clear mathematical statement.

**Anchor purity.** Anchor files expose only `**Math.**` declarations. All `**Eng.**` and `**Mixed.**` live in `Util/` sub-modules. Linter-enforced (`OpenGALib/Util/Linter/AnchorPurity.lean`); exemptions for `instance` (synthesis needs co-location) and `private` (not exposed API).

**Design is subtraction.** No bridge wrappers from old API to new. No `@[deprecated]` aliases for compatibility. No double APIs for the same concept. Migrations are hard: rewrite all call sites in one atomic change.

**Same object, multiple views.** When an object has multiple natural presentations (bundle / function / chart-pullback; matrix / digraph), connect them by bridge lemmas and keep all views first-class. Do not force one canonical view.

**Signature reads as paper.** Headline lemmas are stable when the Lean signature reads as the textbook sentence with no engineering tax inline. UX polish (`@[simp]`, `@[ext]`, naming) applies only past this point — premature polish on evolving interfaces gets discarded.

## Discipline

**Sorries** are categorized (PRE-PAPER / CITED-BLACK-BOX / PAPER-INTERNAL / CONJECTURAL), each with a repair plan in its docstring. Substantive chain proofs (headline theorems + their bridges) stay 0-sorry, non-circular. Never silently weaken a statement to remove a sorry. CI baselines the count against `docs/SORRY_CATALOG.md`.

**Fitness functions** (`OpenGALib/Util/Linter/`) enforce architectural rules at elaboration time. Baselines only ever decrease. Adding a new linter: see `OpenGALib/Util/Linter/README.md`.

**Unused-import hygiene** via `lake exe shake OpenGALib --no-downstream`. CI baselines the count; PRs hold or reduce. Apply suggestions manually (`--fix` over-applies); add explicit imports to broken downstream consumers as needed.

**Refactor protocol** — see `docs/REFACTOR_PLAYBOOK.md`. Plan from first principles, not current state. Execute in atomic chunks with build-verify per commit.

## Role division

- **Moqian** (总指挥) — direction, scope, refactor triggers
- **Claude chat** (参谋) — translates direction into executable Claude Code prompts
- **Claude Code** (executor) — mechanical execution, build verification

Strategic decisions belong to Moqian; mechanical work belongs to Claude Code. Claude Code does not escalate scope when the closure path is mechanical self-build — depth-audit + iterate instead.
