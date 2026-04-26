# CLAUDE.md

## Mission

This framework is a Lean 4 mathematical software project, not a one-shot paper formalization.

Two parallel deliverables:

1. **Paper "Alternative Regularity via Non-Excessive Sweepouts"** (Xinze Li, Yangyang Li): formal verification companion in Lean 4.
2. **Reusable Lean 4 mathematical software libraries**: GeometricMeasureTheory, MinMax theory, Regularity theory — Mathlib upstream candidates.

Both deliverables are first-class. Architectural decisions favor long-term software value over short-term paper expedience.

## Architecture

Four packages, layered:

```
GeometricMeasureTheory     ← infrastructure (Pitts/Simon/Allard primitives)
       ↑
MinMax                     ← domain (min-max theory, contains Sweepout subnamespace)
Regularity                 ← domain (regularity theory; Wickramasekera, Allard, Schoen-Simon, etc.)
       ↑
AltRegularity              ← application (paper-specific chain proofs)
```

Each package independently buildable. Namespace separation reflects layering.
GeometricMeasureTheory must not reference paper-specific or domain-specific concepts.
MinMax and Regularity must not reference paper-specific concepts.
AltRegularity is the paper-specific app; future papers are separate apps consuming the same lib stack.

## Working Mode

This is software engineering, not paper writing. Long-running atomic tasks (refactors, layer additions, cited theorem alignments) are normal. Mid-task broken state is expected.

### Continue, do not retreat

When facing build errors during a refactor or grounding task:

- **Mechanical errors** (unknown identifier, qualify reference, add `open`, propagate typeclass): continue fixing. Pattern is known; pattern is finite.
- **Genuine blockers** (Mathlib API truly missing, typeclass conflict requiring framework-level redesign): stop, report, ask.

Do not propose fall back / revert / simplification mid-task. User decides scope changes.

### Atomic commits

Do not commit mid-refactor. Complete the task and commit once at end, or fail-and-report without committing. Working directory can be reset cleanly.

origin/main is sacred only after explicit commit. Working dir broken state does not affect origin/main.

### Stuck protocol

If genuinely stuck after 5+ attempts on same error: report current state, ask for direction. Do not auto-revert.

## Standards

### Paper-faithful grounding

GMT primitive real definitions must align with Pitts 1981 / Simon 1983 / Allard 1972. Cite source in docstring (`**Ground truth**: ...`).

Cited theorem statements (Wic14, CLS22, DLT, CL03, Pitts, Allard) must be strict-aligned with paper §X verbatim. Three-way alignment table maintained in `references/cite_verification.md`.

### Sorry discipline

Every sorry categorized: PRE-PAPER (Mathlib gap), CITED-BLACK-BOX (theorem quoted, body never proven), PAPER-INTERNAL (paper proof obligation), CONJECTURAL (open mathematics).

Never silently weaken statements to remove sorry. Either prove, leave sorry'd, or document blocker.

### Chain proofs

Substantive chain proofs (`main_theorem_*`, `*_of_nonExcessive`, `regularity_of_*`, etc.) must remain 0-sorry, non-circular. Refactors preserve this invariant.

### Ground truth annotation

All opaque GMT primitives have `**Ground truth**: Simon §X / Pitts §Y` docstring reference, even when retreated. Future grounding attempts inherit this reference.

### Naming

Namespace and package names are concept-level, not person-level. Avoid attribution names (no `Wickramasekera`, no `AlmgrenPitts` as top-level package). People appear in citations + docstrings, not in namespace structure.

## Velocity

This framework moves at software engineering speed, not paper writing speed.

- Statement layer lockdown: days, not months.
- GMT primitive grounding: hours per primitive.
- Cited theorem strict alignment: minutes per theorem.
- Refactor (layer separation, namespace cleanup): hours, not weeks.

Do not estimate task cost using traditional mathematician productivity model. Mathlib + Claude Code + cumulative pattern reuse compounds productivity. Mathlib uses `lake exe cache get` — Mathlib is not built locally, do not estimate Mathlib build time as cost.

## Long-term Trajectory

Short term: complete Layer A grounding, finish Round 5 cited alignment, refactor architecture stable.

Mid term: Layer B grounding (Group C/D primitives via Simon §X infrastructure build), `GeometricMeasureTheory` package extracted to standalone repo, Mathlib upstream PR begins.

Long term: framework is reference for GMT formalization. Reusable across paper formalizations (this paper, future papers, collaborator's work). `GeometricMeasureTheory`, `MinMax`, `Regularity` integrated into Mathlib over time.

The framework's value outlives any single paper. Decisions reflect this.

## Identity

The user is Xinze Li (Moqian), 5th-year math PhD at University of Toronto, advisor Yevgeny Liokumovich. Communication preferred in Chinese. Avoids em-dashes and AI-style phrasing.

Strategic role: 总指挥 — sets direction, decides scope.
Claude (chat): 参谋 — translates direction into Claude Code prompts.
Claude Code: executor — runs prompts, mechanical work, build verify.

These roles are stable. Claude Code's job is execution within scope; scope decisions belong to Moqian via Claude (chat).
