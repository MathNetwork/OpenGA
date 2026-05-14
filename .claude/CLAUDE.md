# CLAUDE.md

## Mission

OpenGALib is a reusable Lean 4 mathematical software library stack — Algebraic, Tensor, Riemannian, GeometricMeasureTheory — engineered for long-term software value. Paper-specific formalization sub-projects live in separate repos and consume this stack via `require OpenGALib from ".."`.

The Lean code is the primary mathematical artifact. Cited papers (Petersen, Pitts, Simon, Allard, Wickramasekera) supply ground truth; prose presentations are renderings of the Lean development, not its source. When code and prose disagree, the code is authoritative; refactoring code does not require co-editing prose.

## Architecture

Single Lake package `OpenGALib`, organised under directory tree:

```
OpenGALib/
├── Algebraic/                 ← BilinearForm, Riesz, RatVector
│         ↑
├── Tensor/                    ← DifferentialForm, MultilinearSection, Alternating
│         ↑
├── Riemannian/                ← Connection, Curvature, Metric, SecondFundamentalForm
│         ↑
└── GeometricMeasureTheory/    ← Variation, HasNormal, Stable, Varifold
```

`OpenGALib` is a package name, never a namespace prefix. Content lives in concept-level namespaces matching Mathlib idiom (`namespace Riemannian`, `namespace BilinearForm`, `namespace DifferentialForm`). Mathlib-extension lemmas live in the Mathlib namespace they extend (`namespace ContinuousLinearMap`, etc.) so dot-notation works.

Layer separation: each layer must not reference paper-specific concepts. Each layer is a candidate for spin-out as a standalone Lean library.

Namespaces and package names are concept-level, not person-level. No `Wickramasekera`, no `AlmgrenPitts` as top-level. People appear in citations and docstrings, not in namespace structure.

### Folder organization

Within each layer, every math concept gets its own folder. Concept folders use **content-named anchor files** (`Connection/LeviCivita.lean`, `Curvature/RiemannCurvature.lean`, `Metric/RiemannianMetric.lean`), never role-named (no `Basic.lean`, `Defs.lean`, `Foundation.lean`). Folder name carries domain meaning ("screaming architecture", Robert C. Martin); anchor name carries the specific math concept.

Standalone concepts (single file, no sub-modules) live inside the layer's relevant folder: `Riemannian/Operators/Gradient.lean`, `Riemannian/Instances/EuclideanSpace.lean`. No top-level scattered files alongside concept folders.

There is one role-named folder, `Util/`. Two-tier layout: top-level `OpenGALib/Util/` for cross-layer Eng (notation, attributes, Mathlib-extension lemmas); per-layer `OpenGALib/<Layer>/Util/` for layer-scoped Eng (`Riemannian/Util/MusicalIso.lean`, `Riemannian/Util/MetricInnerSmoothness.lean`). Files inside `Util/` are content-named — the folder carries the role.

### Software-engineering principles applied

Folder organization, anchor purity, and the Math/Eng/Mixed split stand on well-known software-design principles. References for further reading when redesign questions arise:

- **Information hiding** (Parnas 1972, *On the Criteria to Be Used in Decomposing Systems into Modules*) — each module hides a single design decision. `Util/` sub-modules hide "Mathlib API form mismatches", "chart-pullback glue", "simp normal-form bridges".
- **Package by feature, not layer** — folders correspond to math concepts (Connection, Curvature), not framework roles (Defs, Lemmas, Helpers). Avoids "shotgun surgery" — one math change touching many role folders.
- **Screaming architecture** (Robert C. Martin) — folder names shout the domain (Riemannian geometry), not the framework (Lean 4 / Mathlib).
- **Common Closure Principle** — files that coevolve live in the same folder. Koszul, RieszExtraction, LeviCivita ⇒ `Connection/`.
- **Deep modules** (Ousterhout 2018, *A Philosophy of Software Design*) — anchor files have simple Math interfaces hiding complex proofs; `Util/` files hide engineering tax.
- **Stable Dependencies Principle** — `Algebraic ≺ Tensor ≺ Riemannian ≺ GMT`. `Util/` sits below everything in its layer (most stable, most depended-on).
- **Miller 1956 (7 ± 2)** — keep folder fan-out ≤ ~9 entries per level.

These principles motivate, but do not override, project-specific conventions. When they conflict with explicit OpenGALib rules (e.g. `Util/` is role-named, against package-by-feature purity), the explicit rule wins.

## Working stance

### Self-build is the default

When Mathlib lacks a primitive, exposes a non-firing scoped instance, has a typeclass diamond (lean4#13063), or surfaces an API in a non-applicable form, the response is framework self-build. Self-built primitives are first-class library content, not workarounds. The framework does not synchronize to Mathlib's PR cycle. Mathlib catch-up, when it happens, is a deprecation opportunity for selective subsets — not a milestone planned around.

Canonical pattern: locate the API surface (grep + read source), build framework analog with explicit instances + helpers + bridge typeclasses, drop Mathlib dependency from the cascade. `InnerProductBridge` (Phase 1.6) and `RiemannianMetric` (Phase 4.7) are template examples.

Bridge investment for cross-cutting blockers: when a single typeclass gap, scoped-instance non-firing, or API mismatch blocks multiple primitives, framework builds the explicit instance / accessor / typeclass cascade once and unblocks everything downstream.

### Continue, do not retreat

For build errors mid-task:
- Mechanical errors (unknown identifier, missing `open`, typeclass propagation): continue fixing
- Genuine blockers: report current state, ask for direction

Do not propose fallback, revert, or simplification mid-task. User decides scope changes.

### Retreat triggers

Real retreat triggers (all rare):
- Mathlib lemma genuinely missing AND framework self-build hits Lean kernel impossibility (universe inconsistency, unfixable def-eq diamond after 5+ documented workarounds, type-level constraint that no spike resolves)
- Self-build requires a Lean kernel primitive that does not exist

Rejected framings (all surfaced by Claude Code in the past, all wrong):
- "This is a Mathlib infrastructure issue, only fixable via PR"
- "Blocked by Mathlib upstream catch-up" / "Deferred until Mathlib's X matures"
- "Wait for Mathlib chart-machinery to evolve"
- "Specialized chart-machinery / vector bundle / typeclass-cascade expertise required"
- "Bundle-section conversion exceeds atomic-commit scope"
- "Hand off to expert session" / "Multi-session work needed" / "Dedicated focused session"
- "Strategic decision needed before proceeding"
- "Mathlib API in wrong form, can't directly apply"
- LOC count, component count, expected spike iteration count
- Time framing of any unit (今晚 / 几小时 / 几天 / multi-week / "session budget")

When any of these surface, the correct response is depth-audit Mathlib + framework self-build, not user escalation. Tasks are sized by mathematical content and architectural correctness, not by LOC, time, or session count.

### Atomic commits

Commit once at task end, or fail-and-report without committing. Working directory broken state mid-task is normal and does not affect origin/main. Do not commit mid-refactor.

## Code quality

A passing build is day zero, not done. The criteria below apply to every declaration written or refactored. Framework self-imposes Mathlib conventions (simp normal form, ext lemmas, docstring style, typeclass conventions) as a quality bar, independent of any PR intent.

### Math / Eng / Mixed tagging

Tag every declaration at the start of its docstring:

```lean
/-- **Math.** Paper-side definition of [concept]. ... -/
/-- **Eng.** Type-theoretic glue, no paper analogue. ... -/
/-- **Mixed.** Math: [statement]. Eng: [glue carried in the proof]. ... -/
```

Criteria:
- **Math** — directly corresponds to a paper / textbook concept; rename map is `s/_/ /` reading test
- **Eng** — basepoint mismatches, index translations, chart helpers, bound-carrying boilerplate, simp-normal-form bridges
- **Mixed** — math statement on top of an engineering proof body

Without explicit tagging, decisions about which helpers to extract, inline, or rename lack any criterion. Engineering tax becomes invisible to casual reading. Tags are greppable: `Grep "\*\*Eng\.\*\*"` lists the engineering surface.

### Natural-language reading test

Names must pass: replace underscores with spaces, read aloud, result should be a clear mathematical statement. Failures signal an unclear role (too specific, too abstract, placeholder word, unexpanded abbreviation) and trigger rename, not silent acceptance.

### Design is subtraction

- No bridge wrappers from old API to new
- No `@[deprecated]` aliases retained for compatibility
- No double APIs for the same concept
- Hard migrations across all call sites in a single atomic change

Bridges and aliases are technical debt by default. The Phase 4.7 cascade (dropping `RiemannianBundle` end-to-end with no bridge, retiring `InnerProductBridge.lean`) is the template.

### Same object, multiple views

When a mathematical object has multiple natural type-theoretic presentations (bundle section / function-form / chart pullback; matrix / digraph / active set), connect them by bridge lemmas and keep all views first-class. Do not collapse to one "canonical" view forcing others through it.

### Engineering tax encapsulation

Anchor files expose only `**Math.**`-tagged declarations (paper-side definitions, theorems, notations). All `**Eng.**` and `**Mixed.**` declarations — the "technical infrastructure" supporting proofs — live in `Util/` sub-modules, never inline in the anchor. Mathematical reading of the anchor stays uncluttered; the Eng surface is searchable via the `Util/` folder.

Engineering tax (bound-carrying boilerplate, index translations, chart-pullback wrappers, basepoint-mismatch wrappers, simp-normal-form bridges, `@[simp]` def-unfolds) is unavoidable, but its location is chosen. Push it out of the math-anchor file into a `Util/` sub-module.

Two-tier `Util/` layout, following Mathlib idiom:

- **Top-level** `OpenGALib/Util/` — Eng helpers shared across multiple layers (Mathlib-extension `mfderiv` lemmas, notation, tactics, attributes).
- **Per-layer** `OpenGALib/<Layer>/Util/` — Eng helpers scoped to a single layer (e.g. `Riemannian/Util/CotangentFunctional.lean`, `Riemannian/Util/MusicalIso.lean`). Per-layer `Util/` builds on top-level `Util/`.

Files inside `Util/` are content-named, never role-named: `MusicalIso.lean`, `CotangentFunctional.lean`, `ChartJacobianSmooth.lean`, `ConnectionLaplacianSimp.lean`. The folder name `Util/` carries the role; individual files describe their content. No `Helpers`, `Base`, `Foundation` suffixes inside `Util/`.

### Signature-reads-as-paper criterion

Headline lemmas (`bochner_weitzenboeck`, `leviCivitaConnection_exists`, `firstVariation_*`) are stable when their Lean signature reads as the textbook sentence with no engineering tax exposed. If side-condition predicates and index translations sit inline alongside the mathematical content in the signature, the structural pass is incomplete. UX optimizations (`@[simp]` / `@[ext]` / `@[simps]` / `abbrev` / naming polish) apply only past this point — premature polish on evolving interfaces gets discarded by the next refactor.

## Fitness functions

Architectural rules are enforced by Lean-native linters in `OpenGALib/Util/*Linter.lean`. They fire during elaboration (LSP shows inline warnings; `lake build` emits them) and gate every push / pull request via GitHub Actions.

Background: Neal Ford et al., *Building Evolutionary Architectures* (2017) — coined "fitness functions" for executable architectural tests. OpenGALib adapts the pattern to Lean.

Current linters (in `OpenGALib/Util/`):

- **`MathTagLinter`** (`linter.openGAMathTag`, default `true`, baseline `0`) — every declaration's docstring must begin with `**Math.**`, `**Eng.**`, or `**Mixed.**`.
- **`AnchorPurityLinter`** (`linter.openGAAnchorPurity`, default `true`, baseline `20`) — `**Eng.**` / `**Mixed.**` declarations forbidden outside `Util/` directories. Baseline is current debt; CI fails if count grows.
- **`NamingLinter`** (`linter.openGANaming`, default `true`, baseline `0`) — forbid bare initialisms `CLM`, `NACG`, `IPS` in declaration names; require Mathlib-style full names (`ContinuousLinearMap`, `NormedAddCommGroup`, `InnerProductSpace`).

CI implementation (`.github/workflows/ci.yml`): the build job greps `lake build` output for each linter's warning prefix, fails if count exceeds the hardcoded baseline. Baselines only ever decrease; never grow without explicit justification (same discipline as the sorry count gate).

Adding a new linter: drop `OpenGALib/Util/<Name>Linter.lean`, register the import in `Util/Attributes.lean`, add the baseline check in `ci.yml`. Template pattern: `MathTagLinter.lean`.

## Sorry discipline

Every sorry / opaque / placeholder is categorized:
- PRE-PAPER (Mathlib gap, framework self-build owns repair)
- CITED-BLACK-BOX (theorem quoted as given, body never proven)
- PAPER-INTERNAL (paper proof obligation)
- CONJECTURAL (open mathematics)

Each carries a repair plan in its docstring: missing API or framework primitive, repair trigger, repair owner. Generic "blocked by Mathlib" annotations decay into permanent technical debt and are rejected.

GMT primitives align with Pitts 1981 / Simon 1983 / Allard 1972 and cite source via `**Ground truth**: ...`. Cited theorem statements (Wic14, CLS22, DLT, CL03, Pitts, Allard) are strict-aligned with paper §X verbatim.

Substantive chain proofs (headline theorems and the bridge lemmas they compose through) remain 0-sorry, non-circular. Refactors preserve this invariant.

Never silently weaken a statement to remove a sorry. Either prove, leave sorry'd, or document blocker with repair plan.

## Refactor protocol

Refactor is strategic re-audit triggered by accumulated architectural debt or new mathematical insight, not implementation work.

1. Strategic question batch first (before any code change): hierarchy correct? Concept boundaries placed correctly between layers? Sub-namespace divisions clean? Dependency graph cycle-free?
2. Plan from first principles, not from current state. Current state triggered the refactor; planning anchored on it misses the architectural fix.
3. Execute in atomic chunks with build verify + 0-sorry preservation per commit.
4. Allow strategy adjustment mid-execution. Implementation surfaces details invisible during planning. Do not push through with stale plan.
5. Audit again after refactor. Refactor is recurring ritual.

Playbook detail in `docs/REFACTOR_PLAYBOOK.md`.

## Phase plan

Done:
- Phase 0–1.6: architecture lock, Layer A+B real grounding, Riemannian primitives (9 of 9 real, zero existence axioms)
- Phase 4 / 4.5 / 4.7: Levi-Civita Koszul construction, framework typeclass redesign, `RiemannianMetric` cascade end-to-end, `RiemannianBundle` dropped
- Bochner stack (commit `520b9e6`, 2026-05-13): `bochner_weitzenboeck` + `leviCivitaConnection_exists` (all 3 conjuncts) + `manifoldGradient_smooth_of_smooth` unconditional. Riemannian sorry count = 0. New file `MusicalIso.lean` (~1100 LOC) houses the chart-Gram-matrix machinery.

In flight:
- Engineering optimization pass anchored on Bochner. Apply Math/Eng/Mixed tagging, NL reading test, and signature-reads-as-paper criterion to the Bochner stack first; propagate outward to Connection.lean and the Riemannian package.

Remaining:
- Phase 2: Round 5 cited theorem strict alignment Items 4–9 (DLT13, `exists_minmaxLimit`, `isStationary_of_minmaxLimit`, `locallyStable_of_oneSidedMinimizing`, `interpolation_lemma`, `isRectifiable_of_isStationary_of_density_pos`)
- Phase 3: Isoperimetric production-grade lib (parallel to Riemannian)
- Phase 5 (event-triggered): UX optimization once interfaces stabilize per signature-reads-as-paper
- Phase 6: final pre-release polish (CI, doc-gen4, README, references.bib)

## Identity

Xinze Li (Moqian), 5th-year math PhD, University of Toronto, advisor Yevgeny Liokumovich. Communication in Chinese. Avoids em-dashes and AI-style phrasing in chat.

Role division:
- Moqian (总指挥): direction, scope, refactor triggers
- Claude chat (参谋): translates direction into executable Claude Code prompts
- Claude Code (executor): mechanical execution, build verification

Strategic decisions belong to Moqian. Translation belongs to Claude chat. Mechanical work belongs to Claude Code. Claude Code does not escalate scope decisions: when the closure path is mechanical self-build, the response is depth-audit + iterate, not "strategic decision needed".
