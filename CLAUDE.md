# CLAUDE.md

## Mission

This framework is a Lean 4 mathematical software project, not a one-shot paper formalization.

Two parallel deliverables:

1. **Paper "Alternative Regularity via Non-Excessive Sweepouts"** (Xinze Li, Yangyang Li): formal verification companion in Lean 4.
2. **Reusable Lean 4 mathematical software libraries**: GeometricMeasureTheory, MinMax theory, Regularity theory — Mathlib upstream candidates.

Both deliverables are first-class. Architectural decisions favor long-term software value over short-term paper expedience.

Phase 1 (Layer A + Layer B real grounding) is complete: 20 GMT analysis primitives carry real Lean definitions. Phase 1.5 + 1.6 added a 5th independent Riemannian package: 8 of 9 Riemannian primitives (Riemann curvature, Ricci, scalar curvature, second fundamental form + squared norm, mean curvature, manifold gradient + squared norm) are real definitions; only `leviCivitaConnection` remains as an existence axiom (Levi-Civita Koszul, acceptable per textbook standard).

## Architecture

Single OpenGALib Lean library + AltRegularity sub-project, layered:

```
OpenGALib (single lean_lib, 4 sub-namespaces)
├── Riemannian                 ← lib (Connection, Curvature, SecondFundamentalForm, Gradient)
│         ↑
├── GeometricMeasureTheory     ← lib (Variation/, HasNormal, Stable, Varifold, ...)
│         ↑
├── MinMax                     ← lib (min-max theory, Sweepout subnamespace)
└── Regularity                 ← lib (regularity theory; Wickramasekera, Allard, Schoen-Simon, etc.)
            ↑
AltRegularity (sub-project, requires OpenGALib + paper companion)
```

OpenGALib is a single Lake package containing 4 sub-namespaces (Riemannian, GeometricMeasureTheory,
MinMax, Regularity). Namespace separation reflects layering — sub-namespaces are independently
meaningful and any subset is a future Mathlib-upstream candidate.
Riemannian is independent of paper-domain concerns and is a future spin-out
candidate as a standalone Lean library (Mathlib upstream / community use).
GeometricMeasureTheory must not reference paper-specific or domain-specific concepts.
MinMax and Regularity must not reference paper-specific concepts.
AltRegularity is the paper-specific sub-project (located at `AltRegularity/`, with
`AltRegularity/paper/` as the paper companion); future papers are separate sub-projects
consuming the same OpenGALib lib stack via `require OpenGALib from ".."`.

## Working Mode

This is software engineering, not paper writing. Long-running atomic tasks (refactors, layer additions, cited theorem alignments) are normal. Mid-task broken state is expected.

### Spike + iterate, do not audit-then-retreat

When an opaque primitive needs grounding, the default is to spike a real definition with chart-pullback / Mathlib API combinations, iterate through 2–5 mechanical fixes, and accept the result. Do **not** default to audit-and-decide-this-is-blocked-by-Mathlib. Empirically (Phase 1), "Mathlib lacks X" framings during planning are over-cautious 4 out of 5 times — `extChartAt` + `mfderiv` + `LinearMap.trace` + `Measure.map` + framework-grounded primitives (`VarifoldConverge`, `ofBoundary`) compose to handle most GMT analysis primitives. Real retreat trigger is **implementation failure after iteration**, not audit-stage estimate.

### Continue, do not retreat

When facing build errors during a refactor or grounding task:

- **Mechanical errors** (unknown identifier, qualify reference, add `open`, propagate typeclass): continue fixing. Pattern is known; pattern is finite.
- **Genuine blockers** (Mathlib API truly missing after iteration, typeclass conflict requiring framework-level redesign): stop, report, ask.

Do not propose fall back / revert / simplification mid-task. User decides scope changes.

### Atomic commits

Do not commit mid-refactor. Complete the task and commit once at end, or fail-and-report without committing. Working directory can be reset cleanly. origin/main is sacred only after explicit commit; working-dir broken state does not affect origin/main.

### Stuck protocol

If genuinely stuck after 5+ attempts on same error: report current state, ask for direction. Do not auto-revert.

### Bridge investment for cross-cutting blockers

When a single typeclass gap, scoped-instance non-firing, or API mismatch blocks multiple primitives, the high-leverage move is **bridge investment** — framework self-builds the explicit instance / accessor / typeclass cascade that Mathlib lacks. Bridge cost is typically ~30–100 LOC; cascade unblock is typically 5+ primitives. Refuse to retreat with "this is blocked at infrastructure level" framing without first depth-auditing the bridge cost.

Phase 1.6 canonical example: `InnerProductBridge` (4 explicit instances replicating Mathlib scoped-instance bodies, ~30 LOC) unblocked `manifoldGradient` + `secondFundamentalFormScalar` real defs, cascading to `scalarCurvature` + `secondFundamentalFormSqNorm` + `meanCurvature` via `stdOrthonormalBasis`. Total Phase 1.6: ~250 LOC, 4 commits, single session.

## Refactor Protocol

Refactor is not implementation work. Refactor is **strategic re-audit** triggered by accumulated architectural debt or new mathematical insight.

When refactor is triggered:

1. **Strategic question batch first** (before any code change): is the architecture mathematically correct? Hierarchy inverted (X primary vs Y derived)? Concept boundaries placed correctly between lib layers? Sub-namespace divisions clean? Naming still functional, or has paper-specific terminology leaked into lib? Dependency graphs free of cycles?
2. **Plan from first principles**, not from current state. Current state is what triggered the refactor; planning anchored on it misses the architectural fix.
3. **Execute in atomic chunks** with build verify + chain proof 0-sorry preservation per commit.
4. **Allow strategy adjustment during execution** — implementation surfaces architectural details invisible during planning. Update plan mid-refactor when warranted; do not push through with stale plan.
5. **Audit again after refactor** — what's the next architectural debt? Refactor is recurring ritual, not one-time event.

## Standards

### Paper-faithful grounding

GMT primitive real definitions must align with Pitts 1981 / Simon 1983 / Allard 1972. Cite source in docstring (`**Ground truth**: ...`).

Cited theorem statements (Wic14, CLS22, DLT, CL03, Pitts, Allard) must be strict-aligned with paper §X verbatim. Three-way alignment table maintained in `references/cite_verification.md`.

### Sorry / opaque / placeholder discipline

Every sorry / opaque / placeholder categorized: PRE-PAPER (Mathlib gap), CITED-BLACK-BOX (theorem quoted, body never proven), PAPER-INTERNAL (paper proof obligation), CONJECTURAL (open mathematics).

**Documented gaps require a repair plan**, not just a blocker description. Each gap docstring must specify:
- the missing Mathlib API or framework primitive,
- the repair trigger (e.g., "when Mathlib `Riemannian/` adds Ricci, repair `secondVariation` curvature term"),
- the repair owner (framework self-build vs wait Mathlib upstream).

Generic "blocked by Mathlib" annotations decay into permanent technical debt rather than tracked work.

Never silently weaken statements to remove sorry. Either prove, leave sorry'd, or document blocker with repair plan.

### Chain proofs

Substantive chain proofs (`main_theorem_*`, `*_of_nonExcessive`, `regularity_of_*`, etc.) must remain 0-sorry, non-circular. Refactors preserve this invariant.

### Ground truth annotation

All opaque / partially-grounded GMT primitives have `**Ground truth**: Simon §X / Pitts §Y` docstring reference, even when retreated. Future grounding attempts inherit this reference.

### Naming

Namespace and package names are concept-level, not person-level. Avoid attribution names (no `Wickramasekera`, no `AlmgrenPitts` as top-level package). People appear in citations + docstrings, not in namespace structure.

## Framework Stance vs Mathlib

Framework is an autonomous high-quality math software library, not a Mathlib-pending PR.

- **Self-impose Mathlib standard, do not cater**: framework uses Mathlib naming conventions, docstring requirements, API design (simp normal form, ext lemmas, typeclass conventions) as a self-imposed bar — not because of intent to PR.
- **Self-build is first-class**: when Mathlib lacks a primitive (Ricci curvature, second fundamental form, isoperimetric inequality, etc.), framework builds it. Self-built primitives are first-class library content, not temporary workarounds.
- **Mathlib is upstream, not pacemaker**: framework velocity is set by AI-driven formalization, not by Mathlib's PR review cycle. When Mathlib lacks a primitive, has a non-firing scoped instance, hits a higher-order unification limitation, or any other elaboration gap — framework self-builds. Framework does not wait. Mathlib catch-up, when it happens, is a deprecation opportunity for selective framework self-build subset — but framework does not plan around it. Catch-up is bonus, not milestone.
- **PR readiness is bonus, not motivation**: code built to self-imposed Mathlib standard is naturally compatible for upstream PR if/when relevant. Future PR friction is minimal because design didn't compromise to fit Mathlib's current state.

**Lazy retreat framings to reject:**
- "This is a Mathlib infrastructure issue, only fixable via PR"
- "Blocked by Mathlib upstream catch-up"
- "Deferred until Mathlib's [X] matures"

These framings substitute Mathlib's PR-cycle velocity (months-to-years) for framework's AI-formalization velocity (sessions). Real retreat trigger is *implementation impossibility after depth audit + bridge cost evaluation*, not *upstream-availability framing*.

## UX Optimization Timing

UX optimizations (`@[simp]` / `@[ext]` / `@[simps]` / `abbrev` / naming polish / API ergonomics) require stable interfaces. Apply only when:

- Framework self-build primitive set has stabilized (no further additions or signature changes expected),
- Concepts are settled mathematically and no further refactor is planned.

Premature UX optimization on evolving interfaces wastes work — polish gets discarded when refactor changes signatures. Defer to *event-triggered* timing: typically after refactor consolidation or before `v1.0` release. Phase 5 / Phase 6 work, not now.

## Velocity

This framework moves at software engineering speed, not paper writing speed.

- Statement layer lockdown: days, not months.
- GMT primitive grounding: hours per primitive.
- Cited theorem strict alignment: minutes per theorem.
- Refactor (layer separation, namespace cleanup): hours, not weeks.

Empirical calibration (Phase 1 session): **20 GMT primitives grounded in a single session**, including 5 Group C primitives requiring smooth-manifold typeclass cascade propagation. Layer B real grounding takes hours per primitive once the chart-pullback pattern is established. Refactor sessions handle ~500–800 LOC architectural changes with chain-proof 0-sorry preservation.

Empirical calibration (Phase 1.6, single session): **~250 LOC, 4 commits, 8 of 9 Riemannian primitives moved Classical.choose → real**. Bridge build (`InnerProductBridge`, ~30 LOC, ~30 minutes after depth audit) cascade-unblocked 5 downstream primitives via `stdOrthonormalBasis` + `LinearMap.trace` + `InnerProductSpace.toDual`, each ~5–10 minutes after the bridge unlock. This velocity reflects framework's AI-formalization pace, not Mathlib's PR-review pace (where the same contribution-set would be months-to-years wallclock).

Do not estimate task cost using traditional mathematician productivity model. Mathlib + Claude Code + cumulative pattern reuse compounds productivity. Mathlib uses `lake exe cache get` — Mathlib is not built locally; do not estimate Mathlib build time as cost.

## Phase Plan

- **Phase 0** (done): Architecture lock — monorepo, CLAUDE.md, naming convention.
- **Phase 1** (done): Layer A + Layer B real grounding. 21 → 1 opaque. GMT analysis primitive lib real-grounded.
- **Phase 1.5** (done): Refactor — Riemannian package (5th independent lib), Variation/ sub-namespace, HasNormal typeclass, Stable.lean GMT-level.
- **Phase 1.6** (done): Riemannian production-grade — 8 of 9 primitives real (Riemann curvature, Ricci, scalar curvature, second fundamental form + sq norm, mean curvature, manifold gradient + sq norm); only `leviCivitaConnection` remains as existence axiom for Levi-Civita Koszul (acceptable per textbook standard). `InnerProductBridge` self-build canonical example.
- **Phase 2** (next): Round 5 cited theorem strict alignment Items 4–9 (DLT13, `exists_minmaxLimit`, `isStationary_of_minmaxLimit`, `locallyStable_of_oneSidedMinimizing`, `interpolation_lemma`, `isRectifiable_of_isStationary_of_density_pos`).
- **Phase 3**: Isoperimetric production-grade lib (parallel to Riemannian, framework self-build standard).
- **Phase 4**: Long-term completion work — Levi-Civita Koszul construction, additional GMT primitive completion, framework long-term polish. Mathlib catch-up, if it happens during this phase, is a bonus deprecation opportunity, not a phase trigger.
- **Phase 5** (event-triggered): UX optimization on stabilized framework interface — `@[simp]`, `@[ext]`, `@[simps]`, `abbrev`, naming polish, API ergonomics.
- **Phase 6**: Final pre-release polish — CI, doc-gen4, README, references.bib, optional Mathlib upstream PR for stabilized lib subsets.

Phase ordering reflects dependency: Phase 1.5/1.6 architecture is prerequisite to Phase 2–3; Phase 4 is framework long-term work (not a passive Mathlib wait); Phase 5 UX requires interface stability; Phase 6 final polish requires Phase 5.

## Identity

The user is Xinze Li (Moqian), 5th-year math PhD at University of Toronto, advisor Yevgeny Liokumovich. Communication preferred in Chinese. Avoids em-dashes and AI-style phrasing.

Strategic role: 总指挥 — sets direction, decides scope.
Claude (chat): 参谋 — translates direction into Claude Code prompts.
Claude Code: executor — runs prompts, mechanical work, build verify.

Roles stable across phases. Strategic decisions (scope, architecture, refactor triggers) belong to Moqian. Translation to executable prompts belongs to Claude (chat). Mechanical execution + build verification belongs to Claude Code. Phase 1 completion validates this division — strategic re-audit at phase boundaries (e.g., current Phase 1 → 1.5 → 1.6 transition) is Moqian + Claude (chat) work; sub-layer execution within phases is Claude Code work.

When Claude Code reports retreat with framings like "Mathlib infrastructure issue", "blocked by Mathlib upstream", "deferred to Mathlib catch-up event", or "single-session push too risky" — treat these as candidate lazy retreats. Push back to verify true architectural impossibility (depth audit + bridge investment evaluation) before accepting. Real retreat trigger is a documented build error after iteration plus an explicit accessor blocker after depth audit, not a framing-level claim.
