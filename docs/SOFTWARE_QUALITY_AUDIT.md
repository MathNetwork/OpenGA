# Software-Quality Audit — `comb_arg` (reference) vs Alternative Regularity (target)

**Date:** 2026-04-27
**Audited paths:**
- Reference: `/Users/moqian/comb-arg` (v0.3.0, 2026-04-26, ~1700 LoC)
- Target:   `/Users/moqian/Desktop/Alternative Regularity via Non-Excessive Sweepouts` (no version tag, 5 packages, ~6000 LoC)

**Scope:** software-engineering polish only. No code touched, no commits made. Math
content (Phase 4.5 Koszul, etc.) is *out of scope* — this audit asks only "does the
target meet the reference's repository-engineering standard?"

---

## 1. `comb_arg` reference structure (what "good" looks like)

```
comb-arg/
├── README.md                 18 KB — overview, scope (Provided / Not provided),
│                                     quick-start, public API code blocks,
│                                     "Lifting this library" narrative,
│                                     skeleton client code, "Public API stability"
│                                     section listing 10 stable names
├── CHANGELOG.md              18 KB — Keep-a-Changelog format, v0.1 → v0.3,
│                                     each release tagged "breaking" / "internal" /
│                                     "unchanged" / "known follow-ups"
├── CITATION.cff              cff-version 1.2.0, abstract, ORCID-style metadata,
│                             references to DLT13
├── LICENSE                   Apache 2.0 (full text)
├── lakefile.lean             package + 2 lean_libs + 2 lean_exes + checkdecls
├── lake-manifest.json        Mathlib pinned by SHA
├── lean-toolchain            v4.30.0-rc2 pinned
├── CombArg.lean              ── top-level facade (re-exports, module docstring
│                                with the four public theorems explained)
├── Audit.lean                ── lake exe combarg-audit:
│                                   walks env, asserts axioms ⊆ {propext,
│                                   Classical.choice, Quot.sound}, prints
│                                   public-API listing, exit 0/1
├── Skeleton.lean             ── lake exe combarg-skeleton:
│                                   emits a starter min-max contradiction script
│                                   with YourGMT.* placeholder identifiers,
│                                   options --N <name>, --module <name>
├── CombArg/
│   ├── Witness.lean          input structures
│   ├── Cover.lean            K-generic bookkeeping corollary
│   ├── SupReduction.lean     1D chained corollary
│   ├── OneDim.lean           1D facade
│   └── OneDim/{SpacedIntervals,InitialCover,CoverConstruction,
│                PartialRefinement,Induction,Assembly}.lean
├── docs/
│   ├── project-overview.md   11 KB — narrative API tour, proof architecture,
│   │                                  axiom dependencies, findings
│   └── design-notes.md       6 KB  — load-bearing design choices (4 items)
│                                     + formalization findings (4 items)
├── examples/
│   └── MinimalUsage.lean     worked invocation on f ≡ 1, parameterized in N
├── test/
│   └── Smoke.lean            4 guards: constructibility, end-to-end,
│                             K-generic invocation, #guard_msgs axiom audit
├── .github/workflows/
│   └── ci.yml                lake build + lake build test/examples
│                             + sorry/admit grep + axiom audit
│                             + lake exe combarg-audit
├── scripts/
│   ├── build-blueprint.sh
│   └── build-graph.sh        importGraph → docs/import-graph.svg
├── blueprint/
│   ├── lean_decls            7-line list of public names exposed to blueprint
│   └── src/                  blueprint LaTeX sources
└── paper/                    paper companion
```

**Key engineering moves that lift `comb_arg` above a typical research repo:**
1. **Top-level facade with stable-API contract** — `CombArg.lean` re-exports
   + a README "Public API stability" section names every stable identifier
   and explicitly marks internals (`step_succ_at`, `ExtendResult`, …) mutable.
2. **One-command health check** — `lake exe combarg-audit` walks the
   environment, confirms public theorems depend only on the three
   foundational axioms, and exits 1 if a `sorryAx` ever leaks in. Same
   command runs in CI.
3. **Skeleton generator** — `lake exe combarg-skeleton` emits the exact
   client-side glue code a downstream GMT formalization would write.
   This is *executable* documentation: the skeleton is the contract.
4. **README "Lifting this library" narrative** — 5 paragraphs + table
   mapping each `LocalWitness` field to its DLT-side counterpart, plus a
   line-by-line skeleton showing the chain `LocalWitness → exists_sup_reduction
   → lift_sweepout → contradiction`. Reads like a graduate-course
   recipe: a downstream user knows exactly what to plug in where.
5. **CHANGELOG with rationale** — every release breaks down "Changed
   (breaking)" vs "Internal cleanup" vs "Unchanged" and explains *why*.
   v0.2 entry says: "PairableCover removed because dead weight; see
   design-notes §12". Keeps the design history attached to the artifact.
6. **Test = `#guard_msgs in #print axioms`** — regression guard against
   any new axiom is a *built-in elaboration check*, not an out-of-band script.
7. **Narrow per-file imports** documented as a design choice (design-notes §4).

---

## 2. Alternative Regularity current state (target)

```
Alternative Regularity via Non-Excessive Sweepouts/
├── lakefile.lean             4 require statements, 1 lean_lib (AltRegularity)
├── lake-manifest.json        Mathlib pinned by SHA (5fc02419…)
├── lean-toolchain
├── AltRegularity.lean        ── top-level "facade" (well-commented import list
│                                with section labels mirroring paper §2–§7)
├── CLAUDE.md                 14 KB — mission, architecture, working-mode
│                             discipline, phase plan
├── Riemannian/               5th independent lib — facade + 5 modules, 806 LoC
│   ├── Riemannian.lean       brief facade (40 lines)
│   ├── lakefile.lean
│   └── Riemannian/{Connection, Curvature, SecondFundamentalForm,
│                    Gradient, InnerProductBridge}.lean
├── GeometricMeasureTheory/   facade + 13 modules + Isoperimetric/, 2652 LoC
├── MinMax/                   facade + Sweepout/{8 modules}, 1068 LoC
├── Regularity/               facade + 2 modules, 401 LoC
├── AltRegularity/            paper-specific app — 12 .lean files, 1098 LoC
├── paper/                    main.tex, main.bib, main.pdf, chapters/
└── references/
    └── cite_verification.md  three-way alignment table
```

**Engineering state:**
- 5-package monorepo, each package has its own lakefile + facade .lean.
- 55 `sorry` occurrences across 26 files (per CLAUDE.md discipline:
  PRE-PAPER / CITED-BLACK-BOX / PAPER-INTERNAL / CONJECTURAL).
- Git: branch `main`, ~21 visible commits, **no tags**, no release.
- Top-level facade `AltRegularity.lean` only re-exports; no module-level
  English overview of the public-theorem surface.
- Per-package facades exist and have brief docstrings (Riemannian has a
  layering diagram, GMT/MinMax/Regularity have 1–3 sentences each).

**Missing entirely:** `README.md`, `LICENSE`, `CITATION.cff`, `CHANGELOG.md`,
`examples/`, `test/`, `docs/`, `blueprint/`, `.github/workflows/`,
`scripts/`, no `lake exe` binaries.

---

## 3. Twelve-dimension comparison

Status legend: 🟢 matches reference / 🟡 partial / 🔴 missing.
Cost legend: S (≤ 1 session) / M (~ 2-3 sessions) / L (multi-session).

| # | Dimension | comb_arg | AltReg | Status | Cost | Priority |
|---|---|---|---|---|---|---|
| 1 | **Top-level facade** | `CombArg.lean` re-exports + module docstring naming the 3 public theorems with explanation | `AltRegularity.lean` re-exports with section labels mirroring paper § structure; per-package facades exist with brief docstrings | 🟡 | M | high |
| 2 | **Public API stability promise** | README "Public API stability" section names 10 stable identifiers, declares internals mutable | none — no statement of which names are stable vs internal | 🔴 | M | high |
| 3 | **README scope sections** | 18 KB — overview, "What this provides", quick-start, public theorems, "Provided / Not provided", "Lifting this library to the original min-max proof" with mapping table + skeleton, public-API stability, repo structure, dependencies, citation, changelog, license | none | 🔴 | M | high |
| 4 | **Worked example** | `examples/MinimalUsage.lean` — runnable end-to-end on `f ≡ 1`, parameterized in `N` | none | 🔴 | M | medium |
| 5 | **Audit binary** | `lake exe combarg-audit` — walks env, asserts axioms ⊆ {propext, Classical.choice, Quot.sound}, prints public-API listing | none — no command-line health check | 🔴 | M | high |
| 6 | **Skeleton generator** | `lake exe combarg-skeleton --N <name> --module <name>` — emits starter client script with `YourGMT.*` placeholders | none — and arguably less applicable: AltReg is the application, not a library waiting for clients | 🔴 | L (questionable) | low |
| 7 | **CI workflow** | `.github/workflows/ci.yml` — `lake build` / `lake build test examples` / sorry-grep / 3-theorem axiom audit / `lake exe combarg-audit` | none — `.github/` directory does not exist | 🔴 | S | high |
| 8 | **Smoke test** | `test/Smoke.lean` — 4 guards including `#guard_msgs in #print axioms` regression guard | none — no `test/` directory; no axiom regression guard | 🔴 | M | high |
| 9 | **CHANGELOG** | `CHANGELOG.md` — Keep-a-Changelog format, v0.1.0 → v0.3.0, breaking/internal/unchanged sections | none — git history substitutes | 🔴 | S | medium |
| 10 | **CITATION.cff** | full cff-version 1.2.0 with abstract, references | none | 🔴 | S | medium |
| 11 | **LICENSE** | Apache 2.0 full text + per-file `Copyright (c) 2026 Xinze Li` headers | none | 🔴 | S | high |
| 12 | **Versioning + release** | git tags `v0.1.0`, `v0.1.1`, `v0.2.0`, `v0.3.0`; CHANGELOG entries linked to GitHub release tags | no tags | 🔴 | S (after CHANGELOG exists) | medium |

**Bonus dimensions** (not in the original 12 but visible in `comb_arg`):

| # | Dimension | comb_arg | AltReg | Status | Cost |
|---|---|---|---|---|---|
| 13 | **docs/ narrative** | `project-overview.md` (11 KB API tour) + `design-notes.md` (6 KB load-bearing choices + formalization findings) | none — `paper/` is a separate artifact; no Lean-side narrative docs | 🔴 | M |
| 14 | **Blueprint** | `blueprint/{lean_decls, src/}` LaTeX sources for Patrick Massot's blueprint | none | 🟡 (less applicable: the paper *is* the blueprint analogue here) | M (questionable) |
| 15 | **Per-file copyright headers** | every `.lean` opens with `Copyright (c) 2026 Xinze Li ... Apache 2.0` | none | 🔴 | S |

---

## 4. Gap inventory by effort

### (a) Immediate close-able gaps (~1 session each, no design dependency)

These are pure paperwork — no decisions needed once content is written. Total
estimated cost: **1–2 sessions for the bundle.**

- **LICENSE** — drop in Apache 2.0 boilerplate (`comb_arg` style). Single file.
- **CITATION.cff** — model after `comb_arg/CITATION.cff`; replace title/abstract,
  add Yangyang Li as second author. ~15 minutes.
- **CHANGELOG.md** — backfill from git history. The commit log already
  reads like a structured changelog (Phase 1 / 1.5 / 1.6 / 2 / 3.x / 4.x).
  Render as Keep-a-Changelog with each Phase as a release. ~1 hour.
- **Per-file copyright headers** — sed-pass over all `.lean` files in 5
  packages. Mechanical. ~30 minutes.
- **`.github/workflows/ci.yml`** — adapt `comb_arg/.github/workflows/ci.yml`.
  Change `lake build` target list, drop `lake build test examples` (no test
  dir yet), keep sorry/admit grep — but **expect grep to flag the existing
  55 sorries**, so either (i) skip sorry-grep until test infra exists, or
  (ii) allowlist current sorries inline. ~1 hour.

### (b) Medium-effort gaps (~2–3 sessions, design work required)

- **README.md** (high priority — single biggest gap). A reader landing on the
  repo today has no entry point. Needs:
  - 1-paragraph framework purpose
  - "Provided / Not provided" scope (mirrors `comb_arg` §Scope)
  - Quick-start (`lake exe cache get` + `lake build` per package)
  - Public-theorem code blocks for each layer (Riemannian, GMT, MinMax,
    Regularity, AltRegularity)
  - "Public API stability" section listing stable identifiers per package
  - Repo structure tree
  - Dependencies, citation, changelog, license sections
  - **Design decision needed:** does the README treat the 5 packages as one
    library or as 5 separate libraries with cross-references? `comb_arg`'s
    README is for a single library; AltReg is structurally different.
- **Top-level + per-package facade hardening** — promote
  `AltRegularity.lean` from "import list with section labels" to "API-listing
  facade with module docstring naming each public theorem and what it
  delivers" (`comb_arg/CombArg.lean` style). Same exercise per package. The
  `Riemannian.lean` facade is closest to the bar already.
- **Worked example** — `examples/MinimalUsage.lean` invoking `MainTheorem`
  and `MinMaxExistence` end-to-end on a trivial input (analogue of
  `comb_arg`'s `f ≡ 1`). Requires deciding what the trivial input is — the
  closed metric, the trivial sweepout, or a synthetic stub.
- **Smoke test** — `test/Smoke.lean` with at minimum (i) `#guard_msgs in
  #print axioms MainTheorem`, (ii) construction smoke for each public
  primitive in each package. AltReg has 55 sorries today, so the audit
  will list more axioms than `comb_arg`'s clean three; the test should
  *snapshot the current axiom set* and fail on regression rather than
  demand `[propext, Classical.choice, Quot.sound]` exclusively.
- **Audit binary** — `lake exe altreg-audit` modeled on
  `Audit.lean`. Two extensions over `comb_arg`'s version:
  (i) walk all 5 packages, (ii) classify the surfaced axioms (real
  `axiom` declarations vs `sorryAx` from PRE-PAPER stubs vs the three
  foundational ones). Output: per-package axiom budget snapshot.

### (c) Larger-effort gaps

- **Skeleton generator** (`lake exe altreg-skeleton`). *Questionable
  applicability*: `comb_arg` has skeleton because it is a library
  awaiting downstream clients. AltReg is the application; the
  natural "client" is *another paper* using the same lib stack. If
  Riemannian / GMT spin out as separate libs (per CLAUDE.md), each
  spin-out gets its own skeleton then. Skip for now.
- **`docs/`** — `project-overview.md` (narrative API tour) and
  `design-notes.md` (load-bearing design choices + formalization
  findings). Half the content is already in CLAUDE.md and the
  paper; the work is *re-targeting* it for a Lean-reader audience
  (CLAUDE.md is for *Claude*, paper is for *math reviewers*). 2–3
  sessions if done well.
- **Versioning + release tagging** — easy mechanically once
  CHANGELOG exists; the *decision* of "what counts as v0.1" is the
  real work. Defensible answer: "v0.1.0 = current state of Phase 4.5
  on the day CHANGELOG, README, LICENSE, CITATION land."
- **Blueprint** — `comb_arg`'s blueprint is a small companion to a
  small library. The paper itself functions as AltReg's blueprint
  already. Defer indefinitely unless there is a specific blueprint
  use-case (e.g., shipping an interactive blueprint web build).

---

## 5. Strategic recommendation

Three options, weighed against (i) the `comb_arg` standard, (ii) framework
ready-state, (iii) Riemannian-as-future-spin-out goal in CLAUDE.md.

### Option A — Polish-first (software polish before Phase 4.5 Koszul math)

**Pro:**
- Software polish is mostly orthogonal to math content. LICENSE, README,
  CHANGELOG, CITATION, CI, audit binary, smoke test — none of these
  need Levi-Civita Koszul to land.
- The framework is already in a state that *can be cited* (Phase 3 done,
  4 dimensions ready); software polish elevates "exists in the author's
  filesystem" to "discoverable, attributable, reproducible artifact".
- Matches `comb_arg` standard immediately. If Moqian is asked tomorrow
  "send me the Lean repo" — currently no README exists.
- Riemannian spin-out becomes possible only after Riemannian has its own
  README/LICENSE/CHANGELOG/CITATION at the sub-package level — polish
  pass is the prerequisite for the spin-out story in CLAUDE.md.

**Con:**
- Defers Phase 4.5 Koszul, which is the math content currently
  near-complete (Commit `a2672a1` "Koszul functional def + algebraic
  identity statements").
- Polish work doesn't compound math-research-side.

### Option B — Math-first (Phase 4.5 Koszul, then software polish)

**Pro:**
- Finishes the math story before attempting to "ship" anything.
- Avoids re-doing facade work if Phase 4.5 changes which Riemannian
  identifiers are public.

**Con:**
- The current state is already ship-able as a math artifact (Phase 3
  done, 4 dimensions ✅); waiting on Levi-Civita to start polish is
  not the bottleneck.
- Risk of "framework is great but no one can find the README" persists
  for another N weeks.

### Option C — Hybrid (parallel)

**Pro:**
- Software polish (paperwork bundle (a) + facade hardening + worked
  example) does not block Phase 4.5 Koszul code. Atomic commits per
  track.
- Matches CLAUDE.md "atomic commits, do not commit mid-refactor"
  discipline cleanly: each polish item is its own commit.

**Con:**
- Context-switching cost. Polish needs different headspace than Koszul.
- For a single executor (Moqian + Claude Code), parallelism is
  fictional — work is sequential. Real choice is just "in what order".

### Recommendation

**Option A — Polish-first**, with the caveat that the polish bundle
should be aggressively scoped to gap-set (a) plus the README and the
audit binary from (b). Concretely: **finish bundle (a) + README +
audit binary + smoke test, then return to Phase 4.5 Koszul.** Reason:

1. The single largest current gap is *no README* — the framework is
   undiscoverable to anyone who is not Moqian or Claude. This is fixed
   in one session and unblocks every downstream "send me the repo"
   request.
2. LICENSE / CITATION / CHANGELOG / per-file headers are 30 minutes each
   and are a one-time tax — they don't get cheaper by waiting for math
   content to settle.
3. CI + audit binary + smoke test create a *machine-readable* version
   of "the framework is healthy" that CLAUDE.md currently asserts in
   prose. Once `lake exe altreg-audit` exists, every Phase 4.5 commit
   gets gated by the same check `comb_arg` uses.
4. Phase 4.5 Koszul is currently mid-flight (commit `a2672a1`). Pausing
   for the polish bundle does not lose context; resuming is
   straightforward because the math content is its own atomic task.
5. The Riemannian spin-out narrative in CLAUDE.md (§Architecture: "future
   spin-out candidate as a standalone Lean library") is not credible
   without sub-package-level README/LICENSE/CITATION — polishing now
   is *prerequisite work* for that narrative, not a delay to it.

The skeleton generator and blueprint are deferred; they are
`comb_arg`-shaped tools that don't fit AltReg's structural role
(application, not library awaiting clients).

---

## 6. Phase 5 polish list (Option A, ordered)

If Moqian accepts Option A, the next sub-prompt sequence is:

**Phase 5.A — paperwork bundle (1 session, ~3 hours)**
1. `LICENSE` — Apache 2.0 boilerplate at top level, mirror `comb_arg`.
2. `CITATION.cff` — adapt `comb_arg/CITATION.cff` with two authors
   (Xinze Li, Yangyang Li), AltReg title/abstract, paper reference.
3. `CHANGELOG.md` — Keep-a-Changelog format, render git history's
   Phase 1 → 4.5 commits as releases. Tag `v0.1.0` after this commit.
4. Per-file copyright headers — single-pass sed across all 5 packages.

**Phase 5.B — README (1 session, ~3 hours)**
5. `README.md` — modeled on `comb_arg/README.md` structure:
   purpose + scope + quick-start + per-package public-theorem code
   blocks + Public API stability section + repo tree + deps + citation.
   *Decision needed first*: single-library framing vs 5-library
   framing. Recommend 5-library framing (matches CLAUDE.md
   architecture diagram and Riemannian spin-out story).

**Phase 5.C — facade hardening (1 session, ~3 hours)**
6. Promote `AltRegularity.lean` to API-listing facade with module
   docstring per public theorem.
7. Same pass on `Riemannian.lean`, `GeometricMeasureTheory.lean`,
   `MinMax.lean`, `Regularity.lean` — each gets a "Public API"
   section in its module docstring.
8. README "Public API stability" section gets populated from these
   facades.

**Phase 5.D — verification infrastructure (1 session, ~3 hours)**
9. `Audit.lean` + `lake exe altreg-audit` — adapted from
   `comb_arg/Audit.lean`. Walks all 5 packages, prints axiom budget
   per package, exits 0/1.
10. `test/Smoke.lean` — `#guard_msgs in #print axioms` snapshot
    of current axiom set per public theorem; regression guard.
11. `.github/workflows/ci.yml` — `lake build` per package +
    `lake exe altreg-audit` + sorry-grep with current allowlist.

**Phase 5.E (optional) — narrative docs (~2 sessions)**
12. `docs/project-overview.md` — Lean-reader API tour (CLAUDE.md
    re-targeted from Claude-audience to Lean-reader audience).
13. `docs/design-notes.md` — load-bearing design choices
    (5-package layering rationale, `InnerProductBridge` story,
    `HasNormal` typeclass story, `bvGradientDirection` real-def
    decision) + formalization findings surfaced during Phase 1–4.

After Phase 5.D, framework matches `comb_arg` standard on all 12
core dimensions. Phase 4.5 Koszul resumes with CI + audit binary
already in place.

---

## 7. Out of scope (this audit)

- Math content (Phase 4.5 Koszul, future Phase 4.x).
- Mathlib upstream PRs (CLAUDE.md: "PR readiness is bonus, not motivation").
- Riemannian sub-package spin-out as standalone repo (separate
  multi-session effort once Phase 5 lands).
- Paper companion (`paper/`) — a separate deliverable on its own track.

**No code touched. No commits made.**
Awaiting Moqian decision on Option A / B / C, then Phase 5.A start.
