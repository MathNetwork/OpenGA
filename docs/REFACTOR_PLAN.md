# OpenGALib architecture refactor — plan only

**Date:** 2026-04-27
**Scope:** plan only. No code touched, no commits made.
**Repo path:** `/Users/moqian/OpenGALib` (renamed from
`/Users/moqian/Desktop/Alternative Regularity via Non-Excessive Sweepouts`
this session).

---

## 0. Casing / naming question (decision needed before execute)

Inconsistency between session messages:

| Source | Spelling |
|---|---|
| Earlier turn ("改名字叫OpenGALib") | `OpenGALib` |
| Current refactor prompt body | `OpenGAlib` |
| Filesystem (current state) | `OpenGALib` |

Lake package names, Lean namespaces, and `import` paths are case-sensitive,
so this must be locked before execute. **Recommendation: `OpenGALib`** —
matches both (i) the rename you ran first and (ii) the filesystem.
The remainder of this plan uses `OpenGALib` throughout; if you prefer
`OpenGAlib`, every occurrence in §§5–9 below changes accordingly.

---

## 1. Current architecture inventory

### 1.1 Root layout (audited)

```
OpenGALib/                                ← currently package «altregularity»
├── lakefile.lean                         (24 lines, package altregularity, requires
│                                          mathlib + 4 sub-packages)
├── lake-manifest.json                    (lists 4 sub-packages + Mathlib + transitive)
├── lean-toolchain
├── AltRegularity.lean                    (5972 B, facade, root-level)
├── CLAUDE.md                             (14 KB)
├── SOFTWARE_QUALITY_AUDIT.md             (this session)
├── Riemannian/                           independent sub-package
├── GeometricMeasureTheory/               independent sub-package
├── MinMax/                               independent sub-package
├── Regularity/                           independent sub-package
├── AltRegularity/                        FOLDER (not a package — no lakefile here)
│                                          contains: Basic.lean, MainTheorem.lean,
│                                          MinMaxExistence.lean, PositiveDensity.lean,
│                                          + Integrality/, OneSidedDensity/,
│                                          Regularity/ subfolders
├── paper/                                (root-level)
├── references/                           (root-level)
├── docs/                                 (this file)
├── .github/, .vscode/, .claude/, .git/, .lake/
└── .gitignore
```

**Important:** `AltRegularity/` at root is **not** currently its own
Lake package — there is no `AltRegularity/lakefile.lean`. Instead, the
root `lakefile.lean` declares `lean_lib AltRegularity` with
`globs := #[.andSubmodules `AltRegularity]`, which sweeps both the
root-level facade `AltRegularity.lean` AND the modules under
`AltRegularity/`. The "5-package monorepo" framing in the prompt is
accurate for Riemannian/GMT/MinMax/Regularity, but AltRegularity is
already a sub-folder of the root package, not its own package.

### 1.2 Sub-package layouts (Riemannian / GMT / MinMax / Regularity)

Each follows the pattern:

```
<Pkg>/
├── lakefile.lean              package «<Pkg>», single lean_lib, requires
│                              mathlib + (for non-Riemannian) downstream pkgs
├── lake-manifest.json         own Mathlib pin + own copy of mathlib/aesop/...
├── lean-toolchain             (29 B — same as root)
├── .lake/                     own build artifacts
├── <Pkg>.lean                 facade (at the sub-package root — module name <Pkg>
│                              within sub-package source tree)
└── <Pkg>/                     module dir (e.g. Riemannian/Connection.lean →
                               module Riemannian.Connection)
```

So the on-disk path of, e.g., the Riemannian.Connection module is
`OpenGALib/Riemannian/Riemannian/Connection.lean` (note the doubled
`Riemannian/`). This is correct under the current per-package
source-root convention (each sub-package's source root is its own
directory), but it is the source of the file-move work in §6 below.

### 1.3 AltRegularity layout (current)

```
OpenGALib/
├── AltRegularity.lean                       (root-level facade — 5972 B)
└── AltRegularity/                           (folder, not a package)
    ├── Basic.lean
    ├── MainTheorem.lean
    ├── MinMaxExistence.lean
    ├── PositiveDensity.lean
    ├── Integrality/
    │   ├── PerimeterConvergence.lean
    │   ├── ReducedBoundary.lean
    │   └── Theorem.lean
    ├── OneSidedDensity/
    │   ├── AlmostMinimizer.lean
    │   └── Density.lean
    └── Regularity/
        ├── AlphaStructuralVerification.lean
        ├── ChordBeatsArc.lean
        └── StabilityVerification.lean
```

Lake currently sweeps both `AltRegularity.lean` (root) and
everything under `AltRegularity/` into the same `lean_lib AltRegularity`.

---

## 2. Mathlib pin consistency

Audit result:

| File | mathlib `rev` |
|---|---|
| `lake-manifest.json` (root) | `5fc0241932dd6d465bc5549308cc39011772293a` |
| `Riemannian/lake-manifest.json` | `5fc0241932dd6d465bc5549308cc39011772293a` |
| `GeometricMeasureTheory/lake-manifest.json` | `5fc0241932dd6d465bc5549308cc39011772293a` |
| `MinMax/lake-manifest.json` | `5fc0241932dd6d465bc5549308cc39011772293a` |
| `Regularity/lake-manifest.json` | `5fc0241932dd6d465bc5549308cc39011772293a` |

**All five manifests pin the identical Mathlib SHA.** No mismatch to
resolve. Refactor adopts this SHA in the single root manifest; sub-package
manifests are deleted.

---

## 3. Cross-package import map

```
Riemannian       ← (only Mathlib + Init/Std)
                       ↑
GeometricMeasureTheory  imports:
                          Riemannian.Connection
                          Riemannian.Curvature
                          Riemannian.Gradient
                          Riemannian.InnerProductBridge
                          Riemannian.SecondFundamentalForm
                       ↑                   ↑
MinMax           imports:           Regularity         imports:
  GeometricMeasureTheory.FlatDistance      GeometricMeasureTheory.Rectifiability
  GeometricMeasureTheory.Stationary        GeometricMeasureTheory.SecondVariation
  GeometricMeasureTheory.Varifold          GeometricMeasureTheory.Stable
                                           GeometricMeasureTheory.Stationary
                                           GeometricMeasureTheory.TangentCone
                       ↑                   ↑
AltRegularity    imports (selection):
  GeometricMeasureTheory (+ FinitePerimeter, TangentCone, Varifold)
  MinMax (+ Sweepout.{HomotopicMinimization, MassCancellation,
           MinMaxLimit, NonExcessive, PullTight})
  Regularity (+ AlphaStructural, SmoothRegularity)
```

Layer order: **Riemannian < GeometricMeasureTheory < {MinMax, Regularity}
< AltRegularity**. No cycles. All cross-package imports use
*namespace-qualified* paths (e.g., `import Riemannian.Connection`),
which means they continue to resolve identically once everything is
flattened into a single OpenGALib lib — see §7.

---

## 4. Target architecture spec

```
OpenGALib/                                ← single Lake project, package OpenGALib
├── lakefile.lean                         single lean_lib OpenGALib
├── lake-manifest.json                    single Mathlib pin (transitive deps included)
├── lean-toolchain
├── OpenGALib.lean                        top-level facade — re-exports 4 sub-namespaces
├── Riemannian.lean                       sub-namespace facade
├── Riemannian/
│   ├── Connection.lean                   namespace Riemannian.Connection
│   ├── Curvature.lean
│   ├── SecondFundamentalForm.lean
│   ├── Gradient.lean
│   └── InnerProductBridge.lean
├── GeometricMeasureTheory.lean           sub-namespace facade
├── GeometricMeasureTheory/
│   ├── FinitePerimeter.lean
│   ├── ...                                (13 modules + Isoperimetric/ subdir)
│   └── Isoperimetric/
│       ├── Basic.lean
│       └── ...                            (7 modules)
├── MinMax.lean                           sub-namespace facade
├── MinMax/
│   └── Sweepout/
│       ├── Defs.lean
│       └── ...                            (8 modules)
├── Regularity.lean                       sub-namespace facade
├── Regularity/
│   ├── AlphaStructural.lean
│   └── SmoothRegularity.lean
│
├── docs/                                 narrative docs (Phase 5.E)
├── references/                           cite_verification.md
├── CLAUDE.md
├── README.md       (Phase 5.A)           planned, not part of this refactor
├── LICENSE         (Phase 5.A)           planned, not part of this refactor
├── CITATION.cff    (Phase 5.A)           planned
├── CHANGELOG.md    (Phase 5.A)           planned
│
└── AltRegularity/                        ← separate sub-project, requires OpenGALib
    ├── lakefile.lean                     package AltRegularity, requires OpenGALib + mathlib
    ├── lake-manifest.json                own Mathlib pin (must equal root)
    ├── lean-toolchain                    same toolchain as parent
    ├── AltRegularity.lean                AltRegularity facade
    ├── AltRegularity/                    inner module dir
    │   ├── Basic.lean
    │   ├── MainTheorem.lean
    │   ├── MinMaxExistence.lean
    │   ├── PositiveDensity.lean
    │   ├── Integrality/
    │   ├── OneSidedDensity/
    │   └── Regularity/
    ├── paper/                            paper companion (moved here)
    └── .lake/                            (fresh build artifacts)
```

**Single-project rationale**: a single `lean_lib OpenGALib` glob covers
all four sub-namespaces; no inter-package require-graph to maintain;
no per-package manifest drift; one `lake exe cache get`; one CI build
target for the lib. AltRegularity stays as a *separate project* because
it carries the paper application (which has different upstream-PR
considerations than the lib content per CLAUDE.md
"Mathlib-upstream candidate" framing for the lib).

**AltRegularity-as-nested-sub-project** rationale: keeping the
AltRegularity project under `OpenGALib/AltRegularity/` preserves the
"one repo on disk" working pattern. Lake supports `require OpenGALib
from ".."` from a nested directory. See risk §9 for the alternative
(AltRegularity as sibling outside OpenGALib).

---

## 5. lakefile transformation

### 5.1 New root `lakefile.lean`

Replace the current root `lakefile.lean` (24 lines, package
`«altregularity»`, requires the 4 sub-packages) with:

```lean
import Lake
open Lake DSL

package OpenGALib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "5fc0241932dd6d465bc5549308cc39011772293a"

@[default_target]
lean_lib OpenGALib where
  globs := #[
    .submodules `Riemannian,
    .submodules `GeometricMeasureTheory,
    .submodules `MinMax,
    .submodules `Regularity
  ]
```

Notes:
- `.submodules `Riemannian` picks up `Riemannian.lean` (the facade —
  Lake treats the facade file matching the sub-namespace root as the
  zero-segment submodule) **plus** every `.lean` under `Riemannian/`.
  Verify before commit: if Lake's `.submodules` does *not* include the
  root facade file, switch to `.andSubmodules` (see Risk R3 §9).
- Single Mathlib `require`. Sub-package requires removed.
- `OpenGALib.lean` (top-level facade) is included via the `submodules`
  globs only if at least one of them matches it; if not, it must be
  added to a flat `roots := #[`OpenGALib]` clause. To be confirmed
  during execute (Risk R5).

### 5.2 New `AltRegularity/lakefile.lean`

```lean
import Lake
open Lake DSL

package AltRegularity where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require OpenGALib from ".."

@[default_target]
lean_lib AltRegularity where
  globs := #[.andSubmodules `AltRegularity]
```

Notes:
- `require OpenGALib from ".."` — Lake supports relative-path
  requires; the parent dir is a Lake package because of the new root
  `lakefile.lean`. Verified syntactically by analogy with current
  `require GeometricMeasureTheory from "../GeometricMeasureTheory"` in
  the existing sub-package lakefiles.
- **No direct `require mathlib`** — Mathlib comes transitively through
  the `require OpenGALib from ".."` clause. If Lake's transitive-require
  resolution surprises us (Risk R2), add explicit `require mathlib` here
  with the same SHA.
- `.andSubmodules` (not `.submodules`) because we explicitly want both
  `AltRegularity.lean` (facade) and all submodules under
  `AltRegularity/` to be built.

### 5.3 Lakefiles to delete

- `Riemannian/lakefile.lean`
- `GeometricMeasureTheory/lakefile.lean`
- `MinMax/lakefile.lean`
- `Regularity/lakefile.lean`

(Also their `lake-manifest.json`, `lean-toolchain`, and `.lake/`
directories — see §6.)

---

## 6. File move / create / delete list

### 6.1 DELETE (per-sub-package build infra)

```
Riemannian/lakefile.lean
Riemannian/lake-manifest.json
Riemannian/lean-toolchain
Riemannian/.lake/                          (build artifacts)

GeometricMeasureTheory/lakefile.lean
GeometricMeasureTheory/lake-manifest.json
GeometricMeasureTheory/lean-toolchain
GeometricMeasureTheory/.lake/

MinMax/lakefile.lean
MinMax/lake-manifest.json
MinMax/lean-toolchain
MinMax/.lake/

Regularity/lakefile.lean
Regularity/lake-manifest.json
Regularity/lean-toolchain
Regularity/.lake/
```

### 6.2 MOVE — flatten 4 sub-package source trees up one level

For each `<Pkg> ∈ {Riemannian, GeometricMeasureTheory, MinMax, Regularity}`:

```
OpenGALib/<Pkg>/<Pkg>.lean                 →  OpenGALib/<Pkg>.lean         (facade)
OpenGALib/<Pkg>/<Pkg>/<file>.lean          →  OpenGALib/<Pkg>/<file>.lean  (modules)
OpenGALib/<Pkg>/<Pkg>/<subdir>/...         →  OpenGALib/<Pkg>/<subdir>/... (sub-modules)
DELETE empty OpenGALib/<Pkg>/<Pkg>/         (after move)
```

Concretely (**Riemannian**, 5 modules):

```
OpenGALib/Riemannian/Riemannian.lean                         → OpenGALib/Riemannian.lean
OpenGALib/Riemannian/Riemannian/Connection.lean              → OpenGALib/Riemannian/Connection.lean
OpenGALib/Riemannian/Riemannian/Curvature.lean               → OpenGALib/Riemannian/Curvature.lean
OpenGALib/Riemannian/Riemannian/SecondFundamentalForm.lean   → OpenGALib/Riemannian/SecondFundamentalForm.lean
OpenGALib/Riemannian/Riemannian/Gradient.lean                → OpenGALib/Riemannian/Gradient.lean
OpenGALib/Riemannian/Riemannian/InnerProductBridge.lean      → OpenGALib/Riemannian/InnerProductBridge.lean
DELETE OpenGALib/Riemannian/Riemannian/  (now empty)
```

(**GeometricMeasureTheory**, 13 modules + `Isoperimetric/` subdir): same
pattern, ~21 files to move.

(**MinMax**, 8 modules under `Sweepout/`): same pattern.

(**Regularity**, 2 modules + facade): same pattern.

### 6.3 MOVE — AltRegularity into its own sub-project

```
OpenGALib/AltRegularity.lean (root-level facade)      → OpenGALib/AltRegularity/AltRegularity.lean

(Then create inner OpenGALib/AltRegularity/AltRegularity/ folder and
move modules into it:)

OpenGALib/AltRegularity/Basic.lean              → OpenGALib/AltRegularity/AltRegularity/Basic.lean
OpenGALib/AltRegularity/MainTheorem.lean        → OpenGALib/AltRegularity/AltRegularity/MainTheorem.lean
OpenGALib/AltRegularity/MinMaxExistence.lean    → OpenGALib/AltRegularity/AltRegularity/MinMaxExistence.lean
OpenGALib/AltRegularity/PositiveDensity.lean    → OpenGALib/AltRegularity/AltRegularity/PositiveDensity.lean
OpenGALib/AltRegularity/Integrality/            → OpenGALib/AltRegularity/AltRegularity/Integrality/
OpenGALib/AltRegularity/OneSidedDensity/        → OpenGALib/AltRegularity/AltRegularity/OneSidedDensity/
OpenGALib/AltRegularity/Regularity/             → OpenGALib/AltRegularity/AltRegularity/Regularity/
```

**Important order-of-operations note:** the move
`OpenGALib/AltRegularity.lean → OpenGALib/AltRegularity/AltRegularity.lean`
goes *into* the existing `OpenGALib/AltRegularity/` directory which
currently still contains `Basic.lean`, `MainTheorem.lean`, etc. Use a
temp staging dir (e.g., `OpenGALib/_altreg_stage/`) to avoid shell
collisions:

```bash
mkdir -p OpenGALib/_altreg_stage
mv OpenGALib/AltRegularity.lean         OpenGALib/_altreg_stage/AltRegularity.lean
mv OpenGALib/AltRegularity              OpenGALib/_altreg_stage/AltRegularity_inner
mkdir -p OpenGALib/AltRegularity
mv OpenGALib/_altreg_stage/AltRegularity.lean      OpenGALib/AltRegularity/AltRegularity.lean
mv OpenGALib/_altreg_stage/AltRegularity_inner     OpenGALib/AltRegularity/AltRegularity
rmdir OpenGALib/_altreg_stage
```

### 6.4 MOVE — paper into AltRegularity sub-project

```
OpenGALib/paper/                            → OpenGALib/AltRegularity/paper/
```

### 6.5 CREATE

```
OpenGALib/lakefile.lean                     (rewrite — new content per §5.1)
OpenGALib/OpenGALib.lean                    (new top-level facade, see §6.6)
OpenGALib/AltRegularity/lakefile.lean       (new — content per §5.2)
OpenGALib/AltRegularity/lean-toolchain      (copy from root)
OpenGALib/AltRegularity/lake-manifest.json  (auto-generated by `lake update`
                                             OR copy from root and prune)
```

### 6.6 New `OpenGALib.lean` top-level facade (proposed content)

```lean
/-!
# OpenGALib — Open Geometric Analysis Library

A Lean 4 library of Riemannian-geometry, geometric-measure-theory,
min-max, and regularity primitives. Layered:

```
Riemannian ← GeometricMeasureTheory ← {MinMax, Regularity}
```

Each sub-namespace is built on Mathlib and intended as a future
Mathlib-upstream candidate. Application papers (e.g., AltRegularity)
consume this lib as a separate sub-project.

## Sub-namespaces

* `Riemannian`              — Levi-Civita, Riemann/Ricci/scalar curvature,
                              second fundamental form, manifold gradient
* `GeometricMeasureTheory`  — finite-perimeter, varifolds, stationary,
                              tangent cones, rectifiability, isoperimetric
* `MinMax`                  — sweepout-based min-max (CLS22-style)
* `Regularity`              — Wickramasekera 𝒮_α + smooth regularity
-/

import Riemannian
import GeometricMeasureTheory
import MinMax
import Regularity
```

### 6.7 KEEP at root unchanged

```
OpenGALib/CLAUDE.md
OpenGALib/SOFTWARE_QUALITY_AUDIT.md         (will reference old paths;
                                             update later if desired)
OpenGALib/docs/                             (this REFACTOR_PLAN.md lives here)
OpenGALib/references/
OpenGALib/.git/
OpenGALib/.gitignore
OpenGALib/.github/                          (does not exist yet)
OpenGALib/.vscode/
OpenGALib/.claude/
OpenGALib/.lake/                            (root build artifacts;
                                             will need rebuild after refactor)
OpenGALib/lean-toolchain                    (unchanged)
```

---

## 7. Import path change list

**Expected: zero `.lean` source-file changes.** Reasoning:

- Every cross-package import already uses the *namespace-qualified*
  form (`import Riemannian.Connection`, `import GeometricMeasureTheory.Varifold`,
  `import MinMax.Sweepout.Defs`, etc.).
- The post-refactor file layout preserves these namespace paths
  exactly: `Riemannian.Connection` lives at `OpenGALib/Riemannian/Connection.lean`
  whose Lake-resolved module name is still `Riemannian.Connection`.
- The four sub-namespace facades stay at `Riemannian.lean`,
  `GeometricMeasureTheory.lean`, `MinMax.lean`, `Regularity.lean` — so
  e.g. `import GeometricMeasureTheory` still resolves.
- AltRegularity's imports `import GeometricMeasureTheory.Varifold` etc.
  resolve through the new `require OpenGALib from ".."` chain; no
  source change needed.

**Verification step in execute:** after the moves, grep all `.lean`
files for `import ` lines and confirm no broken paths remain. If a
broken path surfaces (e.g., a module accidentally importing
`SomePkg.SomePkg.Module` from the old nested layout), fix point-wise.

---

## 8. Mathlib pin handling

All five current manifests already pin
`5fc0241932dd6d465bc5549308cc39011772293a` (verified §2). Refactor:

1. New root `lakefile.lean` carries the same SHA
   (`5fc0241932dd6d465bc5549308cc39011772293a`).
2. After deleting the 4 sub-package manifests, run `lake update` from
   `OpenGALib/` to regenerate the root `lake-manifest.json` cleanly.
   Verify the post-update SHA equals the pre-update SHA.
3. From `OpenGALib/AltRegularity/`, run `lake update` to generate the
   sub-project manifest. Verify the AltRegularity manifest's Mathlib
   SHA equals the root's.
4. **Run `lake exe cache get` from both project roots before `lake build`**
   to avoid re-compiling Mathlib from scratch.

If the AltRegularity sub-project Mathlib SHA differs from the root
post-`lake update` (e.g., because Lake's transitive resolution does
something unexpected), pin Mathlib explicitly in
`AltRegularity/lakefile.lean` to match — see Risk R2.

---

## 9. Build verify plan

After refactor (single execute pass or atomic split per §10):

```bash
# Verify OpenGALib root build
cd /Users/moqian/OpenGALib
lake exe cache get
lake build         # builds lean_lib OpenGALib (4 sub-namespaces)
# Expected: same set of modules build as before, no new errors,
# same axiom set per public theorem.

# Verify AltRegularity sub-project build
cd /Users/moqian/OpenGALib/AltRegularity
lake exe cache get
lake build         # builds lean_lib AltRegularity, depending on OpenGALib
# Expected: AltRegularity.MainTheorem and AltRegularity.MinMaxExistence
# elaborate as before with the same #print axioms output.
```

**Pass criteria:**
- Both `lake build` invocations exit 0.
- File count of `.olean` artifacts under `.lake/build/lib/` for each
  sub-namespace matches the pre-refactor count (modulo tooling files).
- `#print axioms AltRegularity.MainTheorem` output unchanged.

---

## 10. Risk assessment

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| **R1** | Casing mismatch (`OpenGALib` vs `OpenGAlib`) breaks Lake / import resolution | High if not locked first | Decide casing in §0 before execute. Bake choice into lakefile + facade + this plan. |
| **R2** | `require OpenGALib from ".."` does not transitively expose Mathlib to AltRegularity, or Lake resolves a different Mathlib SHA than root | Medium | If `lake build` from `AltRegularity/` fails to find Mathlib, add explicit `require mathlib from git "..." @ "<SHA>"` in `AltRegularity/lakefile.lean` matching root. |
| **R3** | `.submodules `Riemannian` does not pick up the `Riemannian.lean` facade (only files under `Riemannian/`) | Medium — Lake docs are ambiguous about whether the bare-namespace file is a "submodule" | Switch to `.andSubmodules` per glob, OR add `roots := #[`Riemannian, `GeometricMeasureTheory, `MinMax, `Regularity]` to the `lean_lib` declaration. |
| **R4** | Move script collision: `mv AltRegularity.lean AltRegularity/AltRegularity.lean` while `AltRegularity/` already contains `Basic.lean` etc. | Low if staging dir used (§6.3) | Use `_altreg_stage/` staging dir as in §6.3. |
| **R5** | `OpenGALib.lean` (top-level facade) is not picked up by any glob and so does not become a build target | Medium | Add `roots := #[`OpenGALib]` to the `lean_lib OpenGALib` declaration, OR import `OpenGALib` from the test/smoke entry once one exists. |
| **R6** | `lake update` from sub-project pulls in a different Mathlib transitive dep set than root, causing olean cache misses | Low — same SHA pinned both places | Run `lake exe cache get` after every `lake update`. If cache miss, accept the one-time rebuild. |
| **R7** | `paper/` move breaks any LaTeX `\input{}` paths or `latexmk` recipes that assume `paper/` is at root | Low (paper compiles inside its own dir) | Inspect `paper/main.tex` for path dependencies before move; fix if any. Currently `paper/main.tex` does not appear to reference any path outside `paper/`. |
| **R8** | `.lake/` directories carry stale absolute paths (Lean 4 uses content hashes, but olean inspector / blueprint tooling may depend on dir structure) | Very low | Delete all `.lake/` directories before first post-refactor build; let them regenerate cleanly. |
| **R9** | Nested AltRegularity sub-project (`OpenGALib/AltRegularity/`) is awkward — VSCode workspace, lake commands, and CI must pick the right `lakefile.lean` | Low — but real ergonomic cost | Document in README. Alternative: move AltRegularity to a sibling at `/Users/moqian/AltRegularity/` requiring `from "../OpenGALib"`. **Cleaner separation, but breaks the "one repo on disk" pattern**. Decision deferred to Moqian. |
| **R10** | Existing 55 sorries surface differently after refactor (e.g., axiom audit on `OpenGALib` vs on individual sub-pkgs gives different totals) | Low semantic risk; no functional impact | Snapshot pre-refactor `#print axioms` for each public theorem; verify post-refactor unchanged. |

---

## 11. Atomic commit sequence

Recommended split — each commit leaves the repo in a buildable state
(except commit C which intentionally introduces the lakefile swap and
is verified by commit D):

### Commit A — flatten 4 sub-package source trees + delete sub-package lakefiles
*(big mechanical commit, ~80 file moves + 16 deletions)*

- Move all `<Pkg>/<Pkg>.lean` → `<Pkg>.lean` and
  `<Pkg>/<Pkg>/*` → `<Pkg>/*` for the four lib sub-packages.
- Delete `<Pkg>/lakefile.lean`, `<Pkg>/lake-manifest.json`,
  `<Pkg>/lean-toolchain`, `<Pkg>/.lake/`.
- Replace root `lakefile.lean` with the new OpenGALib version (§5.1).
- Create `OpenGALib.lean` top-level facade (§6.6).
- **Build verify**: `lake exe cache get && lake build` from root must
  succeed with the new `lean_lib OpenGALib` glob covering all 4
  sub-namespaces.
- **Note**: at this point AltRegularity is broken (it's still in the
  root tree but no longer covered by any lakefile lean_lib). That's
  fine — commit B fixes it.

### Commit B — create AltRegularity sub-project
- Move `AltRegularity.lean` (root facade) and `AltRegularity/*`
  contents into the new nested `AltRegularity/AltRegularity.lean` and
  `AltRegularity/AltRegularity/*` layout (§6.3 staging-dir recipe).
- Move `paper/` → `AltRegularity/paper/`.
- Create `AltRegularity/lakefile.lean` (§5.2),
  `AltRegularity/lean-toolchain` (copy from root).
- Run `lake update` from `AltRegularity/` to generate
  `AltRegularity/lake-manifest.json`.
- **Build verify**: `cd AltRegularity && lake exe cache get && lake build`.

### Commit C — repo-level housekeeping
- Update `.gitignore` to add `AltRegularity/.lake/` and confirm root
  `.lake/` and per-sub-package `.lake/` patterns.
- Update `CLAUDE.md` references that mention the old "5-package"
  framing or the root-level `paper/` location. (Keep as a minimal
  edit; CLAUDE.md restructure is a separate task.)
- Optional: update `SOFTWARE_QUALITY_AUDIT.md` references.

### Commit D — verification + tag (optional)
- Run `lake exe cache get && lake build` in both projects, capture
  `#print axioms` output for `MainTheorem` and `MinMaxExistence`,
  diff against pre-refactor snapshot.
- Tag commit if the Phase 5 sequence now wants `v0.1.0-pre-polish`
  marker.

**Single-big-commit alternative**: collapse A + B + C into one. Faster
to execute, but mid-state is unbuildable. Per CLAUDE.md "atomic
commits, do not commit mid-refactor", **the split (A → B → C → D) is
strictly preferred**. Each commit's "broken sub-project" window is
intentional and bounded.

---

## 12. Summary of decisions Moqian must lock before execute

1. **Casing**: `OpenGALib` (recommended) vs `OpenGAlib`.
2. **AltRegularity location**: nested under `OpenGALib/AltRegularity/`
   (planned) vs sibling at `/Users/moqian/AltRegularity/` (cleaner but
   breaks "one repo" pattern).
3. **Per-file copyright headers** (Phase 5.A): apply during this
   refactor or defer to Phase 5.A?
4. **Single big commit vs 4 atomic commits** (§11).
5. **CHANGELOG entry**: tag this refactor as a release boundary
   (e.g., `v0.1.0-architecture`) or fold into Phase 5.A v0.1.0?

After lock-in, the execute prompt is mechanical (~1 session).

---

## 13. Out of scope (this plan)

- Math content changes (any `.lean` source modification beyond `mv`).
- README / LICENSE / CITATION / CHANGELOG creation (Phase 5.A).
- CI workflow creation (Phase 5.D).
- Audit binary creation (Phase 5.D).
- Smoke test creation (Phase 5.D).
- Riemannian-as-standalone-spin-out (post-Phase 5).

**No code touched. No commits made.** Awaiting Moqian review.
