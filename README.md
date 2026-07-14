<h1 align="center">OpenGA — Hopf–Rinow milestone</h1>

<p align="center"><em>A self-contained slice of the OpenGA Riemannian-geometry
library: the Lean formalization of the Hopf–Rinow theorem and the LaTeX
blueprint it is built from — nothing else.</em></p>

This branch contains **only** what is needed to state, build, and read the
Hopf–Rinow theorem:

- the `OpenGALib` Lean modules on the dependency cone of
  `OpenGALib.Riemannian.Geodesic.HopfRinow` (68 files), and
- the do Carmo blueprint chapters on the path to it (Ch. 0, 1, 2, 3, 7).

No website, dashboard, dependency-graph tooling, or orchestration machinery is
included.

## Layout

```
OpenGALib.lean          root module — imports exactly the Hopf–Rinow cone
OpenGALib/              the 68 Lean modules of that cone
lakefile.lean           Lake package (depends on Mathlib, pinned below)
lake-manifest.json      pinned dependency revisions
lean-toolchain          Lean toolchain (leanprover/lean4:v4.30.0-rc2)
blueprint/
  main.tex              standalone preamble + the 5 chapters
  chapters/*.tex        do Carmo transcription (Ch. 0, 1, 2, 3, 7)
.githooks/commit-msg    strips CI-agent attribution from commit messages
LICENSE
```

## Build the Lean library

```bash
lake exe cache get      # fetch the prebuilt Mathlib for the pinned SHA
lake build              # builds OpenGALib
```

Requires Mathlib at the revision pinned in `lake-manifest.json`
(`leanprover-community/mathlib4 @ 5fc0241932dd6d465bc5549308cc39011772293a`).

## Build the blueprint PDF

```bash
cd blueprint
pdflatex main && pdflatex main   # run twice to resolve cross-references
```

Produces `blueprint/main.pdf`. Only standard TeX Live packages are used
(`amsthm`, `mathtools`, `hyperref`, `cleveref`, `underscore`). The
blueprint-specific markers (`\lean`, `\leanok`, `\uses`, `\dcref`, …) are
defined as no-ops in `main.tex`, so no leanblueprint toolchain is needed.

## Status

**Complete.** The Hopf–Rinow facade is fully proved — `sorry`-free and
axiom-clean (each theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`; verified with `#print axioms`, not just a green build):

| Theorem (do Carmo Ch. 7)                                | Statement |
| ------------------------------------------------------- | --------- |
| `hopfRinow`                                             | `CompleteSpace M ↔ IsGeodesicallyComplete g` (the **c ⟺ d** equivalence) |
| `complete_of_isGeodesicallyComplete`                    | geodesically complete ⟹ metrically complete (**d ⟹ c**) |
| `complete_of_geodesicallyComplete_at`                   | `exp_p` total at one point ⟹ complete (**a ⟹ c**) |
| `exists_minimizing_geodesic`                            | any two points joined by a minimizing geodesic (**f**) |
| `isGeodesicallyComplete_of_compactSpace`                | compact ⟹ complete (**Cor. 2.9**) |

All under the standing hypotheses `ConnectedSpace M` and `g.IsRiemannianDist`
(the metric-space structure is the Riemannian distance of `g`). Blueprint nodes
carry `\lean{…}` / `\leanok` markers recording their correspondence with the
Lean side.

## License

Released under the Apache 2.0 License. See the LICENSE file for details.
