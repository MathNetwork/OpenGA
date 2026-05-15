# `OpenGALib/Util/` — top-level cross-layer engineering

Per CLAUDE.md §Architecture ("two-tier `Util/` layout"), this directory
holds engineering helpers shared **across multiple layers** of OpenGALib:
notation, tactics, simp attributes, Mathlib-extension lemmas, and
Lean-native architecture linters.

Layer-scoped engineering tax lives in `OpenGALib/<Layer>/Util/` instead
(e.g. `Riemannian/Util/`, `Tensor/Alternating/Util/`). When in doubt
about where a helper goes: if more than one layer would import it, it
belongs here.

## Files

| File | Role |
|------|------|
| [`Attributes.lean`](./Attributes.lean) | **Riemannian simp attribute declarations** — registers `[metric_simp]`, `[riem_simp]` and friends without importing the lemma sites that use them. Imported by lemma sites (to make tag available) and by downstream proof code (to invoke `simp [metric_simp]`). |
| [`Notation.lean`](./Notation.lean) | **OpenGALib notation facade** — single import point for the Riemannian notational surface. Doesn't define notation itself; each notation lives next to its `def` (Mathlib convention). Lists the inventory `∇[X] Y`, `⟪V, W⟫_g`, `Ric_g`, `grad_g[I]`, etc. for grep-discoverability. |
| [`Tactic.lean`](./Tactic.lean) | **Riemannian tactic infrastructure** — re-exports the simp sets with their tagged lemmas plus the `riem_normalize` tactic shorthand. Import this to use simp sets without separate attribute machinery. |
| [`MFDeriv.lean`](./MFDeriv.lean) | **Manifold-derivative extensions** — generic `mfderiv` lemmas with no Riemannian / metric dependency. Each theorem self-contained (no `variable` block) so they're reusable without typeclass-pollution. |
| [`Linter.lean`](./Linter.lean) | **OpenGALib fitness-function linter set** — aggregates the three Lean-native linters (`mathTag`, `anchorPurity`, `naming`) into a single `linter.openGA` option set. See `Linter/README.md` for the per-linter details. |

## Subdirectories

| Subdirectory | Role |
|--------------|------|
| [`Linter/`](./Linter/README.md) | **Lean-native fitness-function linters** — `MathTag`, `AnchorPurity`, `Naming`. Three files plus a dedicated `README.md`. Each linter fires during elaboration; CI snapshots their baseline counts in `.github/workflows/ci.yml`. |

## Conventions

* **Cross-layer scope** — content belongs here iff multiple layers would
  import it. Single-layer helpers live in `<Layer>/Util/`. This file
  organisation is the "Stable Dependencies Principle" (Robert C. Martin):
  cross-layer Util sits at the most-depended-on / most-stable position.

* **No `variable` blocks for general lemmas** — see `MFDeriv.lean`.
  Self-contained signatures keep each theorem reusable without dragging
  in a section's typeclass context.

* **Attribute/notation/lemma separation** — `Attributes.lean` registers
  tags only; lemmas tagged with them live where they belong
  mathematically (e.g. `Metric/RiemannianMetric.lean` for
  `[metric_simp]` lemmas). This avoids circular imports and keeps each
  layer self-describing.

* **Linter additions** — drop `Linter/<Name>.lean`, register the option
  in `Linter.lean`'s `register_linter_set`, add a unit test under
  `Tests/Linter/`, add a baseline check to `.github/workflows/ci.yml`.
  Full template in `Linter/README.md`.
