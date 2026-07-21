# Review guide

How to review a pull request here. A PR should be approved because it passed a
**fixed, repeatable checklist** — not because it "looked fine". A PR merges when
the machine gates are green **and** the human dimensions pass.

## Machine gates — CI covers these, don't re-check by hand

If CI is green, these are satisfied:

- **Builds** — `lake build` succeeds.
- **No `sorry`** — `main` is sorry-free (hard gate; sorry-WIP lives on a
  development branch).
- **Linters** — MathTag (docstring tags), AnchorPurity, Naming (no bare
  initialisms like `CLM`).
- **Unused imports** — `shake` baseline.

## Human dimensions — the actual focus

| Dimension | What to check |
|---|---|
| **Correctness** | Statement is non-vacuous; hypotheses are sound and not so strong the result is empty; the conclusion is the intended one. A predicate must mean what its name says (e.g. a "geodesic" predicate should imply continuity). |
| **Reuse** | Not already in Mathlib or elsewhere in OpenGALib. For a "fills a Mathlib gap" lemma, confirm the gap is real. |
| **API** | Hypotheses are minimal; instances vs explicit args used correctly; signatures are clean. |
| **Naming** | Mathlib conventions; the name matches what is actually proved — a name must not over-claim. |
| **Generality** | Not over-specialized; stated at the natural level of generality. |

## Adoption PRs — porting a file from `feat/hopf-rinow`

Most PRs toward v0.1.0 port one proven file from `feat/hopf-rinow`. Additionally:

- **Faithful port** — the file matches its `feat/hopf-rinow` version; no silent
  edits crept in (`git diff mathnetwork/feat/hopf-rinow -- <file>`).
- **Correct layer** — a genuine leaf: every import is already on `main`
  (bottom-up along the dependency cone).
- **Axiom-clean** — for facade theorems, `#print axioms` shows only
  `propext, Classical.choice, Quot.sound` — no `sorryAx`, no stray axiom.
- **[#112](../../issues/112) exposure** — the file is not one flagged there
  (§3.4 `Geodesic/Equation.lean`, §3.1 `Geodesic/HopfRinow.lean`); if it is,
  the prerequisite fix must already be in.

## Roles

Cut PRs: @LehengChen · Review: @AxelDlv00, @JxChen24 · Approve & merge:
@Spring-1211. See milestone [v0.1.0 — Hopf–Rinow](../../milestone/1).
