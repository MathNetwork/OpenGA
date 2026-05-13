# External Integration Plan

Source: `qinz1yang/differential-geometry` (cloned to `external/`,
`.gitignore`-d). Lib is reference material — we re-implement in our
conventions, not copy. See `feedback_independent_lib_stance.md` (memory)
and `feedback_external_repo_passive_reference.md` (memory) for the
guiding stance.

This doc is the **architectural placement decision** — where each
piece of their lib lands in OpenGALib's structure, what we skip, and
the convention for porting.

## Decisions

### Skip

Out of scope for OpenGALib's current focus (geometric analysis lib for
GMT / Riemannian work):

| Their subdir | Files | Reason to skip |
|--------------|-------|----------------|
| `Analysis/` | 122 | Sobolev / Laplacian / spectral PDE — different focus |
| `Integral/` | 92 | Manifold integration — revisit when a consumer needs it |
| `Synthetic/` | 65 | Synthetic differential geometry — different paradigm |
| `External/` | 92 | Their internal Mathlib补丁 — each lib should own its Mathlib gap-fillers |
| `VectorBundle/{VectorField, Section}` | 2 | Subsumed by Mathlib `ContMDiffSection` + our `SmoothVectorField` |

### Map to OpenGALib structure

```
their qinz1yang lib         our OpenGALib
─────────────────────       ───────────────────────────────────
Tensor/Auxiliary/        →  OpenGALib/Algebraic/Auxiliary/
                            (math helpers: Fin equivalences, Perm,
                             Shuffle decomposition, etc. — pure
                             algebra, not engineering Util)

Tensor/Multilinear/      →  OpenGALib/Tensor/Multilinear/
Tensor/Alternating/      →  OpenGALib/Tensor/Alternating/
Tensor/Product/          →  OpenGALib/Tensor/Product/
Tensor/Mixed/            →  OpenGALib/Tensor/Mixed/
DifferentialForm/        →  OpenGALib/Tensor/DifferentialForm/

Tensor/RSTensor/         →  OpenGALib/Riemannian/Tensor/
                            (Riemannian-specific: contraction,
                             Lie derivative, metric on tensors)

Geometry/Curvature/      →  Selective merge into existing
{Ricci, Riemann}            OpenGALib/Riemannian/Curvature.lean
                            (we already have riemannCurvature, ricci;
                             cross-check + adopt better proofs/lemmas)

Geometry/Gradient        →  OpenGALib/Riemannian/Operators/Gradient.lean
                            (our existing Riemannian/Gradient.lean
                             stays; this may extend it)

Geometry/Hessian         →  OpenGALib/Riemannian/Operators/Hessian.lean
Geometry/Laplacian       →  OpenGALib/Riemannian/Operators/Laplacian.lean
Geometry/NormGradSq      →  OpenGALib/Riemannian/Operators/NormGradSq.lean
Geometry/VossWeyl        →  OpenGALib/Riemannian/Operators/VossWeyl.lean
```

### Architectural rationale

**Tensor is top-level**, not under Riemannian. Reason:

* Multilinear / alternating / product / mixed bundles are pure vector
  bundle algebra — no metric required.
* Riemannian-specific tensor structure (lower indices via metric,
  Riemannian inner product on `(r,s)`-tensor sections) lives in
  `Riemannian/Tensor/` — they consume the general tensor framework.
* Future GMT sub-packages can use `OpenGALib/Tensor/` without pulling
  in the Riemannian metric layer.

**`Tensor/Auxiliary/` is math, not engineering Util.** Files like
`Fin.lean`, `Perm.lean`, `ShuffleDecomposition.lean` are linear
algebra / combinatorics primitives. They go in
`OpenGALib/Algebraic/Auxiliary/`, parallel to our existing
`OpenGALib/Algebraic/BilinearForm/` and `OpenGALib/Algebraic/Instances/`.
Engineering Util (`OpenGALib/Util/`) is reserved for notation, simp set
declarations, tactic macros — not math content.

**`Operators/` is a new sub-namespace under Riemannian** for second-order
differential operators (Laplacian, Hessian, etc.) on Riemannian
manifolds. `Gradient.lean` already lives in `Riemannian/`; we could
move it into `Operators/` but that's churn — leaving it where it is for
now, and `Operators/` will host new content.

## Porting convention

When implementing each unit:

1. **Read** their version in `external/differential-geometry/<path>`.
2. **Re-write** in OpenGALib conventions:
   - Use our notation (`∇[X] Y`, `⟦X, Y⟧`, `Riem(X, Y) Z`, etc.) where applicable.
   - Use our `riem_simp` / `metric_simp` simp sets for routine algebra.
   - Use our docstring style (`**Ground truth**: ...`, sorry-classified, etc.).
   - Match our typeclass cascade choices (e.g., `[NormedSpace ℝ E]` not
     `[Bundle.RiemannianBundle]`).
3. **Atomic commit per coherent unit** — one file or one tightly-coupled
   pair, not a whole subdir at once.
4. **Commit message attribution**: include
   `Inspired by qinz1yang/differential-geometry/<source path>`.
5. **Skip what they have but Mathlib already provides cleanly** — don't
   duplicate Mathlib for Mathlib's sake.
6. **Skip auxiliary lemmas we don't need** — only port what a downstream
   theorem in our lib actually consumes.

## Order of operations

Suggested implementation order (dep order):

1. `Algebraic/Auxiliary/Fin` + `Perm` + Kronecker delta (no deps).
2. `Tensor/Multilinear/Bundle` + `Fiber` + `Field` (multilinear foundation).
3. `Tensor/Alternating/Bundle` + `Wedge` (depends on Multilinear).
4. `Tensor/Product/Defs` + `Bundle` (depends on Multilinear).
5. `Tensor/Mixed/{Bundle, Field}` (depends on Multilinear).
6. `Tensor/DifferentialForm` (depends on Alternating).
7. `Riemannian/Tensor/RSTensor` family (depends on all above + our Metric).
8. `Riemannian/Operators/{Hessian, Laplacian, ...}` (depends on Riemannian/Tensor).
9. Selective merge of `Geometry/Curvature/{Ricci, Riemann}` into our
   existing `Riemannian/Curvature.lean`.

Each phase is multiple atomic commits. No specific deadline — driven by
which OpenGALib consumers (current or near-future) need each piece.

## Skipped and why (vs adopted)

* **`VectorBundle/Frame.lean`** — useful in principle (extending local
  frames to global sections), but our `BumpFunction.extendVectorField`
  may already cover this use case. Audit before porting.
* **`VectorBundle/Dual.lean`** — Mathlib has `Bundle.dual` recently;
  check coverage.
* **`Tensor/Auxiliary/LIContDiff.lean`** — looks like a smoothness
  helper for linear isomorphisms. Maybe useful, maybe Mathlib-coverable.
  Audit on-demand.

## What this doc is NOT

* Not a roadmap with deadlines.
* Not a commitment to port every listed file.
* Not a study guide — `external/` is for me (Claude) to consult during
  execution; this doc is for Moqian to validate the architectural
  decisions.

When a specific port is needed, this doc is the authority on **where**
it lands. The act of porting itself is per-task and follows the
[Porting convention](#porting-convention) above.
