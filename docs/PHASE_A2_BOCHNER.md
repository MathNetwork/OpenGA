# Phase A.2 — Bochner-Weitzenböck identity

## Goal

Close `bochner_weitzenboeck` in `OpenGALib/Riemannian/Operators/Bochner.lean`
unconditionally for smooth `f : M → ℝ` on a Riemannian manifold `[HasMetric I M]`:

```
(1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x
  = ‖hess_g[I] f‖²_g x
    + ⟪(grad_g[I] f) x, (grad_g[I] (Δ_g[I] f)) x⟫_g
    + Ric_g((grad_g[I] f) x, (grad_g[I] f) x) x
```

Pointwise version. No boundary, no integration, no Lichnerowicz 1-form
form — those are downstream of the pointwise identity.

## Strategy

Reference `external/differential-geometry` for architecture; re-implement
in our own conventions (`[HasMetric I M]` typeclass, `metricInner`,
`leviCivitaConnection`, `stdOrthonormalBasis trace`). The math is
identical; the translation friction is surface convention only
(typeclass vs explicit metric arg, naming).

Per `feedback_independent_lib_stance.md`: external is reference, not
source. Read for proof structure, re-implement for our framework.

## Prerequisite (done)

| Step | Status | Commit |
|---|---|---|
| A.1 `scalarLaplacian` → `stdOrthonormalBasis` | ✓ | `78a2a88` |
| A.2 `frobeniusSq` / `trace` → `stdOrthonormalBasis` | ✓ | `78a2a88` |
| A.3 Bridge `scalarLaplacian = laplacian (hessianBilin f)` | ✓ | `3940750` |

Bochner statement is now mathematically well-formed (both sides are
geometric / g-trace / g-Hilbert-Schmidt).

## Plan

Each step is an atomic commit. Build-verified at every step. No half-finished
state crosses commit boundaries. Steps later in the list depend on earlier
ones; intermediate steps yield independently useful lemmas.

### A.4 — `manifoldGradient_contMDiffAt`

Foundational smoothness helper: for `f ∈ C^{n+1}` near `x`, `∇f` is `C^n`
near `x` as a bundle section.

**Why first:** consumed by every subsequent step (C, D, G all differentiate
`∇f` twice and need the propagation).

**Closure path:** `manifoldGradient = metricRiesz ∘ mfderiv f`. `mfderiv f`
is smooth one degree less than f (Mathlib `ContMDiff.mfderiv`). `metricRiesz`
is smooth (from `Metric.lean` Riesz section smoothness). Compose.

### A.5 — `hessianBilin_contMDiffAt`

Hessian as smooth `(0,2)`-tensor section. For `f ∈ C^{n+2}` near `x`,
`hessianBilin f` is `C^n` near `x` as a section of `Bilin I M`.

**Why:** `hessianBilin f` evaluated at orthonormal frames must be
differentiable for B (Hessian symmetry) and onwards.

**Closure path:** `hessianBilin f x v w = metricInner x (covDerivAt (∇f) x v) w`.
`covDerivAt (∇f) x v` is smooth in `x` (one degree less than `∇f` — needs
`covDerivAt` smoothness on the framework's `koszulCovDeriv_const_smoothAt`
sorry, which is on the critical path here).

### F — Ricci-trace formula on a g-orthonormal frame

```
Ric_g(V, W) x
  = ∑ᵢ ⟪εᵢ, R(εᵢ, const V) (const W) x⟫_g
```

where `{εᵢ} = stdOrthonormalBasis ℝ (TangentSpace I x)`.

**Why:** mechanical unfolding of `ricciTensor` def + Mathlib's
`LinearMap.trace_eq_sum_inner`. Required to identify
`∑ ⟨R(εᵢ, ∇f) ∇f, εᵢ⟩_g` with `Ric_g(∇f, ∇f)` in the final assembly.

**Closure path:** apply `LinearMap.trace_eq_sum_inner` to `curvatureEndo X Y x`
with `b = stdOrthonormalBasis`.

### B — Hessian symmetry on scalars

```
hessianBilin f x v w = hessianBilin f x w v
```

for `f ∈ C²` near `x`, `IsManifold I 2 M`, chart interior condition.

**Why:** essential for the trace reduction (B2 / `hLeibniz`) — symmetric
Hessian means the two `g(∇²f(·, X), Y)` contractions agree.

**Closure path** (5-step chain, all helper lemmas already exist):
1. apply `leviCivitaConnection_metric_compatible` at `(∇f, const w, const v)`
2. apply `leviCivitaConnection_metric_compatible` at `(∇f, const v, const w)`
3. subtract — get `[Hess sym error] = mfderiv (mfderiv f) ... - mfderiv ... + ⟨∇f, ∇_cv cw - ∇_cw cv⟩`
4. apply `mfderiv_iterate_sub_eq_mlieBracket_apply` (LHS difference = `mfderiv f · [cv, cw]`)
5. apply `covDeriv_sub_swap_eq_mlieBracket` (torsion-free) + `manifoldGradient_inner_eq` (gradient duality) — RHS extra = `mfderiv f · [cv, cw]`
   → terms cancel → `Hess sym error = 0`.

Needs A.4 for `∇f` smoothness.

### C — Connection Laplacian on vector fields

```
def connectionLaplacian (Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x
  := ∑ᵢ covDerivAt (fun y => covDerivAt Z y (parallel εᵢ y)) x εᵢ - covDerivAt Z x (∇_εᵢ εᵢ)
```

or equivalently `Δ_∇ Z := tr_g(∇²Z)` where `∇²Z` is the second covariant
derivative of `Z`.

**Why:** Bochner's heart-of-Bochner identity is
`Δ_∇ (∇f) = ∇(Δ_g f) + Ric^♯(∇f)`. We need both sides to be
typecheckable expressions in the framework.

**Sub-steps:**
- C.1 — define `connectionLaplacian Z x` (using `stdOrthonormalBasis`)
- C.2 — algebra lemmas (`add`, `smul`)
- C.3 — trace-bilinear bridge

External: `Integral/Connection/ConnectionLaplacian.lean` ~657 LOC.

### D — Ricci identity for vector fields

```
covDerivAt (fun y => covDerivAt Z y (X y)) x (Y x)
  - covDerivAt (fun y => covDerivAt Z y (Y y)) x (X x)
  = riemannCurvature X Y Z x + covDerivAt Z x (mlieBracket I X Y x)
```

i.e. `∇_X ∇_Y Z - ∇_Y ∇_X Z = R(X,Y) Z + ∇_{[X,Y]} Z` for smooth `X, Y, Z`.

**Why:** the heart of the heart-of-Bochner identity. `R(X,Y)Z` in our
`riemannCurvature` def is exactly `∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]} Z`,
so this is essentially the def unwound + smoothness propagation. The
work is propagating smoothness hypotheses cleanly through the iterated
derivatives.

**Sub-steps:**
- D.1 — second covariant derivative as a section
- D.2 — Ricci identity at constant frame directions
- D.3 — Ricci identity at smooth frame directions (full statement)

External: `Integral/Connection/RicciIdentity.lean` ~1020 LOC.

### E — Leibniz trace reduction (`hLeibniz_discharge` analog)

```
mfderiv (mfderiv (metricInner _ (∇f _) (∇f _))) x = 2 (Δ_∇ ∇f, ∇f) + 2 ‖Hess f‖²_g
```

Trace form of the Leibniz product rule applied twice to `metricInner (∇f) (∇f)`
in the `stdOrthonormalBasis` frame.

**Why:** rewrites `½ Δ_g ‖∇f‖²_g` into `⟨Δ_∇ ∇f, ∇f⟩ + ‖Hess f‖²_g` —
half the Bochner identity (B2 in external's decomposition).

**Closure path:** apply `leviCivitaConnection_metric_compatible` to
`(∇f, ∇f)` twice, contract via `stdOrthonormalBasis trace`. Needs A.4, B.

External: subset of `Bochner.lean` ~400 LOC.

### G — Heart-of-Bochner reduction (`hInner_discharge` analog)

```
∑ᵢ covDerivAt (fun y => covDerivAt (∇f) y εᵢ) x εᵢ
  = covDerivAt (∇(Δ_g f)) x εᵢ |_{summed}  + ricciSharp (∇f) x
```

Trace form of Ricci identity (D) applied to `Z = ∇f`, with one slot
contracted via `stdOrthonormalBasis`, using Hessian symmetry (B) to
swap `∇²f(εᵢ, εⱼ) ↔ ∇²f(εⱼ, εᵢ)`.

**Why:** rewrites `⟨Δ_∇ ∇f, ∇f⟩` into `⟨∇(Δ_g f), ∇f⟩ + Ric(∇f, ∇f)` —
the second half of Bochner (B3 in external's decomposition).

**Closure path:** chain D + B + F + A.4. The hardest of the sub-steps.

External: `Bochner.lean` ~700 LOC for `hInner_discharge`.

### H — Bochner main assembly

```
½ Δ_g ‖∇f‖²_g = ‖Hess f‖²_g + ⟨∇f, ∇(Δ_g f)⟩_g + Ric(∇f, ∇f)
```

Combine E (½ Δ_g ‖∇f‖²_g = ⟨Δ_∇ ∇f, ∇f⟩ + ‖Hess f‖²_g) with
G (⟨Δ_∇ ∇f, ∇f⟩ = ⟨∇(Δ_g f), ∇f⟩ + Ric(∇f, ∇f)) and substitute.

Closes the `bochner_weitzenboeck` sorry at `Bochner.lean:42`.

External: `bochner_pointwise_abstract_unconditional` (Bochner.lean:3663),
the final composition step ~50 LOC.

## Dependency graph

```
A.1, A.2, A.3 (done)
    ↓
A.4 (gradient smoothness)
    ↓
  ┌─┴────┬────────┐
  ↓      ↓        ↓
A.5    F (Ricci   C (ConnLap)
(Hess  trace)
 smth)
  ↓               ↓
  B (Hess         D (Ricci id)
  symm)
  ↓        ↓      ↓
  ├────────┴──→ E (Leibniz reduction)
  │             ↓
  │             G (heart-of-Bochner) ← also needs B, F
  │             ↓
  └─────────→ H (main assembly)
```

`A.4`, `F`, `C` can be parallelised (no inter-dependencies). The critical
path is `A.4 → A.5 → B → G → H`.

## Acceptance criteria per step

For each step:
- the new lemma typechecks under the project's full variable block;
- `lake build` is green;
- sorry count is unchanged or strictly decreasing (no new sorrys);
- a 1-line docstring states the math claim with `**Ground truth**: ...` citing
  do Carmo / Petersen / Lee where applicable;
- the closing commit message names the step (`Bochner A.4: ...`).

## Out of scope for Phase A.2

- Integrated Bochner (∫ form) — requires `DivergenceTheorem`, separate
  Phase A.2.x.
- Lichnerowicz on 1-forms — derivable from pointwise Bochner, but separate.
- Reilly identity / boundary versions — separate phase.
- `IsLocallyConstantChartedSpace` vs `Boundaryless` reconciliation — both
  give pointwise machinery; postpone harmonisation.

## Source-of-truth citations

- do Carmo, *Riemannian Geometry*, §4 (curvature), §6 (Ricci),
  §8 ex. 14 (Bochner-Weitzenböck).
- Petersen, *Riemannian Geometry* (3rd ed.), Ch. 7 §1 Proposition 33.
- Lee, *Smooth Manifolds*, Ch. 4 + 12 (connections, curvature).
- Schoen-Simon 1981, §1 (variational application — context for GMT use).

For Lean structure: `external/differential-geometry/DifferentialGeometry/Integral/Connection/Bochner.lean`
and supporting `ConnectionLaplacian.lean`, `RicciIdentity.lean`.
