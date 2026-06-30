# Divergence-theorem port — worklist and assessment

Scoped port plan for the closed-manifold divergence theorem, the keystone
(`docs/archive/COMPARISON_GEOMETRY_ROADMAP.md` #6) that unlocks Bishop–Gromov and the
Lichnerowicz estimate. **Assessment only — no code yet.**

## Source and stance

Reference: `external/differential-geometry` (the upstream Ricci-flow project,
refreshed 2026-06-14, gitignored). It already proves the keystone, **0 sorry**:

```
DivergenceTheorem/Closed.lean:
  integral_divergence_eq_zero_of_compact :
    ∫ x, divergence_g g X x ∂(riemannianVolumeMeasure g) = 0   -- closed M
```

Per the independent-library stance, we **re-implement in our conventions on top
of our own `Volume/`**; we do not commit upstream code. Upstream is the proof
blueprint, not a dependency.

## Scope: what actually has to be ported

The transitive dependency cone of `Closed.lean` + `Green.lean` is **46 files**,
but most are facilities OpenGALib already has (Laplacian, Gradient, Divergence
operators; tensor/multilinear bundles; metric API). Subtracting those:

| Upstream layer | Files | OpenGALib status |
|---|---|---|
| `Measure/` (Riemannian measure via chart density + POU) | 8 | 🟡 **mostly have** — our `Volume/` is the same construction (`VolumeForm`, `Util/{ChartLocalMeasure, GramDeterminant, ChartSqrtGramDet, ChartTransition, PartitionOfUnityGlue}`); reconcile, don't re-port |
| **`DivergenceTheorem/`** | 10 | 🔴 **the real port** — we have none of this layer |
| `Operator/{Laplacian,Gradient}`, `Metric/*`, `Tensor/*`, `Bundle/*` | ~16 | ✅ have OpenGALib equivalents |

So the genuine work is the **`DivergenceTheorem/` layer (~10 files / ~4000
lines)**, built on top of our existing `Volume/` foundation.

### The `DivergenceTheorem/` files to port (dependency order)

| # | Upstream file | Lines | Role | Notes |
|---|---|---|---|---|
| 1 | `LocalFormula` | 418 | divergence-in-a-chart local formula | rests on Gram-density; maps to our `Volume/Util/ChartSqrtGramDet` |
| 2 | `TangentAction` | — | tangent-vector action in coordinates | small adapter |
| 3 | `ChartCoeffPullback` | — | chart coefficient pullback | maps to our `ChartPullback` |
| 4 | `ChartInvariance` | — | chart-independence of the local integral | maps to our `ChartOverlap`/`ChartTransition` |
| 5 | `ChartLocalIbp` | 941 | **chart-local integration by parts** (Euclidean IbP transported) | the core; largest file |
| 6 | `POUReduction` | 621 | partition-of-unity reduction global ← local | maps to our `PartitionOfUnityGlue` |
| 7 | `Proper` | 813 | properness / support bookkeeping | |
| 8 | `Closed` | 357 | **headline `∫_M div_g X = 0`** (compact, boundaryless) | the keystone |
| 9 | `IntegrationByParts` | 232 | global IbP corollary | |
| 10 | `Green` | 502 | Green's identities `∫⟨∇u,∇v⟩ = -∫ u Δv` | the direct input to Lichnerowicz |

## Convention translation (upstream → ours)

| Upstream | OpenGALib |
|---|---|
| `SmoothRiemannianMetric I M` | `RiemannianMetric I M` (`Riemannian/Metric/RiemannianMetric`) |
| `riemannianVolumeMeasure g` | `Riemannian.volumeMeasure g` (`Volume/VolumeForm`) |
| `divergence_g g X` | divergence from `Operators/Divergence` |
| `Cₛ^∞⟮I; E, TangentSpace I⟯` (smooth sections) | our smooth vector-field type |
| `Measure/ChartDensity`, `JacobiFormula` | `Volume/Util/{ChartLocalMeasure, GramDeterminant}` |
| docstrings | single `**Math.**` anchor tags; `Provenance:` footer citing upstream commit; book refs in `## References` only (per house style) |

## Scope

Genuine new work: the `DivergenceTheorem/` layer — **~10 files / ~4000 lines**,
re-implemented in our conventions on top of our `Volume/`. The `Measure/` half
is largely reconciliation (we have the construction already). The effort is
**bounded** — the upstream proof is a complete, 0-sorry blueprint — and
**high-leverage**: closing it resolves the COMPARISON_GEOMETRY_ROADMAP keystone,
unlocking Bishop–Gromov, Lichnerowicz, and the Green-identity spectral results
together. Scope is measured in files / lines / blueprint-completeness, not
calendar time.

## Open prerequisite to verify first

Before porting, confirm our `Volume/volumeMeasure` is **definitionally aligned**
with upstream's `riemannianVolumeMeasure` (both = chart density `√det g` pushed
through charts, glued by POU). If they agree, the `Measure/` layer is pure
reconciliation and only the 10 `DivergenceTheorem/` files are new. If they
differ, the gap widens. This one check sizes the whole effort and should precede
any porting decision.

## Recommended first step (when porting starts)

`LocalFormula` (#1) → `ChartLocalIbp` (#5) → `POUReduction` (#6) → `Closed` (#8):
the minimal spine to the keystone, skipping `Green`/`Proper` until the headline
`∫_M div = 0` compiles. Then `Green` for the Lichnerowicz hand-off.
