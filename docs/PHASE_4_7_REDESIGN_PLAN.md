# Phase 4.7 — Framework Typeclass-Level Redesign Plan

**Status**: Plan-only. Awaiting Moqian review before execution.

**Trigger**: lean4#13063 typeclass diamond between `RiemannianBundle`-derived
`NormedAddCommGroup (TangentSpace I y)` and direct `[NormedAddCommGroup E]` via
`TangentSpace I y = E` defeq. 8+ documented workaround attempts across multiple
sessions. Mathlib's own `Topology/VectorBundle/Riemannian.lean:439-440`
explicitly references lean4#13063. The diamond blocks closing
`koszulLinearFunctional_exists` and `leviCivitaConnection_exists`.

## 1. Audit: Current `RiemannianBundle` Dependency Graph

**15 files framework-wide depend on `[RiemannianBundle (fun x : M => TangentSpace I x)]`:**

### Riemannian/ (5 files — core)
- `Connection.lean` — `koszulFunctional`, `leviCivitaConnection_exists`,
  `covDeriv`, 10 koszul algebraic identities, `koszulCovDeriv`
- `Curvature.lean` — Riemann tensor, Ricci, scalar curvature
- `SecondFundamentalForm.lean` — second fundamental form, mean curvature
- `Gradient.lean` — `manifoldGradient` (via Riesz duality)
- `InnerProductBridge.lean` — explicit instance bridge (4 instances)

### GeometricMeasureTheory/ (5 files)
- `HasNormal.lean` — `bvGradientDirection`, unit normal
- `Stable.lean` — second variation stability
- `Variation/FirstVariation.lean` — first variation formula `⟨X, ν⟩`
- `Variation/SecondVariation.lean` — second variation curvature term
- `Isoperimetric/ReducedBoundary.lean`

### Regularity/ (2 files)
- `AlphaStructural.lean` — α-structural regularity (Wic14)
- `SmoothRegularity.lean` — smooth regularity

### AltRegularity/ (3 files)
- `MainTheorem.lean` — paper main theorem chain
- `MinMaxExistence.lean` — min-max existence
- `Regularity/StabilityVerification.lean`

### MinMax/ (0 files — clean)

**Inner product reference count**:
- `Riemannian/`: 118 occurrences of `inner ℝ` / `⟪·, ·⟫`
- Framework-wide: ~250+ inner product references estimated

**Diamond-causing instance**: `Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal`
(Mathlib's scoped instance, priority 80, deliberately ordered for lean4#13063
per the comment in Mathlib source).

## 2. Typeclass Design: Custom `RiemannianMetric`

### Design goal
A framework-owned typeclass providing the Riemannian metric **without** synthesizing
`InnerProductSpace ℝ (TangentSpace I y)` (the synthesis path that triggers the diamond).

### Proposed interface (sketch)

```lean
namespace OpenGALib

/-- Framework-owned Riemannian metric typeclass.
Bypasses lean4#13063 by NOT deriving `InnerProductSpace` on each fiber;
instead provides an explicit operation `metricInner` plus axioms. -/
class RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  /-- The metric tensor at each point: a symmetric bilinear form on `T_xM = E`. -/
  metricTensor : (x : M) → E →L[ℝ] E →L[ℝ] ℝ
  symm : ∀ x v w, metricTensor x v w = metricTensor x w v
  posdef : ∀ x v, v ≠ 0 → 0 < metricTensor x v v
  smoothMetric : ContMDiff I (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ⊤ metricTensor

namespace RiemannianMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [g : RiemannianMetric I M]

/-- The metric inner product at `x`, treating `TangentSpace I x = E` defeq. -/
def metricInner (x : M) (V W : TangentSpace I x) : ℝ :=
  g.metricTensor x V W

notation "⟪" V ", " W "⟫_g[" x "]" => metricInner x V W

end RiemannianMetric

end OpenGALib
```

### Diamond avoidance mechanism

The framework's `RiemannianMetric` typeclass:
- Requires `[InnerProductSpace ℝ E]` (the model space's standard inner product —
  used for the `E →L[ℝ] E →L[ℝ] ℝ` bilinear form's continuity)
- Does **NOT** declare `InnerProductSpace ℝ (TangentSpace I y)` as a derived instance
- The `metricInner` operation is **explicit** (not via `inner ℝ` synthesis)
- The framework's `NormedAddCommGroup (TangentSpace I y)` is the **direct** path
  via `[NormedAddCommGroup E]` and defeq — single canonical path, no diamond

### Operator notation trade-off

- `metricInner x V W` — explicit basepoint, paper-faithful
- `⟪V, W⟫_g[x]` — operator notation with explicit basepoint
- Trade-off: paper-faithful (`⟨V, W⟩_g`) vs Lean ergonomics (basepoint visibility)

**Recommendation**: use explicit `metricInner x V W` in framework body,
notation `⟪V, W⟫_g[x]` in statement-level docstrings/displayed math.

## 3. Refactor Scope: File-by-File Change List

### 3.1 Riemannian/ (5 files)

**Connection.lean** (~1000 LOC):
- `koszulFunctional`: rewrite using `metricInner x` instead of `inner ℝ`
- 10 koszul identities (antisymm, metric_compat_sum, smul_right, add_right,
  add_left, add_middle, smul_left, smul_middle, koszulFunctional_local,
  koszulCovDeriv_inner_eq): statements + bodies refactored
- `directionalDeriv`, `koszulCovDeriv` etc.: inner product references updated
- 5 self-tests in UXTest section: updated

**Curvature.lean** (~150 LOC):
- Ricci trace operation: refactor using `metricInner` + orthonormal basis
  (Ricci uses `Σᵢ ⟨R(eᵢ, X) Y, eᵢ⟩` style summation)
- Scalar curvature: similar trace

**SecondFundamentalForm.lean** (~100 LOC):
- `secondFundamentalFormScalar`: `⟨II(X, Y), ν⟩` → `metricInner x (II ...) ν`
- Mean curvature: trace via `metricInner`

**Gradient.lean** (~80 LOC):
- `manifoldGradient`: Riesz extraction. **CRITICAL** — see §4.

**InnerProductBridge.lean**:
- Deprecated/restructured. See §5.

### 3.2 GeometricMeasureTheory/ (5 files, ~500 LOC total)

**HasNormal.lean**:
- `‖ν x‖ = 1` — norm comes from `[NormedAddCommGroup E]` direct path (single source)
- `bvGradientDirection`: refactor inner product references

**Stable.lean**:
- Stability operator: `∫_Σ ⟨L(X), X⟩ + B(X, X)` — refactor with `metricInner`

**Variation/FirstVariation.lean**:
- `δV(X) = ∫ ⟨X, ν⟩` style: refactor

**Variation/SecondVariation.lean**:
- Riemann curvature term `R(X, ν)X`: refactor

**Isoperimetric/ReducedBoundary.lean**:
- Surface measure inner products

### 3.3 Regularity/ (2 files, ~80 LOC)

**AlphaStructural.lean**, **SmoothRegularity.lean**:
- Mostly statement-level; refactor inner product references

### 3.4 AltRegularity/ (3 files, ~50 LOC)

**MainTheorem.lean**, **MinMaxExistence.lean**, **StabilityVerification.lean**:
- Statement-level refactor; chain proofs use refactored Riemannian + GMT

### 3.5 Total estimated refactor footprint

- ~2000 LOC of statement signature changes
- ~1500 LOC of body re-spike (where `inner ℝ` → `metricInner` cascades)
- ~250 LOC of new typeclass + canonical instance + Riesz infrastructure
- **Total ~3750 LOC** of net framework change

## 4. Riesz Extraction Strategy (Critical Technical Challenge)

**Problem**: Phase 4.5.C's plumbing uses `(InnerProductSpace.toDual ℝ _).symm`.
This requires `InnerProductSpace ℝ (TangentSpace I x)` as an instance — exactly
the synthesis we're avoiding to prevent the diamond.

**Three options:**

### Option (a): Manual Riesz via finite-dim linear algebra

Build a framework-owned Riesz isomorphism using the metric tensor and an
orthonormal basis (from `[InnerProductSpace ℝ E]` on E):

```lean
namespace OpenGALib.RiemannianMetric
variable {M : Type*} [...] [g : RiemannianMetric I M]

/-- Framework-owned Riesz extraction: convert a CLM `T_xM →L[ℝ] ℝ` into a
tangent vector via the metric tensor. -/
noncomputable def riesz (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x := by
  -- Construction: pick any orthonormal basis e₁, ..., eₙ of E
  -- (using `[InnerProductSpace ℝ E]` on the model space)
  -- Riesz vector v = Σᵢ aᵢ eᵢ where aᵢ = φ(eᵢ) (in metric `g`)
  -- Adjust for non-trivial metric via Gram matrix inverse
  sorry  -- substantial linear algebra construction

theorem riesz_inner (x : M) (φ : TangentSpace I x →L[ℝ] ℝ)
    (v : TangentSpace I x) :
    metricInner x (riesz x φ) v = φ v := sorry
```

Pros: framework-owned, no Mathlib InnerProductSpace dependency on TangentSpace.
Cons: substantial new infrastructure (~200 LOC); duplicates Mathlib's Riesz.

### Option (b): Provide InnerProductSpace via single canonical path

The framework provides `InnerProductSpace ℝ (TangentSpace I x)` itself, but in
a way that the instance term is defeq to `[InnerProductSpace ℝ E]`:

```lean
instance : ∀ x : M, InnerProductSpace ℝ (TangentSpace I x) := fun _ =>
  inferInstanceAs (InnerProductSpace ℝ E)
```

Pros: minimal infrastructure; reuses Mathlib's `InnerProductSpace.toDual`.
Cons: forces `metricInner` to coincide with E's standard inner product
(no general Riemannian metric — only the trivial Euclidean metric per chart).
**This kills generality** — only works for flat (Euclidean) metric.

### Option (c): Hybrid — explicit Riesz via metric tensor

Build Riesz directly using metric tensor:

```lean
noncomputable def metricToDual (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) := sorry

noncomputable def metricRiesz (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x := (metricToDual x).symm φ
```

Construction uses metric tensor's positive-definiteness + finite-dim invertibility.

**Recommendation**: Option (c) — gives general Riemannian metrics + framework-owned.
Requires ~200 LOC for `metricToDual` proof of bijectivity.

## 5. InnerProductBridge.lean Fate

**Phase 1.6 substantive infrastructure work** (4 explicit instances bridging
`RiemannianBundle` to `InnerProductSpace ℝ (TangentSpace I x)`).

**Decision options**:

(a) **Delete** — clean break. Phase 4.7 architecture replaces.
(b) **Restructure** — keep file as deprecated shim during transition.
(c) **Move to docs/** — historical record of Phase 1.6 infrastructure.

**Recommendation**: Option (a) — delete. Phase 4.7 replaces conceptually.
Git history preserves the work. Phase 1.6's value was establishing the
framework's self-build pattern (now reused for `RiemannianMetric`).

## 6. Sequenced Sub-Phases (9-Sub-Phase Plan)

| Phase | Content | Atomic | Dependency |
|-------|---------|--------|-----------|
| **4.7.1** | Design + implement `OpenGALib.RiemannianMetric` typeclass + axioms | new file `Riemannian/Metric.lean` | none |
| **4.7.2** | Implement `metricInner` operation + properties (symm, posdef, bilinear) | extend `Metric.lean` | 4.7.1 |
| **4.7.3** | Implement `metricRiesz` (`metricToDual` bijectivity) | extend `Metric.lean` | 4.7.2 |
| **4.7.4** | Refactor `Connection.lean`: `koszulFunctional` + 10 identities | `Connection.lean` | 4.7.1-3 |
| **4.7.5** | Refactor `Curvature.lean`, `SecondFundamentalForm.lean`, `Gradient.lean` | 3 Riemannian files | 4.7.4 |
| **4.7.6** | Refactor GMT (5 files): variation formulas, HasNormal, Stable, ReducedBoundary | 5 GMT files | 4.7.4-5 |
| **4.7.7** | Refactor Regularity + AltRegularity (5 files): downstream chain | 5 downstream files | 4.7.6 |
| **4.7.8** | Close `koszulLinearFunctional_exists` + `leviCivitaConnection_exists` | `Connection.lean` | 4.7.1-7 |
| **4.7.9** | Cleanup: delete `InnerProductBridge.lean`; remove obsolete imports | `InnerProductBridge.lean` | 4.7.8 |

Each sub-phase: atomic commit, build verify, sorry delta documented.

## 7. Per-Sub-Phase Risk Assessment

### 4.7.1 — Typeclass design
**Risk**: typeclass interface choices propagate. Bilinear form vs metric tensor
representation; smoothness encoding; symmetry/posdef as fields vs theorems.
**Mitigation**: minimal viable interface; iterate based on 4.7.4 friction.

### 4.7.2 — `metricInner` operation
**Risk**: coercion subtlety between `TangentSpace I x = E` defeq.
**Mitigation**: explicit `(V : E)` casts where needed.

### 4.7.3 — `metricRiesz` (CRITICAL)
**Risk**: framework-owned Riesz proof requires showing `metricToDual` is
isomorphism. Uses positive-definiteness + finite-dim linear algebra. ~200 LOC.
**Mitigation**: leverage Mathlib `LinearMap.toContinuousLinearMap.isUnit_iff_ker_bot`
+ posdef → injective.

### 4.7.4 — Connection.lean refactor (LARGEST)
**Risk**: 10 koszul identity bodies use `inner_smul_right`, `inner_add_left`,
`real_inner_comm`, `inner_neg_left`, etc. Each Mathlib lemma needs framework
analog using `metricInner` (since `inner ℝ` no longer in scope on TangentSpace).
**Mitigation**: ~10 new `metricInner_*` lemmas wrapping E-side `inner` lemmas
via the bilinear form.

### 4.7.5 — Riemannian downstream
**Risk**: `manifoldGradient` Riesz refactor must thread through `metricRiesz`.
**Mitigation**: established by 4.7.3.

### 4.7.6 — GMT refactor
**Risk**: GMT inner product use is widespread (118+ refs in Riemannian alone,
GMT similar order). Surface area large.
**Mitigation**: per-file pointwise; chain proofs (`MainTheorem` etc.) flag
breakages immediately.

### 4.7.7 — Regularity / AltRegularity propagation
**Risk**: chain proof breakage in paper-essential theorems.
**Mitigation**: chain proofs (`main_theorem_*`, `*_of_nonExcessive`) build
verify after each commit; 0-sorry preservation.

### 4.7.8 — Close 2 axioms
**Risk**: even with redesign, the wrap could surface other elaboration friction.
**Mitigation**: 4.7.1-7 establish all needed infrastructure; this sub-phase
should be mechanical wrap.

### 4.7.9 — Cleanup
**Risk**: minimal — file deletion + import cleanup.
**Mitigation**: full build after.

## 8. Mathlib API Loss + Rebuild List

Framework's custom `metricInner` doesn't go through `Inner ℝ (TangentSpace I y)`.
This loses the following Mathlib APIs (need framework-owned analogs):

### Inner product algebra (~10 lemmas)
- `inner_add_left/right` → `metricInner_add_left/right`
- `inner_smul_left/right` (real) → `metricInner_smul_left/right`
- `real_inner_comm` → `metricInner_comm` (from `RiemannianMetric.symm`)
- `inner_neg_left` → `metricInner_neg_left`
- `inner_sub_left/right` → `metricInner_sub_left/right`
- `inner_zero_left/right` → `metricInner_zero_left/right`

Each is a 1-line proof from the bilinear form structure. ~30 LOC total.

### Smoothness API (~5 lemmas)
- `MDifferentiableAt.inner_bundle` (the diamond source!) → `MDifferentiableAt.metricInner`
  using `metricTensor`'s smoothness + composition. ~30 LOC.

### Norm
- `‖V‖² = ⟨V, V⟩` from `[InnerProductSpace ℝ E]` direct path — single source.
- Bundle-induced norm not needed (uses E direct path).

### Riesz
- `InnerProductSpace.toDual.symm` → `metricRiesz` (4.7.3, ~200 LOC).

### Orthonormal basis
- `OrthonormalBasis E` from `[InnerProductSpace ℝ E]` (E side, not TangentSpace).
- `stdOrthonormalBasis` available.
- Pull back to `TangentSpace I x` via defeq.

### Mathlib losses
- `MDifferentiableAt.inner_bundle` — replaced by framework analog.
- All inner-product-on-TangentSpace API — replaced by `metricInner_*`.

**Total rebuild**: ~250 LOC of framework-owned analogs.

## 9. Effort Estimate (Planning, not LOC retreat)

Sub-phase boundaries by component, not LOC:

- 4.7.1-3 (typeclass + Riesz): foundation, ~400-500 LOC, 3 atomic commits
- 4.7.4 (Connection refactor): largest single commit, ~600-800 LOC
- 4.7.5 (Riemannian downstream): 3 files, ~250-350 LOC, 1-3 commits
- 4.7.6 (GMT): 5 files, ~500-700 LOC, 1-3 commits
- 4.7.7 (downstream): 5 files, ~150-250 LOC, 1-2 commits
- 4.7.8 (close axioms): mechanical, ~100 LOC
- 4.7.9 (cleanup): ~30 LOC

**Total: 9 atomic commits, ~2000-2700 LOC of NET framework change.**

## 10. Pre-Execution Checklist (Moqian Review Points)

Before launching Phase 4.7 execution, decide:

1. **Typeclass interface** (§2): bilinear form vs alternative encoding?
2. **Riesz strategy** (§4): Option (c) `metricRiesz` accepted?
3. **InnerProductBridge fate** (§5): delete vs restructure vs preserve in docs/?
4. **Notation choice** (§2): `metricInner x V W` vs `⟪V, W⟫_g[x]`?
5. **Sub-phase split** (§6): 9 sub-phases acceptable, or further split?
6. **Risk acceptance** (§7): 4.7.4 + 4.7.6 are largest surface; comfortable?
7. **Phase 1.6 sunset** (§5): explicit Moqian acknowledgment?

Once decided, Phase 4.7 execute begins per §6 sequence.

## 11. Honest Trade-Offs

**Pros of Phase 4.7 redesign:**
- Framework owns inner product infrastructure (no lean4#13063 dependency)
- 2 PRE-PAPER axioms close (sorry → 0)
- Future Riemannian work avoids the diamond
- Aligns with framework's "self-build first-class" stance

**Cons:**
- Substantial framework-wide refactor (~2700 LOC net)
- Phase 1.6 InnerProductBridge work sunset
- Mathlib's evolving Riemannian infrastructure (when it matures and resolves
  lean4#13063) might supersede this redesign — requires future re-evaluation
- Multi-commit sequence with build-verify per commit; if any sub-phase fails,
  framework partially refactored state

**Alternative status quo (skip Phase 4.7):**
- 2 PRE-PAPER axioms remain documented architectural blockers
- Phase 4.5 mathematical content is complete (10 koszul identities + Riesz plumbing)
- Paper ship-ready (chain proofs 0-sorry)
- Phase 5 (UX optimization) starts directly

## Recommendation

Phase 4.7 is genuinely substantial framework refactor work. It's the **right
call mathematically** if framework's long-term own-the-stack stance is paramount.
It's the **wrong call short-term** if paper ship-ability is the primary metric
(Phase 4.5's current state is paper ship-ready with documented architectural
blockers).

**Moqian decision needed.** Plan only — no execution until explicit go.
