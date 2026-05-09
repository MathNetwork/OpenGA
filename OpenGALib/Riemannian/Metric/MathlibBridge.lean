import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import OpenGALib.Riemannian.Metric.Basic

/-!
# Mathlib bridge: `OpenGALib.RiemannianMetric` → `Bundle.RiemannianBundle`

This file provides the bridge from our framework's `OpenGALib.RiemannianMetric I M`
typeclass to Mathlib's `Bundle.RiemannianBundle (fun x ↦ TangentSpace I x)` typeclass.

## Architecture

OpenGALib retains its own `RiemannianMetric I M` as the **public-facing**
domain typeclass (Riemannian-geometry-specific naming, narrow scope).
This bridge converts the framework's data into Mathlib's
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` value.

The bridge is provided for **interoperability / future Mathlib catch-up**.
The framework does NOT route its public IPS API through Mathlib's bundle
path — see "Phase 1C architectural lesson" below for the NACG diamond
that prevents this. The framework's own
`OpenGALib.metricInner` (in `Metric/Basic.lean`) is the canonical
geometric inner product API on tangent vectors, NOT `inner ℝ`.

## Phase 1B/1C status

Two PRE-PAPER closures remain in
`OpenGALib.RiemannianMetric.toBundleContMDiffRiemannianMetric`:
* `isVonNBounded` — von Neumann boundedness of `{v | g x v v < 1}`
  via positive-definiteness + finite-dim equivalence of inner products.
* `contMDiff` — bundle-form CLM smoothness from our `g.smoothMetric`.

These are mechanical (provable from existing Mathlib + framework data).
The bridge instance `instBundleRiemannianBundle` typechecks even with
the sorrys (they're inside the field bodies, not at the instance head).

**Ground truth**: Sébastien Gouëzel's pattern in
`Mathlib/Geometry/Manifold/Riemannian/Basic.lean`
(`riemannianMetricVectorSpace`). -/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Coercivity**: a continuous, positive-definite bilinear form on a
finite-dimensional normed space is coercive: there is `c > 0` such that
`c * ‖v‖² ≤ B v v` for all `v`. Phase 1C self-build framework lemma
(used to discharge `isVonNBounded` in the Mathlib bridge below). -/
private lemma _root_.OpenGALib.posDefBilin_isCoercive
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ c > 0, ∀ v : E, c * ‖v‖^2 ≤ B v v := by
  have hcomp : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere _ _
  by_cases hE : Subsingleton E
  · refine ⟨1, by norm_num, fun v => ?_⟩
    have : v = 0 := Subsingleton.elim v 0
    simp [this]
  · rw [not_subsingleton_iff_nontrivial] at hE
    have hne : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hcont : ContinuousOn (fun v : E => B v v) (Metric.sphere 0 1) :=
      ((B.isBoundedBilinearMap.continuous).comp
        (Continuous.prodMk continuous_id continuous_id)).continuousOn
    obtain ⟨v0, hv0, hmin⟩ := hcomp.exists_isMinOn hne hcont
    have hv0_norm : ‖v0‖ = 1 := by simpa [Metric.mem_sphere] using hv0
    have hv0_ne : v0 ≠ 0 := by intro h; rw [h, norm_zero] at hv0_norm; norm_num at hv0_norm
    refine ⟨B v0 v0, hpos v0 hv0_ne, fun v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · set u := ‖v‖⁻¹ • v
      have hvn_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hu_norm : ‖u‖ = 1 := by
        simp [u, norm_smul, inv_mul_cancel₀ (ne_of_gt hvn_pos)]
      have hu_sphere : u ∈ Metric.sphere (0 : E) 1 := by simp [hu_norm]
      have hmin_u : B v0 v0 ≤ B u u := hmin hu_sphere
      have hg_u : B u u = ‖v‖⁻¹^2 * B v v := by
        show B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = _
        rw [(B.map_smul _ _ : B (‖v‖⁻¹ • v) = ‖v‖⁻¹ • B v)]
        rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.map_smul, smul_eq_mul,
            smul_eq_mul]
        ring
      rw [hg_u] at hmin_u
      have hsq_pos : 0 < ‖v‖^2 := by positivity
      have hmul := mul_le_mul_of_nonneg_right hmin_u hsq_pos.le
      have hcancel : ‖v‖⁻¹^2 * B v v * ‖v‖^2 = B v v := by field_simp
      linarith

/-- **Pos-def CLM bilinear form on fin-dim has bounded level set**.
Phase 1C self-build framework lemma. -/
private lemma _root_.OpenGALib.posDefBilin_isVonNBounded
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E | B v v < 1} := by
  obtain ⟨c, hc_pos, hbound⟩ := OpenGALib.posDefBilin_isCoercive B hpos
  have hsub : {v : E | B v v < 1} ⊆ Metric.ball (0 : E) (Real.sqrt (1/c) + 1) := by
    intro v hv
    simp only [Set.mem_setOf_eq] at hv
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : c * ‖v‖^2 ≤ B v v := hbound v
    have h2 : c * ‖v‖^2 < 1 := lt_of_le_of_lt h1 hv
    have h3 : ‖v‖^2 < 1/c := by rw [lt_div_iff₀ hc_pos]; linarith
    have h4 : ‖v‖ < Real.sqrt (1/c) := by
      rw [show ‖v‖ = Real.sqrt (‖v‖^2) by rw [Real.sqrt_sq (norm_nonneg _)]]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) h3
    linarith
  exact NormedSpace.isVonNBounded_of_isBounded _ (Metric.isBounded_ball.subset hsub)

set_option backward.isDefEq.respectTransparency false in
/-- Convert `OpenGALib.RiemannianMetric I M` to Mathlib
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`. -/
noncomputable def RiemannianMetric.toBundleContMDiffRiemannianMetric
    (g : RiemannianMetric I M) :
    Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) where
  inner x := g.metricTensor x
  symm x v w := g.symm x v w
  pos x v hv := g.posdef x v hv
  isVonNBounded x :=
    OpenGALib.posDefBilin_isVonNBounded (g.metricTensor x) (g.posdef x)
  contMDiff := by
    -- Bundle-form CLM-section smoothness from `g.smoothMetric` (function-form
    -- smoothness on `M → (E →L[ℝ] E →L[ℝ] ℝ)`). Phase 1C closure attempt
    -- produced the goal:
    --   `(T_dual x).linearMapAt y ((g.metricTensor y) ((T_tan x).symm y v)) w
    --      = (g.metricTensor y v) w`
    -- where `T_tan x = trivializationAt E (TangentSpace I) x` and
    -- `T_dual x = trivializationAt (E →L[ℝ] ℝ) (fun x ↦ TangentSpace I x →L[ℝ] ℝ) x`.
    -- The two trivializations are dual to each other, so the composition acts as
    -- identity on the metric tensor in `T_x`'s base set. Discharging this requires
    -- chart-pullback machinery (`Trivialization.symmL` + dual-trivialization
    -- cancellation lemma). Self-build follow-up; not needed for current Phase 1C
    -- since the framework does not route its public IPS API through this bridge
    -- (see "Phase 1C architectural lesson — the irreducible NACG diamond" below).
    sorry

set_option backward.isDefEq.respectTransparency false in
/-- Bridge instance: `OpenGALib.RiemannianMetric` provides `Bundle.RiemannianBundle`. -/
noncomputable instance instBundleRiemannianBundle [g : RiemannianMetric I M] :
    Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
  ⟨(g.toBundleContMDiffRiemannianMetric).toRiemannianMetric⟩

/-! ## Phase 1B/1C Architectural Conclusion

**Phase 1B finding** (4 attempts on the same `rfl` failure):
Mathlib's `Bundle.RiemannianBundle`-derived IPS scoped instance
(priority 80) cannot fire while a background `[InnerProductSpace ℝ E]`
hypothesis is in scope — Lean finds the background instance via
`TangentSpace I x = E` def-eq (priority 1000), beating the scoped one.

**Phase 1C migration** (this commit):
* `[InnerProductSpace ℝ E]` → `[NormedSpace ℝ E]` migrated in 18 files
  where the model-space IPS was gratuitous boilerplate (Connection,
  Curvature, Gradient, TangentBundle, Riesz, Metric, FirstVariation,
  Stationary). The `RiemannianMetric` typeclass declaration now requires
  only `[NormedSpace ℝ E]`.
* Framework bridges added on `TangentSpace I x` (`Metric/Basic.lean`
  `NACGBridge` section): `NormedSpace ℝ`, `IsTopologicalAddGroup`,
  `ContinuousConstSMul ℝ`.
* `[InnerProductSpace ℝ E]` retained where structurally necessary:
  `Instances/EuclideanSpace.lean` (uses `innerSL ℝ`),
  `SecondFundamentalForm.lean` + `Variation/SecondVariation.lean` +
  `Stable.lean` + `AlphaStructural.lean` + `SmoothRegularity.lean`
  (use `stdOrthonormalBasis`),
  `Isoperimetric/ReducedBoundary.TangentHyperplane`
  (uses `Submodule.orthogonal`),
  `Metric/Basic.lean InnerProductBridge`
  (provides background-derived IPS bridge).

**Phase 1C architectural lesson — the irreducible NACG diamond**:
Phase 1C audit confirmed that even with `[InnerProductSpace ℝ E]`
removed, Mathlib's bundle IPS scoped instance does NOT fire under our
framework typeclass cascade. Reason: Mathlib's IPS instance produces
its own `Bundle.instNormedAddCommGroupOfRiemannianBundle...` NACG
on each fiber (= metric-norm), which is **incompatible** with our
`OpenGALib.instNormedAddCommGroupTangent` (= chart-background norm).
Two NACGs on the same type cannot coexist (typeclass diamond by design).

The framework chooses chart-background NACG/norm globally (via the
`TangentSpace I x = E` def-eq path). Mathlib's bundle IPS path is
**not** taken; instead, `Metric/Basic.lean InnerProductBridge`
provides background-derived IPS for downstream files needing
`stdOrthonormalBasis`. The geometric inner product is exposed via
`OpenGALib.metricInner` (in `Metric/Basic.lean`), which is the
framework's official API for Riemannian inner products on tangent
vectors — NOT `inner ℝ v w`.

**Mathematical implication**: `stdOrthonormalBasis ℝ (TangentSpace I x)`
returns a basis orthonormal w.r.t. the chart-background inner product.
For `secondFundamentalFormSqNorm` / `meanCurvature` to be the
geometrically correct Frobenius / trace norm, the basis must be
g-orthonormal. This is a **mathematical limitation** of the current
Phase 1C state, **not** a typecheck failure. Future work
(Phase 4 self-build, or Mathlib upstream catch-up) may construct a
g-orthonormal basis primitive (e.g., via Gram-Schmidt over
`metricInner`) to replace `stdOrthonormalBasis`. The basis is
mathematically correct when `g = innerSL ℝ` (the canonical case in
`EuclideanSpace.lean`).

The `IsContMDiffRiemannianBundle` instance is intentionally not
provided (Mathlib's IPS path is not used). The bridge
`instBundleRiemannianBundle` + `toBundleContMDiffRiemannianMetric`
exists for symbolic/future-Mathlib-catch-up purposes; it carries the
2 sorrys above (`isVonNBounded`, `contMDiff`) as documented PRE-PAPER
mechanical closures. -/

end OpenGALib
