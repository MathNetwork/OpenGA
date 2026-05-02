import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Riemannian.Metric.Riesz
import Riemannian.Metric.Smooth
import Riemannian.TangentBundle.SmoothSection
import Riemannian.TangentBundle.Smoothness

/-!
# Metric Riesz inversion: smoothness bridge

Identifies the framework's `metricRiesz x φ` (defined via the `LinearEquiv`
`metricToDualEquiv x` constructed from positive-definiteness) with
Mathlib's `ContinuousLinearMap.inverse (g.metricTensor x) φ` (defined via
`Classical.choose` over the `IsInvertible` witness).

This identification is the foundation for **smoothness of the Riesz
inversion**: Mathlib provides smoothness of `ContinuousLinearMap.inverse`
at invertible CLMs (`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`),
and the framework supplies smoothness of `g.metricTensor` (via the
`smoothMetric` field). Composing the two routes through the
`metricRiesz = inverse` identity proven here.

## Main results

* `metricToDual_isInvertible` — `(g.metricTensor x).IsInvertible`, derived
  from `metricToDual_bijective` via finite-dim `LinearEquiv.toContinuousLinearEquiv`.
* `metricRiesz_eq_inverse` — `metricRiesz x φ = ContinuousLinearMap.inverse (g.metricTensor x) φ`.
  Both sides are inverses of `g.metricTensor x` applied to `φ`; the
  identity is by uniqueness of the inverse.

## Closure status

Real proof, no `sorry`. Sets up the foundation for downstream
`metricRiesz_section_smoothAt` (smoothness of the Riesz section), which
will compose `g.smoothMetric` with `IsInvertible.contDiffAt_map_inverse`.

**Ground truth**: Lee, *Smooth Manifolds*, Prop. 13.3 (Riesz on
finite-dim inner product spaces). -/

open scoped ContDiff Manifold Topology

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [g : RiemannianMetric I M]

/-- The metric tensor at $x$ is `IsInvertible` as a continuous linear map
$T_xM \to_{L} (T_xM \to_L \mathbb{R})$.

Built from `metricToDualEquiv x` (a `LinearEquiv` derived from
positive-definiteness in `Riemannian/Metric/Riesz.lean`), promoted to a
`ContinuousLinearEquiv` via finite-dim `LinearEquiv.toContinuousLinearEquiv`,
which gives the required `IsInvertible` witness directly.

Real proof, no `sorry`. -/
theorem metricToDual_isInvertible (x : M) :
    (g.metricTensor x : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)).IsInvertible := by
  -- Promote `metricToDualEquiv x` (a LinearEquiv) to a ContinuousLinearEquiv.
  set CLE : (TangentSpace I x) ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    (metricToDualEquiv (g := g) x).toContinuousLinearEquiv with hCLE_def
  refine ⟨CLE, ?_⟩
  -- Show CLE coerces to g.metricTensor x as a CLM.
  ext v w
  show CLE v w = g.metricTensor x v w
  show (metricToDualEquiv (g := g) x : (TangentSpace I x) → (TangentSpace I x →L[ℝ] ℝ)) v w
    = g.metricTensor x v w
  rfl

/-- **Riesz inversion identified with `ContinuousLinearMap.inverse`**.

For every $x \in M$ and every cotangent functional $\varphi$, the
framework's `metricRiesz x φ` agrees with Mathlib's
`ContinuousLinearMap.inverse (g.metricTensor x) φ`.

Both sides are characterized by the property
$g_x(\text{result}) = \varphi$ (i.e., $g_x$ applied to the result gives
$\varphi$). By uniqueness of the inverse map, the two sides agree.

Real proof, no `sorry`. -/
theorem metricRiesz_eq_inverse (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    metricRiesz (g := g) x φ
      = ContinuousLinearMap.inverse
          (g.metricTensor x : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) φ := by
  -- Use the IsInvertible witness from `metricToDual_isInvertible`. Both sides are
  -- inverses of `g.metricTensor x` applied to `φ`. Uniqueness via injectivity.
  apply (metricToDual_injective (g := g) x)
  -- Goal: metricToDual x (metricRiesz x φ) = metricToDual x ((g.metricTensor x).inverse φ)
  -- LHS evaluation: metricToDual x (metricRiesz x φ) v = metricInner x (metricRiesz x φ) v = φ v.
  have h_lhs : metricToDual (g := g) x (metricRiesz (g := g) x φ) = φ := by
    ext v
    rw [metricToDual_apply, metricRiesz_inner]
  rw [h_lhs]
  -- RHS: φ = metricToDual x ((g.metricTensor x).inverse φ). Symm of CLE.apply_symm_apply.
  obtain ⟨CLE, hCLE⟩ := metricToDual_isInvertible (g := g) x
  -- `metricToDual x = g.metricTensor x` (def-eq) = `CLE` (as CLM, via hCLE).
  symm
  show metricToDual (g := g) x ((g.metricTensor x).inverse φ) = φ
  rw [show metricToDual (g := g) x = (g.metricTensor x : TangentSpace I x →L[ℝ] _) from rfl,
      ← hCLE]
  rw [ContinuousLinearMap.inverse_equiv CLE]
  exact (CLE.apply_symm_apply φ)

/-! ## Smoothness of Riesz section

Compose `g.smoothMetric` with `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`
to obtain smoothness of the inverse-metric section, then apply at a smooth
cotangent functional, and translate to `TangentSmoothAt` via chart pullback.

The cotangent smoothness predicate is taken in **flat-codomain form** —
`MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ) (fun y => (φ y : E →L[ℝ] ℝ)) x` —
exploiting the `TangentSpace I y = E` def-eq. This avoids the dependent-codomain
`Π y, T_yM →L[ℝ] ℝ` form which is awkward to phrase smoothness for. -/

section RieszSectionSmooth

variable [CompleteSpace E]
  [IsManifold I ∞ M] [IsLocallyConstantChartedSpace H M]

omit [IsManifold I ∞ M] [IsLocallyConstantChartedSpace H M] in
set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of the metric inverse as a CLM section**: `y ↦ inverse (g.metricTensor y)`
is `MDifferentiableAt` at every `x`, viewed as `M → ((E →L[ℝ] ℝ) →L[ℝ] E)`.

Composition of `g.smoothMetric` (smooth metric tensor) with Mathlib's
`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse` (inverse smooth at
invertible CLMs). -/
theorem metricInverse_mdifferentiableAt (x : M) :
    MDifferentiableAt I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)
      (fun y : M => ContinuousLinearMap.inverse
        (g.metricTensor y : E →L[ℝ] E →L[ℝ] ℝ)) x := by
  -- (a) g.metricTensor smooth as M → (E →L E →L ℝ).
  have h_metric : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) g.metricTensor x :=
    (g.smoothMetric x).mdifferentiableAt (by decide)
  -- (b) ContinuousLinearMap.inverse is C^∞ at the invertible point g.metricTensor x.
  have h_inv_at : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (g.metricTensor x) :=
    (metricToDual_isInvertible (g := g) x).contDiffAt_map_inverse
  -- (c) Compose: ContDiffAt → ContMDiffAt → MDifferentiableAt; then `.comp`.
  have h_inv_at' : MDifferentiableAt 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)
      ContinuousLinearMap.inverse (g.metricTensor x) :=
    h_inv_at.contMDiffAt.mdifferentiableAt (by decide)
  exact h_inv_at'.comp x h_metric

set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of the Riesz section**: given a smooth cotangent functional
section `φ : M → (E →L[ℝ] ℝ)` (in flat-codomain form, exploiting
`TangentSpace I y = E` def-eq via `set_option backward.isDefEq.respectTransparency false`
at the call site), the Riesz-extracted tangent section
`y ↦ metricRiesz y (φ y) ∈ T_yM` is `TangentSmoothAt` at every `x`.

Architecture:
1. By `metricRiesz_eq_inverse`: `metricRiesz y (φ y) = inverse (g.metricTensor y) (φ y)`
   (an element of `T_yM ≡ E`).
2. By `metricInverse_mdifferentiableAt`: `y ↦ inverse (g.metricTensor y)` smooth as
   `M → ((E →L[ℝ] ℝ) →L[ℝ] E)`.
3. `clm_apply` with smooth `φ`: smooth `M → E`.
4. Translate to `TangentSmoothAt` via `iff_coord` + chart pullback through
   `continuousLinearMapAtFlat` (smooth on chart base set). -/
theorem metricRiesz_section_smoothAt
    {φ : M → (E →L[ℝ] ℝ)} {x : M}
    (hφ : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ) φ x) :
    TangentSmoothAt (fun y : M => metricRiesz (g := g) y (φ y)) x := by
  -- Step 1: smoothness of `y ↦ metricRiesz y (φ y) : M → E` (using metricRiesz_eq_inverse).
  have h_inverse_at := metricInverse_mdifferentiableAt (g := g) x
  have h_apply_E : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y : M => ContinuousLinearMap.inverse (g.metricTensor y) (φ y)) x :=
    h_inverse_at.clm_apply hφ
  have h_eq : (fun y : M => ContinuousLinearMap.inverse (g.metricTensor y) (φ y))
      = (fun y : M => (metricRiesz (g := g) y (φ y) : E)) := by
    funext y
    exact (metricRiesz_eq_inverse y (φ y)).symm
  rw [h_eq] at h_apply_E
  -- Step 2: translate `M → E` smoothness to `TangentSmoothAt` via chart pullback.
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x with he_def
  -- `(e ⟨y, V y⟩).2` equals `e.continuousLinearMapAt R y (V y)` on `e.baseSet`,
  -- which equals `continuousLinearMapAtFlat x y (V y)` (def-eq).
  -- continuousLinearMapAtFlat smooth in y; clm_apply with smooth V y gives smooth.
  have h_clma_smooth : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y) x :=
    (TangentBundle.continuousLinearMapAtFlat_contMDiffAt
      (I := I) (M := M) x).mdifferentiableAt (by decide)
  have h_clma_apply : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y : M => TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y
        (metricRiesz (g := g) y (φ y))) x :=
    h_clma_smooth.clm_apply h_apply_E
  apply h_clma_apply.congr_of_eventuallyEq
  have h_baseSet : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  filter_upwards [h_baseSet] with y hy
  show (e ⟨y, metricRiesz (g := g) y (φ y)⟩).2
    = TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y
        (metricRiesz (g := g) y (φ y))
  show (e ⟨y, metricRiesz (g := g) y (φ y)⟩).2
    = e.continuousLinearMapAt ℝ y (metricRiesz (g := g) y (φ y))
  exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy _).symm

end RieszSectionSmooth

end OpenGALib
