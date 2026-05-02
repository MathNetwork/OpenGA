import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Riemannian.Metric.Riesz

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

end OpenGALib
