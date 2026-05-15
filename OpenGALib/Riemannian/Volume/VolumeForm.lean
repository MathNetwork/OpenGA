import Mathlib.LinearAlgebra.Alternating.Basic
import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Volume form bridge: `vol_g(A) = ∫_A dV_g`

Phase 2 of the `riemannian-volume` Layer 3a sub-project: pointwise volume
form `dV_g(x) : Λⁿ(T_xM)*` and the bridge theorem identifying integration
of the form with the volume measure from `ChartPullback.lean`.

In any chart `(U, φ)`, the volume form satisfies

  `dV_g(x)(e_1, …, e_n) = √det(g_ij(x))`

where `(e_i)` is the chart-induced frame on `T_xM`. Equivalently, `dV_g(x)`
is the unique positive top form with value `1` on any `g_x`-orthonormal
basis (oriented case) or the corresponding density (non-oriented case).

Ground truth: Lee *Smooth Manifolds* Ch.16 (Riemannian densities + volume
form); do Carmo Ch.1 (form view of the volume element); Petersen Ch.7 §1.
-/

open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **Math.** Pointwise Riemannian volume form `dV_g(x)` at `x ∈ M`:
the top alternating form on `T_xM` characterized by

  `dV_g(x)(e_1, …, e_n) = +1` on any oriented `g_x`-orthonormal basis,

or equivalently `dV_g(x)(v_1, …, v_n) = √det(g_x(v_i, v_j))` on a general
basis `(v_i)`.

Ground truth: Lee Ch.16; do Carmo Ch.1 Eq.(6).

PRE-PAPER (Phase 2). **Repair plan**: construct via Gram matrix
determinant: pick any basis of `T_xM`, take `√det(g_ij(x))` as the form's
value on that basis, then extend by `n`-linear-alternating universal
property. Chart-invariance follows from the same `g' = Jᵀ·g·J` argument
as in `ChartPullback.lean`. Estimated 80-120 LOC. -/
noncomputable def volumeFormAt (g : RiemannianMetric I M) (x : M) :
    AlternatingMap ℝ (TangentSpace I x) ℝ (Fin (Module.finrank ℝ E)) :=
  sorry

@[inherit_doc] scoped[Riemannian]
  notation:max "dV_g[" g ", " x "]" => Riemannian.volumeFormAt g x

/-! ### Bridge theorem (pending Phase 2 follow-up)

`volumeMeasure_eq_integral_volumeForm` will state `vol_g(A) = ∫_A |dV_g|`
(absolute value handles the non-oriented case; oriented manifold gets
`vol_g(A) = ∫_A dV_g` directly).

Ground truth: Lee Ch.16 Thm 16.32; do Carmo Ch.1 Prop 1.7.

Not declared yet: requires form-integration API on the alternating-form
bundle (Mathlib `AlternatingMap` is pointwise; integration of a section
of the top alternating bundle is the missing piece). Estimated 100-150
LOC follow-up commit on this branch.

In any chart `(U, φ)` both sides unfold to
`∫_{φ(A ∩ U)} √det(g_ij ∘ φ⁻¹)(y) dy`; glue across charts by partition
of unity. -/

end Riemannian
