import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Gram matrix and its square-root determinant of a Riemannian metric

For a Riemannian metric `g` on `M`, a point `x ∈ M`, and a basis `b` of
`T_xM`, this file defines

* `g.gramMatrix x b : Matrix (Fin n) (Fin n) ℝ` — the Gram matrix
  `(g_x(b_i, b_j))_{ij}`.
* `g.sqrtGramDet x b : ℝ` — `√det(g.gramMatrix x b)`, the volume
  Jacobian factor in any chart-induced basis.

These are pure LinearAlgebra wrappers around `g.metricInner`. Chart-frame
specialization (the basis `eᵢ = (φ⁻¹)_*(standard_i)` from a chart `(U, φ)`)
is the responsibility of a sibling file (pending).

Ground truth: do Carmo Ch.1 Eq.(5); Lee Ch.13 / Ch.16.
-/

open scoped ContDiff Manifold

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Gram matrix `(g_x(b_i, b_j))_{ij}` of the Riemannian metric
`g` at `x` relative to a basis `b` of `T_xM`. For the chart-induced basis
`eᵢ = (φ⁻¹)_*(standard_i)`, this is the matrix `g_ij(x)` of the textbook
chart-pullback formula

  `vol_g|_U(A) = ∫_{φ(A)} √det(g_ij ∘ φ⁻¹)(y) dy`.

Ground truth: do Carmo Ch.1 Eq.(5). -/
noncomputable def gramMatrix {ι : Type*} [Fintype ι] (g : RiemannianMetric I M)
    (x : M) (b : Module.Basis ι ℝ (TangentSpace I x)) : Matrix ι ι ℝ :=
  Matrix.of fun i j => g.metricInner x (b i) (b j)

/-- **Math.** Square-root determinant `√det(g_x(b_i, b_j))` of the Gram
matrix. This is the **volume Jacobian factor**: in a chart `(U, φ)` with
the chart-induced basis, `√det(g_ij)` is exactly the weight in

  `vol_g|_U(A) = ∫_{φ(A)} √det(g_ij ∘ φ⁻¹)(y) dy`.

For any basis `b` of `T_xM`, this is positive (since `g_x` is
positive-definite, its Gram matrix in any basis is positive-definite,
hence has positive determinant).

Ground truth: do Carmo Ch.1 Eq.(5); Lee Ch.16. -/
noncomputable def sqrtGramDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (x : M)
    (b : Module.Basis ι ℝ (TangentSpace I x)) : ℝ :=
  Real.sqrt (g.gramMatrix x b).det

/-- **Math.** The Gram matrix `(g_x(b_i, b_j))` is symmetric:
`g_x(b_j, b_i) = g_x(b_i, b_j)`. -/
theorem gramMatrix_symm {ι : Type*} [Fintype ι]
    (g : RiemannianMetric I M) (x : M) (b : Module.Basis ι ℝ (TangentSpace I x)) :
    (g.gramMatrix x b).IsSymm := by
  ext i j
  exact g.symm x (b j) (b i)

/-- **Math.** The Gram matrix of a Riemannian metric is positive definite
(symmetric + the quadratic form `y ↦ yᵀ G y` is strictly positive on
nonzero `y`).

Reduction: `yᵀ G y = g_x(Σ y_i b_i, Σ y_i b_i) = g_x(v, v)` where
`v = b.repr.symm y`. Since `b` is a basis, `y ≠ 0` iff `v ≠ 0`, and
positive-definiteness of `g_x` gives `g_x(v, v) > 0`.

PRE-PAPER (Phase 1b). **Repair plan**: the proof unrolls
`y.sum`-over-Finsupp into the bilinear-form expansion via
`Finsupp.linearCombination` + bilinearity of `g.inner x` (specifically,
`ContinuousLinearMap.map_finsupp_sum` applied twice). Standard
LinearAlgebra; estimated 30-50 LOC. -/
theorem gramMatrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (x : M) (b : Module.Basis ι ℝ (TangentSpace I x)) :
    (g.gramMatrix x b).PosDef := by
  sorry

/-- **Math.** `det(g_x(b_i, b_j)) > 0` — strict positivity of the Gram
determinant follows from positive-definiteness via Mathlib's
`Matrix.PosDef.det_pos`. -/
theorem gramMatrix_det_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (x : M) (b : Module.Basis ι ℝ (TangentSpace I x)) :
    0 < (g.gramMatrix x b).det :=
  (g.gramMatrix_posDef x b).det_pos

/-- **Math.** `√det(g_x(b_i, b_j)) ≥ 0` — trivial from `Real.sqrt_nonneg`. -/
theorem sqrtGramDet_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (x : M) (b : Module.Basis ι ℝ (TangentSpace I x)) :
    0 ≤ g.sqrtGramDet x b :=
  Real.sqrt_nonneg _

/-- **Math.** `√det(g_x(b_i, b_j)) > 0` — strict positivity, from
positive-definiteness of the Gram matrix via
`Matrix.PosDef.det_pos` + `Real.sqrt_pos`. This is the **volume Jacobian
positivity** lemma underlying the chart-pullback formula. -/
theorem sqrtGramDet_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (x : M) (b : Module.Basis ι ℝ (TangentSpace I x)) :
    0 < g.sqrtGramDet x b :=
  Real.sqrt_pos.mpr (g.gramMatrix_det_pos x b)

end Riemannian.RiemannianMetric
