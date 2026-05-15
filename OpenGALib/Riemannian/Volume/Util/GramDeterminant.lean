import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Basis
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

open scoped ContDiff Manifold Matrix

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

/-! ## Bilinear sum-distribution helpers

`g.metricInner` is a continuous bilinear form on `TangentSpace I x`.
The two `Finset.induction`-based helpers below give the sum-distribution
identities used by both `gramMatrix_posDef` (quadratic form expansion)
and `gramMatrix_basis_change` (change-of-basis matrix-conjugation). -/

/-- **Eng.** Sum-distribution of `g.metricInner` in the *left* argument
over a `Finset.sum` of scalar-weighted vectors. -/
private lemma metricInner_sum_smul_left {ι : Type*}
    (g : RiemannianMetric I M) (x : M)
    (s : Finset ι) (c : ι → ℝ)
    (v : ι → TangentSpace I x) (w : TangentSpace I x) :
    g.metricInner x (∑ k ∈ s, c k • v k) w
      = ∑ k ∈ s, c k * g.metricInner x (v k) w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro k s hk ih
    rw [Finset.sum_insert hk, g.metricInner_add_left,
        g.metricInner_smul_left, ih, Finset.sum_insert hk]

/-- **Eng.** Sum-distribution of `g.metricInner` in the *right* argument
over a `Finset.sum` of scalar-weighted vectors. -/
private lemma metricInner_sum_smul_right {ι : Type*}
    (g : RiemannianMetric I M) (x : M)
    (s : Finset ι) (c : ι → ℝ)
    (v : TangentSpace I x) (w : ι → TangentSpace I x) :
    g.metricInner x v (∑ k ∈ s, c k • w k)
      = ∑ k ∈ s, c k * g.metricInner x v (w k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro k s hk ih
    rw [Finset.sum_insert hk, g.metricInner_add_right,
        g.metricInner_smul_right, ih, Finset.sum_insert hk]

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
`v = b.equivFun.symm y`. Since `b` is a basis, `y ≠ 0` iff `v ≠ 0`, and
positive-definiteness of `g_x` gives `g_x(v, v) > 0`. Hermitian-ness of
`G` reduces to `gramMatrix_symm` since `ℝ` has `TrivialStar`. -/
theorem gramMatrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (x : M) (b : Module.Basis ι ℝ (TangentSpace I x)) :
    (g.gramMatrix x b).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · -- Hermitian = Symmetric over ℝ (TrivialStar)
    show (g.gramMatrix x b).conjTranspose = g.gramMatrix x b
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact g.gramMatrix_symm x b
  · intro y hy
    -- v := ∑ i, y i • b i ≠ 0 because b is a basis and y ≠ 0
    have hv_ne : (∑ i, y i • b i : TangentSpace I x) ≠ 0 := by
      intro hv0
      apply hy
      have h1 : b.equivFun.symm y = (0 : TangentSpace I x) := by
        rw [Module.Basis.equivFun_symm_apply]; exact hv0
      exact b.equivFun.symm.injective (h1.trans (map_zero _).symm)
    -- star y ⬝ᵥ (G *ᵥ y) = g_x(v, v)
    have hquad : star y ⬝ᵥ (g.gramMatrix x b *ᵥ y)
                  = g.metricInner x (∑ i, y i • b i) (∑ j, y j • b j) := by
      simp only [dotProduct, Matrix.mulVec, gramMatrix, Matrix.of_apply,
        Pi.star_apply, star_trivial]
      rw [g.metricInner_sum_smul_left]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [g.metricInner_sum_smul_right]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hquad]
    exact g.metricInner_self_pos x _ hv_ne

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

/-! ## Basis-change transformation (Phase 1c)

For two bases `b, b'` of `T_xM`, the Gram matrices transform by

  `G(b') = Pᵀ · G(b) · P`,    `√det G(b') = |det P| · √det G(b)`,

where `P = b.toMatrix b'` is the change-of-basis matrix
(`P i j = b.repr (b' j) i`). This is the abstract precursor to the
chart-invariance of the volume measure: when two charts `(U, φ), (V, ψ)`
overlap, the chart-induced bases differ by `P = D(ψ ∘ φ⁻¹)`, and
`|det P|` is precisely the Lebesgue Jacobian factor in the change-of-
variables formula. -/

/-- **Math.** **Gram matrix basis-change formula**:
`G(b') = Pᵀ · G(b) · P` where `P = b.toMatrix b'` is the change-of-basis
matrix. Pure LinearAlgebra: bilinearity of `g_x` expanded over the
`Basis.sum_repr` decomposition `b' i = ∑ k, P k i • b k`.

Ground truth: do Carmo Ch.1 Eq.(5) — the textbook covariance of `g_ij`
under coordinate change. -/
theorem gramMatrix_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (x : M)
    (b b' : Module.Basis ι ℝ (TangentSpace I x)) :
    g.gramMatrix x b' =
      (b.toMatrix b').transpose * g.gramMatrix x b * b.toMatrix b' := by
  ext i j
  calc (g.gramMatrix x b') i j
      = g.metricInner x (b' i) (b' j) := rfl
    _ = g.metricInner x (∑ k, b.repr (b' i) k • b k)
          (∑ l, b.repr (b' j) l • b l) := by rw [b.sum_repr, b.sum_repr]
    _ = ∑ k, b.repr (b' i) k *
          g.metricInner x (b k) (∑ l, b.repr (b' j) l • b l) := by
        rw [g.metricInner_sum_smul_left]
    _ = ∑ k, b.repr (b' i) k *
          ∑ l, b.repr (b' j) l * g.metricInner x (b k) (b l) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [g.metricInner_sum_smul_right]
    _ = ∑ k, ∑ l,
          b.repr (b' i) k * b.repr (b' j) l * g.metricInner x (b k) (b l) := by
        simp_rw [Finset.mul_sum, mul_assoc]
    _ = ((b.toMatrix b').transpose * g.gramMatrix x b * b.toMatrix b') i j := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, gramMatrix,
          Matrix.of_apply, Module.Basis.toMatrix_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

/-- **Math.** **Volume Jacobian basis-change formula**:
`√det G(b') = |det P| · √det G(b)` where `P = b.toMatrix b'`. This is the
Jacobian factor for the change of variables in the volume integral: under
a coordinate change `y = ψ(φ⁻¹(x))`, the chart-pullback weight
`√det(g_ij) dx` transforms as `|det Dψ(φ⁻¹(x))| · √det(g_ij) dx`, making
the measure independent of the chart.

Ground truth: do Carmo Ch.1 Eq.(5); Lee Ch.16. -/
theorem sqrtGramDet_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (x : M)
    (b b' : Module.Basis ι ℝ (TangentSpace I x)) :
    g.sqrtGramDet x b' = |(b.toMatrix b').det| * g.sqrtGramDet x b := by
  unfold sqrtGramDet
  rw [gramMatrix_basis_change g x b b',
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      show ((b.toMatrix b').det * (g.gramMatrix x b).det * (b.toMatrix b').det
            = (b.toMatrix b').det ^ 2 * (g.gramMatrix x b).det) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

end Riemannian.RiemannianMetric
