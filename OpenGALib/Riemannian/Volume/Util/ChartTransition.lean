import OpenGALib.Riemannian.Volume.Util.ChartSqrtGramDet

/-!
# Chart-transition matrix and chart-overlap pullback of `chartGramMatrix`

For a Riemannian metric `g` and two model-space basepoints `α₀, α₁ : M`
whose trivialization base sets share a point `x`, the chart-induced
bases `chartBasisFamily α₀ hx₀` and `chartBasisFamily α₁ hx₁` of
`TangentSpace I x` differ by a linear change-of-basis matrix
`P_{α₀ → α₁}(x)`. This file defines

* `transitionMatrix α₀ α₁ hx₀ hx₁ : Matrix (Fin n) (Fin n) ℝ` — the
  abstract `Basis.toMatrix` between the two chart bases.

and derives the **chart-overlap pullback formulae** for `chartGramMatrix`
and `chartSqrtGramDet`:

* `chartGramMatrix_pullback_eq_mul`
  `G_{α₁}(x) = Pᵀ · G_{α₀}(x) · P`
* `chartGramMatrix_det_pullback`
  `det G_{α₁}(x) = (det P)² · det G_{α₀}(x)`
* `chartSqrtGramDet_pullback`
  `chartSqrtGramDet g α₁ x = |det P| · chartSqrtGramDet g α₀ x`

These specialize the abstract `gramMatrix_basis_change` /
`sqrtGramDet_basis_change` to the chart-frame setting via the
`chartGramMatrix_eq_gramMatrix_chartBasisFamily` /
`chartSqrtGramDet_eq_sqrtGramDet_chartBasisFamily` bridges.

The connection of `transitionMatrix` to the analysis-side chart-transition
derivative `tangentCoordChange` is deferred — it is needed only for the
change-of-variables step in the global measure-invariance theorem
(`chartLocalMeasure_lintegral_U_eq_of_overlap`).

Ground truth: do Carmo Ch.1; Lee Ch.16.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The chart-transition matrix at `x ∈ baseSet α₀ ∩ baseSet α₁`:
the change-of-basis matrix from `chartBasisFamily α₀ hx₀` to
`chartBasisFamily α₁ hx₁` of `TangentSpace I x`. Entries are the
`α₀`-coordinates of the `α₁`-basis vectors.

This is the abstract LinearAlgebra precursor to the chart-transition
derivative matrix; the analysis-side identification with
`tangentCoordChange` is left as a follow-up bridge lemma. -/
noncomputable def transitionMatrix (α₀ α₁ : M) {x : M}
    (hx₀ : x ∈ (trivializationAt E (TangentSpace I) α₀).baseSet)
    (hx₁ : x ∈ (trivializationAt E (TangentSpace I) α₁).baseSet) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartBasisFamily (I := I) α₀ hx₀).toMatrix
    (chartBasisFamily (I := I) α₁ hx₁)

/-- **Math.** **Matrix form of the chart Gram pullback**:
`G_{α₁}(x) = Pᵀ · G_{α₀}(x) · P` where
`P = transitionMatrix α₀ α₁ hx₀ hx₁`. Specialization of the abstract
`gramMatrix_basis_change` via the chart-Gram-matrix bridge.

Ground truth: do Carmo Ch.1 Eq.(5). -/
theorem chartGramMatrix_pullback_eq_mul
    (g : RiemannianMetric I M) (α₀ α₁ : M) {x : M}
    (hx₀ : x ∈ (trivializationAt E (TangentSpace I) α₀).baseSet)
    (hx₁ : x ∈ (trivializationAt E (TangentSpace I) α₁).baseSet) :
    chartGramMatrix (I := I) g α₁ x =
      (transitionMatrix (I := I) α₀ α₁ hx₀ hx₁).transpose *
        chartGramMatrix (I := I) g α₀ x *
        transitionMatrix (I := I) α₀ α₁ hx₀ hx₁ := by
  rw [chartGramMatrix_eq_gramMatrix_chartBasisFamily g α₁ hx₁,
      chartGramMatrix_eq_gramMatrix_chartBasisFamily g α₀ hx₀]
  exact g.gramMatrix_basis_change x
    (chartBasisFamily (I := I) α₀ hx₀)
    (chartBasisFamily (I := I) α₁ hx₁)

/-- **Math.** **Determinant form of the chart Gram pullback**:
`det G_{α₁}(x) = (det P)² · det G_{α₀}(x)`. -/
theorem chartGramMatrix_det_pullback
    (g : RiemannianMetric I M) (α₀ α₁ : M) {x : M}
    (hx₀ : x ∈ (trivializationAt E (TangentSpace I) α₀).baseSet)
    (hx₁ : x ∈ (trivializationAt E (TangentSpace I) α₁).baseSet) :
    (chartGramMatrix (I := I) g α₁ x).det =
      (transitionMatrix (I := I) α₀ α₁ hx₀ hx₁).det ^ 2 *
        (chartGramMatrix (I := I) g α₀ x).det := by
  rw [chartGramMatrix_pullback_eq_mul g α₀ α₁ hx₀ hx₁,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- **Math.** **Volume Jacobian form of the chart pullback**:
`chartSqrtGramDet g α₁ x = |det P| · chartSqrtGramDet g α₀ x`. This is
the change-of-variables Jacobian factor that the volume measure must
absorb at chart overlaps, making `volumeMeasure g` chart-independent.

Ground truth: do Carmo Ch.1 Eq.(5); Lee Ch.16. -/
theorem chartSqrtGramDet_pullback
    (g : RiemannianMetric I M) (α₀ α₁ : M) {x : M}
    (hx₀ : x ∈ (trivializationAt E (TangentSpace I) α₀).baseSet)
    (hx₁ : x ∈ (trivializationAt E (TangentSpace I) α₁).baseSet) :
    chartSqrtGramDet (I := I) g α₁ x =
      |(transitionMatrix (I := I) α₀ α₁ hx₀ hx₁).det| *
        chartSqrtGramDet (I := I) g α₀ x := by
  rw [chartSqrtGramDet_eq_sqrtGramDet_chartBasisFamily g α₁ hx₁,
      chartSqrtGramDet_eq_sqrtGramDet_chartBasisFamily g α₀ hx₀]
  exact g.sqrtGramDet_basis_change x
    (chartBasisFamily (I := I) α₀ hx₀)
    (chartBasisFamily (I := I) α₁ hx₁)

end Riemannian.Tensor
