import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Matrix.ToLin
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

/-! ## Bridge to the chart-transition derivative

`transitionMatrix` was defined as the abstract `Basis.toMatrix` between
chart-induced bases. The two lemmas below identify it with the matrix of
Mathlib's `tangentCoordChange`, the Fréchet derivative within `range I`
of the chart-transition map. This bridges abstract LinearAlgebra to
analysis: Mathlib's change-of-variables (`MeasureTheory.Measure.map`,
`integral_image_eq_integral_abs_det_fderiv_smul`, etc.) consume
`|det fderiv|`, and via this bridge our `|det P|` Jacobian factor
becomes admissible. -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** Bridge: the chart-transition matrix at `x` is the matrix of
the chart-transition derivative `tangentCoordChange I α₁ α₀ x` in the
model basis of `E`. The index swap (`α₁ α₀` on the RHS vs `α₀ α₁` on the
LHS) reflects the contravariance of basis change vs. forward chart
transition: the change-of-basis matrix from `chartBasisFamily α₀` to
`chartBasisFamily α₁` equals the derivative of the chart map
`extChartAt I α₀ ∘ (extChartAt I α₁).symm` (going from `α₁`-coordinates
to `α₀`-coordinates), which is `tangentCoordChange I α₁ α₀ x`. -/
theorem transitionMatrix_eq_toMatrix_tangentCoordChange
    (α₀ α₁ : M) {x : M}
    (hx₀ : x ∈ (trivializationAt E (TangentSpace I) α₀).baseSet)
    (hx₁ : x ∈ (trivializationAt E (TangentSpace I) α₁).baseSet) :
    transitionMatrix (I := I) α₀ α₁ hx₀ hx₁ =
      LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
        (tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).toLinearMap := by
  set T₀ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α₀
  set T₁ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α₁
  set e₀ := T₀.continuousLinearEquivAt ℝ x hx₀ with he₀
  set e₁ := T₁.continuousLinearEquivAt ℝ x hx₁ with he₁
  -- Identify the composition `e₀ ∘ e₁.symm` with `coordChangeL T₁ T₀ x`, then with
  -- `tangentCoordChange I α₁ α₀ x` (via the tangentBundleCore identification).
  have hcomp :=
    Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := ℝ) (F := E) (E := (TangentSpace I : M → Type _))
      T₁ T₀ (b := x) ⟨hx₁, hx₀⟩
  have hcc : ∀ v : E,
      (Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x) v =
        (tangentCoordChange I α₁ α₀ x) v := by
    intro v
    change (Bundle.Trivialization.coordChangeL (R := ℝ)
          ((tangentBundleCore I M).localTriv (achart H α₁))
          ((tangentBundleCore I M).localTriv (achart H α₀)) x) v = _
    exact VectorBundleCore.localTriv_coordChange_eq
      (tangentBundleCore I M) (achart H α₁) (achart H α₀)
      (b := x) ⟨hx₁, hx₀⟩ v
  -- Pointwise identity: e₀ ∘ e₁.symm = tangentCoordChange I α₁ α₀ x.
  have hgeom : ∀ v : E, e₀ (e₁.symm v) = (tangentCoordChange I α₁ α₀ x) v := by
    intro v
    have happ := congrArg (fun L : E ≃L[ℝ] E => L v) hcomp
    simp only [ContinuousLinearEquiv.trans_apply] at happ
    rw [happ, hcc]
  -- Helper: `(chartBasisFamily α₀ hx₀).repr y = (finBasis).repr (e₀ y)`.
  have hrepr : ∀ y : TangentSpace I x,
      (chartBasisFamily (I := I) α₀ hx₀).repr y =
        (Module.finBasis ℝ E).repr (e₀ y) := by
    intro y
    show ((Module.finBasis ℝ E).map
            (ContinuousLinearEquiv.toLinearEquiv e₀.symm)).repr y =
        (Module.finBasis ℝ E).repr (e₀ y)
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply]
    congr 1
  ext k i
  -- LHS unfolds to `(chartBasisFamily α₀).repr (chartBasisFamily α₁ i) k`.
  -- RHS unfolds via `LinearMap.toMatrix_apply` to `(finBasis).repr (tangentCoordChange ...) k`.
  show (chartBasisFamily (I := I) α₀ hx₀).repr
        (chartBasisFamily (I := I) α₁ hx₁ i) k =
      LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
        (tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).toLinearMap k i
  rw [LinearMap.toMatrix_apply]
  rw [hrepr]
  -- `chartBasisFamily α₁ i = e₁.symm (finBasis i)`.
  have h_cBF₁ : chartBasisFamily (I := I) α₁ hx₁ i = e₁.symm (Module.finBasis ℝ E i) := rfl
  rw [h_cBF₁, hgeom]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** Determinant bridge: `det (transitionMatrix α₀ α₁) = det (tangentCoordChange α₁ α₀ x)`. -/
theorem transitionMatrix_det_eq_tangentCoordChange_det
    (α₀ α₁ : M) {x : M}
    (hx₀ : x ∈ (trivializationAt E (TangentSpace I) α₀).baseSet)
    (hx₁ : x ∈ (trivializationAt E (TangentSpace I) α₁).baseSet) :
    (transitionMatrix (I := I) α₀ α₁ hx₀ hx₁).det =
      (tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det := by
  rw [transitionMatrix_eq_toMatrix_tangentCoordChange α₀ α₁ hx₀ hx₁,
      LinearMap.det_toMatrix]

end Riemannian.Tensor
