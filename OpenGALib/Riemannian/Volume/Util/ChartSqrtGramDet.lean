import Mathlib.Analysis.SpecialFunctions.Sqrt
import OpenGALib.Riemannian.TensorBundle.MusicalIso
import OpenGALib.Riemannian.Volume.Util.GramDeterminant

/-!
# Chart-frame volume Jacobian `√det g_ij`

For a Riemannian metric `g`, a model-space basepoint `α : M`, and a
manifold point `x` in the trivialization base set at `α`, this file
defines

* `chartSqrtGramDet g α x : ℝ` — `√det (chartGramMatrix g α x)`, the
  Jacobian factor in the chart-pullback formula
  `vol_g|_U(A) = ∫_{φ(A)} √det(g_ij ∘ φ⁻¹)(y) dy`.

`chartSqrtGramDet` is **strictly positive** and **smooth** on the
trivialization base set, both inherited from `chartGramMatrix`'s
positive-definiteness and entry-smoothness (`MusicalIso.lean`).

Bridge lemmas relate this chart-specialized construction to the abstract
`g.sqrtGramDet x b` from `Volume/Util/GramDeterminant`, allowing the
abstract basis-change formula `sqrtGramDet_basis_change` to specialize to
chart overlaps when `b = chartBasisFamily α hx`.

Ground truth: do Carmo Ch.1 Eq.(5); Lee Ch.16.
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

/-- **Math.** The chart-pullback volume Jacobian factor:
`√det (g_ij(x))` for the chart-induced basis at `α`. Equals the textbook
weight in `vol_g|_U(A) = ∫_{φ(A)} √det(g_ij ∘ φ⁻¹)(y) dy`.

Defined unconditionally on `M`, but mathematically meaningful only on
the trivialization base set at `α` (off-set, the chart basis is junk
and `chartGramMatrix` need not be positive-definite). -/
def chartSqrtGramDet (g : RiemannianMetric I M) (α : M) (x : M) : ℝ :=
  Real.sqrt (chartGramMatrix (I := I) g α x).det

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartSqrtGramDet_apply
    (g : RiemannianMetric I M) (α : M) (x : M) :
    chartSqrtGramDet (I := I) g α x =
      Real.sqrt (chartGramMatrix (I := I) g α x).det := rfl

attribute [simp] chartSqrtGramDet_apply

/-- **Math.** Strict positivity of the volume Jacobian factor on the
trivialization base set. Follows from `chartGramMatrix_det_pos` and
`Real.sqrt_pos`. -/
lemma chartSqrtGramDet_pos
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    0 < chartSqrtGramDet (I := I) g α x :=
  Real.sqrt_pos.mpr (chartGramMatrix_det_pos (I := I) g α hx)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Nonnegativity holds everywhere (from `Real.sqrt_nonneg`). -/
lemma chartSqrtGramDet_nonneg
    (g : RiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartSqrtGramDet (I := I) g α x :=
  Real.sqrt_nonneg _

/-- **Math.** The volume Jacobian factor is `C^∞`-smooth on the
trivialization base set. Composition of the smooth Gram-matrix
determinant (`chartGramMatrix_det_contMDiffOn`) with `Real.sqrt`, which
is `C^∞` on `(0, ∞)`. -/
lemma chartSqrtGramDet_contMDiffOn
    (g : RiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartSqrtGramDet (I := I) g α)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  have h_det :
      ContMDiffWithinAt I 𝓘(ℝ) ∞
        (fun y => (chartGramMatrix (I := I) g α y).det)
        (trivializationAt E (TangentSpace I) α).baseSet x :=
    chartGramMatrix_det_contMDiffOn (I := I) g α x hx
  have h_pos : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
    (chartGramMatrix_det_pos (I := I) g α hx).ne'
  have h_sqrt :
      ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ Real.sqrt
        ((chartGramMatrix (I := I) g α x).det) :=
    (Real.contDiffAt_sqrt h_pos).contMDiffAt
  exact h_sqrt.comp_contMDiffWithinAt x h_det

/-! ## Bridge to the abstract `gramMatrix` / `sqrtGramDet`

`chartGramMatrix` and `chartSqrtGramDet` are chart-specialized
constructions; the abstract `g.gramMatrix x b` / `g.sqrtGramDet x b` take
an arbitrary basis `b`. The bridges below identify the chart-specialized
form with the abstract form at `b = chartBasisFamily α hx`. This lets
`gramMatrix_basis_change` / `sqrtGramDet_basis_change` specialize to
chart overlaps. -/

/-- **Eng.** Bridge: the chart Gram matrix equals the abstract Gram
matrix applied to the chart-induced basis on the trivialization base
set. -/
theorem chartGramMatrix_eq_gramMatrix_chartBasisFamily
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix (I := I) g α x =
      g.gramMatrix x (chartBasisFamily (I := I) α hx) := by
  ext i j
  show g.inner x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      g.metricInner x
        ((chartBasisFamily (I := I) α hx) i)
        ((chartBasisFamily (I := I) α hx) j)
  rw [chartBasisFamily_apply, chartBasisFamily_apply]
  rfl

/-- **Eng.** Bridge: the chart √det Gram matrix equals the abstract
`sqrtGramDet` applied to the chart-induced basis on the trivialization
base set. Specializing `sqrtGramDet_basis_change` through this bridge
yields the chart-overlap transformation
`chartSqrtGramDet g α₂ x = |det P_{α₁→α₂}(x)| · chartSqrtGramDet g α₁ x`. -/
theorem chartSqrtGramDet_eq_sqrtGramDet_chartBasisFamily
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartSqrtGramDet (I := I) g α x =
      g.sqrtGramDet x (chartBasisFamily (I := I) α hx) := by
  show Real.sqrt (chartGramMatrix (I := I) g α x).det =
      Real.sqrt (g.gramMatrix x (chartBasisFamily (I := I) α hx)).det
  rw [chartGramMatrix_eq_gramMatrix_chartBasisFamily g α hx]

end Riemannian.Tensor
