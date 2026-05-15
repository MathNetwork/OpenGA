import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import OpenGALib.Riemannian.Volume.Util.ChartTransition

/-!
# Geometric / measure-theoretic plumbing on chart-source overlaps

Foundational set-theoretic and analytic lemmas about the images and
chart-transition map on overlap of two chart sources. These feed the
B3 invariance theorem `chartLocalMeasure_lintegral_U_eq_of_overlap`.

  * `extChartAt_image_measurableSet_of_open_subset_source` — image of
    an open subset of the chart source is Borel-measurable in `E`
    (works without `[I.Boundaryless]`: uses that `I` is a closed
    embedding, hence a measurable embedding).
  * `extChartAt_transition_image` — the chart-transition map
    `extChartAt I α₁ ∘ (extChartAt I α₀).symm` carries
    `(extChartAt I α₀) '' U` to `(extChartAt I α₁) '' U`.
  * `extChartAt_transition_injOn_overlap_image` — injectivity of the
    chart-transition map on the overlap image.
  * `extChartAt_transition_hasFDerivWithinAt_on_overlap_image` — the
    chart-transition map has Fréchet derivative
    `tangentCoordChange I α₀ α₁ x` at the overlap-image point
    `extChartAt I α₀ x`, within the overlap image itself.
-/

noncomputable section


open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace H := borel H
private local instance : BorelSpace H := ⟨rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] in
/-- **Eng.** Image of an open subset of a chart source under `extChartAt`
is Borel-measurable in `E`. Works without `[I.Boundaryless]`: factors
through the open image in `H` followed by the closed (hence measurable)
embedding `I`. -/
lemma extChartAt_image_measurableSet_of_open_subset_source (α : M)
    {U : Set M} (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H α).source) :
    MeasurableSet ((extChartAt I α) '' U) := by
  have hchart_img : IsOpen ((chartAt H α) '' U) :=
    (chartAt H α).isOpen_image_of_subset_source hUopen hUsub
  have himg_eq : (extChartAt I α) '' U = I '' ((chartAt H α) '' U) := by
    rw [extChartAt]
    simp only [OpenPartialHomeomorph.extend_coe]
    rw [image_comp]
  rw [himg_eq]
  exact I.isClosedEmbedding.measurableEmbedding.measurableSet_image.mpr
    hchart_img.measurableSet

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] in
/-- **Eng.** The chart-transition map
`extChartAt I α₁ ∘ (extChartAt I α₀).symm` carries `(extChartAt I α₀) '' U`
to `(extChartAt I α₁) '' U` when `U` is a subset of both chart sources. -/
lemma extChartAt_transition_image (α₀ α₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H α₀).source) :
    (extChartAt I α₁ ∘ (extChartAt I α₀).symm) '' ((extChartAt I α₀) '' U) =
      (extChartAt I α₁) '' U := by
  rw [← Set.image_comp]
  refine Set.image_congr ?_
  intro x hx
  have hxsrc0 : x ∈ (extChartAt I α₀).source := by
    rw [extChartAt_source]; exact hUsub0 hx
  change extChartAt I α₁ ((extChartAt I α₀).symm (extChartAt I α₀ x)) = _
  rw [(extChartAt I α₀).left_inv hxsrc0]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] in
/-- **Eng.** Injectivity of the chart-transition map on the overlap image. -/
lemma extChartAt_transition_injOn_overlap_image
    (α₀ α₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H α₀).source) (hUsub1 : U ⊆ (chartAt H α₁).source) :
    Set.InjOn (extChartAt I α₁ ∘ (extChartAt I α₀).symm)
      ((extChartAt I α₀) '' U) := by
  intro y hy z hz hyz
  obtain ⟨a, haU, rfl⟩ := hy
  obtain ⟨b, hbU, rfl⟩ := hz
  have haS0 : a ∈ (extChartAt I α₀).source := by
    rw [extChartAt_source]; exact hUsub0 haU
  have hbS0 : b ∈ (extChartAt I α₀).source := by
    rw [extChartAt_source]; exact hUsub0 hbU
  have haS1 : a ∈ (extChartAt I α₁).source := by
    rw [extChartAt_source]; exact hUsub1 haU
  have hbS1 : b ∈ (extChartAt I α₁).source := by
    rw [extChartAt_source]; exact hUsub1 hbU
  simp only [Function.comp_apply, (extChartAt I α₀).left_inv haS0,
    (extChartAt I α₀).left_inv hbS0] at hyz
  have hab := (extChartAt I α₁).injOn haS1 hbS1 hyz
  rw [hab]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** On the overlap image, the chart-transition map has Fréchet
derivative `tangentCoordChange I α₀ α₁ x` at `y = extChartAt I α₀ x`,
within the overlap image itself.

Reduces to Mathlib's `hasFDerivWithinAt_tangentCoordChange` on `range I`
by monotonicity (`HasFDerivWithinAt.mono`), since the overlap image is a
subset of `(extChartAt I α₀).target ⊆ range I`. -/
lemma extChartAt_transition_hasFDerivWithinAt_on_overlap_image
    (α₀ α₁ : M) {U : Set M}
    (hUsub0 : U ⊆ (chartAt H α₀).source) (hUsub1 : U ⊆ (chartAt H α₁).source) :
    ∀ y ∈ (extChartAt I α₀) '' U,
      HasFDerivWithinAt (extChartAt I α₁ ∘ (extChartAt I α₀).symm)
        (tangentCoordChange I α₀ α₁ ((extChartAt I α₀).symm y))
        ((extChartAt I α₀) '' U) y := by
  intro y hy
  obtain ⟨x, hxU, rfl⟩ := hy
  have hxS0 : x ∈ (extChartAt I α₀).source := by
    rw [extChartAt_source]; exact hUsub0 hxU
  have hxS1 : x ∈ (extChartAt I α₁).source := by
    rw [extChartAt_source]; exact hUsub1 hxU
  have hfull := hasFDerivWithinAt_tangentCoordChange (I := I)
    (x := α₀) (y := α₁) (z := x) ⟨hxS0, hxS1⟩
  have himage_sub : (extChartAt I α₀) '' U ⊆ Set.range I := by
    intro y' hy'
    rcases hy' with ⟨z, hzU, rfl⟩
    have hzS0 : z ∈ (extChartAt I α₀).source := by
      rw [extChartAt_source]; exact hUsub0 hzU
    exact extChartAt_target_subset_range α₀ ((extChartAt I α₀).map_source hzS0)
  have hsymm_eq : (extChartAt I α₀).symm ((extChartAt I α₀) x) = x :=
    (extChartAt I α₀).left_inv hxS0
  rw [hsymm_eq]
  exact hfull.mono himage_sub

/-! ## Inverse relation between `tangentCoordChange` in both directions

The two chart-transition derivatives at a common overlap point compose
to the identity (via the triple-composition identity `tangentCoordChange_comp`
+ self-identity `tangentCoordChange_self`). Determinants of the two
opposite transitions are reciprocals; their absolute values, and the
`ENNReal.ofReal` of those, multiply to `1`. These identities cancel the
Jacobian factor in the chart-overlap change-of-variables step of the
upcoming B3 invariance theorem. -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** Composition of the two opposite chart-transition derivatives
at a common overlap point is the identity. -/
lemma tangentCoordChange_comp_self_overlap
    (α₀ α₁ : M) {x : M}
    (h : x ∈ (extChartAt I α₀).source ∩ (extChartAt I α₁).source) (v : E) :
    tangentCoordChange I α₁ α₀ x (tangentCoordChange I α₀ α₁ x v) = v := by
  have h3 : x ∈ (extChartAt I α₀).source ∩ (extChartAt I α₁).source ∩
      (extChartAt I α₀).source := ⟨h, h.1⟩
  have := tangentCoordChange_comp (I := I) (w := α₀) (x := α₁) (y := α₀)
    (z := x) (v := v) h3
  rw [this]
  exact tangentCoordChange_self (I := I) h.1

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** `det (tangentCoordChange α₀ α₁ x) · det (tangentCoordChange α₁ α₀ x) = 1`
on the chart-source overlap. Follows from
`tangentCoordChange_comp_self_overlap` + `LinearMap.det_comp`. -/
lemma tangentCoordChange_det_mul_inv_det_eq_one
    (α₀ α₁ : M) {x : M}
    (h : x ∈ (extChartAt I α₀).source ∩ (extChartAt I α₁).source) :
    (tangentCoordChange I α₀ α₁ x : E →L[ℝ] E).det *
      (tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det = 1 := by
  classical
  have hcomp_id :
      ((tangentCoordChange I α₁ α₀ x : E →L[ℝ] E) :
            E →ₗ[ℝ] E).comp
          ((tangentCoordChange I α₀ α₁ x : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        LinearMap.id := by
    ext v
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
      LinearMap.id_coe, id_eq]
    exact tangentCoordChange_comp_self_overlap α₀ α₁ h v
  have hdet := congrArg LinearMap.det hcomp_id
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  -- `det(tcc α₁ α₀) * det(tcc α₀ α₁) = 1`; want `det(tcc α₀ α₁) * det(tcc α₁ α₀) = 1`.
  linarith [mul_comm
    ((tangentCoordChange I α₀ α₁ x : E →L[ℝ] E).det)
    ((tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** Absolute-value version: `|det(tcc α₀ α₁ x)| · |det(tcc α₁ α₀ x)| = 1`. -/
lemma abs_det_tangentCoordChange_mul_abs_det_inv
    (α₀ α₁ : M) {x : M}
    (h : x ∈ (extChartAt I α₀).source ∩ (extChartAt I α₁).source) :
    |(tangentCoordChange I α₀ α₁ x : E →L[ℝ] E).det| *
      |(tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det| = 1 := by
  rw [← abs_mul,
      tangentCoordChange_det_mul_inv_det_eq_one α₀ α₁ h,
      abs_one]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Eng.** ENNReal form: the chart-overlap Jacobian factors cancel
when promoted to `ℝ≥0∞`. -/
lemma ennreal_abs_det_tangentCoordChange_mul_abs_det_inv
    (α₀ α₁ : M) {x : M}
    (h : x ∈ (extChartAt I α₀).source ∩ (extChartAt I α₁).source) :
    ENNReal.ofReal |(tangentCoordChange I α₀ α₁ x : E →L[ℝ] E).det| *
      ENNReal.ofReal
        |(tangentCoordChange I α₁ α₀ x : E →L[ℝ] E).det| = 1 := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
      abs_det_tangentCoordChange_mul_abs_det_inv α₀ α₁ h]
  exact ENNReal.ofReal_one

end Riemannian.Tensor
