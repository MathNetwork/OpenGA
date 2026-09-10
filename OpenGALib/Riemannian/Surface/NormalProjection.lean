import OpenGALib.Riemannian.Surface.TangentNormal
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projection

/-!
# Metric tangent and normal projections

Positive definiteness and finite dimensionality give the orthogonal splitting
of the ambient tangent space along a map. Mathlib supplies the bilinear-form
complement theorem and the associated linear projections. The metric used
here is the actual ambient Riemannian metric.

The constructions are pointwise. Smooth dependence on the source point, which
requires a constant-rank hypothesis, is a separate result.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace OpenGA.Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]

/-- The image of the differential and its metric normal space are complementary. -/
theorem isCompl_tangentPlane_normalSpace
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N) :
    IsCompl (tangentPlane (I := I) (J := J) f x) (normalSpace (I := I) g f x) := by
  have : FiniteDimensional ℝ (TangentSpace J (f x)) :=
    (inferInstance : FiniteDimensional ℝ F)
  let B : LinearMap.BilinForm ℝ (TangentSpace J (f x)) :=
    LinearMap.mk₂ ℝ (fun v w => g.inner (f x) v w)
      (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have hB : B.IsRefl := by
    intro v w h
    exact (g.symm (f x) w v).trans h
  have heq : B.orthogonal (tangentPlane (I := I) (J := J) f x) =
      normalSpace (I := I) g f x := by
    ext w
    constructor
    · intro hw v
      exact (g.symm (f x) w (mfderiv I J f x v)).trans
        (hw _ (mfderiv_mem_tangentPlane f x v))
    · intro hw v hv
      exact (g.symm (f x) v w).trans (inner_normal_tangent_eq_zero g f x hw hv)
  rw [← heq]
  apply (B.isCompl_orthogonal_iff_disjoint hB).2
  rw [heq, disjoint_iff]
  exact tangentPlane_inf_normalSpace g f x

/-- The metric normal space has the codimension of the differential's image. -/
theorem finrank_normalSpace
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N)
    (hinj : Function.Injective (mfderiv I J f x)) :
    Module.finrank ℝ (normalSpace (I := I) g f x) =
      Module.finrank ℝ F - Module.finrank ℝ E := by
  have : FiniteDimensional ℝ (TangentSpace J (f x)) :=
    (inferInstance : FiniteDimensional ℝ F)
  have h := Submodule.finrank_add_eq_of_isCompl
    (isCompl_tangentPlane_normalSpace (I := I) g f x)
  rw [finrank_tangentPlane f x hinj] at h
  exact Nat.eq_sub_of_add_eq' h

/-- The ambient linear projection onto the tangent plane using the metric complement. -/
def tangentProjection
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N) :
    TangentSpace J (f x) →ₗ[ℝ] TangentSpace J (f x) :=
  (tangentPlane (I := I) (J := J) f x).projection (normalSpace (I := I) g f x)
    (isCompl_tangentPlane_normalSpace g f x)

/-- The ambient linear projection onto the normal space using the metric complement. -/
def normalProjection
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N) :
    TangentSpace J (f x) →ₗ[ℝ] TangentSpace J (f x) :=
  (normalSpace (I := I) g f x).projection (tangentPlane (I := I) (J := J) f x)
    (isCompl_tangentPlane_normalSpace g f x).symm

theorem tangentProjection_mem
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N)
    (v : TangentSpace J (f x)) :
    tangentProjection (I := I) g f x v ∈ tangentPlane (I := I) (J := J) f x :=
  Submodule.projection_apply_mem _ _

theorem normalProjection_mem
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N)
    (v : TangentSpace J (f x)) :
    normalProjection (I := I) g f x v ∈ normalSpace (I := I) g f x :=
  Submodule.projection_apply_mem _ _

@[simp] theorem normalProjection_mfderiv
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N)
    (v : TangentSpace I x) :
    normalProjection (I := I) g f x (mfderiv I J f x v) = 0 :=
  Submodule.projection_apply_of_mem_right _ (mfderiv_mem_tangentPlane f x v)

theorem tangentProjection_add_normalProjection
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N)
    (v : TangentSpace J (f x)) :
    tangentProjection (I := I) g f x v + normalProjection (I := I) g f x v = v :=
  Submodule.projection_add_projection_eq_self _ _

end OpenGA.Surface
