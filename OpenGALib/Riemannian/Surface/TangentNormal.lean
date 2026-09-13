import OpenGALib.Riemannian.Surface.InducedMetric
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Tangent and normal spaces along an immersion

The tangent plane is the range of the actual manifold derivative. The normal
space uses the ambient Riemannian metric, rather than an auxiliary norm on the
model vector space. Both are defined pointwise along the map, so distinct
preimages of a self-intersection retain their own tangent planes.

These definitions do not assert smoothness of the normal bundle or construct
its connection. They provide the pointwise spaces needed for those results.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace OpenGA.Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M]

/-- The image of the differential at a point of the source manifold. -/
def tangentPlane (f : N → M) (x : N) : Submodule ℝ (TangentSpace J (f x)) :=
  (mfderiv I J f x).range

@[simp] theorem mem_tangentPlane (f : N → M) (x : N)
    (w : TangentSpace J (f x)) :
    w ∈ tangentPlane (I := I) (J := J) f x ↔ ∃ v, mfderiv I J f x v = w := Iff.rfl

theorem mfderiv_mem_tangentPlane (f : N → M) (x : N) (v : TangentSpace I x) :
    mfderiv I J f x v ∈ tangentPlane (I := I) (J := J) f x := ⟨v, rfl⟩

/-- An injective differential preserves the dimension of the tangent space. -/
theorem finrank_tangentPlane (f : N → M) (x : N)
    (hinj : Function.Injective (mfderiv I J f x)) :
    Module.finrank ℝ (tangentPlane (I := I) (J := J) f x) = Module.finrank ℝ E :=
  LinearMap.finrank_range_of_inj hinj

variable [IsManifold J ∞ M]

/-- Vectors orthogonal, in the ambient metric, to every vector in the image
of the differential. No global normal vector or orientation is chosen. -/
def normalSpace (g : DifferentialGeometry.SmoothRiemannianMetric J M)
    (f : N → M) (x : N) : Submodule ℝ (TangentSpace J (f x)) where
  carrier := {w | ∀ v : TangentSpace I x, g.inner (f x) w (mfderiv I J f x v) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb v
    simp [map_add, ha v, hb v]
  smul_mem' := by
    intro c a ha v
    simp [ha v]

@[simp] theorem mem_normalSpace
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N)
    (w : TangentSpace J (f x)) :
    w ∈ normalSpace (I := I) g f x ↔
      ∀ v : TangentSpace I x, g.inner (f x) w (mfderiv I J f x v) = 0 := Iff.rfl

theorem inner_normal_tangent_eq_zero
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N)
    {w v : TangentSpace J (f x)}
    (hw : w ∈ normalSpace (I := I) g f x)
    (hv : v ∈ tangentPlane (I := I) (J := J) f x) :
    g.inner (f x) w v = 0 := by
  obtain ⟨u, rfl⟩ := hv
  exact hw u

/-- Positive definiteness forces the tangent and normal spaces to intersect
only at zero, even before any immersion hypothesis is imposed. -/
theorem tangentPlane_inf_normalSpace
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M) (x : N) :
    tangentPlane (I := I) (J := J) f x ⊓ normalSpace (I := I) g f x = ⊥ := by
  apply le_antisymm
  · intro w hw
    change w = 0
    by_contra h
    have hz := inner_normal_tangent_eq_zero g f x hw.2 hw.1
    exact (ne_of_gt (g.pos (f x) w h)) hz
  · exact bot_le

end OpenGA.Surface
