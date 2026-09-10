import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.MetricExistence
import DifferentialGeometry.Bundle.ClmSectionSmooth
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Metrics induced by smooth immersions

The metric is pulled back by the actual manifold derivative. The assumptions
are smoothness and injectivity of the differential, with no injectivity of the
map itself. Thus immersed surfaces, including self-intersections, are allowed.

The smoothness argument adapts the pullback construction in
`DifferentialGeometry.Geometry.Metric.PullbackCross` from diffeomorphisms to
immersions. Boundedness follows from finite-dimensional positive definiteness.
Upstream: qinz1yang/differential-geometry, Apache-2.0, v0.1.2,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Reference: Lee, Introduction to Riemannian Manifolds, second edition, Chapter 8.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace OpenGA.Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]

/-- Pull back the ambient inner product along the differential of a map. -/
def inducedInner (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (x : N) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
    ((g.inner (f x)).comp (mfderiv I J f x))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ N] in
@[simp] theorem inducedInner_apply
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (x : N) (v w : TangentSpace I x) :
    inducedInner (I := I) g f x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ N] in
theorem inducedInner_pos
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : N) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < inducedInner (I := I) g f x v v := by
  apply g.pos
  intro h
  exact hv (hinj x (by simpa using h))

theorem inducedInner_contMDiff [T2Space N]
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (hf : ContMDiff I J ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (inducedInner (I := I) g f x)) := by
  apply DifferentialGeometry.cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : N => TangentSpace I x →L[ℝ] ℝ)
  intro Y
  apply DifferentialGeometry.cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : N => ℝ)
  intro W
  have htf : ContMDiff I.tangent J.tangent ∞ (tangentMap I J f) :=
    hf.contMDiff_tangentMap (le_refl _)
  have hv := htf.comp Y.contMDiff
  have hw := htf.comp W.contMDiff
  have hg := g.contMDiff.comp hf
  have htotal := ContMDiff.clm_bundle_apply₂
    (E₁ := fun b : M => TangentSpace J b)
    (E₂ := fun b : M => TangentSpace J b)
    (E₃ := fun _ : M => ℝ)
    (b := f) (ψ := fun x => g.inner (f x))
    (v := fun x => mfderiv I J f x (Y x))
    (w := fun x => mfderiv I J f x (W x)) hg hv hw
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner (f x) (mfderiv I J f x (Y x)) (mfderiv I J f x (W x))) := by
    intro x
    have hx := htotal x
    rw [contMDiffAt_totalSpace] at hx
    simpa using hx.2
  intro x
  rw [contMDiffAt_section]
  exact hscalar x

/-- The smooth metric induced by a smooth map with injective differential. -/
def inducedMetric [T2Space N]
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (hf : ContMDiff I J ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    DifferentialGeometry.SmoothRiemannianMetric I N where
  inner := inducedInner (I := I) g f
  symm x v w := g.symm (f x) (mfderiv I J f x v) (mfderiv I J f x w)
  pos := inducedInner_pos g f hinj
  isVonNBounded x := DifferentialGeometry.Geometry.posDef_isVonNBounded (E := E)
    (inducedInner (I := I) g f x) (inducedInner_pos g f hinj x)
  contMDiff := inducedInner_contMDiff g f hf

@[simp] theorem inducedMetric_inner [T2Space N]
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (hf : ContMDiff I J ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : N) (v w : TangentSpace I x) :
    (inducedMetric g f hf hinj).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

end OpenGA.Surface
