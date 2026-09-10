import OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Finite-time area comparison from tangential Ricci trace

Integrate the proved global area variation formula for a fixed smooth
immersion. The lower bound is required on the whole time interval. Obtaining
such bounds uniformly for a sweepout, including singular or branched slices,
is a separate geometric task.
-/

noncomputable section
open Bundle Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

namespace OpenGA.RicciFlow

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Surface.Model N]
  [IsManifold 𝓘(ℝ, Surface.Model) ∞ N] [T2Space N] [CompactSpace N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- An integrated tangential Ricci lower bound `-C` gives an area increment
at most `C * (b - a)`. There is no sign restriction on `C`. -/
theorem area_sub_le_of_integral_inducedRicciTrace_lower
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x))
    {a b C : ℝ} (hab : a ≤ b) (hregular : Icc a b ⊆ D.regular)
    (htrace : ∀ t ∈ Ioo a b, -C ≤ ∫ x, inducedRicciTrace S f hf hinj t x
      ∂(Surface.areaMeasure (S.family.metric t) f hf hinj)) :
    Surface.area (S.family.metric b) f hf hinj -
      Surface.area (S.family.metric a) f hf hinj ≤ C * (b - a) := by
  have hdiff := fun (t : ℝ) (ht : t ∈ Icc a b) =>
    hasDerivAt_area S hS f hf hinj (hregular ht)
  apply (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdiff t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    _ a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  intro t ht
  rw [(hdiff t (interior_subset ht)).deriv]
  have h := htrace t (by simpa only [interior_Icc] using ht)
  linarith

end OpenGA.RicciFlow
