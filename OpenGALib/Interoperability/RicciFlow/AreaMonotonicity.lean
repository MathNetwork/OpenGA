import OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea

/-!
# Monotonicity of immersed-surface area

This is the first bridge from the global Ricci-flow area variation formula to
the width route: a nonnegative tangential Ricci trace gives a nonpositive
instantaneous area derivative. The theorem is deliberately stated for a
fixed smooth immersion; sweepouts and minimal-sphere estimates are separate
interfaces.
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

/-- The area derivative is nonpositive when the integrated tangential Ricci
trace is nonnegative. -/
theorem deriv_area_nonpos_of_integral_inducedRicciTrace_nonneg
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x))
    {t : ℝ} (ht : t ∈ D.regular)
    (htrace : 0 ≤ ∫ x, inducedRicciTrace S f hf hinj t x
      ∂(Surface.areaMeasure (S.family.metric t) f hf hinj)) :
    deriv (fun s => Surface.area (S.family.metric s) f hf hinj) t ≤ 0 := by
  have hderiv := (hasDerivAt_area S hS f hf hinj ht).deriv
  linarith

end OpenGA.RicciFlow
