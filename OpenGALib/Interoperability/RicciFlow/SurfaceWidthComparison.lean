import OpenGALib.Interoperability.RicciFlow.SurfaceSliceFamily
import OpenGALib.Analysis.WidthComparison

/-!
# Surface-slice input for the width comparison argument

`WidthComparisonData` is an analytic interface whose competitors are finite
energy pairs. This file records the additional geometric data needed to use
that interface with actual immersed surface slices. The construction of the
comparison witnesses from a sweepout remains a separate theorem.
-/

noncomputable section

open Bundle Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

namespace OpenGA.RicciFlow

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Surface.Model N]
  [IsManifold 𝓘(ℝ, Surface.Model) ∞ N] [T2Space N] [CompactSpace N]
  {D : RealTimeInterval}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- Geometric slices together with the analytic comparison witnesses used by
the Colding--Minicozzi width estimate. The trace condition is explicit: this
interface does not claim that a sweepout or a minimal sphere has been built.
-/
structure SurfaceWidthComparisonData (ι : Type*) [Fintype ι]
    (S : SolutionOn (I := I) (M := M) D) (width : ℝ → ℝ) (t scalar : ℝ) where
  slices : SurfaceSliceFamily (N := N) (I := I) (D := D) ι S
  comparison : OpenGA.WidthComparisonData width t scalar
  trace_nonneg : ∀ i, 0 ≤ ∫ x, inducedRicciTrace S (slices.map i)
    (slices.smooth i) (slices.immersion i) t x
    ∂(Surface.areaMeasure (S.family.metric t) (slices.map i)
      (slices.smooth i) (slices.immersion i))

/-- The surface-slice package supplies both the analytic width slope estimate
and the nonpositive derivative of every geometric slice. -/
theorem surface_width_comparison
    {ι : Type*} [Fintype ι]
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    {width : ℝ → ℝ} {t scalar q : ℝ}
    (data : SurfaceWidthComparisonData (N := N) (I := I) (D := D) ι S width t scalar)
    (ht : t ∈ D.regular)
    (hq : -(4 * Real.pi) - scalar / 2 * width t < q) :
    (∀ᶠ s in 𝓝[>] t, slope width t s < q) ∧
      (∀ i, deriv (fun s => Surface.area (S.family.metric s)
        (data.slices.map i) (data.slices.smooth i) (data.slices.immersion i)) t ≤ 0) := by
  constructor
  · exact OpenGA.eventually_width_slope_lt_of_comparison data.comparison q hq
  · exact deriv_slice_area_nonpos S hS data.slices
      ht data.trace_nonneg

end OpenGA.RicciFlow
