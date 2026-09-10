import OpenGALib.Interoperability.RicciFlow.AreaMonotonicity

/-!
# Finite families of immersed surface slices

This file provides the small interface needed before connecting Ricci-flow
area variation to a sweepout or width construction. The family is finite, so
pointwise slice estimates can later be combined with a maximum argument. The
geometric construction of a sweepout is intentionally not asserted here.
-/

noncomputable section

open Bundle Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

namespace OpenGA.RicciFlow

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Surface.Model N]
  [IsManifold 𝓘(ℝ, Surface.Model) ∞ N] [T2Space N] [CompactSpace N]
  {D : RealTimeInterval}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- A finite collection of fixed immersed surface slices for one Ricci flow.
The smoothness and differential-injectivity fields are the exact hypotheses
needed by the global area variation theorem. No sweepout topology is included.
-/
structure SurfaceSliceFamily (ι : Type*) [Fintype ι]
    (S : SolutionOn (I := I) (M := M) D) where
  map : ι → N → M
  smooth : ∀ i, ContMDiff 𝓘(ℝ, Surface.Model) I ∞ (map i)
  immersion : ∀ i x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I (map i) x)

/-- Every slice in a family has nonpositive area derivative under a
nonnegative integrated tangential Ricci trace assumption. -/
theorem deriv_slice_area_nonpos
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {ι : Type*} [Fintype ι] (family : SurfaceSliceFamily (I := I) (D := D) ι S)
    {t : ℝ} (ht : t ∈ D.regular)
    (htrace : ∀ i, 0 ≤ ∫ x, inducedRicciTrace (N := N) (I := I) (M := M) S (family.map i)
      (family.smooth i) (family.immersion i) t x
      ∂(Surface.areaMeasure (S.family.metric t) (family.map i)
        (family.smooth i) (family.immersion i))) :
    ∀ i, deriv (fun s => Surface.area (S.family.metric s) (family.map i)
      (family.smooth i) (family.immersion i)) t ≤ 0 := by
  intro i
  exact deriv_area_nonpos_of_integral_inducedRicciTrace_nonneg S hS
    (family.map i) (family.smooth i) (family.immersion i) ht (htrace i)

end OpenGA.RicciFlow
