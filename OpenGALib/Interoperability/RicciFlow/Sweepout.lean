import OpenGALib.Interoperability.RicciFlow.SurfaceSliceFamily

/-!
# Sweepouts by immersed surface slices

This is the topological and smooth interface needed before constructing the
Colding--Minicozzi comparison data. Endpoint slices are allowed to be
different constant maps; a based or relative homotopy convention is a later
layer.
-/

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Topology

namespace OpenGA.RicciFlow

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Surface.Model N]
  [IsManifold 𝓘(ℝ, Surface.Model) ∞ N] [T2Space N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- A continuous sweepout of a target manifold by maps from the surface N.
The endpoint maps are constant, with no assertion that their constants agree.
-/
structure Sweepout where
  map : Icc (0 : ℝ) 1 → N → M
  continuous_joint : Continuous (fun p : Icc (0 : ℝ) 1 × N => map p.1 p.2)
  endpoint_zero_constant : ∃ c : M, ∀ x, map ⟨0, ⟨le_rfl, zero_le_one⟩⟩ x = c
  endpoint_one_constant : ∃ c : M, ∀ x, map ⟨1, ⟨zero_le_one, le_rfl⟩⟩ x = c

/-- A smooth immersed sweepout. The smoothness and immersion conditions are
pointwise in the sweepout parameter and can later be strengthened to joint
space-parameter regularity when constructing harmonic replacements.
-/
structure SmoothSweepout where
  map : Icc (0 : ℝ) 1 → N → M
  continuous_joint : Continuous (fun p : Icc (0 : ℝ) 1 × N => map p.1 p.2)
  smooth : ∀ u, ContMDiff 𝓘(ℝ, Surface.Model) I ∞ (map u)
  immersion : ∀ u x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I (map u) x)
  endpoint_zero_constant : ∃ c : M, ∀ x, map ⟨0, ⟨le_rfl, zero_le_one⟩⟩ x = c
  endpoint_one_constant : ∃ c : M, ∀ x, map ⟨1, ⟨zero_le_one, le_rfl⟩⟩ x = c

/-- Sampling a smooth sweepout at finitely many parameters gives the finite
surface-slice interface used by width comparison. -/
def sampleFamily
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {ι : Type*} [Fintype ι]
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (W : SmoothSweepout (N := N) (I := I) (M := M))
    (sample : ι → Icc (0 : ℝ) 1) :
    SurfaceSliceFamily (N := N) (I := I) (D := D) ι S :=
  { map := fun i => W.map (sample i)
    smooth := fun i => W.smooth (sample i)
    immersion := fun i => W.immersion (sample i) }

end OpenGA.RicciFlow
