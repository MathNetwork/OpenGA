import Theorems.Thm_OpenGA_RicciFlow_surfaceDensity_comp
import Definitions.Def_OpenGA_SurfaceArea
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section

open Bundle Matrix MeasureTheory Set Filter

open scoped Manifold ContDiff Topology

open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open OpenGA.RicciFlow

theorem OpenGA.RicciFlow.patchArea_comp
    (g : SmoothRiemannianMetric I M) (f : SurfaceParameter → M)
    {φ : SurfaceParameter → SurfaceParameter} {Ω : Set SurfaceParameter}
    (hΩ : MeasurableSet Ω) (hφ : ∀ u ∈ Ω, DifferentiableAt ℝ φ u)
    (hinj : Set.InjOn φ Ω)
    (hf : ∀ v ∈ φ '' Ω, MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I f v) :
    patchArea g (f ∘ φ) Ω = patchArea g f (φ '' Ω) := by sorry
