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

theorem OpenGA.RicciFlow.surfaceDensity_comp
    (g : SmoothRiemannianMetric I M) (f : SurfaceParameter → M)
    {φ : SurfaceParameter → SurfaceParameter} {u : SurfaceParameter}
    {A : SurfaceParameter →L[ℝ] SurfaceParameter} (hφ : HasFDerivAt φ A u)
    (hf : MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I f (φ u)) :
    surfaceDensity g (f ∘ φ) u =
      |(LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearMap).det| *
      surfaceDensity g f (φ u) := by sorry
