import Definitions.Def_DifferentialGeometry_SmoothRiemannianMetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Area density of a parametrized surface

The pullback metric is computed from the manifold derivative of the actual
surface map. Area is its Gram determinant density integrated against Euclidean
parameter volume, with multiplicity. The metric type reuses DifferentialGeometry
and Mathlib. No orientation or global tangent frame is chosen on the surface.
-/

noncomputable section

open Bundle Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry

namespace OpenGA.RicciFlow

abbrev SurfaceParameter := EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-- The two images of the standard orthonormal parameter vectors under `df`. -/
def surfaceTangent (f : SurfaceParameter → M) (u : SurfaceParameter) (i : Fin 2) :
    TangentSpace I (f u) :=
  mfderiv 𝓘(ℝ, SurfaceParameter) I f u (EuclideanSpace.basisFun (Fin 2) ℝ i)

/-- The induced metric matrix of a parametrized surface. -/
def surfaceMetricMatrix (g : SmoothRiemannianMetric I M)
    (f : SurfaceParameter → M) (u : SurfaceParameter) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => g.inner (f u) (surfaceTangent (I := I) f u i) (surfaceTangent (I := I) f u j)

/-- Parametrized area density relative to Euclidean parameter volume. -/
def surfaceDensity (g : SmoothRiemannianMetric I M)
    (f : SurfaceParameter → M) (u : SurfaceParameter) : ℝ :=
  Real.sqrt (surfaceMetricMatrix g f u).det

/-- Area of a fixed parameter domain, with multiplicity. -/
def patchArea (g : SmoothRiemannianMetric I M) (f : SurfaceParameter → M)
    (Ω : Set SurfaceParameter) : ℝ :=
  ∫ u in Ω, surfaceDensity g f u

end OpenGA.RicciFlow
