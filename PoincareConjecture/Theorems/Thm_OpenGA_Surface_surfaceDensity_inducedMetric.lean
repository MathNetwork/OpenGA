import Definitions.Def_OpenGA_ImmersedMetric
import Definitions.Def_OpenGA_SurfaceArea
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.VectorBundle.Basic

noncomputable section

open Bundle MeasureTheory Set

open scoped Manifold ContDiff

open DifferentialGeometry OpenGA.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]

open OpenGA.Surface

theorem OpenGA.Surface.surfaceDensity_inducedMetric
    (g : SmoothRiemannianMetric J M) (f : N → M) (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (p : SurfaceParameter → N) {u : SurfaceParameter}
    (hp : MDifferentiableAt 𝓘(ℝ, SurfaceParameter) I p u) :
    surfaceDensity (inducedMetric g f hf hinj) p u = surfaceDensity g (f ∘ p) u := by sorry
