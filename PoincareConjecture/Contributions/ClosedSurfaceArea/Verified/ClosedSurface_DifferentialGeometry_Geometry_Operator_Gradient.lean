import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bundle
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.VectorBundle.Basic
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs

noncomputable section

open Bundle Manifold Set MeasureTheory

open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Integral.DivergenceTheorem
end DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry

namespace Geometry

namespace Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def metricFlatLinear (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    rw [map_add, add_apply]
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    rw [map_smul, smul_apply]

omit [Module.Finite ℝ E] in
@[simp] lemma metricFlatLinear_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatLinear (I := I) g x v w = g.inner x v w := rfl

omit [Module.Finite ℝ E] in
lemma metricFlatLinear_injective (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (metricFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : ∀ z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L z) hvw
    simp only [metricFlatLinear_apply] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub, sub_apply]
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl 0) (hzero (v - w) ▸ hpos)

 instance _root_.DifferentialGeometry.Geometry.Operator.tangentSpace_finiteDimensional_closedSurface_DifferentialGeometry_Geometry_Operator_Gradient (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
 lemma _root_.DifferentialGeometry.Geometry.Operator.metricFlatLinear_finrank_eq_closedSurface_DifferentialGeometry_Geometry_Operator_Gradient (x : M) :
    Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I x →ₗ[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm

def metricFlatMap (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) :=
  LinearMap.linearEquivOfInjective
    (metricFlatLinear (I := I) g x)
    (metricFlatLinear_injective (I := I) g x)
    (_root_.DifferentialGeometry.Geometry.Operator.metricFlatLinear_finrank_eq_closedSurface_DifferentialGeometry_Geometry_Operator_Gradient (I := I) (M := M) x)

@[simp] lemma metricFlatMap_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatMap (I := I) g x v w = g.inner x v w := rfl

lemma metricFlatMap_apply_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x ((metricFlatMap (I := I) g x).symm α) w = α w := by
  have h := (metricFlatMap (I := I) g x).apply_symm_apply α
  have hh : metricFlatMap (I := I) g x ((metricFlatMap (I := I) g x).symm α) w = α w :=
    congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L w) h
  rw [metricFlatMap_apply] at hh
  exact hh

def metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) : TangentSpace I x :=
  (metricFlatMap (I := I) g x).symm α

lemma inner_metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x (metricSharp (I := I) g x α) w = α w :=
  metricFlatMap_apply_symm (I := I) g x α w

end Operator

end Geometry

end DifferentialGeometry

end
