import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_TimeInterval
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_LocalFrameRegularity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_Section
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_MetricCompatibility
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Sections
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Tensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_Family_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_CotangentRiemannian
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Operator_Gradient
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Operator_Operators
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Operator_RoughLaplacian
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Auxiliary_PredualBasis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_CotangentRiemannian
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_NablaOnTensors
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_LocalFrameRegularity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Metric
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_MetricCompatibility
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Smooth
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Tangent
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_TangentMetric
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bundle
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
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
import Mathlib.Order.Interval.Set.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Cases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Bundle

namespace DifferentialGeometry.Tensor.Coordinates
end DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor.Coordinates

open DifferentialGeometry.Tensor0SBundle

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

variable [FiniteDimensional Real E] [CompleteSpace E]

variable {H : Type*} [TopologicalSpace H]

variable {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_homSection_contMDiffAt
    {ι : Type*} [Finite ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun y : M =>
        (⟨y, leviCivitaConnectionOfMetric (I := I) g σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x :=
  covariantDerivative_homSection_contMDiffAt_of_coeff
    (I := I) (leviCivitaConnectionOfMetric (I := I) g) e b hx hσdiff hσ
    (fun i k j => lc_christoffel_contMDiffAt (I := I) e b g hx i j k)

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M)
      (leviCivitaConnectionOfMetric (I := I) g) ∞ := by
  intro u hu
  refine ⟨?_⟩
  intro σ hσ x hx
  let e : Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M) :=
    trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis Real E
  have hxBase : x ∈ e.baseSet := by
    simp [e]
  have hσAtTop :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) x :=
    hσ.contMDiffAt (hu.mem_nhds hx)
  have hσAt :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x :=
    hσAtTop.of_le (by simp)
  have hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y := by
    filter_upwards [hu.mem_nhds hx] with y hy
    have hyTop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) y :=
      hσ.contMDiffAt (hu.mem_nhds hy)
    have hyOne :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞) (T% σ) y :=
      hyTop.of_le (by simp)
    exact hyOne.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  exact
    (leviCivitaConnectionOfMetric_homSection_contMDiffAt
      (I := I) e b g hxBase hσdiff hσAt).contMDiffWithinAt

end DifferentialGeometry.Geometry.Connection

end
