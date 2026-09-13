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
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_Connection
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_MetricCompatibility
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_Smoothness
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Bochner_BochnerTensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Metric
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Sections
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Tensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Flow_RicciFlow_Solution_Defs
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

open DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

variable [FiniteDimensional Real E]

variable {H : Type*} [TopologicalSpace H]

variable {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [IsManifold I 1 M]

abbrev RicciSectionFamily : Type _ :=
  Real -> DifferentialGeometry.Geometry.Curvature.Tensor02Section (I := I) (M := M)

abbrev RicciAtFamily : Type _ :=
  Real -> (x : M) -> DifferentialGeometry.Geometry.Curvature.Tensor02At (I := I) (M := M) x

namespace RicciAtFamily

def toTensorField (Ric : RicciAtFamily (I := I) (M := M)) :
    DifferentialGeometry.PDE.RicciFlow.RicciTensorField (I := I) (M := M) Real :=
  fun t x X Y => Ric t x (DifferentialGeometry.Geometry.Curvature.vec2 X Y)

end RicciAtFamily

variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

structure SolutionFamily where
  metric : Real -> SmoothRiemannianMetric I M

namespace SolutionFamily

noncomputable def connection
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  fun t => DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I)
             (G.metric t)

noncomputable def ricciAt
    (G : SolutionFamily (I := I) (M := M)) :
    RicciAtFamily (I := I) (M := M) :=
  fun t x => metricRicciAt (I := I) (M := M) (G.metric t) x

noncomputable def scalar
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> M -> Real :=
  fun t x => metricScalarAt (I := I) (M := M) (G.metric t) x

noncomputable def rm04
    (G : SolutionFamily (I := I) (M := M)) :
    Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M) :=
  fun t => metricRm04 (I := I) (M := M) (G.metric t)

noncomputable def ricci
    (G : SolutionFamily (I := I) (M := M)) :
    RicciSectionFamily (I := I) (M := M) :=
  fun t => metricRicci (I := I) (M := M) (G.metric t)

def MetricCompatibleOn
    (G : SolutionFamily (I := I) (M := M))
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) : Prop :=
  forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D,
    DifferentialGeometry.Geometry.Connection.IsMetricCompatibleGen (I := I)
      (G.connection (t : Real)) (G.metric (t : Real))

end SolutionFamily

structure SolutionOn (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) where
  base : SolutionFamily (I := I) (M := M)

namespace SolutionOn

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCompatible {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    S.base.MetricCompatibleOn D := by
  intro t
  exact DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
    (I := I) (S.base.metric (t : Real))

def family {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D where
  metric := S.base.metric
  connection := S.base.connection
  metricCompatible := S.metricCompatible

def ricci {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    RicciSectionFamily (I := I) (M := M) :=
  S.base.ricci

def ricciAt {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    RicciAtFamily (I := I) (M := M) :=
  S.base.ricciAt

def scalar {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  S.base.scalar

end SolutionOn

def MetricVariationEquationOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  DifferentialGeometry.PDE.RicciFlow.MetricConnectionFamilyVariationEquationOn (I := I) S.family
    (RicciAtFamily.toTensorField (I := I) S.ricciAt)

def ricciNorm
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)

structure IsSolutionOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  smoothMetric : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn (I := I) (M := M) D
    S.family.metric
  smoothConnection : DifferentialGeometry.Geometry.Connection.ConnectionFamilySmoothOn (I := I)
    (M := M) S.family
  equation : MetricVariationEquationOn (I := I) S
  scalarCont : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
    (D.carrier ×ˢ (Set.univ : Set M))
  scalarTime :
    ∀ {K : Set Real} {t : Real}, t ∈ K -> K ⊆ D.carrier -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => S.scalar s x) K t
  ricciCont :
    DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      D.carrier
      (fun t x => S.ricci t x)
  rm04Cont :
    DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
      D.carrier
      (fun t x => S.base.rm04 t x)
  ricciNormSpace :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (ricciNorm (I := I) S t) x
  ricciNormGrad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (ricciNorm (I := I) S t) y) x

structure ScalarSTContOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  scalar_continuousOn : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
    (D.carrier ×ˢ (Set.univ : Set M))

structure CanonicalScalarRegularOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  scalar_continuousOn : ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
    (D.carrier ×ˢ (Set.univ : Set M))
  scalar_time_within :
    ∀ {K : Set Real} {t : Real}, t ∈ K -> K ⊆ D.carrier -> ∀ x : M,
      DifferentiableWithinAt Real (fun s : Real => S.scalar s x) K t
  scalar_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar t) x
  scalar_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (S.scalar t) y) x
  scalar_mul_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% ((S.scalar t) • fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (S.scalar t) y)) x
  scalar_sq_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => S.scalar t y ^ 2) x
  scalar_sq_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2) y) x
  scalar_sq_div_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => S.scalar t y ^ 2 / 3) x
  scalar_sq_div_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2 / 3) y) x
  scalar_grad_sub_const :
    ∀ t : Real, t ∈ D.carrier -> ∀ c : Real, ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z - c) y) x
  scalar_grad_const_mul_sub_const :
    ∀ t : Real, t ∈ D.carrier -> ∀ a c : Real, ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (fun z : M => a * (S.scalar t z - c)) y) x

structure CanonicalRicciRegularOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  ricci_cont :
    DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      D.carrier
      (fun t x => S.ricci t x)
  rm04_cont :
    DifferentialGeometry.Geometry.Curvature.tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
      D.carrier
      (fun t x => S.base.rm04 t x)
  ricci_norm_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (ricciNorm (I := I) S t) x
  ricci_norm_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Geometry.Operator.gradientFun (I := I) (S.family.metric t)
          (ricciNorm (I := I) S t) y) x

end DifferentialGeometry.PDE.RicciFlow

end
