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

open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle

open scoped Bundle Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

variable [FiniteDimensional Real E] [CompleteSpace E]

variable {H : Type*} [TopologicalSpace H]

variable {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

 instance _root_.DifferentialGeometry.Geometry.Connection.tangentSpace_finiteDimensional_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)

def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x
    ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x v) p

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tangentConstAt_self (x : M) (v : TangentSpace I x) :
    tangentConstAt (I := I) x v x = v := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_self_continuousLinearMapAt
    (𝕜 := Real) (I := I) x v

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p)) x := by
  unfold tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x) (p := x)
    ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt Real x v)
    (mem_baseSet_trivializationAt E (TangentSpace I) x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      MDifferentiableAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    g.contMDiff.mdifferentiableAt (by simp)
  have htotal :
      MDifferentiableAt I (I.prod 𝓘(Real, Real))
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact MDifferentiableAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [mdifferentiableAt_totalSpace] at htotal
  exact htotal.2

def directionalDerivAlong
    (X : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M) : Real :=
  mvfderiv (I := I) f x (X x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem directionalDerivAlong_add_left
    (X X' : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M) :
  directionalDerivAlong (I := I) (X + X') f x =
      directionalDerivAlong (I := I) X f x +
        directionalDerivAlong (I := I) X' f x := by
  unfold directionalDerivAlong
  rw [Pi.add_apply, map_add]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_add_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDerivAlong (I := I) X (f + h) x =
      directionalDerivAlong (I := I) X f x +
        directionalDerivAlong (I := I) X h x := by
  unfold directionalDerivAlong
  rw [mvfderiv_add hf hh]
  rw [add_apply]

def koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) : Real :=
  directionalDerivAlong (I := I) X (fun y : M => g.inner y (Y y) (Z y)) x +
    directionalDerivAlong (I := I) Y (fun y : M => g.inner y (Z y) (X y)) x -
    directionalDerivAlong (I := I) Z (fun y : M => g.inner y (X y) (Y y)) x -
    g.inner x (X x) (VectorField.mlieBracket I Y Z x) +
    g.inner x (Y x) (VectorField.mlieBracket I Z X x) +
    g.inner x (Z x) (VectorField.mlieBracket I X Y x)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_add_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (X X' Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g (X + X') Y Z x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X' Y Z x := by
  have hZX := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hZ hX
  have hZX' := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hZ hX'
  have hXY := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hX hY
  have hX'Y := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hX' hY
  unfold koszulScalar directionalDerivAlong
  rw [show (fun y : M => g.inner y (Z y) ((X + X') y)) =
      (fun y : M => g.inner y (Z y) (X y)) +
        (fun y : M => g.inner y (Z y) (X' y)) by
        funext y; simp [Pi.add_apply]]
  rw [mvfderiv_add hZX hZX']
  rw [show (fun y : M => g.inner y ((X + X') y) (Y y)) =
      (fun y : M => g.inner y (X y) (Y y)) +
        (fun y : M => g.inner y (X' y) (Y y)) by
        funext y; simp [Pi.add_apply]]
  rw [mvfderiv_add hXY hX'Y]
  rw [VectorField.mlieBracket_add_right (I := I) (V := Z) hX hX']
  rw [VectorField.mlieBracket_add_left (I := I) (W := Y) hX hX']
  simp [Pi.add_apply, map_add, add_apply]
  abel_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_add_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (X Y Y' Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X (Y + Y') Z x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X Y' Z x := by
  have hYZ := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hY hZ
  have hY'Z := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hY' hZ
  have hXY := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hX hY
  have hXY' := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hX hY'
  unfold koszulScalar
  rw [show (fun y : M => g.inner y ((Y + Y') y) (Z y)) =
      (fun y : M => g.inner y (Y y) (Z y)) +
        (fun y : M => g.inner y (Y' y) (Z y)) by
        funext y; simp [Pi.add_apply]]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_add_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) X x hYZ hY'Z]
  rw [directionalDerivAlong_add_left]
  rw [show (fun y : M => g.inner y (X y) ((Y + Y') y)) =
      (fun y : M => g.inner y (X y) (Y y)) +
        (fun y : M => g.inner y (X y) (Y' y)) by
        funext y; simp [Pi.add_apply]]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_add_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) Z x hXY hXY']
  rw [VectorField.mlieBracket_add_left (I := I) (W := Z) hY hY']
  rw [VectorField.mlieBracket_add_right (I := I) (V := X) hY hY']
  simp [Pi.add_apply, map_add, add_apply]
  abel_nf

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.mvfderiv_mul_at_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    mvfderiv (I := I) (fun y : M => f y * h y) x v =
      f x * mvfderiv (I := I) h x v +
        mvfderiv (I := I) f x v * h x := by
  change mvfderiv (I := I) (f • h) x v =
      f x * mvfderiv (I := I) h x v +
        mvfderiv (I := I) f x v * h x
  rw [mvfderiv_smul hf hh]
  simp [smul_eq_mul, mul_comm]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_mul_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDerivAlong (I := I) X (fun y : M => f y * h y) x =
      f x * directionalDerivAlong (I := I) X h x +
        directionalDerivAlong (I := I) X f x * h x := by
  unfold directionalDerivAlong
  exact _root_.DifferentialGeometry.Geometry.Connection.mvfderiv_mul_at_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) (v := X x) hf hh

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_smul_fun_left_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    {f : M -> Real} (X : (p : M) -> TangentSpace I p) (h : M -> Real) (x : M) :
    directionalDerivAlong (I := I) (f • X) h x =
      f x * directionalDerivAlong (I := I) X h x := by
  unfold directionalDerivAlong
  change (mvfderiv (I := I) h x) (f x • X x) =
    f x * (mvfderiv (I := I) h x) (X x)
  rw [map_smul]
  rfl

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_smul_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g (f • X) Y Z x =
      f x * koszulScalar (I := I) g X Y Z x := by
  have hZX := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hZ hX
  have hXY := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hX hY
  unfold koszulScalar
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_smul_fun_left_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula]
  rw [show (fun y : M => g.inner y (Z y) ((f • X) y)) =
      (fun y : M => f y * g.inner y (Z y) (X y)) by
        funext y; simp]
  rw [show (fun y : M => g.inner y ((f • X) y) (Y y)) =
      (fun y : M => f y * g.inner y (X y) (Y y)) by
        funext y; simp]
  unfold directionalDerivAlong
  rw [_root_.DifferentialGeometry.Geometry.Connection.mvfderiv_mul_at_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) (v := Y x) hf hZX]
  rw [_root_.DifferentialGeometry.Geometry.Connection.mvfderiv_mul_at_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) (v := Z x) hf hXY]
  rw [VectorField.mlieBracket_smul_right (I := I) (V := Z) (W := X) hf hX]
  rw [VectorField.mlieBracket_smul_left (I := I) (V := X) (W := Y) hf hX]
  have hdfY :
      mvfderiv (I := I) f x (Y x) =
        mvfderiv (I := I) f x (Y x) := by
    rfl
  have hdfZ :
      mvfderiv (I := I) f x (Z x) =
        mvfderiv (I := I) f x (Z x) := by
    rfl
  simp only [map_add, map_smul, map_neg, smul_eq_mul,
    neg_smul, sub_eq_add_neg]
  rw [show (f • X) x = f x • X x by rfl]
  simp only [map_smul]
  rw [show
      (f x • (g.inner x) (X x)) (VectorField.mlieBracket I Y Z x) =
        f x * ((g.inner x) (X x)) (VectorField.mlieBracket I Y Z x) by rfl]
  rw [g.symm x (Y x) (X x), g.symm x (Z x) (X x)]
  ring_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_smul_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X (f • Y) Z x =
      f x * koszulScalar (I := I) g X Y Z x +
        (2 * directionalDerivAlong (I := I) X f x) *
          g.inner x (Y x) (Z x) := by
  have hYZ := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hY hZ
  have hXY := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hX hY
  unfold koszulScalar
  rw [show (fun y : M => g.inner y ((f • Y) y) (Z y)) =
      (fun y : M => f y * g.inner y (Y y) (Z y)) by
        funext y; simp]
  rw [show (fun y : M => g.inner y (X y) ((f • Y) y)) =
      (fun y : M => f y * g.inner y (X y) (Y y)) by
        funext y; simp]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_mul_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) X x hf hYZ]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_smul_fun_left_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_mul_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) Z x hf hXY]
  rw [VectorField.mlieBracket_smul_left (I := I) (W := Z) hf hY]
  rw [VectorField.mlieBracket_smul_right (I := I) (V := X) hf hY]
  have hdfZ :
      mvfderiv (I := I) f x (Z x) =
        directionalDerivAlong (I := I) Z f x := by
    rfl
  have hdfX :
      mvfderiv (I := I) f x (X x) =
        directionalDerivAlong (I := I) X f x := by
    rfl
  simp only [hdfZ, hdfX, map_add, map_smul, map_neg, smul_eq_mul,
    neg_smul, sub_eq_add_neg]
  rw [show (f • Y) x = f x • Y x by rfl]
  simp only [map_smul]
  rw [show
      (f x • (g.inner x) (Y x)) (VectorField.mlieBracket I Z X x) =
        f x * ((g.inner x) (Y x)) (VectorField.mlieBracket I Z X x) by rfl]
  rw [g.symm x (Z x) (Y x)]
  ring_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_add_third_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (X Y Z Z' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    koszulScalar (I := I) g X Y (Z + Z') x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X Y Z' x := by
  have hYZ := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hY hZ
  have hYZ' := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hY hZ'
  have hZX := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hZ hX
  have hZ'X := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hZ' hX
  have hXY := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hX hY
  unfold koszulScalar
  rw [show (fun y : M => g.inner y (Y y) ((Z + Z') y)) =
      (fun y : M => g.inner y (Y y) (Z y)) +
        (fun y : M => g.inner y (Y y) (Z' y)) by
        funext y; simp [Pi.add_apply]]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_add_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) X x hYZ hYZ']
  rw [show (fun y : M => g.inner y ((Z + Z') y) (X y)) =
      (fun y : M => g.inner y (Z y) (X y)) +
        (fun y : M => g.inner y (Z' y) (X y)) by
        funext y; simp [Pi.add_apply]]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_add_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) Y x hZX hZ'X]
  rw [directionalDerivAlong_add_left]
  rw [VectorField.mlieBracket_add_right (I := I) (V := Y) hZ hZ']
  rw [VectorField.mlieBracket_add_left (I := I) (W := X) hZ hZ']
  simp [Pi.add_apply, map_add, add_apply]
  abel_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_smul_third_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X Y (f • Z) x =
      f x * koszulScalar (I := I) g X Y Z x := by
  have hYZ := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hY hZ
  have hZX := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hZ hX
  have hXY := _root_.DifferentialGeometry.Geometry.Connection.mdifferentiableAt_metric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g hX hY
  unfold koszulScalar
  rw [show (fun y : M => g.inner y (Y y) ((f • Z) y)) =
      (fun y : M => f y * g.inner y (Y y) (Z y)) by
        funext y; simp]
  rw [show (fun y : M => g.inner y ((f • Z) y) (X y)) =
      (fun y : M => f y * g.inner y (Z y) (X y)) by
        funext y; simp]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_mul_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) X x hf hYZ]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_mul_fun_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) Y x hf hZX]
  rw [_root_.DifferentialGeometry.Geometry.Connection.directionalDerivAlong_smul_fun_left_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula]
  rw [VectorField.mlieBracket_smul_right (I := I) (V := Y) hf hZ]
  rw [VectorField.mlieBracket_smul_left (I := I) (W := X) hf hZ]
  have hdfX :
      mvfderiv (I := I) f x (X x) =
        directionalDerivAlong (I := I) X f x := by
    rfl
  have hdfY :
      mvfderiv (I := I) f x (Y x) =
        directionalDerivAlong (I := I) Y f x := by
    rfl
  simp only [hdfX, hdfY, map_add, map_smul, map_neg, smul_eq_mul,
    neg_smul, sub_eq_add_neg]
  rw [show (f • Z) x = f x • Z x by rfl]
  simp only [map_smul]
  rw [show
      (f x • (g.inner x) (Z x)) (VectorField.mlieBracket I X Y x) =
        f x * ((g.inner x) (Z x)) (VectorField.mlieBracket I X Y x) by rfl]
  rw [g.symm x (Y x) (Z x), g.symm x (X x) (Z x)]
  ring_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_tensorial_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X : (p : M) -> TangentSpace I p =>
      koszulScalar (I := I) g X Y Z x) x where
  smul := by
    intro f X hf hX
    simpa [smul_eq_mul] using
      _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_smul_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y Z x hf hX hY hZ
  add := by
    intro X X' hX hX'
    exact _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_add_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X X' Y Z x hX hX' hY hZ

def koszulCovectorField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) :
    Module.Dual Real (TangentSpace I x) :=
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
    ((1 / 2 : Real) *
      koszulScalar (I := I) g X Y (tangentConstAt (I := I) x (B i)) x) •
        (B.coord i)

def koszulNablaField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (koszulCovectorField (I := I) g X Y x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem koszulNablaField_inner_eq_covector
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (Z : TangentSpace I x) :
    g.inner x (koszulNablaField (I := I) g X Y x) Z =
      koszulCovectorField (I := I) g X Y x Z := by
  unfold koszulNablaField
  exact inner_metricSharp (I := I) g x
    (koszulCovectorField (I := I) g X Y x) Z

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulCovectorField_smul_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g (f • X) Y x =
      f x • koszulCovectorField (I := I) g X Y x := by
  ext v
  unfold koszulCovectorField
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x
        ((Module.finBasis Real (TangentSpace I x)) i) :
          (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)
  rw [_root_.DifferentialGeometry.Geometry.Connection.koszulScalar_smul_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y
    (tangentConstAt (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)) x hf hX hY hZi]
  ring

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulCovectorField_add_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g (X + X') Y x =
      koszulCovectorField (I := I) g X Y x +
        koszulCovectorField (I := I) g X' Y x := by
  ext v
  unfold koszulCovectorField
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x
        ((Module.finBasis Real (TangentSpace I x)) i) :
          (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)
  rw [_root_.DifferentialGeometry.Geometry.Connection.koszulScalar_add_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X X' Y
    (tangentConstAt (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)) x hX hX' hY hZi]
  ring

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_smul_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g (f • X) Y x =
      f x • koszulNablaField (I := I) g X Y x := by
  unfold koszulNablaField metricSharp
  rw [_root_.DifferentialGeometry.Geometry.Connection.koszulCovectorField_smul_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y x hf hX hY]
  exact LinearEquiv.map_smul (metricFlatEquiv (I := I) g x).symm
    (f x) (koszulCovectorField (I := I) g X Y x)

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_add_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g (X + X') Y x =
      koszulNablaField (I := I) g X Y x +
        koszulNablaField (I := I) g X' Y x := by
  unfold koszulNablaField metricSharp
  rw [_root_.DifferentialGeometry.Geometry.Connection.koszulCovectorField_add_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X X' Y x hX hX' hY]
  exact LinearEquiv.map_add (metricFlatEquiv (I := I) g x).symm
    (koszulCovectorField (I := I) g X Y x)
    (koszulCovectorField (I := I) g X' Y x)

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulCovectorField_add_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (X Y Y' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    koszulCovectorField (I := I) g X (Y + Y') x =
      koszulCovectorField (I := I) g X Y x +
        koszulCovectorField (I := I) g X Y' x := by
  ext v
  unfold koszulCovectorField
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x
        ((Module.finBasis Real (TangentSpace I x)) i) :
          (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)
  rw [_root_.DifferentialGeometry.Geometry.Connection.koszulScalar_add_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y Y'
    (tangentConstAt (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)) x hX hY hY' hZi]
  ring

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_add_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (X Y Y' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    koszulNablaField (I := I) g X (Y + Y') x =
      koszulNablaField (I := I) g X Y x +
        koszulNablaField (I := I) g X Y' x := by
  unfold koszulNablaField metricSharp
  rw [_root_.DifferentialGeometry.Geometry.Connection.koszulCovectorField_add_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y Y' x hX hY hY']
  exact LinearEquiv.map_add (metricFlatEquiv (I := I) g x).symm
    (koszulCovectorField (I := I) g X Y x)
    (koszulCovectorField (I := I) g X Y' x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.metric_inner_sum_basis_coord_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x))
    (Y v : TangentSpace I x) :
    (∑ i, g.inner x Y (B i) * (B.coord i) v) = g.inner x Y v := by
  calc
    (∑ i, g.inner x Y (B i) * (B.coord i) v)
        = ∑ i, (B.repr v i) * g.inner x Y (B i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [B.coord_apply, mul_comm]
    _ = g.inner x Y (∑ i, (B.repr v i) • B i) := by
          calc
            (∑ i, (B.repr v i) * g.inner x Y (B i))
                = ∑ i, g.inner x Y ((B.repr v i) • B i) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  simp [map_smul, smul_eq_mul]
            _ = g.inner x Y (∑ i, (B.repr v i) • B i) := by
                  rw [map_sum]
    _ = g.inner x Y v := by
          rw [B.sum_repr v]

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulCovectorField_smul_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g X (f • Y) x =
      f x • koszulCovectorField (I := I) g X Y x +
        directionalDerivAlong (I := I) X f x • metricFlatLinear (I := I) g x (Y x) := by
  ext v
  unfold koszulCovectorField
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul, metricFlatLinear_apply]
  rw [Finset.mul_sum]
  have hbasis :
      (∑ i : Fin (Module.finrank Real (TangentSpace I x)),
          g.inner x (Y x) ((Module.finBasis Real (TangentSpace I x)) i) *
            ((Module.finBasis Real (TangentSpace I x)).coord i) v) =
        g.inner x (Y x) v :=
    _root_.DifferentialGeometry.Geometry.Connection.metric_inner_sum_basis_coord_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g
      (Module.finBasis Real (TangentSpace I x)) (Y x) v
  rw [← hbasis]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x
        ((Module.finBasis Real (TangentSpace I x)) i) :
          (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)
  rw [_root_.DifferentialGeometry.Geometry.Connection.koszulScalar_smul_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y
    (tangentConstAt (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)) x hf hX hY hZi]
  rw [tangentConstAt_self]
  ring_nf

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_smul_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g X (f • Y) x =
      f x • koszulNablaField (I := I) g X Y x +
        directionalDerivAlong (I := I) X f x • Y x := by
  unfold koszulNablaField metricSharp
  rw [_root_.DifferentialGeometry.Geometry.Connection.koszulCovectorField_smul_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y x hf hX hY]
  rw [LinearEquiv.map_add, LinearEquiv.map_smul]
  congr 1
  change (metricFlatEquiv (I := I) g x).symm
      (directionalDerivAlong (I := I) X f x • metricFlatLinear (I := I) g x (Y x)) =
    directionalDerivAlong (I := I) X f x • Y x
  rw [LinearEquiv.map_smul]
  congr 1
  exact LinearEquiv.symm_apply_apply (metricFlatEquiv (I := I) g x) (Y x)

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_tensorial_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun X : (p : M) -> TangentSpace I p =>
      koszulNablaField (I := I) g X Y x) x where
  smul := by
    intro f X hf hX
    exact _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_smul_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y x hf hX hY
  add := by
    intro X X' hX hX'
    exact _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_add_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X X' Y x hX hX' hY

def koszulNablaAt
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (v : TangentSpace I x) : TangentSpace I x :=
  koszulNablaField (I := I) g (tangentConstAt (I := I) x v) Y x

def KoszulCovectorCorrectAt
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) : Prop :=
  forall Z : (p : M) -> TangentSpace I p,
    MDiffAt (T% Z) x ->
      koszulCovectorField (I := I) g X Y x (Z x) =
        (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulCovectorField_apply_of_mdiff
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulCovectorField (I := I) g X Y x (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x := by
  classical
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  let Φ : ((p : M) -> TangentSpace I p) -> Real :=
    fun Z => (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x
  have hΦ : TensorialAt I E Φ x := by
    refine { smul := ?_, add := ?_ }
    · intro f Z hf hZ
      dsimp [Φ]
      rw [_root_.DifferentialGeometry.Geometry.Connection.koszulScalar_smul_third_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y Z x hf hX hY hZ]
      ring
    · intro Z Z' hZ hZ'
      dsimp [Φ]
      rw [_root_.DifferentialGeometry.Geometry.Connection.koszulScalar_add_third_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g X Y Z Z' x hX hY hZ hZ']
      ring
  have hEq :
      koszulCovectorField (I := I) g X Y x =
        TensorialAt.mkHom (I := I) (F := E) Φ x hΦ := by
    apply LinearMap.ext
    intro v
    rw [← B.sum_repr v]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul]
    congr 1
    have hmk := TensorialAt.mkHom_apply (I := I) (F := E) hΦ
      (mdifferentiableAt_tangentConstAt_self (I := I) x (B i))
    rw [tangentConstAt_self] at hmk
    have hmk' :
        (TensorialAt.mkHom (I := I) (F := E) Φ x hΦ) (B i) =
          (1 / 2 : Real) * koszulScalar (I := I) g X Y
            (tangentConstAt (I := I) x (B i)) x := by
      simpa [Φ] using hmk
    change (koszulCovectorField (I := I) g X Y x) (B i) =
      (TensorialAt.mkHom (I := I) (F := E) Φ x hΦ) (B i)
    rw [hmk']
    simp [koszulCovectorField, B, Finsupp.single_apply]
  rw [hEq]
  exact TensorialAt.mkHom_apply (I := I) (F := E) hΦ hZ

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulCovectorCorrectAt_of_mdiff
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    KoszulCovectorCorrectAt (I := I) g X Y x := by
  intro Z hZ
  exact koszulCovectorField_apply_of_mdiff (I := I) g X Y Z x hX hY hZ

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_eval_of_covector_correct
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hcorrect : KoszulCovectorCorrectAt (I := I) g X Y x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (koszulNablaField (I := I) g X Y x) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x := by
  rw [koszulNablaField_inner_eq_covector]
  exact hcorrect Z hZ

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_inner_eq_koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (koszulNablaField (I := I) g X Y x) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x :=
  koszulNablaField_eval_of_covector_correct (I := I) g X Y Z x
    (koszulCovectorCorrectAt_of_mdiff (I := I) g X Y x hX hY) hZ

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_pair_sum
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) :
    (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x +
      (1 / 2 : Real) * koszulScalar (I := I) g X Z Y x =
        directionalDerivAlong (I := I) X (fun y : M => g.inner y (Y y) (Z y)) x := by
  unfold koszulScalar
  rw [show (fun y : M => g.inner y (Z y) (Y y)) =
      (fun y : M => g.inner y (Y y) (Z y)) by
      funext y; exact g.symm y (Z y) (Y y)]
  rw [show (fun y : M => g.inner y (Y y) (X y)) =
      (fun y : M => g.inner y (X y) (Y y)) by
      funext y; exact g.symm y (Y y) (X y)]
  rw [show (fun y : M => g.inner y (X y) (Z y)) =
      (fun y : M => g.inner y (Z y) (X y)) by
      funext y; exact g.symm y (X y) (Z y)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Z) (W := Y) (x := x)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Y) (W := X) (x := x)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := X) (W := Z) (x := x)]
  simp only [map_neg]
  ring

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_eq_of_first_eq_at
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x)
    (hxx : X x = X' x) :
    koszulNablaField (I := I) g X Y x =
      koszulNablaField (I := I) g X' Y x := by
  unfold koszulNablaField
  congr 1
  ext v
  unfold koszulCovectorField
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x (B i) :
        (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x (B i)
  have hK :
      koszulScalar (I := I) g X Y
          (tangentConstAt (I := I) x (B i)) x =
        koszulScalar (I := I) g X' Y
          (tangentConstAt (I := I) x (B i)) x :=
    TensorialAt.pointwise
      (I := I) (F := E)
      (_root_.DifferentialGeometry.Geometry.Connection.koszulScalar_tensorial_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g Y
        (tangentConstAt (I := I) x (B i)) x hY hZi)
      hX hX' hxx
  rw [hK]

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaAt_eq_of_extension
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) (hXx : X x = v) :
    koszulNablaAt (I := I) g Y x v =
      koszulNablaField (I := I) g X Y x := by
  unfold koszulNablaAt
  have hconst :
      (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p) x =
        X x := by
    rw [tangentConstAt_self]
    exact hXx.symm
  exact koszulNablaField_eq_of_first_eq_at (I := I) g
    (tangentConstAt (I := I) x v) X Y x
    (mdifferentiableAt_tangentConstAt_self (I := I) x v) hX hY hconst

def leviCivitaConnectionCandidateAt
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x := by
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  let W : Fin (Module.finrank Real (TangentSpace I x)) -> TangentSpace I x := fun i =>
    koszulNablaField (I := I) g (tangentConstAt (I := I) x (B i)) Y x
  exact LinearMap.toContinuousLinearMap
    (B.constr Real W)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem leviCivitaConnectionCandidateAt_apply_basis
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (i : Fin (Module.finrank Real (TangentSpace I x))) :
    leviCivitaConnectionCandidateAt (I := I) g Y x
        ((Module.finBasis Real (TangentSpace I x)) i) =
      koszulNablaField (I := I) g
        (tangentConstAt (I := I) x ((Module.finBasis Real (TangentSpace I x)) i)) Y x := by
  classical
  unfold leviCivitaConnectionCandidateAt
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  let W : Fin (Module.finrank Real (TangentSpace I x)) -> TangentSpace I x := fun i =>
    koszulNablaField (I := I) g (tangentConstAt (I := I) x (B i)) Y x
  change LinearMap.toContinuousLinearMap (B.constr Real W) (B i) = W i
  simp [B.constr_basis (S := Real) W i]

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionCandidateAt_agreesWithField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    leviCivitaConnectionCandidateAt (I := I) g Y x (X x) =
      koszulNablaField (I := I) g X Y x := by
  classical
  let Φ : ((p : M) -> TangentSpace I p) -> TangentSpace I x :=
    fun X => koszulNablaField (I := I) g X Y x
  have hΦ : TensorialAt I E Φ x :=
    _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_tensorial_first_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g Y x hY
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    TensorialAt.mkHom (I := I) (F := E) Φ x hΦ
  have hLX : L (X x) = koszulNablaField (I := I) g X Y x := by
    simpa [Φ, L] using TensorialAt.mkHom_apply (I := I) (F := E) hΦ hX
  rw [← hLX]
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  rw [← B.sum_repr (X x)]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  congr 1
  rw [leviCivitaConnectionCandidateAt_apply_basis]
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x (B i) :
        (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x (B i)
  have hLi : L (B i) =
      koszulNablaField (I := I) g
        (tangentConstAt (I := I) x (B i)) Y x := by
    have hmk := TensorialAt.mkHom_apply (I := I) (F := E) hΦ hZi
    rw [tangentConstAt_self] at hmk
    simpa [Φ, L] using hmk
  exact hLi.symm

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionCandidateAt_agreesWithDescended
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    leviCivitaConnectionCandidateAt (I := I) g Y x v =
      koszulNablaAt (I := I) g Y x v := by
  have hfield := leviCivitaConnectionCandidateAt_agreesWithField
    (I := I) g (tangentConstAt (I := I) x v) Y x
    (mdifferentiableAt_tangentConstAt_self (I := I) x v) hY
  unfold koszulNablaAt
  convert hfield using 1
  exact congrArg (leviCivitaConnectionCandidateAt (I := I) g Y x)
    (tangentConstAt_self (I := I) x v).symm

def leviCivitaConnectionOfMetric
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) where
  toFun := fun Y x => leviCivitaConnectionCandidateAt (I := I) g Y x
  isCovariantDerivativeOnUniv := by
    refine
      { add := ?_
        leibniz := ?_ }
    · intro Y Y' x hY hY' _hx
      ext v
      rw [add_apply]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g (Y + Y') x (mdifferentiableAt_add_section hY hY') v]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g Y x hY v]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g Y' x hY' v]
      unfold koszulNablaAt
      exact _root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_add_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g
        (tangentConstAt (I := I) x v) Y Y' x
        (mdifferentiableAt_tangentConstAt_self (I := I) x v) hY hY'
    · intro Y f x hY hf _hx
      ext v
      rw [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g (f • Y) x (hf.smul_section hY) v]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g Y x hY v]
      unfold koszulNablaAt
      rw [_root_.DifferentialGeometry.Geometry.Connection.koszulNablaField_smul_second_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula (I := I) g
        (tangentConstAt (I := I) x v) Y x hf
        (mdifferentiableAt_tangentConstAt_self (I := I) x v) hY]
      congr 1
      unfold directionalDerivAlong
      rw [tangentConstAt_self]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem leviCivitaConnectionOfMetric_apply
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M) :
    leviCivitaConnectionOfMetric (I := I) g Y x =
      leviCivitaConnectionCandidateAt (I := I) g Y x := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_apply_descended
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    leviCivitaConnectionOfMetric (I := I) g Y x v =
      koszulNablaAt (I := I) g Y x v := by
  rw [leviCivitaConnectionOfMetric_apply]
  exact leviCivitaConnectionCandidateAt_agreesWithDescended (I := I) g Y x hY v

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x := by
  rw [leviCivitaConnectionOfMetric_apply_descended (I := I) g Y x hY (X x)]
  rw [koszulNablaAt_eq_of_extension (I := I) g X Y x hX hY (X x) rfl]
  exact koszulNablaField_inner_eq_koszulScalar (I := I) g X Y Z x hX hY hZ

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isMetricCompatible
    (g : SmoothRiemannianMetric I M) :
    IsMetricCompatibleGen (I := I) (leviCivitaConnectionOfMetric (I := I) g) g := by
  intro x X Y Z hX hY hZ
  change directionalDerivAlong (I := I) X
      (fun y : M => g.inner y (Y y) (Z y)) x =
    g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) +
      g.inner x (Y x) ((leviCivitaConnectionOfMetric (I := I) g Z x) (X x))
  have hXYZ := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := I) g X Y Z x hX hY hZ
  have hXZY := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := I) g X Z Y x hX hZ hY
  calc
    directionalDerivAlong (I := I) X
        (fun y : M => g.inner y (Y y) (Z y)) x
        = (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x +
            (1 / 2 : Real) * koszulScalar (I := I) g X Z Y x := by
          exact (koszulScalar_pair_sum (I := I) g X Y Z x).symm
    _ = g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) +
          g.inner x ((leviCivitaConnectionOfMetric (I := I) g Z x) (X x)) (Y x) := by
          rw [← hXYZ, ← hXZY]
    _ = g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) +
          g.inner x (Y x) ((leviCivitaConnectionOfMetric (I := I) g Z x) (X x)) := by
          rw [g.symm x ((leviCivitaConnectionOfMetric (I := I) g Z x) (X x)) (Y x)]

end

end DifferentialGeometry.Geometry.Connection
