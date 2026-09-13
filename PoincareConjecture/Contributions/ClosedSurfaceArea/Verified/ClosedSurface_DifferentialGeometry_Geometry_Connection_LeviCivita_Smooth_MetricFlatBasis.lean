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
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Verified.ClosedSurface_DifferentialGeometry_Analysis_TimeInterval
import Verified.ClosedSurface_DifferentialGeometry_Bundle_LocalFrameRegularity
import Verified.ClosedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Basic
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_MetricCompatibility
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Basic
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Field
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Sections
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_Family_Basic
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_CotangentRiemannian
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Operator_Gradient
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Operator_Operators
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Operator_RoughLaplacian
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Auxiliary_PredualBasis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_CotangentRiemannian
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_NablaOnTensors
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_FiberMetric_Tensor0SMetric
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_LocalFrameRegularity
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Metric
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_MetricCompatibility
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Smooth
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Tangent
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_TangentMetric

open DifferentialGeometry.Geometry.Curvature

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

 def _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E) (g : SmoothRiemannianMetric I M)
    (i j : ι) (y : M) : Real :=
  g.inner y (e.localFrame b i y) (e.localFrame b j y)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% (e.localFrame b i)) x :=
  (e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
    e.open_baseSet hx i

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g i j y) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun y : M =>
                TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)))
        x :=
    (g.contMDiff.contMDiffAt (x := x)).of_le (by simp)
  have hi := _root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx i
  have hj := _root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx j
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun y : M =>
          (⟨y, _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g i j y⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x := by
    simpa [_root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis] using
      ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hj
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_deriv_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (a i j : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I)
          (fun q : M => _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g i j q)
          y (e.localFrame b a y)) x := by
  exact mvfderiv_apply_contMDiffAt_of_section
    (I := I)
    (f := fun q : M => _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g i j q)
    (X := e.localFrame b a)
    (_root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx i j)
    (_root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx a)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localMetricBracket_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        g.inner y (e.localFrame b i y)
          (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k) y)) x := by
  have : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  have : IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have hi := _root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx i
  have hj := _root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx j
  have hk := _root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx k
  have hbr :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k))) x := by
    simpa using
      (ContMDiffAt.mlieBracket_vectorField
        (I := I) (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
        hj hk (by simp))
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun y : M =>
                TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)))
        x :=
    (g.contMDiff.contMDiffAt (x := x)).of_le (by simp)
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun y : M =>
          (⟨y,
            g.inner y (e.localFrame b i y)
              (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k) y)⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x := by
    exact ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hbr
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.koszulScalar_localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
          (e.localFrame b k) y) x := by
  have h1 := _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_deriv_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx i j k
  have h2 := _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_deriv_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx j k i
  have h3 := _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_deriv_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx k i j
  have h4 := _root_.DifferentialGeometry.Geometry.Connection.localMetricBracket_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx i j k
  have h5 := _root_.DifferentialGeometry.Geometry.Connection.localMetricBracket_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx j k i
  have h6 := _root_.DifferentialGeometry.Geometry.Connection.localMetricBracket_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx k i j
  have hsum := (((h1.add h2).sub h3).sub h4).add h5 |>.add h6
  simp only [_root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis] at hsum
  unfold koszulScalar directionalDerivAlong
  refine hsum.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun _ => rfl

 noncomputable def _root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} (b : Module.Basis ι Real E) (i : ι) :
    E →L[Real] Real :=
  LinearMap.toContinuousLinearMap (b.coord i)

 noncomputable def _root_.DifferentialGeometry.Geometry.Connection.basisBilin_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} (b : Module.Basis ι Real E) (i j : ι) :
    E →L[Real] E →L[Real] Real :=
  (_root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b i).smulRight (_root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b j)

omit [CompleteSpace E] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.basisBilin_apply_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} (b : Module.Basis ι Real E) (i j : ι)
    (v w : E) :
    _root_.DifferentialGeometry.Geometry.Connection.basisBilin_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b i j v w = b.coord i v * b.coord j w := by
  simp [_root_.DifferentialGeometry.Geometry.Connection.basisBilin_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis, _root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis]

noncomputable def localMetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (y : M) :
    E →L[Real] E →L[Real] Real :=
  ∑ i : ι, ∑ j : ι,
    _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g i j y • _root_.DifferentialGeometry.Geometry.Connection.basisBilin_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b i j

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localMetricFlatBasis_apply_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (y : M) (v w : E) :
    localMetricFlatBasis (I := I) e b g y v w =
      ∑ i : ι, ∑ j : ι,
        _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g i j y * b.coord i v * b.coord j w := by
  simp [localMetricFlatBasis, _root_.DifferentialGeometry.Geometry.Connection.basisBilin_apply_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis, mul_assoc]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localFrame_sum_coord_smul_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
    {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (v : E) :
    (∑ i : ι, b.coord i v • e.localFrame b i x) = e.symmL Real x v := by
  calc
    (∑ i : ι, b.coord i v • e.localFrame b i x)
        = ∑ i : ι, b.coord i v • e.symmL Real x (b i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
          exact congrArg ((b.coord i v) • ·) (e.symmL_apply hx (b i)).symm
    _ = e.symmL Real x (∑ i : ι, b.coord i v • b i) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp [map_smul]
    _ = e.symmL Real x v := by
          have hsum : (∑ i : ι, b.coord i v • b i) = v := by
            simp [b.sum_repr v]
          rw [hsum]

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
theorem localMetricFlatBasis_eq_inner {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) (v w : E) :
    localMetricFlatBasis (I := I) e b g x v w =
      g.inner x (e.symmL Real x v) (e.symmL Real x w) := by
  have hv := _root_.DifferentialGeometry.Geometry.Connection.localFrame_sum_coord_smul_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx v
  have hw := _root_.DifferentialGeometry.Geometry.Connection.localFrame_sum_coord_smul_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx w
  calc
    localMetricFlatBasis (I := I) e b g x v w
        = g.inner x
            (∑ i : ι, b.coord i v • e.localFrame b i x)
            (∑ j : ι, b.coord j w • e.localFrame b j x) := by
          suffices h :
              ∑ i, ∑ j, (b.repr v) i *
                  ((b.repr w) j * ((g.inner x) (e.localFrame b i x)) (e.localFrame b j x)) =
                ∑ i, ∑ j, (b.repr v) j *
                  ((b.repr w) i * ((g.inner x) (e.localFrame b j x)) (e.localFrame b i x)) by
            simpa [_root_.DifferentialGeometry.Geometry.Connection.localMetricFlatBasis_apply_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis, _root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis, map_sum, map_smul,
              smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_comm] using h
          conv_rhs => rw [Finset.sum_comm]
    _ = g.inner x (e.symmL Real x v) (e.symmL Real x w) := by
          rw [hv, hw]

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
theorem localMetricFlatBasis_isInvertible {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) :
    (localMetricFlatBasis (I := I) e b g x).IsInvertible := by
  have : CompleteSpace (E →L[Real] Real) := inferInstance
  let A : E →ₗ[Real] (E →L[Real] Real) :=
    (localMetricFlatBasis (I := I) e b g x).toLinearMap
  have hker : LinearMap.ker A = ⊥ := by
    ext v
    constructor
    · intro hv
      change A v = 0 at hv
      have hself :
          localMetricFlatBasis (I := I) e b g x v v = 0 := by
        exact congrArg (fun L : E →L[Real] Real => L v) hv
      have hinner :
          g.inner x (e.symmL Real x v) (e.symmL Real x v) = 0 := by
        simpa [localMetricFlatBasis_eq_inner (I := I) e b g hx v v] using hself
      by_contra hvne
      have hsymm_ne : e.symmL Real x v ≠ 0 := by
        intro hzero
        have hmap := congrArg (e.continuousLinearMapAt Real x) hzero
        have hcancel :
            e.continuousLinearMapAt Real x (e.symmL Real x v) = v :=
          e.continuousLinearMapAt_symmL (R := Real) hx v
        rw [hcancel] at hmap
        exact hvne (by simpa using hmap)
      exact False.elim ((ne_of_gt (g.pos x (e.symmL Real x v) hsymm_ne)) hinner)
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      simp [A, hv0]
  have hdim :
      Module.finrank Real E = Module.finrank Real (E →L[Real] Real) := by
    calc
      Module.finrank Real E = Module.finrank Real (Module.Dual Real E) :=
        Subspace.dual_finrank_eq.symm
      _ = Module.finrank Real (E →L[Real] Real) :=
        (LinearMap.toContinuousLinearMap :
          (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real)).finrank_eq
  let Aequiv : E ≃ₗ[Real] (E →L[Real] Real) :=
    A.linearEquivOfInjective (LinearMap.ker_eq_bot.mp hker) hdim
  let Acle : E ≃L[Real] (E →L[Real] Real) :=
    Aequiv.toContinuousLinearEquiv
  have hA : (Acle : E →L[Real] E →L[Real] Real) =
      localMetricFlatBasis (I := I) e b g x := by
    ext v w
    change Aequiv v w = localMetricFlatBasis (I := I) e b g x v w
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  rw [← hA]
  exact ContinuousLinearMap.isInvertible_equiv

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem localMetricFlatBasis_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
      (fun y => localMetricFlatBasis (I := I) e b g y) x := by
  unfold localMetricFlatBasis
  refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
  exact (_root_.DifferentialGeometry.Geometry.Connection.localMetricCoeff_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx i j).smul contMDiffAt_const

 noncomputable def _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (k l : ι) (y : M) : Real :=
  b.coord k
    ((ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y))
      (_root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b l))

omit [CompleteSpace E] in
omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_contMDiffAt_of_isInvertible_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (hInv : (localMetricFlatBasis (I := I) e b g x).IsInvertible) (k l : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l y) x := by
  have : CompleteSpace E := FiniteDimensional.complete Real E
  let εl : E →L[Real] Real := _root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b l
  let εk : E →L[Real] Real := _root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b k
  have hflat :=
    localMetricFlatBasis_contMDiffAt (I := I) e b g hx
  have hinv :
      ContMDiffAt I 𝓘(Real, (E →L[Real] Real) →L[Real] E) ∞
        (fun y : M =>
          ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y)) x := by
    simpa [Function.comp_def] using
      (hInv.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp x hflat
  have happ :
      ContMDiffAt I 𝓘(Real, E) ∞
        (fun y : M =>
          ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y) εl) x := by
    simpa [εl] using hinv.clm_apply contMDiffAt_const
  simpa [_root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis, εk, εl, _root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis] using
    (contMDiffAt_const (c := εk)).clm_apply happ

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) (k l : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l y) x :=
  _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_contMDiffAt_of_isInvertible_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx
    (localMetricFlatBasis_isInvertible (I := I) e b g hx) k l

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localMetricFlatBasis_eq_dual_sum_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    localMetricFlatBasis (I := I) e b g x v =
      ∑ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) • _root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b l := by
  ext w
  calc
    localMetricFlatBasis (I := I) e b g x v w
        = localMetricFlatBasis (I := I) e b g x v
            (∑ l : ι, b.coord l w • b l) := by
          rw [show (∑ l : ι, b.coord l w • b l) = w by
            exact b.sum_repr w]
    _ = ∑ l : ι,
          localMetricFlatBasis (I := I) e b g x v (b l) *
            b.coord l w := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro l _
          simp [smul_eq_mul, mul_comm]
    _ = (∑ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) • _root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b l) w := by
          simp [_root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis, smul_eq_mul]

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.basis_coord_eq_sum_localInvMetric_flat_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (k : ι) (v : E) :
    b.coord k v =
      ∑ l : ι,
        _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l x *
          localMetricFlatBasis (I := I) e b g x v (b l) := by
  let A := localMetricFlatBasis (I := I) e b g x
  have hInv := localMetricFlatBasis_isInvertible (I := I) e b g hx
  calc
    b.coord k v = b.coord k (A.inverse (A v)) := by
      rw [hInv.inverse_apply_self]
    _ = b.coord k
        (A.inverse
          (∑ l : ι, A v (b l) • _root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b l)) := by
          rw [← _root_.DifferentialGeometry.Geometry.Connection.localMetricFlatBasis_eq_dual_sum_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g x v]
    _ = ∑ l : ι, A v (b l) *
          b.coord k (A.inverse (_root_.DifferentialGeometry.Geometry.Connection.coordCLM_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (E := E) b l)) := by
          simp [map_sum, map_smul, smul_eq_mul]
    _ = ∑ l : ι,
        _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l x *
          localMetricFlatBasis (I := I) e b g x v (b l) := by
          apply Finset.sum_congr rfl
          intro l _
          simp [A, _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis, mul_comm]

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.localFrame_coeff_eq_sum_localInvMetric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (k : ι) (V : TangentSpace I x) :
    e.localFrameCoeff I b k x V =
      ∑ l : ι,
        _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l x *
          g.inner x (e.localFrame b l x) V := by
  let v : E := e.continuousLinearMapAt Real x V
  have hcoeff :
      e.localFrameCoeff I b k x V = b.coord k v := by
    classical
    let σ : (y : M) → TangentSpace I y := fun y => if h : x = y then h ▸ V else 0
    have hσx : σ x = V := by
      simp [σ]
    have hσ := Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
      (𝕜 := Real) (F := E) (V := (TangentSpace I : M → Type _)) (I := I)
      (e := e) (b := b) hx σ k
    rw [hσx] at hσ
    rw [hσ]
    simp [v, Bundle.Trivialization.basisAt, Bundle.Trivialization.continuousLinearMapAt_apply,
      e.coe_linearMapAt_of_mem hx]
  have hflat :
      ∀ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) =
          g.inner x V (e.localFrame b l x) := by
    intro l
    have hv : e.symmL Real x v = V := by
      exact e.symmL_continuousLinearMapAt (R := Real) hx V
    have hl : e.symmL Real x (b l) = e.localFrame b l x := by
      rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
      exact e.symmL_apply hx (b l)
    rw [localMetricFlatBasis_eq_inner (I := I) e b g hx v (b l), hv, hl]
  rw [hcoeff, _root_.DifferentialGeometry.Geometry.Connection.basis_coord_eq_sum_localInvMetric_flat_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx]
  apply Finset.sum_congr rfl
  intro l _
  rw [hflat l, g.symm x V (e.localFrame b l x)]

omit [SigmaCompactSpace M] [T2Space M] in
 theorem _root_.DifferentialGeometry.Geometry.Connection.lc_christoffel_eq_koszul_sum_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    e.localFrameCoeff I b k x
        ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) x)
          (e.localFrame b i x)) =
      (1 / 2 : Real) *
        ∑ l : ι,
          _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l x *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
  let A : TangentSpace I x :=
    (leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) x)
      (e.localFrame b i x)
  have hcoeff := _root_.DifferentialGeometry.Geometry.Connection.localFrame_coeff_eq_sum_localInvMetric_inner_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
    (I := I) e b g hx k A
  have hinner :
      ∀ l : ι,
        g.inner x (e.localFrame b l x) A =
          (1 / 2 : Real) *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
    intro l
    have hi := (_root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx i).mdifferentiableAt (by simp)
    have hj := (_root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx j).mdifferentiableAt (by simp)
    have hl := (_root_.DifferentialGeometry.Geometry.Connection.localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b hx l).mdifferentiableAt (by simp)
    have hKos := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) g (e.localFrame b i) (e.localFrame b j)
      (e.localFrame b l) x hi hj hl
    calc
      g.inner x (e.localFrame b l x) A = g.inner x A (e.localFrame b l x) := by
        exact g.symm x (e.localFrame b l x) A
      _ = (1 / 2 : Real) *
          koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
            (e.localFrame b l) x := by
          simpa [A] using hKos
  rw [hcoeff]
  calc
    (∑ l : ι,
        _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l x * g.inner x (e.localFrame b l x) A)
        = ∑ l : ι,
            _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l x *
              ((1 / 2 : Real) *
                koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                  (e.localFrame b l) x) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [hinner l]
    _ = (1 / 2 : Real) *
        ∑ l : ι,
          _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l x *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring

omit [SigmaCompactSpace M] [T2Space M] in
theorem lc_christoffel_contMDiffAt {ι : Type*} [Finite ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) y)
            (e.localFrame b i y))) x := by
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M =>
          (1 / 2 : Real) *
            ∑ l : ι,
              _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l y *
                koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                  (e.localFrame b l) y) x := by
    refine contMDiffAt_const.mul (ContMDiffAt.sum fun l _ => ?_)
    exact (_root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx k l).mul
      (_root_.DifferentialGeometry.Geometry.Connection.koszulScalar_localFrame_contMDiffAt_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hx i j l)
  have heq :
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) y)
            (e.localFrame b i y))) =ᶠ[𝓝 x]
      fun y : M =>
        (1 / 2 : Real) *
          ∑ l : ι,
            _root_.DifferentialGeometry.Geometry.Connection.localInvMetricCoeff_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g k l y *
              koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                (e.localFrame b l) y := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact _root_.DifferentialGeometry.Geometry.Connection.lc_christoffel_eq_koszul_sum_closedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis (I := I) e b g hy i j k
  exact hRhs.congr_of_eventuallyEq heq

end DifferentialGeometry.Geometry.Connection

end
