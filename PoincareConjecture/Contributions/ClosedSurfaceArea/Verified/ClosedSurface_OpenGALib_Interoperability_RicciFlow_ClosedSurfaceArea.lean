import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Bilinear
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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
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
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Family
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_FamilyDecomposition
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_FamilyDefs
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_JacobiFormula
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_VolumeVariation
import Verified.ClosedSurface_DifferentialGeometry_Analysis_TimeInterval
import Verified.ClosedSurface_DifferentialGeometry_Bundle_LocalFrameRegularity
import Verified.ClosedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Basic
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_KoszulFormula
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_Connection
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_LeviCivita_Smooth_MetricFlatBasis
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_MetricCompatibility
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_Smoothness
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Basic
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Bochner_BochnerTensor
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Metric
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Field
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Sections
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Curvature_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Flow_RicciFlow_Solution_Basic
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Flow_RicciFlow_Solution_Defs
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_Family_Basic
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_Family_PairSmoothness
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
import Verified.ClosedSurface_OpenGALib_Riemannian_Surface_Area
import Verified.ClosedSurface_OpenGALib_Riemannian_VolumeVariation

noncomputable section

open Bundle Matrix MeasureTheory Set Filter

open scoped Manifold ContDiff Topology

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

namespace OpenGA.RicciFlow

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Surface.Model N]
  [IsManifold 𝓘(ℝ, Surface.Model) ∞ N] [T2Space N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

 local instance _root_.OpenGAExport.OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea.instance_35 : MeasurableSpace N := borel N

 local instance _root_.OpenGAExport.OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea.instance_36 : BorelSpace N := ⟨rfl⟩

omit [T2Space M] in
/-- Pulling back a smooth ambient metric family by a fixed immersion preserves
the local space-time regularity needed for volume variation. -/
theorem inducedMetric_regularOn
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) (f : N → M)
    (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x)) :
    MetricFamilyRegularOn (fun s => Surface.inducedMetric (g s) f hf hinj) D.regular := by
  apply MetricFamilyRegularOn.of_contMDiffAt
  intro a i j t ht x hx
  have hbase := (trivializationAt Surface.Model (TangentSpace 𝓘(ℝ, Surface.Model)) a).open_baseSet.mem_nhds hx
  have htf : ContMDiff 𝓘(ℝ, Surface.Model).tangent I.tangent ∞
      (tangentMap 𝓘(ℝ, Surface.Model) I f) := hf.contMDiff_tangentMap (le_refl _)
  have hv (k : Fin (Module.finrank ℝ Surface.Model)) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Surface.Model)) I.tangent ∞
        (fun p : ℝ × N => TotalSpace.mk' E (f p.2)
          (mfderiv 𝓘(ℝ, Surface.Model) I f p.2
            (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) a k p.2))) (t, x) :=
    htf.contMDiffAt.comp (t, x)
      (((chartBasisVec_contMDiffOn a k).contMDiffAt hbase).comp (t, x) contMDiffAt_snd)
  have hmetric := (hg.metricCLMSmoothAt (x := f x) (D.regular_isOpen.mem_nhds ht)).comp (t, x)
    (contMDiffAt_fst.prodMk (hf.contMDiffAt.comp (t, x) contMDiffAt_snd))
  have hpair := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun b : M => TangentSpace I b) (E₂ := fun b : M => TangentSpace I b)
    (E₃ := fun _ : M => ℝ)
    (b := fun p : ℝ × N => f p.2) (ψ := fun p => (g p.1).inner (f p.2))
    (v := fun p => mfderiv 𝓘(ℝ, Surface.Model) I f p.2
      (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) a i p.2))
    (w := fun p => mfderiv 𝓘(ℝ, Surface.Model) I f p.2
      (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) a j p.2)) hmetric (hv i) (hv j)
  rw [contMDiffAt_totalSpace] at hpair
  exact hpair.2

/-- The ambient Ricci tensor evaluated on the images of a centered chart basis.
The same basis is used in the induced metric matrix below. -/
def inducedRicciMatrix {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (f : N → M) (t : ℝ) (x : N) :
    Matrix (Fin (Module.finrank ℝ Surface.Model)) (Fin (Module.finrank ℝ Surface.Model)) ℝ :=
  fun i j => S.ricciAt t (f x) (vec2
    (mfderiv 𝓘(ℝ, Surface.Model) I f x
      (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) x i x))
    (mfderiv 𝓘(ℝ, Surface.Model) I f x
      (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) x j x)))

/-- Trace of the ambient Ricci tensor along the immersed tangent plane. -/
def inducedRicciTrace {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x))
    (t : ℝ) (x : N) : ℝ :=
  Matrix.trace ((chartGramMatrix (Surface.inducedMetric (S.family.metric t) f hf hinj) x x)⁻¹ *
    inducedRicciMatrix S f t x)

theorem traceTimeDeriv_inducedMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x))
    {t : ℝ} (ht : t ∈ D.regular) (x : N) :
    traceTimeDerivMetric 𝓘(ℝ, Surface.Model)
      (fun s => Surface.inducedMetric (S.family.metric s) f hf hinj) t x =
      -2 * inducedRicciTrace S f hf hinj t x := by
  have hentries : (Matrix.of fun i j =>
      deriv (fun s => chartGramMatrix (Surface.inducedMetric (S.family.metric s) f hf hinj)
        x x i j) t) = (-2 : ℝ) • inducedRicciMatrix S f t x := by
    ext i j
    exact (metricDerivAt S hS ⟨t, ht⟩ (f x)
      (mfderiv 𝓘(ℝ, Surface.Model) I f x
        (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) x i x))
      (mfderiv 𝓘(ℝ, Surface.Model) I f x
        (chartBasisVecFiber (I := 𝓘(ℝ, Surface.Model)) x j x))).deriv
  unfold traceTimeDerivMetric inducedRicciTrace
  rw [hentries, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Global area variation of a fixed smooth immersion of a closed surface.
All regularity and domination needed for the integral are derived from the
actual smooth Ricci flow and compactness of the domain surface. -/
theorem hasDerivAt_area [CompactSpace N]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Surface.Model) I f x))
    {t : ℝ} (ht : t ∈ D.regular) :
    HasDerivAt (fun s => Surface.area (S.family.metric s) f hf hinj)
      (-∫ x, inducedRicciTrace S f hf hinj t x
        ∂(Surface.areaMeasure (S.family.metric t) f hf hinj)) t := by
  have h := hasDerivAt_totalRiemannianVolume
    (fun s => Surface.inducedMetric (S.family.metric s) f hf hinj)
    (inducedMetric_regularOn S.family.metric hS.smoothMetric f hf hinj)
    (D.regular_isOpen.mem_nhds ht)
  simp_rw [traceTimeDeriv_inducedMetric S hS f hf hinj ht] at h
  have halg : ∀ x, (1 / 2 : ℝ) * (-2 * inducedRicciTrace S f hf hinj t x) =
      -inducedRicciTrace S f hf hinj t x := by intro x; ring
  simpa only [halg, integral_neg, Surface.area, Surface.areaMeasure] using h

end OpenGA.RicciFlow

end
