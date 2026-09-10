import Theorems.Thm_DifferentialGeometry_Integral_Measure_FunctionRegularAt_const
import Theorems.Thm_DifferentialGeometry_Integral_Measure_volume_variation_formula
import Theorems.Thm_OpenGA_MetricFamilyRegularOn_comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Family
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_FamilyDecomposition
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_FamilyDefs
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_VolumeVariation
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_TimeInterval
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_Section
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Connection_MetricCompatibility
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_Family_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Auxiliary_PredualBasis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_NablaOnTensors
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_LocalFrameRegularity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Metric
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_MetricCompatibility
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Smooth
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Tangent
import Definitions.Def_ClosedSurface_OpenGALib_Riemannian_VolumeVariation
import Definitions.Def_OpenGA_ImmersedMetric
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
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bundle
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
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
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
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
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
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


section

noncomputable section

open Bundle Filter Set MeasureTheory

open scoped Manifold ContDiff Topology

open DifferentialGeometry DifferentialGeometry.Integral.Measure

namespace OpenGA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.OpenGALib.Riemannian.VolumeVariation.instance_29

attribute [local instance] _root_.OpenGAExport.OpenGALib.Riemannian.VolumeVariation.instance_30

 theorem _root_.OpenGA.exists_smooth_time_localization_closedSurface_OpenGALib_Riemannian_VolumeVariation {U : Set ℝ} {t : ℝ} (hU : U ∈ 𝓝 t) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ (∀ s, r s ∈ U) ∧ r =ᶠ[𝓝 t] id := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  let b : ContDiffBump t := ⟨ε / 2, ε, by positivity, by linarith⟩
  refine ⟨fun s => t + b s * (s - t),
    contDiff_const.add (b.contDiff.mul (contDiff_id.sub contDiff_const)), ?_, ?_⟩
  · intro s
    apply hball
    by_cases hs : s ∈ Metric.ball t ε
    · rw [Metric.mem_ball, Real.dist_eq]
      have hst : |s - t| < ε := by simpa [Metric.mem_ball, Real.dist_eq] using hs
      calc |t + b s * (s - t) - t| = |b s| * |s - t| := by
             rw [add_sub_cancel_left, abs_mul]
           _ ≤ 1 * |s - t| := mul_le_mul_of_nonneg_right
             (by rw [abs_of_nonneg b.nonneg]; exact b.le_one) (abs_nonneg _)
           _ < ε := by simpa using hst
    · have hb : b s = 0 := b.zero_of_le_dist (by simpa [b, Metric.mem_ball] using hs)
      simpa [hb] using Metric.mem_ball_self (x := t) hε
  · filter_upwards [b.eventuallyEq_one] with s hs
    simp [hs]

theorem hasDerivAt_totalRiemannianVolume_of_regular [T2Space M] [CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (hg : MetricFamilyRegularAt g t) :
    HasDerivAt (fun s => totalRiemannianVolume (g s))
      (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric I g t x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t))) t := by
  simpa [totalRiemannianVolume, riemannianMeasureFamily, deriv_const] using
    volume_variation_formula (f := fun _ _ => (1 : ℝ)) hg (FunctionRegularAt_const 1 t)

end OpenGA

end

end

noncomputable section

open Bundle Filter Set MeasureTheory

open scoped Manifold ContDiff Topology

open DifferentialGeometry DifferentialGeometry.Integral.Measure

namespace OpenGA
end OpenGA
open _root_.OpenGA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.OpenGALib.Riemannian.VolumeVariation.instance_29

attribute [local instance] _root_.OpenGAExport.OpenGALib.Riemannian.VolumeVariation.instance_30

namespace OpenGA
end OpenGA
open _root_.OpenGA

/-- Volume variation needs regularity only near the time of differentiation. -/
theorem solution [T2Space M] [CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) {U : Set ℝ} {t : ℝ}
    (hg : MetricFamilyRegularOn g U) (hU : U ∈ 𝓝 t) :
    HasDerivAt (fun s => totalRiemannianVolume (g s))
      (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric I g t x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t))) t := by
  obtain ⟨r, hr, hmap, heq⟩ := _root_.OpenGA.exists_smooth_time_localization_closedSurface_OpenGALib_Riemannian_VolumeVariation hU
  have hrt : r t = t := heq.eq_of_nhds
  have h := hasDerivAt_totalRiemannianVolume_of_regular (fun s => g (r s)) t
    (hg.comp r hr hmap t)
  have htrace : ∀ x, traceTimeDerivMetric I (fun s => g (r s)) t x =
      traceTimeDerivMetric I g t x := by
    intro x
    unfold traceTimeDerivMetric
    dsimp only
    rw [hrt]
    congr 3
    funext i j
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [heq] with s hs
    simp only [hs, id_eq]
  simp_rw [hrt, htrace] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [heq] with s hs
  simp only [hs, id_eq]
