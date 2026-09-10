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
import Verified.ClosedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Connection_MetricCompatibility
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_Family_Basic
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Auxiliary_PredualBasis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_NablaOnTensors
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_LocalFrameRegularity
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Metric
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_MetricCompatibility
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Smooth
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Tangent

noncomputable section

open Bundle Filter Set MeasureTheory

open scoped Manifold ContDiff Topology

open DifferentialGeometry DifferentialGeometry.Integral.Measure

namespace OpenGA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

 local instance _root_.OpenGAExport.OpenGALib.Riemannian.VolumeVariation.instance_29 : MeasurableSpace M := borel M

 local instance _root_.OpenGAExport.OpenGALib.Riemannian.VolumeVariation.instance_30 : BorelSpace M := ⟨rfl⟩

/-- Joint continuity of the metric coefficients and their time derivatives on
an open time interval. These are regularity assumptions, not a variation formula. -/
structure MetricFamilyRegularOn (g : ℝ → SmoothRiemannianMetric I M) (U : Set ℝ) : Prop where
  differentiableAt : ∀ a i j x,
    x ∈ (trivializationAt E (TangentSpace I) a).baseSet → ∀ t ∈ U,
    DifferentiableAt ℝ (fun s => chartGramMatrix (g s) a x i j) t
  continuousOn : ∀ a i j,
    ContinuousOn (fun p : ℝ × M => chartGramMatrix (g p.1) a p.2 i j)
      (U ×ˢ (trivializationAt E (TangentSpace I) a).baseSet)
  continuousOn_deriv : ∀ a i j,
    ContinuousOn (fun p : ℝ × M => deriv (fun s => chartGramMatrix (g s) a p.2 i j) p.1)
      (U ×ˢ (trivializationAt E (TangentSpace I) a).baseSet)

omit [FiniteDimensional ℝ E] in
 theorem _root_.OpenGA.contMDiffAt_partial_deriv_time_closedSurface_OpenGALib_Riemannian_VolumeVariation
    {f : ℝ × M → ℝ} {p : ℝ × M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ f p) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => deriv (fun t => f (t, q.2)) q.1) p := by
  have harg : ContMDiffAt ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) ∞ (fun q : (ℝ × M) × ℝ => (q.2, q.1.2)) (p, p.1) :=
    contMDiffAt_snd.prodMk contMDiffAt_fst.snd
  have hF := hf.comp (p, p.1) harg
  have h := ContMDiffAt.mfderiv_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (f := fun (q : ℝ × M) (t : ℝ) => f (t, q.2))
    (g := fun q : ℝ × M => q.1) (g₁ := fun q : ℝ × M => q)
    (g₂ := fun _ : ℝ × M => (1 : ℝ)) (x₀ := p) (m := ∞)
    hF contMDiffAt_fst contMDiffAt_id contMDiffAt_const (le_refl _)
  simpa [inTangentCoordinates_model_space] using! h

/-- Smooth space-time metric coefficients supply the local regularity interface. -/
theorem MetricFamilyRegularOn.of_contMDiffAt
    {g : ℝ → SmoothRiemannianMetric I M} {U : Set ℝ}
    (hg : ∀ a i j t, t ∈ U → ∀ x,
      x ∈ (trivializationAt E (TangentSpace I) a).baseSet →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) a p.2 i j) (t, x)) :
    MetricFamilyRegularOn g U where
  differentiableAt a i j x hx t ht := by
    have h := (hg a i j t ht x hx).comp t
      (contMDiffAt_id.prodMk contMDiffAt_const)
    exact (contMDiffAt_iff_contDiffAt.mp h).differentiableAt (by simp)
  continuousOn a i j p hp := (hg a i j p.1 hp.1 p.2 hp.2).continuousAt.continuousWithinAt
  continuousOn_deriv a i j p hp :=
    (_root_.OpenGA.contMDiffAt_partial_deriv_time_closedSurface_OpenGALib_Riemannian_VolumeVariation (hg a i j p.1 hp.1 p.2 hp.2)).continuousAt.continuousWithinAt

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

theorem MetricFamilyRegularOn.comp
    {g : ℝ → SmoothRiemannianMetric I M} {U : Set ℝ}
    (hg : MetricFamilyRegularOn g U) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hmap : ∀ s, r s ∈ U) (t : ℝ) :
    MetricFamilyRegularAt (fun s => g (r s)) t := by
  apply MetricFamilyRegularAt.of_chartGram_timeDeriv
  intro a i j
  refine ⟨fun s x => deriv (fun u => chartGramMatrix (g u) a x i j) (r s) * deriv r s,
    ?_, ?_, ?_⟩
  · intro s x hx
    exact (hg.differentiableAt a i j x hx (r s) (hmap s)).hasDerivAt.comp s
      (hr.differentiable (by simp)).differentiableAt.hasDerivAt
  · exact (hg.continuousOn a i j).comp
      ((hr.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨hmap p.1, hp.2⟩)
  · exact ((hg.continuousOn_deriv a i j).comp
      ((hr.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨hmap p.1, hp.2⟩)).mul
      ((hr.continuous_deriv (by simp)).comp continuous_fst).continuousOn

/-- Total Riemannian volume, as a real integral. It is finite on compact manifolds. -/
def totalRiemannianVolume [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) : ℝ :=
  ∫ _ : M, (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g)

theorem hasDerivAt_totalRiemannianVolume_of_regular [T2Space M] [CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (hg : MetricFamilyRegularAt g t) :
    HasDerivAt (fun s => totalRiemannianVolume (g s))
      (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric I g t x ∂(riemannianVolumeMeasure (I := I) (M := M) (g t))) t := by
  simpa [totalRiemannianVolume, riemannianMeasureFamily, deriv_const] using
    volume_variation_formula (f := fun _ _ => (1 : ℝ)) hg (FunctionRegularAt_const 1 t)

/-- Volume variation needs regularity only near the time of differentiation. -/
theorem hasDerivAt_totalRiemannianVolume [T2Space M] [CompactSpace M]
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

end OpenGA

end
