import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Calculus.MeanValue
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
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
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
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
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
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Verified.ClosedSurface_DifferentialGeometry_Analysis_TimeInterval
import Verified.ClosedSurface_DifferentialGeometry_Bundle_LocalFrameRegularity
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

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.Geometry.Curvature

open Bundle

open scoped Manifold ContDiff Topology BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]

variable [FiniteDimensional Real E] [CompleteSpace E]

variable {H : Type uH} [TopologicalSpace H]

variable {I : ModelWithCorners Real E H}

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I ∞ M]

namespace MetricFamilySmoothOn

omit [CompleteSpace E] in
 lemma _root_.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.metricCoord_eq_sum_closedSurface_DifferentialGeometry_Geometry_Metric_Family_PairSmoothness
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (v w : E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun y : M => TangentSpace I y →L[Real] Real) x₀ x x₀ x (g.inner x) v w =
      ∑ i, ∑ j,
        ((Module.finBasis Real E).repr v) i * ((Module.finBasis Real E).repr w) j *
          g.inner x
            ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
              (Module.finBasis Real E) i x)
            ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
              (Module.finBasis Real E) j x) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis Real E
  have hxR : x ∈ (trivializationAt Real (Bundle.Trivial M Real) x₀).baseSet :=
    Set.mem_univ x
  rw [inCoordinates_apply_eq₂ (𝕜 := Real)
    (F₁ := E) (F₂ := E) (F₃ := Real)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M Real)
    (x₀ := x₀) (x := x) (ϕ := g.inner x) (v := v) (w := w) hx hx hxR]
  rw [(trivializationAt Real (Bundle.Trivial M Real) x₀).coe_linearMapAt_of_mem hxR]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply]
  rw [← Bundle.Trivialization.symmL_apply (R := Real)
      (trivializationAt E (TangentSpace I : M → Type _) x₀) hx v,
    ← Bundle.Trivialization.symmL_apply (R := Real)
      (trivializationAt E (TangentSpace I : M → Type _) x₀) hx w]
  change g.inner x (e.symmL Real x v) (e.symmL Real x w) = _
  have hvdec : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have hwdec : w = ∑ j, b.repr w j • b j := (b.sum_repr w).symm
  have hsymm_v : e.symmL Real x v = ∑ i, b.repr v i • e.localFrame b i x := by
    conv_lhs => rw [hvdec]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
    exact Bundle.Trivialization.symmL_apply e hx (b i)
  have hsymm_w : e.symmL Real x w = ∑ j, b.repr w j • e.localFrame b j x := by
    conv_lhs => rw [hwdec]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    congr 1
    rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
    exact Bundle.Trivialization.symmL_apply e hx (b j)
  rw [hsymm_v, hsymm_w]
  have hleft :
      g.inner x (∑ i, b.repr v i • e.localFrame b i x) =
        ∑ i, b.repr v i • g.inner x (e.localFrame b i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  rw [hleft, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

omit [CompleteSpace E] in
theorem metricCLMSmoothAt
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {t : Real} {x : M} (hDreg : D.regular ∈ 𝓝 t) :
    ContMDiffAt (𝓘(Real, Real).prod I)
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun q : Real × M =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          q.2 ((g_fam q.1).inner q.2))
      (t, x) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis Real E
  have hxe : x ∈ e.baseSet := by
    simp [e]
  have hframe :
      IsLocalFrameOn I E ∞ (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I ∞ b
  have hcompOn := hG.frameCompSmooth (e.localFrame b) hframe
  have hmemProd : (D.regular ×ˢ e.baseSet : Set (Real × M)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds hDreg (e.open_baseSet.mem_nhds hxe)
  have hcompAt : ∀ i j,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M =>
          (g_fam q.1).inner q.2
            (e.localFrame b i q.2) (e.localFrame b j q.2))
        (t, x) := fun i j =>
    (hcompOn i j).contMDiffAt hmemProd
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(Real, Real).prod I) (X := Real × M)
  intro v
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(Real, Real).prod I) (X := Real × M)
  intro w
  have hsum : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M =>
        ∑ i, ∑ j, b.repr v i * b.repr w j *
          (g_fam q.1).inner q.2
            (e.localFrame b i q.2) (e.localFrame b j q.2))
      (t, x) := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (contMDiffAt_const (c := b.repr v i * b.repr w j)).mul (hcompAt i j)
  refine hsum.congr_of_eventuallyEq ?_
  have hbase : ∀ᶠ q : Real × M in 𝓝 (t, x), q.2 ∈ e.baseSet :=
    (continuous_snd.tendsto (t, x)).eventually (e.open_baseSet.mem_nhds hxe)
  filter_upwards [hbase] with q hq
  change ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
      (fun y : M => TangentSpace I y →L[Real] Real)
      x q.2 x q.2 ((g_fam q.1).inner q.2) v w = _
  simpa only [e, b] using
    _root_.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.metricCoord_eq_sum_closedSurface_DifferentialGeometry_Geometry_Metric_Family_PairSmoothness (I := I) (g_fam q.1) x hq v w

end MetricFamilySmoothOn

end DifferentialGeometry.Geometry.Curvature

end
