import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciTensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckVectorFieldContinuousInMetric
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem differentiableOn_and_deriv_eq_of_hasDerivWithinAt_Ici
    (f : ℝ → ℝ) {T : ℝ} (e : ℝ → ℝ)
    (h_int : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt f (e t) (Set.Ici 0) t) :
    DifferentiableOn ℝ f (Set.Ioo 0 T) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, deriv f t = e t) := by
  have hsub : Set.Ioo (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := fun y hy => le_of_lt hy.1
  have h_within : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt f (e t) (Set.Ioo 0 T) t := fun t ht => (h_int t ht).mono hsub
  refine ⟨fun t ht => (h_within t ht).differentiableWithinAt, fun t ht => ?_⟩
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  rw [← derivWithin_of_isOpen hopen ht]
  exact (h_within t ht).derivWithin (hopen.uniqueDiffWithinAt ht)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricci_flow_pde_at_zero
    (g_fam : ℝ → SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (x : M)
    (v w : TangentSpace I x)
    (h_cont : ContinuousOn (fun s : ℝ => (g_fam s).inner x v w) (Set.Ico 0 T))
    (h_ric_cont : ContinuousWithinAt
      (fun s : ℝ => (-2) * ricciTensor (I := I) (g_fam s) x v w) (Set.Ioi 0) 0)
    (h_interior : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt
      (fun s : ℝ => (g_fam s).inner x v w)
      ((-2) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici 0) t) :
    HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
      ((-2) * ricciTensor (I := I) (g_fam 0) x v w) (Set.Ici 0) 0 := by
  set f : ℝ → ℝ := fun s : ℝ => (g_fam s).inner x v w with hf
  set e : ℝ → ℝ := fun s : ℝ => (-2) * ricciTensor (I := I) (g_fam s) x v w with he
  have h_int : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt f (e t) (Set.Ici 0) t :=
    h_interior
  obtain ⟨h_diff, h_derivEq⟩ := differentiableOn_and_deriv_eq_of_hasDerivWithinAt_Ici f e h_int
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo 0 T) h_diff ?_ ?_ ?_
  · have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
    exact (h_cont.continuousWithinAt h0).mono Set.Ioo_subset_Ico_self
  · exact Ioo_mem_nhdsGT hT
  · have h_eventuallyEq : (fun s : ℝ => deriv f s) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] e :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hT) h_derivEq
    exact (h_ric_cont.tendsto).congr' h_eventuallyEq.symm

end DifferentialGeometry.PDE.RicciFlow
