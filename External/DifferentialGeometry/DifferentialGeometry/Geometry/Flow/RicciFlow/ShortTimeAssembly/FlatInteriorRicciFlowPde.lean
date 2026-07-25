import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
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
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] in
theorem pullbackMetric_hasDerivWithinAt_ricciFlow_interior
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E))
    (hDT_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (hbase : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w))
        (-metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t)
    (h_total_eval : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w))
        (((-2 : ℝ) * ricciTensor (I := I) (g_DT t) (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)
              (mfderiv I I (Φ_fam t : M → M) x w)
            + lieDerivMetric (I := I) (g_DT t)
                (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
                (mfderiv I I (Φ_fam t : M → M) x v)
                (mfderiv I I (Φ_fam t : M → M) x w))
          + (- lieDerivMetric (I := I) (g_DT t)
                (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
                (mfderiv I I (Φ_fam t : M → M) x v)
                (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t)
    (hv_flat : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v))
    (hcorr : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
        ((-2) * ricciTensor (I := I)
          (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) (Set.Ici 0) t := by
  intro t ht x v w
  have _h_metric : HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
      ((-2 : ℝ) * ricciTensor (I := I) (g_DT t) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + lieDerivMetric (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
    have h := hDT_deriv t ht (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
    rwa [deTurckRicciRHS_apply] at h
  have _h_base := hbase t ht x v w
  have _h_push :=
    variational_flow_flat_pairing_hasDerivWithinAt (I := I)
      (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w
      (T' t x v) (P' t x v) (T' t x w) (P' t x w)
      (hv_flat t ht x v) (hv_flat t ht x w) (hcorr t ht x v) (hcorr t ht x w)
  exact deTurck_pullback_eval_value_hasDerivWithinAt (I := I)
    g_bg g_DT Φ_fam t x v w (h_total_eval t ht x v w)

end DifferentialGeometry.PDE.RicciFlow
