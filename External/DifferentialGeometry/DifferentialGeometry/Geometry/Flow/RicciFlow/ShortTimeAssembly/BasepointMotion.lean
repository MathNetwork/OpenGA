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
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatToCovariant
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem basepoint_metric_along_curve
    (g : SmoothRiemannianMetric I M) (X : Cₛ^∞⟮I; E, (TangentSpace I)⟯)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (t : ℝ) (x : M) (v w : TangentSpace I x)
    (horbit : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(X (Φ_fam t x)))))
    (D : ℝ)
    (h_reg : HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      D (Set.Ici 0) t)
    (h_compat : D = -metricTransportResidual (I := I) g X Φ_fam t x v w) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      (-metricTransportResidual (I := I) g X Φ_fam t x v w) (Set.Ici 0) t := by
  let _ := horbit
  rwa [h_compat] at h_reg

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem basepoint_motion_datum
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (horbit : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg (Φ_fam t x)))))
    (D : ℝ → (x : M) → (v w : TangentSpace I x) → ℝ)
    (h_reg : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
        (D t x v w) (Set.Ici 0) t)
    (h_compat : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      D t x v w
        = -metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
        (-metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t := by
  intro t ht x v w
  exact basepoint_metric_along_curve (I := I) (g_DT t)
    (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w (horbit t ht x)
    (D t x v w) (h_reg t ht x v w) (h_compat t ht x v w)

end DifferentialGeometry.PDE.RicciFlow
