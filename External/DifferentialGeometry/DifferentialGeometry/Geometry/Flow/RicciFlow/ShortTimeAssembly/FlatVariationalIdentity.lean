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
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.FlowRealisation.LocalChart
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.FlatPairedResidual


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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem flatVariationalIdentity_eq_rawFderiv_add_movingTrivCorrection
    (X : Cₛ^∞⟮I; E, (TangentSpace I)⟯)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (t : ℝ) (x : M) (v : TangentSpace I x)
    (T' P' : E →L[ℝ] E)
    (hflat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T' P')
    (hodejet : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      (fderiv ℝ (fun z => -(chartTrivRepr (I := I) (Φ_fam t x)
          (X : ∀ y : M, TangentSpace I y) z))
        (extChartAt I (Φ_fam t x) (Φ_fam t x))
        (mfderiv I I (Φ_fam t : M → M) x v)) t)
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x))) :
    T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v
      = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v)
          + movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v)) := by
  have hflat' : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      (T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v) t := hflat
  have hval := hflat'.unique hodejet
  rw [hval]
  exact flatLinearization_eq_rawFderiv_add_movingTriv (I := I) (Φ_fam t x)
    (X : ∀ y : M, TangentSpace I y) (mfderiv I I (Φ_fam t : M → M) x v) hRdiff hCdiff

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem flat_raw_variational_identity
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (hXauto : AutonomizedFieldJointC1 (I := I) X)
    (hΦfam_ode : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∀ y ∈ W, ∀ s ∈ Set.Ioo (t - T₀) (t + T₀),
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y)
            (Set.Ioo (t - T₀) (t + T₀)) s
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) y))))
    (horbit_cont : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      ContinuousAt (fun y : M => (Φ_fam t : M → M) y) x ∧
      ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hx_src : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, x ∈ (chartAt H (Φ_fam t x)).source)
    (hGfd : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      ∃ G' : E →L[ℝ] (E →L[ℝ] E),
        HasFDerivAt (fun z => chartMovingTriv (I := I) (Φ_fam t x) z) G'
          (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) x))) :
    ∃ T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E),
      ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
        RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v) := by
  classical
  have hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      ∃ Tv Pv : E →L[ℝ] E, RawVariationalIdentityFlat (I := I) Φ_fam t x v Tv Pv := by
    intro t ht x v
    obtain ⟨T₀, hT₀, W, hW, hxW, hode⟩ := hΦfam_ode t ht x
    obtain ⟨G', hG'⟩ := hGfd t ht x
    obtain ⟨ΦE, velChart, Pv, _hvel, hident⟩ :=
      rawVariationalIdentityFlat_of_jointSmoothBareField (I := I) X hX hXauto Φ_fam t x v
        (hx_src t ht x) hT₀ hW hxW hode (horbit_cont t ht x).1 (horbit_cont t ht x).2 hG'
    exact ⟨_, _, hident⟩
  choose! Tv Pv hTv using hpoint
  exact ⟨Tv, Pv, fun t ht x v => hTv t ht x v⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem flat_christoffel_correction_eqn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E))
    (hjet : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                ((deTurckVF (I := I) (g_DT t) g_bg :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
                  ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                ((deTurckVF (I := I) (g_DT t) g_bg :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
                  ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x v)))
    (hα : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      (Φ_fam t x) ∈ chartLeviCivitaGoodSet (I := I) (Φ_fam t x))
    (hRdiff : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      DifferentiableAt ℝ
        (chartRawRepr (I := I) (Φ_fam t x)
          ((deTurckVF (I := I) (g_DT t) g_bg :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
            ∀ y : M, TangentSpace I y))
        (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      DifferentiableAt ℝ
        (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
        (extChartAt I (Φ_fam t x) (Φ_fam t x))) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v) := by
  intro t ht x v
  have hbridge :=
    leviCivita_basepoint_eq_rawFderiv_add_corrections (I := I) (g_DT t) (Φ_fam t x)
      ((deTurckVF (I := I) (g_DT t) g_bg :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ y : M, TangentSpace I y)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (hα t ht x)
      ((deTurckVF (I := I) (g_DT t) g_bg).mdifferentiableAt)
      (hRdiff t ht x) (hCdiff t ht x)
  rw [hjet t ht x v, negCovariantSlotValue, hbridge]
  abel

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem flat_value_jet_identity
    (X : Cₛ^∞⟮I; E, (TangentSpace I)⟯)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (t : ℝ) (x : M) (v : TangentSpace I x)
    (T' P' : E →L[ℝ] E)
    (hflat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T' P')
    (hodejet : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      (fderiv ℝ (fun z => -(chartTrivRepr (I := I) (Φ_fam t x)
          (X : ∀ y : M, TangentSpace I y) z))
        (extChartAt I (Φ_fam t x) (Φ_fam t x))
        (mfderiv I I (Φ_fam t : M → M) x v)) t)
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x))) :
    T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v
      = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v)
          + movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v)) :=
  flatVariationalIdentity_eq_rawFderiv_add_movingTrivCorrection (I := I) X Φ_fam t x v T' P'
    hflat hodejet hRdiff hCdiff

end DifferentialGeometry.PDE.RicciFlow
