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
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.FlatPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.BasepointMotion


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
theorem exists_jointFDerivWithinAt_evalForm_pullbackPart
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Cgeom : (x : M) → (ℝ × ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
    (hclm : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (g_DT t).inner ((Φ_fam p.1 : M → M) x))
        (Cgeom x) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t))
    (Vpush : (x : M) → TangentSpace I x → (ℝ × ℝ) →L[ℝ] E)
    (hpush_v : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (mfderiv I I (Φ_fam p.2 : M → M) x v : E))
        (Vpush x v) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t))
    (Wpush : (x : M) → TangentSpace I x → (ℝ × ℝ) →L[ℝ] E)
    (hpush_w : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I x,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (mfderiv I I (Φ_fam p.2 : M → M) x w : E))
        (Wpush x w) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      ∃ R' : (ℝ × ℝ) →L[ℝ] ℝ,
        HasFDerivWithinAt
          (fun p : ℝ × ℝ => (g_DT t).inner ((Φ_fam p.1 : M → M) x)
            (mfderiv I I (Φ_fam p.2 : M → M) x v)
            (mfderiv I I (Φ_fam p.2 : M → M) x w)) R'
          ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t) := by
  intro t ht x v w
  let _ := hΦ
  exact ⟨_, ((hclm t ht x).clm_apply (hpush_v t ht x v)).clm_apply (hpush_w t ht x w)⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem exists_jointFDerivWithinAt_evalFormTwoVar
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (Cmet : (x : M) → (ℝ × ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
    (hclm : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (g_DT p.1).inner ((Φ_fam p.2 : M → M) x))
        (Cmet x) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t))
    (Vpush : (x : M) → TangentSpace I x → (ℝ × ℝ) →L[ℝ] E)
    (hpush_v : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (mfderiv I I (Φ_fam p.2 : M → M) x v : E))
        (Vpush x v) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t))
    (Wpush : (x : M) → TangentSpace I x → (ℝ × ℝ) →L[ℝ] E)
    (hpush_w : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I x,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (mfderiv I I (Φ_fam p.2 : M → M) x w : E))
        (Wpush x w) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      ∃ Q' : (ℝ × ℝ) →L[ℝ] ℝ,
        HasFDerivWithinAt (evalFormTwoVar (I := I) g_DT Φ_fam x v w) Q'
          ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t) := by
  intro t ht x v w
  let _ := hΦ
  exact ⟨_, ((hclm t ht x).clm_apply (hpush_v t ht x v)).clm_apply (hpush_w t ht x w)⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem evalForm_pullbackPart_hasDerivWithinAt_neg_lieDerivMetric_deTurckVF
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦ_orbit : ∀ x : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x)
        (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) x)))))
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (T'v P'v : (x : M) → TangentSpace I x → ℝ → (E →L[ℝ] E))
    (T'w P'w : (x : M) → TangentSpace I x → ℝ → (E →L[ℝ] E))
    (hv_flat : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentityFlat (I := I) Φ_fam t x v (T'v x v t) (P'v x v t))
    (hw_flat : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I x,
      RawVariationalIdentityFlat (I := I) Φ_fam t x w (T'w x w t) (P'w x w t))
    (hcorr_v : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T'v x v t) (mfderiv I I (Φ_fam t : M → M) x v) + (P'v x v t) v
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                ((deTurckVF (I := I) (g_DT t) g_bg :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
                  ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hcorr_w : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I x,
      (T'w x w t) (mfderiv I I (Φ_fam t : M → M) x w) + (P'w x w t) w
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x w
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                ((deTurckVF (I := I) (g_DT t) g_bg :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
                  ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w))
    (Dbase : ℝ → (x : M) → (v w : TangentSpace I x) → ℝ)
    (h_reg_base : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
        (Dbase t x v w) (Set.Ici 0) t)
    (h_compat_base : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      Dbase t x v w
        = -metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w)
    (Cgeom : (x : M) → (ℝ × ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))
    (hclm_geom : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (g_DT t).inner ((Φ_fam p.1 : M → M) x))
        (Cgeom x) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t))
    (Vpush : (x : M) → TangentSpace I x → (ℝ × ℝ) →L[ℝ] E)
    (hpush_v : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (mfderiv I I (Φ_fam p.2 : M → M) x v : E))
        (Vpush x v) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t))
    (Wpush : (x : M) → TangentSpace I x → (ℝ × ℝ) →L[ℝ] E)
    (hpush_w : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I x,
      HasFDerivWithinAt (fun p : ℝ × ℝ => (mfderiv I I (Φ_fam p.2 : M → M) x w : E))
        (Wpush x w) ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
        (- lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
  intro t ht x v w
  have ht0 : (0 : ℝ) ≤ t := ht.1.le
  let R : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => (g_DT t).inner ((Φ_fam p.1 : M → M) x)
      (mfderiv I I (Φ_fam p.2 : M → M) x v)
      (mfderiv I I (Φ_fam p.2 : M → M) x w)
  obtain ⟨R', hR'⟩ := exists_jointFDerivWithinAt_evalForm_pullbackPart (I := I) g_DT T Φ_fam hΦ
    (Cgeom) hclm_geom (Vpush) hpush_v (Wpush) hpush_w t ht x v w
  have hdiag : HasDerivWithinAt (fun s : ℝ => R (s, s)) (R' (1, 0) + R' (0, 1))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_diagonal_hasDerivWithinAt_of_jointFDeriv R t R' hR'
  have hpart1 : HasDerivWithinAt (fun s : ℝ => R (s, t)) (R' (1, 0))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_jointFDeriv_partial_fst R t R' hR'
  have hpart2 : HasDerivWithinAt (fun s : ℝ => R (t, s)) (R' (0, 1))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_jointFDeriv_partial_snd R t ht0 R' hR'
  have hΦ_orbit' : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y)
        (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) y)))) :=
    fun s hs y => hΦ_orbit y s hs
  have hbase := basepoint_motion_datum (I := I) g_DT g_bg T Φ_fam hΦ_orbit'
    Dbase h_reg_base h_compat_base t ht x v w
  have hR10 : R' (1, 0)
      = -metricTransportResidual (I := I) (g_DT t)
          (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w :=
    hasDerivWithinAt_Ici_unique ht0 hpart1 hbase
  have hpush := DifferentialGeometry.PDE.RicciFlow.ODE.variational_flow_flat_pairing_hasDerivWithinAt
    (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w
    (T'v x v t) (P'v x v t) (T'w x w t) (P'w x w t)
    (hv_flat t ht x v) (hw_flat t ht x w) (hcorr_v t ht x v) (hcorr_w t ht x w)
  have hR01 : R' (0, 1)
      = -lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
          + metricTransportResidual (I := I) (g_DT t)
              (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w :=
    hasDerivWithinAt_Ici_unique ht0 hpart2 hpush
  have hsum : R' (1, 0) + R' (0, 1)
      = -lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w) := by
    rw [hR10, hR01]; ring
  rw [hsum] at hdiag
  exact hdiag

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem evalFormTwoVar_diag_hasDerivWithinAt_deTurckRicciRHS_chainRule
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hDT_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
        (deTurckRicciRHS (I := I) g_bg (g_DT s) y a b) (Set.Ici 0) s)
    (hΦ_orbit : ∀ x : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x)
        (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) x)))))
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (h_geom : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
        (- lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t)
    (h_joint : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      ∃ Q' : (ℝ × ℝ) →L[ℝ] ℝ,
        HasFDerivWithinAt (evalFormTwoVar (I := I) g_DT Φ_fam x v w) Q'
          ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT s).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
        ( ((-2) * ricciTensor (I := I) (g_DT t) (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
            + lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
                (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
          + (- lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
                (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)) )
        (Set.Ici 0) t := by
  intro t ht x v w
  let _ := hΦ_orbit; let _ := hΦ
  have h_push_moving := h_geom t ht x v w
  obtain ⟨Q', hQ'⟩ := h_joint t ht x v w
  exact DifferentialGeometry.PDE.RicciFlow.Pullback.deTurck_pullback_h_total_eval
    (I := I) g_bg g_DT T hDT_deriv Φ_fam t ⟨ht.1.le, ht.2⟩ x v w h_push_moving hQ'

end DifferentialGeometry.PDE.RicciFlow
