import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.FlatPairing
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatToCovariant
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.Transport


noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ODE

open Bundle Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.Pullback

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem trivFromE_basepoint (α : M) (v : TangentSpace I α) :
    trivFromE (I := I) α α v = v := by
  classical
  have hcore : trivFromE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) v

omit [InnerProductSpace ℝ E] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem leviCivita_basepoint_eq_rawFderiv_add_corrections
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π y : M, TangentSpace I y) (w : TangentSpace I α)
    (hα : α ∈ chartLeviCivitaGoodSet (I := I) α)
    (hX : MDiffAt (T% X) α)
    (hRdiff : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    (LeviCivita (I := I) g) X α w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + movingTrivCorrection (I := I) α X w
        + christoffelCorrection (I := I) g α α
            (chartE_section_repr (I := I) α X α) w := by
  classical
  have hbridge :
      trivFromE (I := I) α α (chartLeviCivitaInnerCLM (I := I) g α X α w)
        = (LeviCivita (I := I) g) X α w :=
    trivFromE_innerCLM_eq_leviCivita_at_orbit (I := I) g X α w hα hX
  rw [trivFromE_basepoint (I := I) α (chartLeviCivitaInnerCLM (I := I) g α X α w)] at hbridge
  rw [← hbridge]
  exact chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections (I := I) g α X w
    hRdiff hCdiff

end Bridge

section MainPairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem variational_flow_flat_paired_residual_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (T'v P'v T'w P'w : E →L[ℝ] E)
    (hv_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T'v P'v)
    (hw_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x w T'w P'w)
    (hflatval_v :
      T'v (mfderiv I I (Φ_fam t : M → M) x v) + P'v v
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x v)))
    (hflatval_w :
      T'w (mfderiv I I (Φ_fam t : M → M) x w) + P'w w
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x w)))
    (hbridge_v :
      (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
        = (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x v))
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hbridge_w :
      (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x w)
        = (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x w))
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)) :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + metricTransportResidual (I := I) g X Φ_fam t x v w) t := by
  classical
  set α := Φ_fam t x with hα_def
  set dΦv : TangentSpace I α := mfderiv I I (Φ_fam t : M → M) x v with hdΦv
  set dΦw : TangentSpace I α := mfderiv I I (Φ_fam t : M → M) x w with hdΦw
  set Vflat : TangentSpace I α := T'v dΦv + P'v v with hVflat
  set Wflat : TangentSpace I α := T'w dΦw + P'w w with hWflat
  set Xα : E := chartE_section_repr (I := I) α (X : ∀ y : M, TangentSpace I y) α with hXα
  set nablaV : TangentSpace I α :=
    (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) α dΦv with hnablaV
  set nablaW : TangentSpace I α :=
    (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) α dΦw with hnablaW
  set Cv : TangentSpace I α := christoffelCorrection (I := I) g α α Xα dΦv with hCv
  set Cw : TangentSpace I α := christoffelCorrection (I := I) g α α Xα dΦw with hCw
  set Fv : TangentSpace I α :=
    fderiv ℝ (chartRawRepr (I := I) α (X : ∀ y : M, TangentSpace I y))
        (extChartAt I α α) dΦv
      + movingTrivCorrection (I := I) α (X : ∀ y : M, TangentSpace I y) dΦv with hFv
  set Fw : TangentSpace I α :=
    fderiv ℝ (chartRawRepr (I := I) α (X : ∀ y : M, TangentSpace I y))
        (extChartAt I α α) dΦw
      + movingTrivCorrection (I := I) α (X : ∀ y : M, TangentSpace I y) dΦw with hFw
  have hVflat_eq : Vflat = -Fv := hflatval_v
  have hWflat_eq : Wflat = -Fw := hflatval_w
  have hbr_v : nablaV = Fv + Cv := hbridge_v
  have hbr_w : nablaW = Fw + Cw := hbridge_w
  have hcorr_v' : Vflat = -nablaV + Cv := by
    rw [hVflat_eq, hbr_v]; abel
  have hcorr_w' : Wflat = -nablaW + Cw := by
    rw [hWflat_eq, hbr_w]; abel
  have h_total :=
    variational_flow_inner_total_derivative (I := I) g Φ_fam t x v w Vflat Wflat hv_flat hw_flat
  have hval :
      g.inner α Vflat dΦw + g.inner α dΦv Wflat
        = -lieDerivMetric (I := I) g X α dΦv dΦw
          + metricTransportResidual (I := I) g X Φ_fam t x v w := by
    have hbil1 : (g.inner α) (-nablaV + Cv)
        = -(g.inner α) nablaV + (g.inner α) Cv := by
      rw [ContinuousLinearMap.map_add (g.inner α) _ _,
        ContinuousLinearMap.map_neg (g.inner α) _]
    have hslot1 : g.inner α Vflat dΦw
        = -g.inner α nablaV dΦw + g.inner α Cv dΦw := by
      rw [hcorr_v', hbil1, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.neg_apply]
    have hslot2 : g.inner α dΦv Wflat
        = -g.inner α dΦv nablaW + g.inner α dΦv Cw := by
      rw [hcorr_w', ContinuousLinearMap.map_add (g.inner α dΦv) _ _,
        ContinuousLinearMap.map_neg (g.inner α dΦv) _]
    have hcartan :
        -g.inner α nablaV dΦw + -g.inner α dΦv nablaW
          = -lieDerivMetric (I := I) g X α dΦv dΦw := by
      rw [hnablaV, hnablaW]
      exact (neg_lieDerivMetric_eq_neg_killing_sum (I := I) g X α dΦv dΦw).symm
    have hres : g.inner α Cv dΦw + g.inner α dΦv Cw
        = metricTransportResidual (I := I) g X Φ_fam t x v w := by
      rw [metricTransportResidual, hCv, hCw, hXα]
    rw [hslot1, hslot2, ← hcartan, ← hres]
    ring
  rwa [hval] at h_total

end MainPairing

end ODE
end RicciFlow
end PDE
end DifferentialGeometry
