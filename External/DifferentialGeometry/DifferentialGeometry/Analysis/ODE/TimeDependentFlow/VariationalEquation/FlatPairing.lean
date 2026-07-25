import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.VariationalFlow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def negCovariantSlotValue
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x) : E :=
  -(LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
    (mfderiv I I (Φ_fam t : M → M) x v)

def metricTransportResidual
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v w : TangentSpace I x) : ℝ :=
  g.inner (Φ_fam t x)
      (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
        (chartE_section_repr (I := I) (Φ_fam t x)
          (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
        (mfderiv I I (Φ_fam t : M → M) x v))
      (mfderiv I I (Φ_fam t : M → M) x w)
    + g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
          (chartE_section_repr (I := I) (Φ_fam t x)
            (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
          (mfderiv I I (Φ_fam t : M → M) x w))

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem variational_flow_flat_pairing_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (T'v P'v T'w P'w : E →L[ℝ] E)
    (hv_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T'v P'v)
    (hw_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x w T'w P'w)
    (hcorr_v :
      T'v (mfderiv I I (Φ_fam t : M → M) x v) + P'v v
        = negCovariantSlotValue (I := I) g X Φ_fam t x v
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hcorr_w :
      T'w (mfderiv I I (Φ_fam t : M → M) x w) + P'w w
        = negCovariantSlotValue (I := I) g X Φ_fam t x w
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
  set α := Φ_fam t x with hα
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
  have hcorr_v' : Vflat = -nablaV + Cv := by
    rw [hcorr_v]; rfl
  have hcorr_w' : Wflat = -nablaW + Cw := by
    rw [hcorr_w]; rfl
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

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem variational_flow_flat_pairing_hasDerivWithinAt
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (T'v P'v T'w P'w : E →L[ℝ] E)
    (hv_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T'v P'v)
    (hw_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x w T'w P'w)
    (hcorr_v :
      T'v (mfderiv I I (Φ_fam t : M → M) x v) + P'v v
        = negCovariantSlotValue (I := I) g X Φ_fam t x v
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hcorr_w :
      T'w (mfderiv I I (Φ_fam t : M → M) x w) + P'w w
        = negCovariantSlotValue (I := I) g X Φ_fam t x w
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + metricTransportResidual (I := I) g X Φ_fam t x v w) (Set.Ici 0) t :=
  (variational_flow_flat_pairing_hasDerivAt (I := I) g X Φ_fam t x v w
    T'v P'v T'w P'w hv_flat hw_flat hcorr_v hcorr_w).hasDerivWithinAt

end ODE
end RicciFlow
end PDE
end DifferentialGeometry
