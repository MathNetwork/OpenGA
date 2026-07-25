import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullback
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.FlatPairing

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open Bundle Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

theorem hamiltonDeTurck_pullback_isRicciFlow_flat
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E))
    (hv_flat : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v))
    (hcorr : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (deTurckVF (I := I) (g_DT t) g_bg : ∀ y : M, TangentSpace I y)
                (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hbase : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w))
        (-metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t)
    (h_total_eval : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
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
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
      ((-2 : ℝ) * ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) (Set.Ici 0) t := by
  have _h_metric := deTurck_metric_slot_hasDerivWithinAt (I := I)
    g_bg g_DT T hDT_deriv Φ_fam t ht x v w
  have _h_base := hbase t ht x v w
  have _h_push := variational_flow_flat_pairing_hasDerivWithinAt (I := I)
    (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w
    (T' t x v) (P' t x v) (T' t x w) (P' t x w)
    (hv_flat t ht x v) (hv_flat t ht x w) (hcorr t ht x v) (hcorr t ht x w)
  exact deTurck_pullback_eval_value_hasDerivWithinAt (I := I)
    g_bg g_DT Φ_fam t x v w (h_total_eval t ht x v w)

theorem hamiltonDeTurck_pullback_ricciFlow_family_flat
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E))
    (hv_flat : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v))
    (hcorr : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (deTurckVF (I := I) (g_DT t) g_bg : ∀ y : M, TangentSpace I y)
                (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hbase : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w))
        (-metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t)
    (h_total_eval : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
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
                (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t) :
    ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
      (∀ s : ℝ, g_fam s = Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) ∧
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
          ((-2 : ℝ) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici 0) t := by
  refine ⟨fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s), fun _ => rfl, ?_⟩
  intro t ht x v w
  exact hamiltonDeTurck_pullback_isRicciFlow_flat (I := I)
    g_bg g_DT T hDT_deriv Φ_fam T' P' hv_flat hcorr hbase h_total_eval t ht x v w

end RicciFlow
end PDE
end DifferentialGeometry
