import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciTensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.VariationalFlow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.PushforwardSmooth
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import Mathlib.Analysis.Calculus.Deriv.Basic

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurck_metric_slot_hasDerivWithinAt
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
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

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurck_pushforward_slot_hasDerivWithinAt
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (hv_raw : RawVariationalIdentity (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v)
    (hw_raw : RawVariationalIdentity (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x w) :
    HasDerivWithinAt
      (fun s : ℝ => (g_DT t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (- lieDerivMetric (I := I) (g_DT t)
          (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t :=
  (variational_flow_feeds_cartan_witness (I := I) (g_DT t)
    (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w hv_raw hw_raw).hasDerivWithinAt

theorem deTurck_pullback_eval_value_hasDerivWithinAt
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (h_total_eval : HasDerivWithinAt
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
    HasDerivWithinAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
      ((-2 : ℝ) * ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) (Set.Ici 0) t := by
  set L : ℝ := lieDerivMetric (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) with hL_def
  set R_DT : ℝ := ricciTensor (I := I) (g_DT t) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) with hR_DT_def
  set R_fam : ℝ := ricciTensor (I := I)
      (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w with hR_fam_def
  have h_cancel : (((-2 : ℝ) * R_DT + L) + (-L)) = (-2 : ℝ) * R_DT := by ring
  have h_ric_nat : R_DT = R_fam := by
    rw [hR_fam_def, hR_DT_def]
    exact (ricci_tensor_pullback_natural_under_diffeomorphism (I := I) (g_DT t) (Φ_fam t) x v w).symm
  have h_value : (((-2 : ℝ) * R_DT + L) + (-L)) = (-2 : ℝ) * R_fam := by
    rw [h_cancel, h_ric_nat]
  have h_eval' : HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((-2 : ℝ) * R_fam) (Set.Ici 0) t := by
    convert h_total_eval using 1
    exact h_value.symm
  exact pullbackMetric_inner_hasDerivWithinAt_of_eval (I := I) g_DT Φ_fam x v w h_eval'

theorem hamilton_deturck_pullback_solves_ricci_flow
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hv_raw : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentity (I := I) (g_DT t)
        (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v)
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
  have _h_push := deTurck_pushforward_slot_hasDerivWithinAt (I := I)
    g_bg g_DT Φ_fam t x v w (hv_raw t ht x v) (hv_raw t ht x w)
  exact deTurck_pullback_eval_value_hasDerivWithinAt (I := I)
    g_bg g_DT Φ_fam t x v w (h_total_eval t ht x v w)

theorem hamiltonDeTurck_pullback_ricciFlow_family
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hv_raw : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentity (I := I) (g_DT t)
        (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v)
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
  exact hamilton_deturck_pullback_solves_ricci_flow (I := I)
    g_bg g_DT T hDT_deriv Φ_fam hv_raw h_total_eval t ht x v w

end RicciFlow
end PDE
end DifferentialGeometry
