import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ChainRule
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciTensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Naturality.LieDerivativeMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Formula
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric
import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

theorem hasDerivAt_deTurck_pullback_eval_form
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (Lpush : ℝ)
    (h_DT_PDE : HasDerivAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
      ((-2 : ℝ) *
          ricciTensor (I := I) (g_DT t) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)
        + lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg)
            (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)) t)
    (h_pushforward_total : HasDerivAt
      (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      Lpush t)
    (h_cartan_cancellation :
      Lpush = - lieDerivMetric (I := I) (g_DT t)
        (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
    (h_total_eval : HasDerivAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (((-2 : ℝ) *
            ricciTensor (I := I) (g_DT t) (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)
              (mfderiv I I (Φ_fam t : M → M) x w)
          + lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg)
              (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)
              (mfderiv I I (Φ_fam t : M → M) x w))
        + Lpush) t) :
    HasDerivAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((-2 : ℝ) *
        ricciTensor (I := I) (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) t := by
  let _ := h_DT_PDE; let _ := h_pushforward_total
  set L : ℝ := lieDerivMetric (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) with hL_def
  set R_DT : ℝ := ricciTensor (I := I) (g_DT t) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) with hR_DT_def
  set R_fam : ℝ := ricciTensor (I := I)
      (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w with hR_fam_def
  have h_cancel :
      (((-2 : ℝ) * R_DT + L) + Lpush) = (-2 : ℝ) * R_DT := by
    rw [h_cartan_cancellation]
    ring
  have h_ric_nat : R_DT = R_fam := by
    rw [hR_fam_def, hR_DT_def]
    exact (ricci_tensor_pullback_natural_under_diffeomorphism (I := I) (g_DT t) (Φ_fam t) x v w).symm
  have h_value :
      (((-2 : ℝ) * R_DT + L) + Lpush) = (-2 : ℝ) * R_fam := by
    rw [h_cancel, h_ric_nat]
  have h_total_eval' :
      HasDerivAt
        (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w))
        ((-2 : ℝ) * R_fam) t := by
    convert h_total_eval using 1
    exact h_value.symm
  exact h_total_eval'

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
