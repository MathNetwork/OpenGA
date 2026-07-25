import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivita
import DifferentialGeometry.Geometry.Connection.MLieBracket
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.PushforwardVF
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Formula
import DifferentialGeometry.Geometry.Connection.LeviCivita.CovariantDerivativePointwise
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ChainRule
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

theorem lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x)
    (hY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)))
    (hPush_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward Φ Y x)))
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetric (I := I) (Diffeomorph.pullbackMetric g Φ)
        ⟨Y, hY_smooth⟩ x v w
      = lieDerivMetric (I := I) g
          ⟨Diffeomorph.pushforward Φ Y, hPush_smooth⟩ (Φ x)
            (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  rw [cartan_formula_for_lie_deriv_metric (I := I)
    (Diffeomorph.pullbackMetric g Φ) ⟨Y, hY_smooth⟩ x v w]
  rw [cartan_formula_for_lie_deriv_metric (I := I) g
    ⟨Diffeomorph.pushforward Φ Y, hPush_smooth⟩ (Φ x)
    (mfderiv I I (⇑Φ) x v) (mfderiv I I (⇑Φ) x w)]
  change (Diffeomorph.pullbackMetric g Φ).inner x
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x v) w
      + (Diffeomorph.pullbackMetric g Φ).inner x v
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x w)
    = g.inner (Φ x) ((LeviCivita (I := I) g)
        (Diffeomorph.pushforward Φ Y) (Φ x) (mfderiv I I (⇑Φ) x v))
        (mfderiv I I (⇑Φ) x w)
      + g.inner (Φ x) (mfderiv I I (⇑Φ) x v) ((LeviCivita (I := I) g)
        (Diffeomorph.pushforward Φ Y) (Φ x) (mfderiv I I (⇑Φ) x w))
  rw [pullback_metric_evaluation_formula (I := I) g Φ x
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x v) w,
      pullback_metric_evaluation_formula (I := I) g Φ x v
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x w)]
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hY_mdiff : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x :=
    (hY_smooth x).mdifferentiableAt hinfty
  rw [LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise (I := I) g Φ v hY_mdiff,
      LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise (I := I) g Φ w hY_mdiff]

theorem assemble_lie_deriv_naturality
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x)
    (hY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)))
    (hPush_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward Φ Y x))) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      lieDerivMetric (I := I) (Diffeomorph.pullbackMetric g Φ)
          ⟨Y, hY_smooth⟩ x v w
        = lieDerivMetric (I := I) g
            ⟨Diffeomorph.pushforward Φ Y, hPush_smooth⟩ (Φ x)
              (mfderiv I I Φ x v) (mfderiv I I Φ x w) :=
  fun x v w =>
    lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise g Φ Y hY_smooth hPush_smooth x v w

end DifferentialGeometry.PDE.RicciFlow.Pullback
