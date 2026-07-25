import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Formula
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric
import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.PushforwardVF
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add


noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem neg_lieDerivMetric_eq_neg_killing_sum
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : M) (p q : TangentSpace I y) :
    -lieDerivMetric (I := I) g X y p q =
      (-g.inner y ((LeviCivita (I := I) g)
          (X : ∀ x : M, TangentSpace I x) y p) q)
      + (-g.inner y p ((LeviCivita (I := I) g)
          (X : ∀ x : M, TangentSpace I x) y q)) := by
  rw [cartan_formula_for_lie_deriv_metric (I := I) g X y p q]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lie_deriv_metric_neg_eq_pushforward_variation_sum
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : M) (p q : TangentSpace I y)
    (A' B' : ℝ)
    (h_A_value : A' = -g.inner y ((LeviCivita (I := I) g)
        (X : ∀ x : M, TangentSpace I x) y p) q)
    (h_B_value : B' = -g.inner y p ((LeviCivita (I := I) g)
        (X : ∀ x : M, TangentSpace I x) y q)) :
    A' + B' = -lieDerivMetric (I := I) g X y p q := by
  rw [h_A_value, h_B_value]
  rw [neg_lieDerivMetric_eq_neg_killing_sum (I := I) g X y p q]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem pushforward_pairing_deriv_eq_neg_lieDerivMetric_of_sum
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : M) (p q : TangentSpace I y)
    (A' B' Lpush : ℝ)
    (h_sum : Lpush = A' + B')
    (h_AB : A' + B' = -lieDerivMetric (I := I) g X y p q) :
    Lpush = -lieDerivMetric (I := I) g X y p q := by
  rw [h_sum, h_AB]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem cartan_cancellation_value_identity
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : M) (p q : TangentSpace I y)
    (A' B' Lpush : ℝ)
    (h_A_value : A' = -g.inner y ((LeviCivita (I := I) g)
        (X : ∀ x : M, TangentSpace I x) y p) q)
    (h_B_value : B' = -g.inner y p ((LeviCivita (I := I) g)
        (X : ∀ x : M, TangentSpace I x) y q))
    (h_sum : Lpush = A' + B') :
    Lpush = -lieDerivMetric (I := I) g X y p q :=
  pushforward_pairing_deriv_eq_neg_lieDerivMetric_of_sum (I := I) g X y p q A' B' Lpush h_sum
    (lie_deriv_metric_neg_eq_pushforward_variation_sum (I := I) g X y p q
      A' B' h_A_value h_B_value)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hasDerivAt_pushforward_pairing_eq_neg_lieDerivMetric
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M)
    (v w : TangentSpace I x)
    (Lpush A' B' : ℝ)
    (h_A : HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
      A' t)
    (h_B : HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      B' t)
    (h_A_value : A' = -g.inner (Φ_fam t x)
      ((LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v))
      (mfderiv I I (Φ_fam t : M → M) x w))
    (h_B_value : B' = -g.inner (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      ((LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x w)))
    (h_total : HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      Lpush t)
    (h_sum : Lpush = A' + B') :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w)) t := by
  let _ := h_A; let _ := h_B
  have hL : Lpush = -lieDerivMetric (I := I) g X (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) :=
    cartan_cancellation_value_identity (I := I) g X (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w)
      A' B' Lpush h_A_value h_B_value h_sum
  convert h_total using 1
  exact hL.symm

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurck_pullback_cartan_cancellation
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M)
    (v w : TangentSpace I x)
    (A' B' Lpush : ℝ)
    (h_A_value : A' = -(g_DT t).inner (Φ_fam t x)
      ((LeviCivita (I := I) (g_DT t))
        (deTurckVF (I := I) (g_DT t) g_bg :
            ∀ x : M, TangentSpace I x) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v))
      (mfderiv I I (Φ_fam t : M → M) x w))
    (h_B_value : B' = -(g_DT t).inner (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      ((LeviCivita (I := I) (g_DT t))
        (deTurckVF (I := I) (g_DT t) g_bg :
            ∀ x : M, TangentSpace I x) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x w)))
    (h_sum : Lpush = A' + B') :
    Lpush = -lieDerivMetric (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) :=
  cartan_cancellation_value_identity (I := I) (g_DT t)
    (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
    (mfderiv I I (Φ_fam t : M → M) x v)
    (mfderiv I I (Φ_fam t : M → M) x w)
    A' B' Lpush h_A_value h_B_value h_sum

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
