import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Cancellation
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import Mathlib.Analysis.Calculus.Deriv.Mul

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

theorem variational_flow_inner_slot1_derivative
    (g : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) (V' : E)
    (hu : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E)) V' t) :
    HasDerivAt
      (fun s => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
      (g.inner (Φ_fam t x) V' (mfderiv I I (Φ_fam t : M → M) x w)) t := by
  set y := Φ_fam t x
  set c : E := mfderiv I I (Φ_fam t : M → M) x w with hc
  set L : E →L[ℝ] ℝ := (g.inner y).flip c with hL
  have hcomp : HasDerivAt (fun s => L (mfderiv I I (Φ_fam s : M → M) x v : E)) (L V') t :=
    L.hasFDerivAt.comp_hasDerivAt t hu
  have hfun : (fun s => L (mfderiv I I (Φ_fam s : M → M) x v : E))
      = (fun s => g.inner y (mfderiv I I (Φ_fam s : M → M) x v) c) := by
    funext s; rw [hL]; rfl
  rw [hfun] at hcomp
  have hval : L V' = g.inner y V' c := by rw [hL]; rfl
  rw [hval] at hcomp
  exact hcomp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

theorem variational_flow_inner_slot2_derivative
    (g : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) (W' : E)
    (hw : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x w : E)) W' t) :
    HasDerivAt
      (fun s => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (g.inner (Φ_fam t x) (mfderiv I I (Φ_fam t : M → M) x v) W') t := by
  set y := Φ_fam t x
  set c : E := mfderiv I I (Φ_fam t : M → M) x v with hc
  set L : E →L[ℝ] ℝ := g.inner y c with hL
  have hcomp : HasDerivAt (fun s => L (mfderiv I I (Φ_fam s : M → M) x w : E)) (L W') t :=
    L.hasFDerivAt.comp_hasDerivAt t hw
  have hfun : (fun s => L (mfderiv I I (Φ_fam s : M → M) x w : E))
      = (fun s => g.inner y c (mfderiv I I (Φ_fam s : M → M) x w)) := rfl
  rw [hfun] at hcomp
  exact hcomp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

theorem variational_flow_inner_total_derivative
    (g : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) (V' W' : E)
    (hu : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E)) V' t)
    (hw : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x w : E)) W' t) :
    HasDerivAt
      (fun s => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (g.inner (Φ_fam t x) V' (mfderiv I I (Φ_fam t : M → M) x w)
        + g.inner (Φ_fam t x) (mfderiv I I (Φ_fam t : M → M) x v) W') t := by
  set y := Φ_fam t x
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner y with hB
  set u : ℝ → E := fun s => (mfderiv I I (Φ_fam s : M → M) x v : E) with hudef
  set ww : ℝ → E := fun s => (mfderiv I I (Φ_fam s : M → M) x w : E) with hwdef
  have hprod := ContinuousLinearMap.hasDerivWithinAt_of_bilinear (B := B)
    (u := u) (v := ww) (s := Set.univ) (x := t)
    hu.hasDerivWithinAt hw.hasDerivWithinAt
  rw [hasDerivWithinAt_univ] at hprod
  rw [add_comm]
  exact hprod

def RawVariationalIdentity
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) : Prop :=
  HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
    (-(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)) t

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem variational_flow_feeds_cartan_witness
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (hv_raw : RawVariationalIdentity (I := I) g X Φ_fam t x v)
    (hw_raw : RawVariationalIdentity (I := I) g X Φ_fam t x w) :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w)) t := by
  set y := Φ_fam t x with hy
  set dΦv : E := mfderiv I I (Φ_fam t : M → M) x v with hdΦv
  set dΦw : E := mfderiv I I (Φ_fam t : M → M) x w with hdΦw
  set Vraw : E := -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) y dΦv with hVraw
  set Wraw : E := -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) y dΦw with hWraw
  have h_A := variational_flow_inner_slot1_derivative (I := I) g Φ_fam t x v w Vraw hv_raw
  have h_B := variational_flow_inner_slot2_derivative (I := I) g Φ_fam t x v w Wraw hw_raw
  have h_total := variational_flow_inner_total_derivative (I := I) g Φ_fam t x v w
    Vraw Wraw hv_raw hw_raw
  have h_A_value : g.inner y Vraw dΦw
      = -g.inner y ((LeviCivita (I := I) g)
          (X : ∀ x : M, TangentSpace I x) y dΦv) dΦw := by
    rw [hVraw, map_neg, ContinuousLinearMap.neg_apply]
  have h_B_value : g.inner y dΦv Wraw
      = -g.inner y dΦv ((LeviCivita (I := I) g)
          (X : ∀ x : M, TangentSpace I x) y dΦw) := by
    rw [hWraw, map_neg]
  exact hasDerivAt_pushforward_pairing_eq_neg_lieDerivMetric (I := I) g X Φ_fam t x v w
    (g.inner y Vraw dΦw + g.inner y dΦv Wraw)
    (g.inner y Vraw dΦw) (g.inner y dΦv Wraw)
    h_A h_B h_A_value h_B_value h_total rfl

end ODE
end RicciFlow
end PDE
end DifferentialGeometry
