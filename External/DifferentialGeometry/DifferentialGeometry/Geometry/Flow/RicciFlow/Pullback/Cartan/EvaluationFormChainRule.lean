import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ChainRule
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.TimeDerivativeChainRule
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real


noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

theorem evalForm_diagonal_hasDerivWithinAt_of_jointFDeriv
    (Q : ℝ × ℝ → ℝ) (t : ℝ) (Q' : (ℝ × ℝ) →L[ℝ] ℝ)
    (hQ : HasFDerivWithinAt Q Q' ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt (fun s : ℝ => Q (s, s)) (Q' (1, 0) + Q' (0, 1))
      (Set.Ici (0 : ℝ)) t := by
  have hδ : HasDerivWithinAt (fun s : ℝ => (s, s)) ((1 : ℝ), (1 : ℝ))
      (Set.Ici (0 : ℝ)) t :=
    (hasDerivWithinAt_id t (Set.Ici (0 : ℝ))).prodMk
      (hasDerivWithinAt_id t (Set.Ici (0 : ℝ)))
  have hmaps : Set.MapsTo (fun s : ℝ => (s, s)) (Set.Ici (0 : ℝ))
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) := fun s hs => ⟨hs, Set.mem_univ _⟩
  have hcomp : HasDerivWithinAt (Q ∘ fun s : ℝ => (s, s)) (Q' ((1 : ℝ), (1 : ℝ)))
      (Set.Ici (0 : ℝ)) t :=
    HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (f := fun s : ℝ => (s, s)) t hQ hδ
      hmaps (by simp)
  have hval : Q' ((1 : ℝ), (1 : ℝ)) = Q' (1, 0) + Q' (0, 1) := by
    rw [← map_add]; congr 1; ext <;> simp
  rwa [hval] at hcomp

theorem evalForm_jointFDeriv_partial_fst
    (Q : ℝ × ℝ → ℝ) (t : ℝ) (Q' : (ℝ × ℝ) →L[ℝ] ℝ)
    (hQ : HasFDerivWithinAt Q Q' ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt (fun s : ℝ => Q (s, t)) (Q' (1, 0)) (Set.Ici (0 : ℝ)) t := by
  have hε : HasDerivWithinAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ))
      (Set.Ici (0 : ℝ)) t :=
    (hasDerivWithinAt_id t (Set.Ici (0 : ℝ))).prodMk
      (hasDerivWithinAt_const t (Set.Ici (0 : ℝ)) t)
  have hmaps : Set.MapsTo (fun s : ℝ => (s, t)) (Set.Ici (0 : ℝ))
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) := fun s hs => ⟨hs, Set.mem_univ _⟩
  exact HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (f := fun s : ℝ => (s, t)) t hQ hε
    hmaps (by simp)

theorem evalForm_jointFDeriv_partial_snd
    (Q : ℝ × ℝ → ℝ) (t : ℝ) (ht : (0 : ℝ) ≤ t) (Q' : (ℝ × ℝ) →L[ℝ] ℝ)
    (hQ : HasFDerivWithinAt Q Q' ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt (fun s : ℝ => Q (t, s)) (Q' (0, 1)) (Set.Ici (0 : ℝ)) t := by
  have hε : HasDerivWithinAt (fun s : ℝ => (t, s)) ((0 : ℝ), (1 : ℝ))
      (Set.Ici (0 : ℝ)) t :=
    (hasDerivWithinAt_const t (Set.Ici (0 : ℝ)) t).prodMk
      (hasDerivWithinAt_id t (Set.Ici (0 : ℝ)))
  have hmaps : Set.MapsTo (fun s : ℝ => (t, s)) (Set.Ici (0 : ℝ))
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) := fun s _ => ⟨ht, Set.mem_univ _⟩
  exact HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (f := fun s : ℝ => (t, s)) t hQ hε
    hmaps (by simp)

theorem hasDerivWithinAt_Ici_unique
    {f : ℝ → ℝ} {t a b : ℝ} (ht : (0 : ℝ) ≤ t)
    (ha : HasDerivWithinAt f a (Set.Ici (0 : ℝ)) t)
    (hb : HasDerivWithinAt f b (Set.Ici (0 : ℝ)) t) : a = b := by
  have hu : UniqueDiffWithinAt ℝ (Set.Ici (0 : ℝ)) t := uniqueDiffOn_Ici (0 : ℝ) t ht
  rw [← ha.derivWithin hu, ← hb.derivWithin hu]

def evalFormTwoVar
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) : ℝ × ℝ → ℝ :=
  fun p => (g_DT p.1).inner (Φ_fam p.2 x)
    (mfderiv I I (Φ_fam p.2 : M → M) x v)
    (mfderiv I I (Φ_fam p.2 : M → M) x w)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem evalFormTwoVar_diag
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => evalFormTwoVar (I := I) g_DT Φ_fam x v w (s, s))
      = (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem evalFormTwoVar_fst
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => evalFormTwoVar (I := I) g_DT Φ_fam x v w (s, t))
      = (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem evalFormTwoVar_snd
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => evalFormTwoVar (I := I) g_DT Φ_fam x v w (t, s))
      = (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurck_evalForm_chain_hasDerivWithinAt
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (ht : (0 : ℝ) ≤ t) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_metric : HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w)) G' (Set.Ici (0 : ℝ)) t)
    (h_push : HasDerivWithinAt
      (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w)) L' (Set.Ici (0 : ℝ)) t)
    {Q' : (ℝ × ℝ) →L[ℝ] ℝ}
    (h_joint : HasFDerivWithinAt (evalFormTwoVar (I := I) g_DT Φ_fam x v w) Q'
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w)) (G' + L') (Set.Ici (0 : ℝ)) t := by
  set Q := evalFormTwoVar (I := I) g_DT Φ_fam x v w with hQ
  have hdiag : HasDerivWithinAt (fun s : ℝ => Q (s, s)) (Q' (1, 0) + Q' (0, 1))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_diagonal_hasDerivWithinAt_of_jointFDeriv Q t Q' h_joint
  have hpart1 : HasDerivWithinAt (fun s : ℝ => Q (s, t)) (Q' (1, 0))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_jointFDeriv_partial_fst Q t Q' h_joint
  have hpart2 : HasDerivWithinAt (fun s : ℝ => Q (t, s)) (Q' (0, 1))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_jointFDeriv_partial_snd Q t ht Q' h_joint
  have hmetric_eq : (fun s : ℝ => Q (s, t))
      = (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) := by
    rw [hQ]; exact evalFormTwoVar_fst (I := I) g_DT Φ_fam t x v w
  have hG : Q' (1, 0) = G' :=
    hasDerivWithinAt_Ici_unique ht (hmetric_eq ▸ hpart1) h_metric
  have hpush_eq : (fun s : ℝ => Q (t, s))
      = (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := by
    rw [hQ]; exact evalFormTwoVar_snd (I := I) g_DT Φ_fam t x v w
  have hL : Q' (0, 1) = L' :=
    hasDerivWithinAt_Ici_unique ht (hpush_eq ▸ hpart2) h_push
  rw [hG, hL] at hdiag
  have hdiag_eq : (fun s : ℝ => Q (s, s))
      = (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := by
    rw [hQ]; exact evalFormTwoVar_diag (I := I) g_DT Φ_fam x v w
  rwa [hdiag_eq] at hdiag

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurck_pullback_h_total_eval
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
        (deTurckRicciRHS (I := I) g_bg (g_DT s) y a b) (Set.Ici 0) s)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T) (x : M) (v w : TangentSpace I x)
    (h_push_moving : HasDerivWithinAt
      (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (- lieDerivMetric (I := I) (g_DT t)
          (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t)
    {Q' : (ℝ × ℝ) →L[ℝ] ℝ}
    (h_joint : HasFDerivWithinAt (evalFormTwoVar (I := I) g_DT Φ_fam x v w) Q'
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
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
              (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t := by
  have h_metric := DifferentialGeometry.PDE.RicciFlow.deTurck_metric_slot_hasDerivWithinAt
    (I := I) g_bg g_DT T hDT_deriv Φ_fam t ht x v w
  exact deTurck_evalForm_chain_hasDerivWithinAt (I := I) g_DT Φ_fam t ht.1 x v w _ _
    h_metric h_push_moving h_joint

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
