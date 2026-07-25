import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ChainRule
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.Basic


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

theorem trilinear_eval_hasDerivWithinAt
    {B : ℝ → (E →L[ℝ] E →L[ℝ] ℝ)} {a b : ℝ → E} {S : Set ℝ} {t : ℝ}
    {B' : E →L[ℝ] E →L[ℝ] ℝ} {a' b' : E}
    (hB : HasDerivWithinAt B B' S t) (ha : HasDerivWithinAt a a' S t)
    (hb : HasDerivWithinAt b b' S t) :
    HasDerivWithinAt (fun s : ℝ => B s (a s) (b s))
      ((B' (a t) (b t) + B t a' (b t)) + B t (a t) b') S t := by
  have step1 := hB.clm_apply ha
  have step2 := step1.clm_apply hb
  convert step2 using 1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

theorem trilinear_eval_hasDerivAt
    {B : ℝ → (E →L[ℝ] E →L[ℝ] ℝ)} {a b : ℝ → E} {t : ℝ}
    {B' : E →L[ℝ] E →L[ℝ] ℝ} {a' b' : E}
    (hB : HasDerivAt B B' t) (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s : ℝ => B s (a s) (b s))
      ((B' (a t) (b t) + B t a' (b t)) + B t (a t) b') t := by
  have step1 := hB.clm_apply ha
  have step2 := step1.clm_apply hb
  convert step2 using 1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem pullback_eval_form_hasDerivAt_of_slots
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t) :
    HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((B' (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
          + ((g_fam t).inner (Φ_fam t x)) a' (mfderiv I I (Φ_fam t : M → M) x w))
        + ((g_fam t).inner (Φ_fam t x)) (mfderiv I I (Φ_fam t : M → M) x v) b') t :=
  trilinear_eval_hasDerivAt hB ha hb

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem pullback_eval_form_hasDerivWithinAt_of_slots
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {S : Set ℝ} (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (hB : HasDerivWithinAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' S t)
    (ha : HasDerivWithinAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' S t)
    (hb : HasDerivWithinAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' S t) :
    HasDerivWithinAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((B' (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
          + ((g_fam t).inner (Φ_fam t x)) a' (mfderiv I I (Φ_fam t : M → M) x w))
        + ((g_fam t).inner (Φ_fam t x)) (mfderiv I I (Φ_fam t : M → M) x v) b') S t :=
  trilinear_eval_hasDerivWithinAt hB ha hb

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem pullback_eval_form_total_hasDerivAt
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (G' A' B'' : ℝ)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t)
    (hG' : G' = B' (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hA' : A' = ((g_fam t).inner (Φ_fam t x)) a'
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hB_val : B'' = ((g_fam t).inner (Φ_fam t x))
      (mfderiv I I (Φ_fam t : M → M) x v) b') :
    HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + A' + B'') t := by
  rw [hG', hA', hB_val]
  exact pullback_eval_form_hasDerivAt_of_slots g_fam Φ_fam t x v w B' a' b' hB ha hb

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem pullback_eval_form_chain_hasDerivAt
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (G' L' : ℝ)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t)
    (hG' : G' = B' (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hL' : L' = ((g_fam t).inner (Φ_fam t x)) a'
        (mfderiv I I (Φ_fam t : M → M) x w)
      + ((g_fam t).inner (Φ_fam t x))
        (mfderiv I I (Φ_fam t : M → M) x v) b') :
    HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + L') t := by
  have hkey := pullback_eval_form_hasDerivAt_of_slots g_fam Φ_fam t x v w B' a' b' hB ha hb
  have hval :
      (B' (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
          + ((g_fam t).inner (Φ_fam t x)) a' (mfderiv I I (Φ_fam t : M → M) x w))
        + ((g_fam t).inner (Φ_fam t x)) (mfderiv I I (Φ_fam t : M → M) x v) b'
      = G' + L' := by
    rw [hG', hL']; ring
  rwa [hval] at hkey

omit [NeZero (Module.finrank ℝ E)] in
theorem pullback_metric_chain_rule_of_slots
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (G' L' : ℝ)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t)
    (hG' : G' = B' (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hL' : L' = ((g_fam t).inner (Φ_fam t x)) a'
        (mfderiv I I (Φ_fam t : M → M) x w)
      + ((g_fam t).inner (Φ_fam t x))
        (mfderiv I I (Φ_fam t : M → M) x v) b') :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  pullback_time_derivative_chain_rule g_fam Φ_fam t x v w G' L'
    (pullback_eval_form_chain_hasDerivAt g_fam Φ_fam t x v w B' a' b' G' L'
      hB ha hb hG' hL')

omit [NeZero (Module.finrank ℝ E)] in
theorem pullback_metric_chain_rule_of_slots_total
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (G' A' B'' : ℝ)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t)
    (hG' : G' = B' (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hA' : A' = ((g_fam t).inner (Φ_fam t x)) a'
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hB_val : B'' = ((g_fam t).inner (Φ_fam t x))
      (mfderiv I I (Φ_fam t : M → M) x v) b') :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + A' + B'') t :=
  pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w
    (pullback_eval_form_total_hasDerivAt g_fam Φ_fam t x v w B' a' b' G' A' B''
      hB ha hb hG' hA' hB_val)

end DifferentialGeometry.PDE.RicciFlow.Pullback
