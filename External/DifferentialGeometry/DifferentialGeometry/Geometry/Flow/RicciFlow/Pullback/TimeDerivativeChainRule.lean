import DifferentialGeometry.Geometry.Metric.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_eq_inner_mfderiv
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w
      = (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w) := by
  change Diffeomorph.pullbackInner (g_fam s) (Φ_fam s) x v w
      = (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_funext
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      = (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := by
  funext s
  exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w s

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_hasDerivWithinAt_of_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_eval : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t := by
  refine h_eval.congr ?_ ?_
  · intro u _
    exact (pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w u).symm
  · exact (pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w t).symm

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_hasDerivWithinAt_to_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_pullback : HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t) :
    HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t := by
  refine h_pullback.congr ?_ ?_
  · intro u _
    exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w u
  · exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w t

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_hasDerivWithinAt_iff
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t
    ↔ HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t :=
  ⟨pullbackMetric_inner_hasDerivWithinAt_to_eval g_fam Φ_fam x v w,
    pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_hasDerivAt_of_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_eval : HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t) :
    HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t := by
  rw [← hasDerivWithinAt_univ] at h_eval ⊢
  exact pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_eval

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_hasDerivAt_to_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_pullback : HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t) :
    HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t := by
  rw [← hasDerivWithinAt_univ] at h_pullback ⊢
  exact pullbackMetric_inner_hasDerivWithinAt_to_eval g_fam Φ_fam x v w h_pullback

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_hasDerivAt_iff
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t
    ↔ HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t :=
  ⟨pullbackMetric_inner_hasDerivAt_to_eval g_fam Φ_fam x v w,
    pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_hasDerivWithinAt_product_rule
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' A' B' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_total : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      (G' + A' + B') s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      (G' + A' + B') s t :=
  pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_total

omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackMetric_inner_hasDerivWithinAt_sum
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' L' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_total : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      (G' + L') s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      (G' + L') s t :=
  pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_total

end DifferentialGeometry.PDE.RicciFlow.Pullback
