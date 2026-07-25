




















import DifferentialGeometry.Geometry.Metric.Pullback
import DifferentialGeometry.Geometry.Metric.MetricBallMonotone
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Bundle.ClmSectionSmooth
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private lemma infty_ne_zero_cross : (∞ : WithTop ℕ∞) ≠ 0 := by decide









noncomputable def Diffeomorph.pullbackInnerCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let step1 : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) →L[ℝ] ℝ :=
    (g.inner (Φ x)).comp (mfderiv I J Φ x)
  let precompOp : (TangentSpace J (Φ x) →L[ℝ] ℝ) →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (mfderiv I J Φ x)
  precompOp.comp step1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInnerCross_symm
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInnerCross g Φ x v w
      = Diffeomorph.pullbackInnerCross g Φ x w v := by
  unfold Diffeomorph.pullbackInnerCross
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  exact g.symm (Φ x) _ _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInnerCross_pos
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < Diffeomorph.pullbackInnerCross g Φ x v v := by
  unfold Diffeomorph.pullbackInnerCross
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  set hΦeq : TangentSpace I x ≃L[ℝ] TangentSpace J (Φ x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero_cross x with hΦeq_def
  have hvImg : mfderiv I J Φ x v ≠ 0 := by
    have h1 : hΦeq v ≠ 0 := (hΦeq.map_ne_zero_iff).mpr hv
    have h2 : (hΦeq : TangentSpace I x →L[ℝ] TangentSpace J (Φ x)) v
        = mfderiv I J Φ x v := by
      rw [hΦeq_def]
      have heq := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) infty_ne_zero_cross
      exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) => f v) heq
    have hcoe : (hΦeq : TangentSpace I x → TangentSpace J (Φ x)) v = hΦeq v := rfl
    rw [← h2]; exact fun h => h1 (by simpa [hcoe] using h)
  exact g.pos (Φ x) _ hvImg




omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem inner_comp_smooth_along_diffeoCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      ((fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g.inner b)) ∘ (Φ : M → N)) :=
  g.contMDiff.comp Φ.contMDiff

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
private theorem pullbackInnerCross_eval
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInnerCross g Φ x v w
      = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) := by
  unfold Diffeomorph.pullbackInnerCross
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem mfderiv_eq_mfderivCLE_applyCross
    (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) (v : TangentSpace I x) :
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero_cross x v
      = mfderiv I J Φ x v := by
  have h := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) infty_ne_zero_cross
  exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) => f v) h



omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] in
theorem Diffeomorph.pullbackInnerCross_isVonNBounded
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    ∀ x : M, Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | Diffeomorph.pullbackInnerCross g Φ x v v < 1} := by
  intro x
  set hΦeq := Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero_cross x with hΦeq_def
  have hg := g.isVonNBounded (Φ x)
  have himg := hg.image (hΦeq.symm : TangentSpace J (Φ x) →L[ℝ] TangentSpace I x)
  have hseteq :
      {v : TangentSpace I x | Diffeomorph.pullbackInnerCross g Φ x v v < 1}
        = ((hΦeq.symm : TangentSpace J (Φ x) →L[ℝ] TangentSpace I x) : _ → _)
            '' {w : TangentSpace J (Φ x) | g.inner (Φ x) w w < 1} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image]
    refine ⟨fun hv => ⟨hΦeq v, ?_, ?_⟩, ?_⟩
    · have h1 := pullbackInnerCross_eval (g := g) (Φ := Φ) x v v
      rw [h1] at hv
      have h2 := mfderiv_eq_mfderivCLE_applyCross (Φ := Φ) (x := x) v
      rw [← h2] at hv
      exact hv
    · change (hΦeq.symm : TangentSpace J (Φ x) → TangentSpace I x) (hΦeq v) = v
      exact hΦeq.symm_apply_apply v
    · rintro ⟨w, hw, rfl⟩
      have hsym : ((hΦeq.symm : TangentSpace J (Φ x) →L[ℝ] TangentSpace I x) :
            TangentSpace J (Φ x) → TangentSpace I x) w = hΦeq.symm w := rfl
      rw [hsym]
      rw [pullbackInnerCross_eval]
      have hImg : mfderiv I J Φ x (hΦeq.symm w) = w := by
        have hmap := mfderiv_eq_mfderivCLE_applyCross (Φ := Φ) (x := x) (hΦeq.symm w)
        rw [← hmap]
        exact hΦeq.apply_symm_apply w
      rw [hImg]; exact hw
  rw [hseteq]
  exact himg





omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem mfderiv_apply_section_smooth_along_diffeoCross
    (Φ : M ≃ₘ⟮I, J⟯ N)
    (Y : ∀ x : M, TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) ∞
      (fun x : M => TotalSpace.mk' F (E := (TangentSpace J : N → Type _))
        (Φ x) (mfderiv I J (Φ : M → N) x (Y x))) := by
  have h_tangentMap : ContMDiff I.tangent J.tangent ∞ (tangentMap I J (Φ : M → N)) :=
    Φ.contMDiff.contMDiff_tangentMap (le_refl _)
  have h := h_tangentMap.comp hY
  exact h



noncomputable def Diffeomorph.pullbackMetricCross
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    SmoothRiemannianMetric I M where
  inner x := Diffeomorph.pullbackInnerCross g Φ x
  symm x v w := Diffeomorph.pullbackInnerCross_symm g Φ x v w
  pos x v hv := Diffeomorph.pullbackInnerCross_pos g Φ x v hv
  isVonNBounded x := Diffeomorph.pullbackInnerCross_isVonNBounded g Φ x
  contMDiff := by
    classical
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun x : M => Diffeomorph.pullbackInnerCross g Φ x)
    intro Y
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun _ : M => ℝ)
      (φ := fun x : M => Diffeomorph.pullbackInnerCross g Φ x (Y x))
    intro W
    have hv := mfderiv_apply_section_smooth_along_diffeoCross Φ (fun x => Y x) Y.contMDiff
    have hw := mfderiv_apply_section_smooth_along_diffeoCross Φ (fun x => W x) W.contMDiff
    have hg : ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
        (fun x : M => TotalSpace.mk'
          (F →L[ℝ] F →L[ℝ] ℝ)
          (E := fun b : N => TangentSpace J b →L[ℝ] TangentSpace J b →L[ℝ] ℝ)
          (Φ x) (g.inner (Φ x))) :=
      g.contMDiff.comp Φ.contMDiff
    have h_total : ContMDiff I (J.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ
          (E := Bundle.Trivial N ℝ)
          (Φ x)
          (g.inner (Φ x) (mfderiv I J (Φ : M → N) x (Y x))
            (mfderiv I J (Φ : M → N) x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun b : N => TangentSpace J b)
        (E₂ := fun b : N => TangentSpace J b)
        (E₃ := fun _ : N => ℝ)
        (b := fun x : M => Φ x)
        (ψ := fun x : M => g.inner (Φ x))
        (v := fun x : M => mfderiv I J (Φ : M → N) x (Y x))
        (w := fun x : M => mfderiv I J (Φ : M → N) x (W x))
        hg hv hw
    have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g.inner (Φ x) (mfderiv I J (Φ : M → N) x (Y x))
            (mfderiv I J (Φ : M → N) x (W x))) := by
      intro x
      have h_at := h_total x
      rw [contMDiffAt_totalSpace] at h_at
      have := h_at.2
      convert this using 1
    have h_pullback_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Diffeomorph.pullbackInnerCross g Φ x (Y x) (W x)) := by
      have h_eq : (fun x : M => Diffeomorph.pullbackInnerCross g Φ x (Y x) (W x))
          = fun x : M => g.inner (Φ x) (mfderiv I J (Φ : M → N) x (Y x))
              (mfderiv I J (Φ : M → N) x (W x)) := by
        funext x; exact pullbackInnerCross_eval g Φ x (Y x) (W x)
      rw [h_eq]; exact h_scalar
    intro x
    rw [contMDiffAt_section]
    refine (h_pullback_smooth.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards with y
    change Diffeomorph.pullbackInnerCross g Φ y (Y y) (W y) =
      (trivializationAt ℝ (Bundle.Trivial M ℝ) x
        ⟨y, Diffeomorph.pullbackInnerCross g Φ y (Y y) (W y)⟩).2
    rfl


omit [FiniteDimensional ℝ F] in
theorem diffeomorph_pullback_metric_existsCross
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    ∃ g' : SmoothRiemannianMetric I M, g' = Diffeomorph.pullbackMetricCross g Φ :=
  ⟨Diffeomorph.pullbackMetricCross g Φ, rfl⟩




omit [FiniteDimensional ℝ F] in
theorem Diffeomorph.pullbackMetricCross_inner
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetricCross g Φ).inner x v w
      = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) :=
  pullbackInnerCross_eval g Φ x v w



omit [FiniteDimensional ℝ F] in
theorem Diffeomorph.pullbackInnerCross_contMDiff
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        ((Diffeomorph.pullbackInnerCross g Φ x : E →L[ℝ] E →L[ℝ] ℝ))) :=
  (Diffeomorph.pullbackMetricCross g Φ).contMDiff



omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem Diffeomorph.mfderiv_contMDiffCross
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff I J ∞ (Φ : M → N) :=
  Φ.contMDiff

end DifferentialGeometry
