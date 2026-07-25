import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.InnerProductSpace.Basic


namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

noncomputable def Diffeomorph.pullbackInner
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let step1 : TangentSpace I x →L[ℝ] TangentSpace I (Φ x) →L[ℝ] ℝ :=
    (g.inner (Φ x)).comp (mfderiv I I Φ x)
  let precompOp : (TangentSpace I (Φ x) →L[ℝ] ℝ) →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (mfderiv I I Φ x)
  precompOp.comp step1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem Diffeomorph.pullbackInner_symm
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInner g Φ x v w
      = Diffeomorph.pullbackInner g Φ x w v := by
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  exact g.symm (Φ x) _ _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem Diffeomorph.pullbackInner_pos
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < Diffeomorph.pullbackInner g Φ x v v := by
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  set hΦeq : TangentSpace I x ≃L[ℝ] TangentSpace I (Φ x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero x with hΦeq_def
  have hvImg : mfderiv I I Φ x v ≠ 0 := by
    have h1 : hΦeq v ≠ 0 := (hΦeq.map_ne_zero_iff).mpr hv
    have h2 : (hΦeq : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)) v
        = mfderiv I I Φ x v := by
      rw [hΦeq_def]
      have heq := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) infty_ne_zero
      exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I (Φ x) => f v) heq
    have hcoe : (hΦeq : TangentSpace I x → TangentSpace I (Φ x)) v = hΦeq v := rfl
    rw [← h2]; exact fun h => h1 (by simpa [hcoe] using h)
  exact g.pos (Φ x) _ hvImg

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem inner_comp_smooth_along_diffeo
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      ((fun b ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g.inner b)) ∘ (Φ : M → M)) :=
  g.contMDiff.comp Φ.contMDiff

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem pullbackInner_eval
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInner g Φ x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private theorem mfderiv_eq_mfderivCLE_apply
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (v : TangentSpace I x) :
    Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero x v
      = mfderiv I I Φ x v := by
  have h := Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) infty_ne_zero
  exact congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I (Φ x) => f v) h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem Diffeomorph.pullbackInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ∀ x : M, Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | Diffeomorph.pullbackInner g Φ x v v < 1} := by
  intro x
  set hΦeq := Diffeomorph.mfderivToContinuousLinearEquiv Φ infty_ne_zero x with hΦeq_def
  have hg := g.isVonNBounded (Φ x)
  have himg := hg.image (hΦeq.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x)
  have hseteq :
      {v : TangentSpace I x | Diffeomorph.pullbackInner g Φ x v v < 1}
        = ((hΦeq.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x) : _ → _)
            '' {w : TangentSpace I (Φ x) | g.inner (Φ x) w w < 1} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image]
    refine ⟨fun hv => ⟨hΦeq v, ?_, ?_⟩, ?_⟩
    · have h1 := pullbackInner_eval (g := g) (Φ := Φ) x v v
      rw [h1] at hv
      have h2 := mfderiv_eq_mfderivCLE_apply (Φ := Φ) (x := x) v
      rw [← h2] at hv
      exact hv
    · change (hΦeq.symm : TangentSpace I (Φ x) → TangentSpace I x) (hΦeq v) = v
      exact hΦeq.symm_apply_apply v
    · rintro ⟨w, hw, rfl⟩
      have hsym : ((hΦeq.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x) :
            TangentSpace I (Φ x) → TangentSpace I x) w = hΦeq.symm w := rfl
      rw [hsym]
      rw [pullbackInner_eval]
      have hImg : mfderiv I I Φ x (hΦeq.symm w) = w := by
        have hmap := mfderiv_eq_mfderivCLE_apply (Φ := Φ) (x := x) (hΦeq.symm w)
        rw [← hmap]
        exact hΦeq.apply_symm_apply w
      rw [hImg]; exact hw
  rw [hseteq]
  exact himg

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem mfderiv_apply_section_smooth_along_diffeo
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I)
        (Φ x) (mfderiv I I (Φ : M → M) x (Y x))) := by
  have h_tangentMap : ContMDiff I.tangent I.tangent ∞ (tangentMap I I (Φ : M → M)) :=
    Φ.contMDiff.contMDiff_tangentMap (le_refl _)
  have h := h_tangentMap.comp hY
  exact h

noncomputable def Diffeomorph.pullbackMetric
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    SmoothRiemannianMetric I M where
  inner x := Diffeomorph.pullbackInner g Φ x
  symm x v w := Diffeomorph.pullbackInner_symm g Φ x v w
  pos x v hv := Diffeomorph.pullbackInner_pos g Φ x v hv
  isVonNBounded x := Diffeomorph.pullbackInner_isVonNBounded g Φ x
  contMDiff := by
    classical
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun x : M => Diffeomorph.pullbackInner g Φ x)
    intro Y
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun _ : M => ℝ)
      (φ := fun x : M => Diffeomorph.pullbackInner g Φ x (Y x))
    intro W
    have hv := mfderiv_apply_section_smooth_along_diffeo Φ (fun x => Y x) Y.contMDiff
    have hw := mfderiv_apply_section_smooth_along_diffeo Φ (fun x => W x) W.contMDiff
    have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x : M => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
          (Φ x) (g.inner (Φ x))) :=
      g.contMDiff.comp Φ.contMDiff
    have h_total : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ
          (E := Bundle.Trivial M ℝ)
          (Φ x)
          (g.inner (Φ x) (mfderiv I I (Φ : M → M) x (Y x))
            (mfderiv I I (Φ : M → M) x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x)
        (E₃ := fun _ : M => ℝ)
        (b := fun x : M => Φ x)
        (ψ := fun x : M => g.inner (Φ x))
        (v := fun x : M => mfderiv I I (Φ : M → M) x (Y x))
        (w := fun x : M => mfderiv I I (Φ : M → M) x (W x))
        hg hv hw
    have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g.inner (Φ x) (mfderiv I I (Φ : M → M) x (Y x))
            (mfderiv I I (Φ : M → M) x (W x))) := by
      intro x
      have h_at := h_total x
      rw [contMDiffAt_totalSpace] at h_at
      have := h_at.2
      convert this using 1
    have h_pullback_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Diffeomorph.pullbackInner g Φ x (Y x) (W x)) := by
      have h_eq : (fun x : M => Diffeomorph.pullbackInner g Φ x (Y x) (W x))
          = fun x : M => g.inner (Φ x) (mfderiv I I (Φ : M → M) x (Y x))
              (mfderiv I I (Φ : M → M) x (W x)) := by
        funext x; exact pullbackInner_eval g Φ x (Y x) (W x)
      rw [h_eq]; exact h_scalar
    intro x
    rw [contMDiffAt_section]
    refine (h_pullback_smooth.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards with y
    change Diffeomorph.pullbackInner g Φ y (Y y) (W y) =
      (trivializationAt ℝ (Bundle.Trivial M ℝ) x
        ⟨y, Diffeomorph.pullbackInner g Φ y (Y y) (W y)⟩).2
    rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem diffeomorph_pullback_metric_exists
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ∃ g' : SmoothRiemannianMetric I M, g' = Diffeomorph.pullbackMetric g Φ :=
  ⟨Diffeomorph.pullbackMetric g Φ, rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem Diffeomorph.pullbackMetric_refl
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) :
    Diffeomorph.pullbackMetric g (_root_.Diffeomorph.refl I M ∞) = g := by
  rcases g with ⟨inner_g, symm_g, pos_g, isVonN_g, contMDiff_g⟩
  have hinner :
      (fun x => Diffeomorph.pullbackInner
          ⟨inner_g, symm_g, pos_g, isVonN_g, contMDiff_g⟩
          (_root_.Diffeomorph.refl I M ∞) x)
        = inner_g := by
    funext x
    apply ContinuousLinearMap.ext; intro v
    apply ContinuousLinearMap.ext; intro w
    rw [pullbackInner_eval]
    have hmfd : mfderiv I I (Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x
        = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      have h1 : mfderiv I I (fun y : M => (Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) y) x
          = mfderiv I I (id : M → M) x := rfl
      rw [h1]
      exact mfderiv_id
    have hv : mfderiv I I (Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x v = v := by
      rw [hmfd]; rfl
    have hw : mfderiv I I (Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) x w = w := by
      rw [hmfd]; rfl
    rw [hv, hw]
    rfl
  unfold Diffeomorph.pullbackMetric
  congr 1

omit [NeZero (Module.finrank ℝ E)] in
theorem Diffeomorph.pullbackInner_contMDiff
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        ((Diffeomorph.pullbackInner g Φ x : E →L[ℝ] E →L[ℝ] ℝ))) :=
  (Diffeomorph.pullbackMetric g Φ).contMDiff

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem Diffeomorph.mfderiv_contMDiff
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    ContMDiff I I ∞ (Φ : M → M) :=
  Φ.contMDiff

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem bilinear_pullback_bundle_smooth
    (_Φ : M ≃ₘ⟮I, I⟯ M) :
    ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        ContinuousLinearMap.bilinearComp p.1 p.2 p.2) := by
  have hfst : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) => p.1) :=
    contMDiff_fst
  have hsnd : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) => p.2) :=
    contMDiff_snd
  have hflipDiff : ContDiff ℝ ∞
      ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ) :
        (E →L[ℝ] E →L[ℝ] ℝ) → (E →L[ℝ] E →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have h1 : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) => p.1.comp p.2) :=
    hfst.clm_comp hsnd
  have h2 : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) => (p.1.comp p.2).flip) := by
    have hcomp := hflipDiff.comp_contMDiff h1
    simpa [ContinuousLinearMap.coe_flipₗᵢ, Function.comp_def] using hcomp
  have h3 : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        (p.1.comp p.2).flip.comp p.2) := h2.clm_comp hsnd
  have h4 : ContMDiff
      (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ).prod 𝓘(ℝ, E →L[ℝ] E))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) =>
        ((p.1.comp p.2).flip.comp p.2).flip) := by
    have hcomp := hflipDiff.comp_contMDiff h3
    simpa [ContinuousLinearMap.coe_flipₗᵢ, Function.comp_def] using hcomp
  exact h4

end DifferentialGeometry.PDE.RicciFlow.Pullback
