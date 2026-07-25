import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.PushforwardVF
import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Connection.MLieBracket
import DifferentialGeometry.Geometry.Connection.LeviCivita.PullbackConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mfderiv_self_after_symm_at_image
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    (mfderiv I I (⇑Φ) x).comp (mfderiv I I (⇑Φ.symm) (Φ x))
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ x) :=
    Φ.symm.mdifferentiable infty_ne_zero (Φ x)
  have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm (Φ x)) := by
    have : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
    rw [this]; exact Φ.mdifferentiable infty_ne_zero x
  have hcomp : (⇑Φ) ∘ (⇑Φ.symm) = (id : M → M) := by
    funext z; exact Φ.apply_symm_apply z
  have hchain := mfderiv_comp (Φ x) hΦ hΦsymm
  rw [hcomp, mfderiv_id] at hchain
  have hsym : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
  have hΦatx : mfderiv I I (⇑Φ) (Φ.symm (Φ x)) = mfderiv I I (⇑Φ) x := by
    congr 1
  rw [hΦatx] at hchain
  exact hchain.symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mfderiv_apply_mfderiv_symm
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (w : TangentSpace I (Φ x)) :
    mfderiv I I (⇑Φ) x (mfderiv I I (⇑Φ.symm) (Φ x) w) = w := by
  have h := mfderiv_self_after_symm_at_image (I := I) Φ x
  have := congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I x => f w) h
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mfderiv_symm_apply_mfderiv
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (v : TangentSpace I x) :
    mfderiv I I (⇑Φ.symm) (Φ x) (mfderiv I I (⇑Φ) x v) = v := by
  have hΦ : MDifferentiableAt I I (⇑Φ) x := Φ.mdifferentiable infty_ne_zero x
  have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ x) :=
    Φ.symm.mdifferentiable infty_ne_zero (Φ x)
  have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
    funext z; exact Φ.symm_apply_apply z
  have hchain := mfderiv_comp x hΦsymm hΦ
  rw [hcomp, mfderiv_id] at hchain
  have := congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I x => f v) hchain.symm
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using this

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma pushforward_at_image
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) (x : M) :
    Diffeomorph.pushforward Φ Y (Φ x) = mfderiv I I (⇑Φ) x (Y x) := by
  change (Φ.apply_symm_apply (Φ x)) ▸
    (mfderiv I I (⇑Φ) (Φ.symm (Φ x))) (Y (Φ.symm (Φ x))) = mfderiv I I (⇑Φ) x (Y x)
  have hbase : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
  refine eq_of_heq ?_
  refine (eqRec_heq (φ := fun z => TangentSpace I z)
    (Φ.apply_symm_apply (Φ x))
    ((mfderiv I I (⇑Φ) (Φ.symm (Φ x))) (Y (Φ.symm (Φ x))))).trans ?_
  rw [hbase]

def conjCovFun
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  let inner : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x :=
    (mfderiv I I (⇑Φ.symm) (Φ x)).comp
      ((LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x))
  inner.comp (mfderiv I I (⇑Φ) x)

omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma conjCovFun_apply
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    conjCovFun g Φ Y x v =
      mfderiv I I (⇑Φ.symm) (Φ x)
        ((LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
          (mfderiv I I (⇑Φ) x v)) := rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma pushforward_eq_mpullback_symm_fun
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) :
    (Diffeomorph.pushforward Φ Y : ∀ x : M, TangentSpace I x)
      = (VectorField.mpullback I I (⇑Φ.symm) Y : ∀ x : M, TangentSpace I x) := by
  funext z
  have hinv : (mfderiv I I (⇑Φ.symm) z).inverse = mfderiv I I (⇑Φ) (Φ.symm z) := by
    apply ContinuousLinearMap.inverse_eq
    · have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable infty_ne_zero _
      have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ (Φ.symm z)) := by
        have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
        rw [hap]; exact Φ.symm.mdifferentiable infty_ne_zero z
      have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
        funext w; exact Φ.symm_apply_apply w
      have hchain := mfderiv_comp (Φ.symm z) hΦsymm hΦ
      rw [hcomp, mfderiv_id] at hchain
      have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
      rw [hap] at hchain
      exact hchain.symm
    · have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) z :=
        Φ.symm.mdifferentiable infty_ne_zero z
      have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable infty_ne_zero _
      have hcomp : (⇑Φ) ∘ (⇑Φ.symm) = (id : M → M) := by
        funext w; exact Φ.apply_symm_apply w
      have hchain := mfderiv_comp z hΦ hΦsymm
      rw [hcomp, mfderiv_id] at hchain
      exact hchain.symm
  change (Φ.apply_symm_apply z) ▸
      (mfderiv I I (⇑Φ) (Φ.symm z)) (Y (Φ.symm z))
    = (mfderiv I I (⇑Φ.symm) z).inverse (Y (Φ.symm z))
  rw [hinv]
  refine eq_of_heq ?_
  exact eqRec_heq (φ := fun w => TangentSpace I w) (Φ.apply_symm_apply z)
    ((mfderiv I I (⇑Φ) (Φ.symm z)) (Y (Φ.symm z)))

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma pushforward_mdiffAt
    (Φ : M ≃ₘ⟮I, I⟯ M) {Y : ∀ x : M, TangentSpace I x} {x : M}
    (hY : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x) :
    MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Diffeomorph.pushforward Φ Y y) : TangentBundle I M))
      (Φ x) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hfun_eq := pushforward_eq_mpullback_symm_fun (I := I) Φ Y
  have hY' : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M))
      (Φ.symm (Φ x)) := by
    rw [Φ.symm_apply_apply]; exact hY
  have hΦsymm_smooth : ContMDiffAt I I (∞ : WithTop ℕ∞) (⇑Φ.symm) (Φ x) :=
    Φ.symm.contMDiffAt
  have hinv : (mfderiv I I (⇑Φ.symm) (Φ x)).IsInvertible := by
    refine ⟨(Diffeomorph.mfderivToContinuousLinearEquiv Φ.symm infty_ne_zero (Φ x)), ?_⟩
    exact Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ.symm) (x := Φ x) infty_ne_zero
  have hmn : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h1 : (2 : ℕ∞) ≤ ⊤ := le_top
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr h1
    convert h2 using 1
  have hmpb := MDifferentiableAt.mpullback_vectorField (I := I) (I' := I)
    (V := Y) (f := (⇑Φ.symm)) (x₀ := Φ x) (n := (∞ : WithTop ℕ∞))
    hY' hΦsymm_smooth hinv hmn
  have hfun_total :
      (fun z : M => (TotalSpace.mk' E z (Diffeomorph.pushforward Φ Y z) : TangentBundle I M))
        = (fun z : M => (TotalSpace.mk' E z (VectorField.mpullback I I (⇑Φ.symm) Y z) :
            TangentBundle I M)) := by
    funext z; congr 1
    exact congrFun hfun_eq z
  rw [hfun_total]
  exact hmpb

omit [SigmaCompactSpace M] in
private lemma conjCovFun_torsion_free
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {X Y : ∀ x : M, TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (X y) : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x) :
    conjCovFun g Φ Y x (X x) - conjCovFun g Φ X x (Y x)
      = VectorField.mlieBracket I X Y x := by
  have hPushX := pushforward_mdiffAt (I := I) Φ hX
  have hPushY := pushforward_mdiffAt (I := I) Φ hY
  have htor_g : (LeviCivita (I := I) g).torsion = 0 :=
    LeviCivita_torsion_eq_zero (I := I) g
  have hTF_g := (CovariantDerivative.torsion_eq_zero_iff (LeviCivita (I := I) g)).mp
    htor_g hPushX hPushY
  have hpfX : Diffeomorph.pushforward Φ X (Φ x) = mfderiv I I (⇑Φ) x (X x) :=
    pushforward_at_image (I := I) Φ X x
  have hpfY : Diffeomorph.pushforward Φ Y (Φ x) = mfderiv I I (⇑Φ) x (Y x) :=
    pushforward_at_image (I := I) Φ Y x
  have hbracket := mlie_bracket_pullback_naturality (I := I) Φ X Y (Φ x)
    (by rw [Φ.symm_apply_apply]; exact hX)
    (by rw [Φ.symm_apply_apply]; exact hY)
  have hbracket_pf : Diffeomorph.pushforward Φ (VectorField.mlieBracket I X Y) (Φ x)
      = mfderiv I I (⇑Φ) x ((VectorField.mlieBracket I X Y) x) :=
    pushforward_at_image (I := I) Φ (VectorField.mlieBracket I X Y) x
  rw [hbracket_pf] at hbracket
  simp only [conjCovFun_apply]
  rw [show (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
        (mfderiv I I (⇑Φ) x (X x)) =
      (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
        (Diffeomorph.pushforward Φ X (Φ x)) from by rw [hpfX]]
  rw [show (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ X) (Φ x)
        (mfderiv I I (⇑Φ) x (Y x)) =
      (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ X) (Φ x)
        (Diffeomorph.pushforward Φ Y (Φ x)) from by rw [hpfY]]
  set A := (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
    (Diffeomorph.pushforward Φ X (Φ x)) with hA_def
  set B := (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ X) (Φ x)
    (Diffeomorph.pushforward Φ Y (Φ x)) with hB_def
  have hAB : A - B = VectorField.mlieBracket I (Diffeomorph.pushforward Φ X)
      (Diffeomorph.pushforward Φ Y) (Φ x) := hTF_g
  calc mfderiv I I (⇑Φ.symm) (Φ x) A - mfderiv I I (⇑Φ.symm) (Φ x) B
      = mfderiv I I (⇑Φ.symm) (Φ x) (A - B) := by
        rw [← ContinuousLinearMap.map_sub]
    _ = mfderiv I I (⇑Φ.symm) (Φ x)
          (VectorField.mlieBracket I (Diffeomorph.pushforward Φ X)
            (Diffeomorph.pushforward Φ Y) (Φ x)) := by rw [hAB]
    _ = mfderiv I I (⇑Φ.symm) (Φ x)
          (mfderiv I I (⇑Φ) x ((VectorField.mlieBracket I X Y) x)) := by rw [hbracket]
    _ = (VectorField.mlieBracket I X Y) x :=
        mfderiv_symm_apply_mfderiv (I := I) Φ x ((VectorField.mlieBracket I X Y) x)

omit [NeZero (Module.finrank ℝ E)] in
private lemma pullbackMetric_inner_eval
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y Z : ∀ x : M, TangentSpace I x) (b : M) :
    (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b)
      = g.inner (Φ b) (mfderiv I I (⇑Φ) b (Y b)) (mfderiv I I (⇑Φ) b (Z b)) := by
  change Diffeomorph.pullbackInner g Φ b (Y b) (Z b) = _
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

private lemma conjCovFun_metric_compatible
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {Y Z : ∀ x : M, TangentSpace I x} {x : M}
    (hY : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Z y) : TangentBundle I M)) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b =>
        (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b)) x) v
      = (Diffeomorph.pullbackMetric g Φ).inner x (conjCovFun g Φ Y x v) (Z x)
        + (Diffeomorph.pullbackMetric g Φ).inner x (Y x) (conjCovFun g Φ Z x v) := by
  have hPushY := pushforward_mdiffAt (I := I) Φ hY
  have hPushZ := pushforward_mdiffAt (I := I) Φ hZ
  have hfun_eq : (fun b : M => (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b))
      = (fun b' : M => g.inner b' (Diffeomorph.pushforward Φ Y b')
          (Diffeomorph.pushforward Φ Z b')) ∘ (⇑Φ) := by
    funext b
    change (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b)
      = g.inner (Φ b) (Diffeomorph.pushforward Φ Y (Φ b))
          (Diffeomorph.pushforward Φ Z (Φ b))
    rw [pullbackMetric_inner_eval, pushforward_at_image, pushforward_at_image]
  have hg_smooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b' => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b' (g.inner b')) :=
    g.contMDiff
  have hinner_smooth_at_Φx : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b' : M => g.inner b' (Diffeomorph.pushforward Φ Y b')
          (Diffeomorph.pushforward Φ Z b')) (Φ x) := by
    have hClmAt : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
        (fun b' => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b' (g.inner b'))
        (Φ x) :=
      hg_smooth.contMDiffAt.mdifferentiableAt (by simp)
    have h_total :=
      MDifferentiableAt.clm_bundle_apply₂ (b := fun b' : M => b')
        (E₁ := fun b' : M => TangentSpace I b')
        (E₂ := fun b' : M => TangentSpace I b')
        (E₃ := fun _ : M => ℝ)
        (ψ := fun b' : M => g.inner b')
        (v := fun b' : M => Diffeomorph.pushforward Φ Y b')
        (w := fun b' : M => Diffeomorph.pushforward Φ Z b')
        (x := Φ x) hClmAt hPushY hPushZ
    have h_at_scalar : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun b' : M =>
          g.inner b' (Diffeomorph.pushforward Φ Y b') (Diffeomorph.pushforward Φ Z b'))
        (Φ x) := by
      rw [mdifferentiableAt_totalSpace] at h_total
      exact h_total.2
    exact h_at_scalar
  have hΦ_smooth_at_x : MDifferentiableAt I I (⇑Φ) x :=
    Φ.mdifferentiable infty_ne_zero x
  have h_chain := mfderiv_comp (I := I) (I' := I) (I'' := 𝓘(ℝ)) x
    hinner_smooth_at_Φx hΦ_smooth_at_x
  rw [show (fun b : M => (Diffeomorph.pullbackMetric g Φ).inner b (Y b) (Z b))
        = (fun b' : M => g.inner b' (Diffeomorph.pushforward Φ Y b')
            (Diffeomorph.pushforward Φ Z b')) ∘ (⇑Φ) from hfun_eq]
  rw [h_chain]
  have hMC_g : IsMetricCompatible (LeviCivita (I := I) g) g :=
    LeviCivita_isMetricCompatible (I := I) g
  have hMC_at := hMC_g.apply hPushY hPushZ (mfderiv I I (⇑Φ) x v)
  change (mfderiv I 𝓘(ℝ) (fun b' : M => g.inner b'
        (Diffeomorph.pushforward Φ Y b') (Diffeomorph.pushforward Φ Z b')) (Φ x))
      (mfderiv I I (⇑Φ) x v)
    = (Diffeomorph.pullbackMetric g Φ).inner x (conjCovFun g Φ Y x v) (Z x) +
        (Diffeomorph.pullbackMetric g Φ).inner x (Y x) (conjCovFun g Φ Z x v)
  rw [hMC_at]
  have hrhs1 : (Diffeomorph.pullbackMetric g Φ).inner x (conjCovFun g Φ Y x v) (Z x)
      = g.inner (Φ x) ((LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
          (mfderiv I I (⇑Φ) x v)) (Diffeomorph.pushforward Φ Z (Φ x)) := by
    change Diffeomorph.pullbackInner g Φ x (conjCovFun g Φ Y x v) (Z x) = _
    unfold Diffeomorph.pullbackInner
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
    have h1 : mfderiv I I (⇑Φ) x (conjCovFun g Φ Y x v)
        = (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Y) (Φ x)
            (mfderiv I I (⇑Φ) x v) := by
      simp only [conjCovFun_apply]
      exact mfderiv_apply_mfderiv_symm (I := I) Φ x _
    have h2 : mfderiv I I (⇑Φ) x (Z x) = Diffeomorph.pushforward Φ Z (Φ x) :=
      (pushforward_at_image (I := I) Φ Z x).symm
    rw [h1, h2]
  have hrhs2 : (Diffeomorph.pullbackMetric g Φ).inner x (Y x) (conjCovFun g Φ Z x v)
      = g.inner (Φ x) (Diffeomorph.pushforward Φ Y (Φ x))
          ((LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Z) (Φ x)
            (mfderiv I I (⇑Φ) x v)) := by
    change Diffeomorph.pullbackInner g Φ x (Y x) (conjCovFun g Φ Z x v) = _
    unfold Diffeomorph.pullbackInner
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
    have h1 : mfderiv I I (⇑Φ) x (Y x) = Diffeomorph.pushforward Φ Y (Φ x) :=
      (pushforward_at_image (I := I) Φ Y x).symm
    have h2 : mfderiv I I (⇑Φ) x (conjCovFun g Φ Z x v)
        = (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Z) (Φ x)
            (mfderiv I I (⇑Φ) x v) := by
      simp only [conjCovFun_apply]
      exact mfderiv_apply_mfderiv_symm (I := I) Φ x _
    rw [h1, h2]
  rw [hrhs1, hrhs2]

private lemma conjCovFun_eq_LeviCivita_pullback
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {X Y : ∀ x : M, TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (X y) : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x) :
    conjCovFun g Φ Y x (X x)
      = (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun Y x (X x) := by
  set cov₁ := fun (W : ∀ y : M, TangentSpace I y) (y : M) => conjCovFun g Φ W y with hcov₁_def
  set cov₂ := (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun with hcov₂_def
  have hTF₁ : ∀ ⦃A B : ∀ y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDifferentiableAt I I.tangent
        (fun z : M => (TotalSpace.mk' E z (A z) : TangentBundle I M)) y →
      MDifferentiableAt I I.tangent
        (fun z : M => (TotalSpace.mk' E z (B z) : TangentBundle I M)) y →
      y ∈ (Set.univ : Set M) →
      cov₁ B y (A y) - cov₁ A y (B y) = VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact conjCovFun_torsion_free (I := I) g Φ hA hB
  have hTF₂ : ∀ ⦃A B : ∀ y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDifferentiableAt I I.tangent
        (fun z : M => (TotalSpace.mk' E z (A z) : TangentBundle I M)) y →
      MDifferentiableAt I I.tangent
        (fun z : M => (TotalSpace.mk' E z (B z) : TangentBundle I M)) y →
      y ∈ (Set.univ : Set M) →
      cov₂ B y (A y) - cov₂ A y (B y) = VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff _).mp
      (LeviCivita_torsion_eq_zero (I := I) (Diffeomorph.pullbackMetric g Φ)) hA hB
  have hMC₁ : IsMetricCompatibleOn cov₁ (Diffeomorph.pullbackMetric g Φ)
      (Set.univ : Set M) := by
    intro A B y hA hB _ v
    exact conjCovFun_metric_compatible (I := I) g Φ hA hB v
  have hMC₂ : IsMetricCompatibleOn cov₂ (Diffeomorph.pullbackMetric g Φ)
      (Set.univ : Set M) := by
    exact (LeviCivita_isMetricCompatible (I := I) (Diffeomorph.pullbackMetric g Φ))
  exact koszul_local_uniqueness (s := Set.univ) hTF₁ hTF₂ hMC₁ hMC₂ hX hY (Set.mem_univ _)

theorem LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {X : ∀ y : M, TangentSpace I y} {x : M} (v : TangentSpace I x)
    (hX : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (X y) : TangentBundle I M)) x) :
    mfderiv I I (⇑Φ) x
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun X x v)
      = (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ X) (Φ x)
          (mfderiv I I (⇑Φ) x v) := by
  obtain ⟨V, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hV_mdiff : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (V y) : TangentBundle I M)) x :=
    V.mdifferentiableAt
  have hKey : (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun X x (V x)
      = conjCovFun g Φ X x (V x) :=
    (conjCovFun_eq_LeviCivita_pullback (I := I) g Φ hV_mdiff hX).symm
  rw [show v = V x from hVx.symm] at *
  rw [hKey]
  simp only [conjCovFun_apply]
  exact mfderiv_apply_mfderiv_symm (I := I) Φ x _

end DifferentialGeometry.PDE.RicciFlow.Pullback
