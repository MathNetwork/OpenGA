import DifferentialGeometry.Geometry.Connection.LeviCivita.CovariantDerivativePointwise
import DifferentialGeometry.Geometry.Connection.MLieBracket
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import Mathlib.LinearAlgebra.Trace


namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private lemma infty_ne_zero_ricci : (∞ : WithTop ℕ∞) ≠ 0 := by decide

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma pushforward_eval_at_image
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

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma pushforward_eval
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) (b : M) :
    Diffeomorph.pushforward Φ Y b = mfderiv I I (⇑Φ) (Φ.symm b) (Y (Φ.symm b)) := by
  conv_lhs => rw [show b = Φ (Φ.symm b) from (Φ.apply_symm_apply b).symm]
  exact pushforward_eval_at_image (I := I) Φ Y (Φ.symm b)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mfderiv_symm_compose
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (v : TangentSpace I x) :
    mfderiv I I (⇑Φ.symm) (Φ x) (mfderiv I I (⇑Φ) x v) = v := by
  have hΦ : MDifferentiableAt I I (⇑Φ) x := Φ.mdifferentiable infty_ne_zero_ricci x
  have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ x) :=
    Φ.symm.mdifferentiable infty_ne_zero_ricci (Φ x)
  have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
    funext z; exact Φ.symm_apply_apply z
  have hchain := mfderiv_comp x hΦsymm hΦ
  rw [hcomp, mfderiv_id] at hchain
  have := congrArg (fun f : TangentSpace I x →L[ℝ] TangentSpace I x => f v) hchain.symm
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mfderiv_compose_symm
    (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) (w : TangentSpace I (Φ x)) :
    mfderiv I I (⇑Φ) x (mfderiv I I (⇑Φ.symm) (Φ x) w) = w := by
  have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ x) :=
    Φ.symm.mdifferentiable infty_ne_zero_ricci (Φ x)
  have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm (Φ x)) := by
    have : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
    rw [this]; exact Φ.mdifferentiable infty_ne_zero_ricci x
  have hcomp : (⇑Φ) ∘ (⇑Φ.symm) = (id : M → M) := by
    funext z; exact Φ.apply_symm_apply z
  have hchain := mfderiv_comp (Φ x) hΦ hΦsymm
  rw [hcomp, mfderiv_id] at hchain
  have hsym : Φ.symm (Φ x) = x := Φ.symm_apply_apply x
  have hΦatx : mfderiv I I (⇑Φ) (Φ.symm (Φ x)) = mfderiv I I (⇑Φ) x := by congr 1
  rw [hΦatx] at hchain
  have := congrArg (fun f : TangentSpace I (Φ x) →L[ℝ] TangentSpace I (Φ x) => f w) hchain.symm
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using this

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma pushforward_eq_mpullback_symm_global
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) :
    (Diffeomorph.pushforward Φ Y : ∀ x : M, TangentSpace I x)
      = (VectorField.mpullback I I (⇑Φ.symm) Y : ∀ x : M, TangentSpace I x) := by
  funext z
  have hinv : (mfderiv I I (⇑Φ.symm) z).inverse = mfderiv I I (⇑Φ) (Φ.symm z) := by
    apply ContinuousLinearMap.inverse_eq
    · have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable infty_ne_zero_ricci _
      have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ (Φ.symm z)) := by
        have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
        rw [hap]; exact Φ.symm.mdifferentiable infty_ne_zero_ricci z
      have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
        funext w; exact Φ.symm_apply_apply w
      have hchain := mfderiv_comp (Φ.symm z) hΦsymm hΦ
      rw [hcomp, mfderiv_id] at hchain
      have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
      rw [hap] at hchain
      exact hchain.symm
    · have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) z :=
        Φ.symm.mdifferentiable infty_ne_zero_ricci z
      have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable infty_ne_zero_ricci _
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
private lemma pushforward_contMDiff
    (Φ : M ≃ₘ⟮I, I⟯ M) {Y : ∀ x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (Diffeomorph.pushforward Φ Y)) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hfun_eq := pushforward_eq_mpullback_symm_global (I := I) Φ Y
  have hfun_total :
      (fun z : M => (TotalSpace.mk' E z (Diffeomorph.pushforward Φ Y z) : TangentBundle I M))
        = (fun z : M => (TotalSpace.mk' E z (VectorField.mpullback I I (⇑Φ.symm) Y z) :
            TangentBundle I M)) := by
    funext z; congr 1
    exact congrFun hfun_eq z
  rw [hfun_total]
  have hΦsymm_smooth : ContMDiff I I (∞ : WithTop ℕ∞) (⇑Φ.symm) := Φ.symm.contMDiff
  have hinv : ∀ x, (mfderiv I I (⇑Φ.symm) x).IsInvertible := by
    intro x
    refine ⟨(Diffeomorph.mfderivToContinuousLinearEquiv Φ.symm infty_ne_zero_ricci x), ?_⟩
    exact Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ.symm) (x := x)
      infty_ne_zero_ricci
  exact ContMDiff.mpullback_vectorField (I := I) (I' := I) (V := Y)
    (f := ⇑Φ.symm) (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞))
    hY hΦsymm_smooth hinv (by simp)

private lemma pushforward_covApply_eq
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {Y Z : ∀ x : M, TangentSpace I x}
    (_hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    Diffeomorph.pushforward Φ
        (covApply (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y Z)
      = covApply (LeviCivita (I := I) g) (Diffeomorph.pushforward Φ Y)
          (Diffeomorph.pushforward Φ Z) := by
  funext b
  let y := Φ.symm b
  have hb : Φ y = b := Φ.apply_symm_apply b
  have hLHS_eval : Diffeomorph.pushforward Φ
        (covApply (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y Z) b
      = mfderiv I I (⇑Φ) y
          ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)).toFun Z y (Y y)) :=
    pushforward_eval (I := I) Φ _ b
  have hRHS_pf_Y : Diffeomorph.pushforward Φ Y b = mfderiv I I (⇑Φ) y (Y y) :=
    pushforward_eval (I := I) Φ Y b
  change Diffeomorph.pushforward Φ
        (covApply (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y Z) b
    = (LeviCivita (I := I) g).toFun (Diffeomorph.pushforward Φ Z) b
        (Diffeomorph.pushforward Φ Y b)
  rw [hLHS_eval, hRHS_pf_Y]
  have hZ_at : MDifferentiableAt I I.tangent (T% Z) y :=
    (hZ y).mdifferentiableAt (by simp)
  have hchain := LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise (I := I) g Φ (Y y) hZ_at
  rw [hchain, hb]

private lemma riemannSec_pullback_pointwise
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    {X Y Z : ∀ x : M, TangentSpace I x} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    mfderiv I I (⇑Φ) x
        (riemannSec (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) X Y Z x)
      = riemannSec (LeviCivita (I := I) g)
          (Diffeomorph.pushforward Φ X) (Diffeomorph.pushforward Φ Y)
            (Diffeomorph.pushforward Φ Z) (Φ x) := by
  set cov₁ := LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ) with hcov₁_def
  set cov₂ := LeviCivita (I := I) g with hcov₂_def
  set X' := Diffeomorph.pushforward Φ X with hX'_def
  set Y' := Diffeomorph.pushforward Φ Y with hY'_def
  set Z' := Diffeomorph.pushforward Φ Z with hZ'_def
  rw [riemannSec_def, riemannSec_def]
  rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub]
  have hcovYZ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov₁ Y Z)) := by
    have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
    intro x'
    exact (covApply_contMDiffOn (cov := cov₁) hY hZ_le).contMDiffAt (Filter.univ_mem)
  have hcovYZ_at : MDifferentiableAt I I.tangent (T% (covApply cov₁ Y Z)) x :=
    (hcovYZ_smooth x).mdifferentiableAt (by simp)
  have hterm1 : mfderiv I I (⇑Φ) x (cov₁.toFun (covApply cov₁ Y Z) x (X x))
      = cov₂.toFun (Diffeomorph.pushforward Φ (covApply cov₁ Y Z)) (Φ x)
          (mfderiv I I (⇑Φ) x (X x)) :=
    LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise (I := I) g Φ (X x) hcovYZ_at
  have hcovXZ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov₁ X Z)) := by
    have hZ_le : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% Z) := by simpa using hZ
    intro x'
    exact (covApply_contMDiffOn (cov := cov₁) hX hZ_le).contMDiffAt (Filter.univ_mem)
  have hcovXZ_at : MDifferentiableAt I I.tangent (T% (covApply cov₁ X Z)) x :=
    (hcovXZ_smooth x).mdifferentiableAt (by simp)
  have hterm2 : mfderiv I I (⇑Φ) x (cov₁.toFun (covApply cov₁ X Z) x (Y x))
      = cov₂.toFun (Diffeomorph.pushforward Φ (covApply cov₁ X Z)) (Φ x)
          (mfderiv I I (⇑Φ) x (Y x)) :=
    LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise (I := I) g Φ (Y x) hcovXZ_at
  have hZ_at : MDifferentiableAt I I.tangent (T% Z) x :=
    (hZ x).mdifferentiableAt (by simp)
  have hterm3 : mfderiv I I (⇑Φ) x (cov₁.toFun Z x (mlieBracket I X Y x))
      = cov₂.toFun Z' (Φ x) (mfderiv I I (⇑Φ) x (mlieBracket I X Y x)) := by
    have h := LeviCivita_covariant_derivative_natural_under_diffeomorphism_pointwise (I := I) g Φ
      (mlieBracket I X Y x) hZ_at
    exact h
  rw [hterm1, hterm2, hterm3]
  have hcovYZ_eq := pushforward_covApply_eq (I := I) g Φ hY hZ
  have hcovXZ_eq := pushforward_covApply_eq (I := I) g Φ hX hZ
  have hX_eval : mfderiv I I (⇑Φ) x (X x) = X' (Φ x) := by
    rw [hX'_def]; exact (pushforward_eval_at_image (I := I) Φ X x).symm
  have hY_eval : mfderiv I I (⇑Φ) x (Y x) = Y' (Φ x) := by
    rw [hY'_def]; exact (pushforward_eval_at_image (I := I) Φ Y x).symm
  have hX_at : MDifferentiableAt I I.tangent (T% X) (Φ.symm (Φ x)) := by
    rw [Φ.symm_apply_apply]
    exact (hX x).mdifferentiableAt (by simp)
  have hY_at : MDifferentiableAt I I.tangent (T% Y) (Φ.symm (Φ x)) := by
    rw [Φ.symm_apply_apply]
    exact (hY x).mdifferentiableAt (by simp)
  have hbracket_pf : Diffeomorph.pushforward Φ (mlieBracket I X Y) (Φ x)
      = mfderiv I I (⇑Φ) x (mlieBracket I X Y x) :=
    pushforward_eval_at_image (I := I) Φ (mlieBracket I X Y) x
  have hbracket_nat :
      mlieBracket I X' Y' (Φ x) = Diffeomorph.pushforward Φ (mlieBracket I X Y) (Φ x) := by
    rw [hX'_def, hY'_def]
    exact mlie_bracket_pullback_naturality (I := I) Φ X Y (Φ x) hX_at hY_at
  have hbracket_eq : mfderiv I I (⇑Φ) x (mlieBracket I X Y x) = mlieBracket I X' Y' (Φ x) := by
    rw [← hbracket_pf, hbracket_nat]
  rw [hcovYZ_eq, hcovXZ_eq, hX_eval, hY_eval, hbracket_eq]

private lemma riemannOp_pullback_pointwise
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w u : TangentSpace I x) :
    mfderiv I I (⇑Φ) x
        (riemannOp (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) x u v w)
      = riemannOp (LeviCivita (I := I) g) (Φ x)
          (mfderiv I I (⇑Φ) x u)
          (mfderiv I I (⇑Φ) x v)
          (mfderiv I I (⇑Φ) x w) := by
  classical
  set U := smoothExtensionTangent (I := I) x u
  set V := smoothExtensionTangent (I := I) x v
  set W := smoothExtensionTangent (I := I) x w
  have hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U) := smoothExtensionTangent_contMDiff x u
  have hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) := smoothExtensionTangent_contMDiff x v
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) := smoothExtensionTangent_contMDiff x w
  have hU_eq : U x = u := smoothExtensionTangent_eq x u
  have hV_eq : V x = v := smoothExtensionTangent_eq x v
  have hW_eq : W x = w := smoothExtensionTangent_eq x w
  rw [show u = U x from hU_eq.symm, show v = V x from hV_eq.symm, show w = W x from hW_eq.symm]
  rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ))
        hU hV hW]
  rw [riemannSec_pullback_pointwise (I := I) g Φ hU hV hW]
  have hPushU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (Diffeomorph.pushforward Φ U)) :=
    pushforward_contMDiff (I := I) Φ hU
  have hPushV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (Diffeomorph.pushforward Φ V)) :=
    pushforward_contMDiff (I := I) Φ hV
  have hPushW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (Diffeomorph.pushforward Φ W)) :=
    pushforward_contMDiff (I := I) Φ hW
  rw [← riemannOp_apply_smooth (cov := LeviCivita (I := I) g) hPushU hPushV hPushW]
  rw [pushforward_eval_at_image (I := I) Φ U x,
      pushforward_eval_at_image (I := I) Φ V x,
      pushforward_eval_at_image (I := I) Φ W x]

private lemma ricciEndo_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    ricciEndo (I := I) (Diffeomorph.pullbackMetric g Φ) x v w
      = ((mfderiv I I (⇑Φ.symm) (Φ x)).toLinearMap.comp
            ((ricciEndo (I := I) g (Φ x)
                (mfderiv I I (⇑Φ) x v) (mfderiv I I (⇑Φ) x w)).comp
              (mfderiv I I (⇑Φ) x).toLinearMap)) := by
  apply LinearMap.ext
  intro Z
  change riemannOp (LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) x Z v w
    = mfderiv I I (⇑Φ.symm) (Φ x)
        (riemannOp (LeviCivita (I := I) g) (Φ x)
          (mfderiv I I (⇑Φ) x Z)
          (mfderiv I I (⇑Φ) x v) (mfderiv I I (⇑Φ) x w))
  rw [← riemannOp_pullback_pointwise (I := I) g Φ x v w Z]
  rw [mfderiv_symm_compose (I := I) Φ x]

theorem ricciTensor_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (Diffeomorph.pullbackMetric g Φ) x v w
      = ricciTensor (I := I) g (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  classical
  rw [ricciTensor_apply (I := I) (Diffeomorph.pullbackMetric g Φ) x v w,
      ricciTensor_apply (I := I) g (Φ x) (mfderiv I I (⇑Φ) x v) (mfderiv I I (⇑Φ) x w)]
  rw [ricciEndo_conjugation (I := I) g Φ x v w]
  set e : TangentSpace I x ≃L[ℝ] TangentSpace I (Φ x) :=
    Diffeomorph.mfderivToContinuousLinearEquiv (I := I) Φ infty_ne_zero_ricci x with he_def
  have he_coe : (e : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)) = mfderiv I I (⇑Φ) x :=
    Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) (x := x) infty_ne_zero_ricci
  have hsymm_coe : (e.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x)
      = mfderiv I I (⇑Φ.symm) (Φ x) := by
    apply ContinuousLinearMap.ext
    intro y
    have h2 : mfderiv I I (⇑Φ) x (mfderiv I I (⇑Φ.symm) (Φ x) y) = y :=
      mfderiv_compose_symm (I := I) Φ x y
    have hee : (e : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)) (e.symm y) = y := e.right_inv y
    have h1' : mfderiv I I (⇑Φ) x (e.symm y) = y := by
      rw [← he_coe]; exact hee
    have hinj : Function.Injective (mfderiv I I (⇑Φ) x) := by
      intro a₁ a₂ h
      have h' : (e : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)) a₁
          = (e : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)) a₂ := by rw [he_coe]; exact h
      exact e.injective h'
    exact hinj (h1'.trans h2.symm)
  set F := ricciEndo (I := I) g (Φ x) (mfderiv I I (⇑Φ) x v) (mfderiv I I (⇑Φ) x w) with hF_def
  have hreplace_outer : ((mfderiv I I (⇑Φ.symm) (Φ x)).toLinearMap.comp
        (F.comp (mfderiv I I (⇑Φ) x).toLinearMap)) =
      ((e.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x).toLinearMap.comp
        (F.comp (e : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)).toLinearMap)) := by
    have h1 : ((e.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x).toLinearMap :
        TangentSpace I (Φ x) →ₗ[ℝ] TangentSpace I x) =
        (mfderiv I I (⇑Φ.symm) (Φ x)).toLinearMap := by rw [hsymm_coe]
    have h2 : ((e : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)).toLinearMap :
        TangentSpace I x →ₗ[ℝ] TangentSpace I (Φ x)) =
        (mfderiv I I (⇑Φ) x).toLinearMap := by rw [he_coe]
    rw [h1, h2]; rfl
  rw [hreplace_outer]
  have hconj : (e.toLinearEquiv.symm.conj F :
      TangentSpace I x →ₗ[ℝ] TangentSpace I x) =
      ((e.symm : TangentSpace I (Φ x) →L[ℝ] TangentSpace I x).toLinearMap.comp
        (F.comp (e : TangentSpace I x →L[ℝ] TangentSpace I (Φ x)).toLinearMap)) := by
    rw [LinearEquiv.conj_apply]
    rfl
  rw [← hconj]
  exact LinearMap.trace_conj' F e.toLinearEquiv.symm

end DifferentialGeometry.PDE.RicciFlow.Pullback
