import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.PushforwardVF
import Mathlib.Geometry.Manifold.VectorField.LieBracket


namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma mfderiv_symm_comp_self
    (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    (mfderiv I I (⇑Φ.symm) (Φ y)).comp (mfderiv I I (⇑Φ) y)
      = ContinuousLinearMap.id ℝ (TangentSpace I y) := by
  have hΦ : MDifferentiableAt I I (⇑Φ) y := Φ.mdifferentiable infty_ne_zero y
  have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ y) := Φ.symm.mdifferentiable infty_ne_zero (Φ y)
  have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
    funext z; exact Φ.symm_apply_apply z
  have hchain := mfderiv_comp y hΦsymm hΦ
  rw [hcomp] at hchain
  rw [mfderiv_id] at hchain
  exact hchain.symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma mfderiv_self_comp_symm
    (Φ : M ≃ₘ⟮I, I⟯ M) (y : M) :
    (mfderiv I I (⇑Φ) (Φ.symm y)).comp (mfderiv I I (⇑Φ.symm) y)
      = ContinuousLinearMap.id ℝ (TangentSpace I y) := by
  have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) y := Φ.symm.mdifferentiable infty_ne_zero y
  have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm y) := Φ.mdifferentiable infty_ne_zero (Φ.symm y)
  have hcomp : (⇑Φ) ∘ (⇑Φ.symm) = (id : M → M) := by
    funext z; exact Φ.apply_symm_apply z
  have hchain := mfderiv_comp y hΦ hΦsymm
  rw [hcomp] at hchain
  rw [mfderiv_id] at hchain
  exact hchain.symm

private lemma pushforward_eq_mpullback_symm
    (Φ : M ≃ₘ⟮I, I⟯ M) (V : ∀ x : M, TangentSpace I x) (x : M) :
    Diffeomorph.pushforward Φ V x = VectorField.mpullback I I (⇑Φ.symm) V x := by
  have hinv : (mfderiv I I (⇑Φ.symm) x).inverse = mfderiv I I (⇑Φ) (Φ.symm x) := by
    apply ContinuousLinearMap.inverse_eq
    · have h := mfderiv_symm_comp_self Φ (Φ.symm x)
      have hap : Φ (Φ.symm x) = x := Φ.apply_symm_apply x
      rw [hap] at h
      exact h
    · exact mfderiv_self_comp_symm Φ x
  change (Φ.apply_symm_apply x ▸ (mfderiv I I (⇑Φ) (Φ.symm x)) (V (Φ.symm x))
        : TangentSpace I x)
        = (mfderiv I I (⇑Φ.symm) x).inverse (V (Φ.symm x))
  rw [hinv]
  refine eq_of_heq ?_
  exact eqRec_heq (φ := fun z => TangentSpace I z) (Φ.apply_symm_apply x)
    ((mfderiv I I (⇑Φ) (Φ.symm x)) (V (Φ.symm x)))

theorem mlie_bracket_pullback_naturality
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (X Y : ∀ x : M, TangentSpace I x)
    (x : M)
    (hX : MDifferentiableAt I I.tangent
      (fun y => (TotalSpace.mk' E y (X y) : TangentBundle I M)) (Φ.symm x))
    (hY : MDifferentiableAt I I.tangent
      (fun y => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) (Φ.symm x)) :
    mlieBracket I (Diffeomorph.pushforward Φ X) (Diffeomorph.pushforward Φ Y) x
      = Diffeomorph.pushforward Φ (mlieBracket I X Y) x := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hpf_eq : ∀ V : ∀ x : M, TangentSpace I x,
      (Diffeomorph.pushforward Φ V : ∀ x : M, TangentSpace I x)
        = (VectorField.mpullback I I (⇑Φ.symm) V : ∀ x : M, TangentSpace I x) := by
    intro V; funext z
    exact pushforward_eq_mpullback_symm Φ V z
  rw [hpf_eq X, hpf_eq Y, hpf_eq (mlieBracket I X Y)]
  have hΦsymm_smooth : ContMDiffAt I I ∞ (⇑Φ.symm) x := Φ.symm.contMDiffAt
  haveI : IsManifold I (minSmoothness ℝ (2 : WithTop ℕ∞)) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hn : minSmoothness ℝ (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    have h1 : (2 : ℕ∞) ≤ ⊤ := le_top
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr h1
    convert h2 using 1
  exact (VectorField.mpullback_mlieBracket hX hY hΦsymm_smooth hn).symm

end DifferentialGeometry.PDE.RicciFlow.Pullback
