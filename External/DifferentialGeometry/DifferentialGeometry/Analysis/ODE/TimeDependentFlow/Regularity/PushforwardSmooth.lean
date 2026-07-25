import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.PushforwardVF
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph


namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

section SpatialAtFixedTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] in
theorem flowFamily_contMDiff_fixed_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ) :
    ContMDiff I I ∞ (Φ_fam s : M → M) :=
  (Φ_fam s).contMDiff

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] in
theorem flowFamily_mdifferentiableAt_fixed_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ) (x : M) :
    MDifferentiableAt I I (Φ_fam s : M → M) x := by
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  exact (Φ_fam s).mdifferentiable hinfty x

end SpatialAtFixedTime

section Pushforward

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.PDE.RicciFlow.Pullback

private lemma pushforward_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma flowFamily_pushforward_eq_mpullback_symm
    (Φ : M ≃ₘ⟮I, I⟯ M) (Y : ∀ x : M, TangentSpace I x) :
    (Diffeomorph.pushforward Φ Y : ∀ x : M, TangentSpace I x)
      = (VectorField.mpullback I I (⇑Φ.symm) Y : ∀ x : M, TangentSpace I x) := by
  funext z
  have hinv : (mfderiv I I (⇑Φ.symm) z).inverse = mfderiv I I (⇑Φ) (Φ.symm z) := by
    apply ContinuousLinearMap.inverse_eq
    · have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable pushforward_infty_ne_zero _
      have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) (Φ (Φ.symm z)) := by
        have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
        rw [hap]; exact Φ.symm.mdifferentiable pushforward_infty_ne_zero z
      have hcomp : (⇑Φ.symm) ∘ (⇑Φ) = (id : M → M) := by
        funext w; exact Φ.symm_apply_apply w
      have hchain := mfderiv_comp (Φ.symm z) hΦsymm hΦ
      rw [hcomp, mfderiv_id] at hchain
      have hap : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
      rw [hap] at hchain
      exact hchain.symm
    · have hΦsymm : MDifferentiableAt I I (⇑Φ.symm) z :=
        Φ.symm.mdifferentiable pushforward_infty_ne_zero z
      have hΦ : MDifferentiableAt I I (⇑Φ) (Φ.symm z) :=
        Φ.mdifferentiable pushforward_infty_ne_zero _
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
theorem flowFamily_pushforward_contMDiff
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (s : ℝ)
    {Y : ∀ x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward (Φ_fam s) Y x)) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set Φ := Φ_fam s with hΦ
  have hfun_eq := flowFamily_pushforward_eq_mpullback_symm (I := I) Φ Y
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
    refine ⟨(Diffeomorph.mfderivToContinuousLinearEquiv Φ.symm pushforward_infty_ne_zero x), ?_⟩
    exact Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ.symm) (x := x)
      pushforward_infty_ne_zero
  exact ContMDiff.mpullback_vectorField (I := I) (I' := I) (V := Y)
    (f := ⇑Φ.symm) (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞))
    hY hΦsymm_smooth hinv (by simp)

end Pushforward

section TimeRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M] in
theorem flowFamily_hasMFDerivWithinAt_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))))
    (s : ℝ) (hs : 0 < s) (hsT : s < T) (x : M) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))) :=
  hbare s hs hsT x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M] in
theorem flowFamily_continuousWithinAt_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x))))
    (s : ℝ) (hs : 0 < s) (hsT : s < T) (x : M) :
    ContinuousWithinAt (fun u : ℝ => Φ_fam u x) (Ici 0) s :=
  (hbare s hs hsT x).continuousWithinAt

end TimeRegularity

section RegularityPackage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [CompactSpace M]

open DifferentialGeometry.PDE.RicciFlow.Pullback

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [CompactSpace M] in
theorem flowFamily_regularity_package
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hbare : ∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) :
    (∀ s : ℝ, ContMDiff I I ∞ (Φ_fam s : M → M)) ∧
    (∀ (s : ℝ) (Y : ∀ x : M, TangentSpace I x),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
          (Diffeomorph.pushforward (Φ_fam s) Y x))) ∧
    (∀ (s : ℝ) (x : M), MDifferentiableAt I I (Φ_fam s : M → M) x) ∧
    (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) ∧
    (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
      ContinuousWithinAt (fun u : ℝ => Φ_fam u x) (Ici 0) s) :=
  ⟨fun s => flowFamily_contMDiff_fixed_time Φ_fam s,
   fun s _Y hY => flowFamily_pushforward_contMDiff Φ_fam s hY,
   fun s x => flowFamily_mdifferentiableAt_fixed_time Φ_fam s x,
   hbare,
   fun s hs hsT x => (hbare s hs hsT x).continuousWithinAt⟩

end RegularityPackage

end DifferentialGeometry.PDE.RicciFlow.ODE
