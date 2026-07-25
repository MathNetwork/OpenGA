import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Bundle.Equiv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.Normed.Module.Multilinear.Curry


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def covGradModelEquiv (r s : ℕ) :
    (E →L[ℝ] TensorRSModel r s ℝ E) ≃L[ℝ] TensorRSModel r (s + 1) ℝ E :=
  (ContinuousLinearMap.flipₗᵢ ℝ E (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E)).toContinuousLinearEquiv.trans
    ((ContinuousLinearEquiv.refl ℝ (Tensor0SModel r ℝ E)).arrowCongr
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (s + 1) => E) ℝ).symm.toContinuousLinearEquiv)

theorem covGradModelEquiv_apply (r s : ℕ)
    (Φ : E →L[ℝ] TensorRSModel r s ℝ E) (D : Tensor0SModel r ℝ E)
    (v : Fin (s + 1) → E) :
    covGradModelEquiv (E := E) r s Φ D v = Φ (v 0) D (Matrix.vecTail v) := by
  rfl

theorem covGradModelEquiv_symm_apply (r s : ℕ)
    (T : TensorRSModel r (s + 1) ℝ E) (w : E) (D : Tensor0SModel r ℝ E)
    (v : Fin s → E) :
    (covGradModelEquiv (E := E) r s).symm T w D v = T D (Fin.cons w v) := by
  rfl

def covGradBundleEquiv (r s : ℕ) (x : M) :
    (TangentSpace I x →L[ℝ] TensorRSSpace r s I x) ≃L[ℝ]
      TensorRSSpace r (s + 1) I x :=
  ((ContinuousLinearEquiv.refl ℝ (TangentSpace I x)).arrowCongr
      (tensorRSSpace_continuousLinearEquiv (I := I) r s x)).trans
    ((covGradModelEquiv (E := E) r s).trans
      (tensorRSSpace_continuousLinearEquiv (I := I) r (s + 1) x).symm)

set_option backward.isDefEq.respectTransparency true in

theorem covGradBundleEquiv_apply (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r s I x) :
    covGradBundleEquiv (I := I) (M := M) r s x Φ =
      TensorRSSpace.ofModel
        (covGradModelEquiv (E := E) r s
          (((tensorRSSpace_continuousLinearEquiv (I := I) r s x : _ →L[ℝ] _).comp
            Φ : TangentSpace I x →L[ℝ] TensorRSModel r s ℝ E))) :=
  rfl

set_option backward.isDefEq.respectTransparency true in

theorem covGradBundleEquiv_symm_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace r (s + 1) I x) :
    (covGradBundleEquiv (I := I) (M := M) r s x).symm T =
      ((tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm
          : TensorRSModel r s ℝ E →L[ℝ] TensorRSSpace r s I x).comp
        ((covGradModelEquiv (E := E) r s).symm
          (TensorRSSpace.toModel T)) :=
  rfl

set_option backward.isDefEq.respectTransparency true in

theorem covGradBundleEquiv_apply_eval (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r s I x)
    (D : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) r s x Φ) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ (v 0)) D)
        (Matrix.vecTail v) := by
  rw [covGradBundleEquiv_apply (I := I) (M := M) r s x Φ]
  rfl

set_option backward.isDefEq.respectTransparency true in

theorem covGradBundleEquiv_symm_apply_eval (r s : ℕ) (x : M)
    (T : TensorRSSpace r (s + 1) I x) (w : TangentSpace I x)
    (D : Tensor0SSpace r I x) (v : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          ((covGradBundleEquiv (I := I) (M := M) r s x).symm T) w) D) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) D)
        (Fin.cons w v) := by
  rw [covGradBundleEquiv_symm_apply (I := I) (M := M) r s x T]
  rfl

section Trivialisation

private theorem tensorRSBundle_baseSet_eq (r s : ℕ) (α : M) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (trivializationAt E (TangentSpace I) α).baseSet := by
  change (trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet =
    (trivializationAt E (TangentSpace I) α).baseSet
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet =
    (trivializationAt E (TangentSpace I) α).baseSet
  exact Set.inter_self _

private theorem covGradBundle_baseSet_eq (r s : ℕ) (α : M) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α).baseSet =
      (trivializationAt E (TangentSpace I) α).baseSet := by
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
    (trivializationAt E (TangentSpace I) α).baseSet
  rw [tensorRSBundle_baseSet_eq (I := I) r s α, Set.inter_self]

open TensorMultilinear in

private theorem tensor0S_trivFibre_apply (n : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) α).baseSet)
    (X : Tensor0SSpace n I b) (v : Fin n → E) :
    (trivializationAt (Tensor0SModel n ℝ E)
        (fun x : M => Tensor0SSpace n I x) α ⟨b, X⟩).2 v =
      Tensor0SSpace.toModel X
        (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ b (v j)) := by
  have hX : X = (tensor0SSpace_continuousLinearEquiv (I := I) n b).symm
      (Tensor0SSpace.toModel X) :=
    (Tensor0SSpace.ofModel_toModel X).symm
  have hkey := tensor0SBundle_linearMapAt_apply_of_mem (I := I) (M := M) α b hb
    (Tensor0SSpace.toModel X) v
  have hlm : (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) α ⟨b, X⟩).2 =
    (trivializationAt (Tensor0SModel n ℝ E)
      (fun x : M => Tensor0SSpace n I x) α).linearMapAt ℝ b X := by
    rw [Trivialization.coe_linearMapAt_of_mem _ hb]
  rw [hlm]
  conv_lhs => rw [hX]
  exact hkey

set_option maxHeartbeats 1600000 in
open TensorMultilinear in

theorem covGradBundleEquiv_trivializationAt_eq (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Φ : TangentSpace I b →L[ℝ] TensorRSSpace r s I b) :
    (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y) α
        ⟨b, covGradBundleEquiv (I := I) (M := M) r s b Φ⟩).2 =
      covGradModelEquiv (E := E) r s
        ((trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
          ⟨b, Φ⟩).2) := by
  letI : TopologicalSpace (TotalSpace (Tensor0SModel r ℝ E)
      (fun x : M => Tensor0SSpace r I x)) := tensor0SBundle_topology r
  letI : TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x)) := tensor0SBundle_topology s
  letI : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) := tensor0SBundle_topology (s + 1)
  have hb_r : b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun x : M => Tensor0SSpace r I x) α).baseSet := hb
  have hb_s : b ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace s I x) α).baseSet := hb
  have hb_s1 : b ∈ (trivializationAt (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x) α).baseSet := hb

  apply ContinuousLinearMap.ext
  intro D

  apply ContinuousMultilinearMap.ext
  intro v

  have hLHS_fibre :
      (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y) α
        ⟨b, covGradBundleEquiv (I := I) (M := M) r s b Φ⟩).2 =
      ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x) α).continuousLinearMapAt ℝ b).comp
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace (s + 1) I b from
            covGradBundleEquiv (I := I) (M := M) r s b Φ).comp
          ((trivializationAt (Tensor0SModel r ℝ E)
            (fun x : M => Tensor0SSpace r I x) α).symmL ℝ b)) := rfl

  have hG_fibre :
      (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, Φ⟩).2 =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
        (Φ.comp ((trivializationAt E (TangentSpace I) α).symmL ℝ b)) := rfl

  have hRS_fibre : ∀ Ψ : TensorRSSpace r s I b,
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α ⟨b, Ψ⟩).2 =
      ((trivializationAt (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) α).continuousLinearMapAt ℝ b).comp
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Ψ).comp
          ((trivializationAt (Tensor0SModel r ℝ E)
            (fun x : M => Tensor0SSpace r I x) α).symmL ℝ b)) :=
    fun Ψ => rfl

  have hclmAt_r : ∀ Z : Tensor0SSpace r I b,
      (trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).continuousLinearMapAt ℝ b Z =
      (trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α ⟨b, Z⟩).2 := by
    intro Z
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hb_r]
  have hclmAt_s : ∀ Z : Tensor0SSpace s I b,
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).continuousLinearMapAt ℝ b Z =
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α ⟨b, Z⟩).2 := by
    intro Z
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hb_s]
  have hclmAt_s1 : ∀ Z : Tensor0SSpace (s + 1) I b,
      (trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x) α).continuousLinearMapAt ℝ b Z =
      (trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x) α ⟨b, Z⟩).2 := by
    intro Z
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hb_s1]
  have hclmAt_RS : ∀ Ψ : TensorRSSpace r s I b,
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Ψ =
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α ⟨b, Ψ⟩).2 := by
    intro Ψ
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ (show b ∈ _ from
        (tensorRSBundle_baseSet_eq (I := I) r s α).symm ▸ hb)]

  set Dr : Tensor0SSpace r I b :=
    (trivializationAt (Tensor0SModel r ℝ E)
      (fun x : M => Tensor0SSpace r I x) α).symmL ℝ b D with hDr

  have hLHS :
      (trivializationAt (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y) α
        ⟨b, covGradBundleEquiv (I := I) (M := M) r s b Φ⟩).2 D v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            Φ ((trivializationAt E (TangentSpace I) α).symmL ℝ b (v 0))) Dr)
        (Matrix.vecTail
          (fun j : Fin (s + 1) =>
            (trivializationAt E (TangentSpace I) α).symmL ℝ b (v j))) := by
    rw [hLHS_fibre]
    change ((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun x : M => Tensor0SSpace (s + 1) I x) α).continuousLinearMapAt ℝ b)
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace (s + 1) I b from
            covGradBundleEquiv (I := I) (M := M) r s b Φ) Dr) v = _
    rw [hclmAt_s1, tensor0S_trivFibre_apply (I := I) (M := M) (s + 1) α hb_s1]
    rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r s b Φ Dr]

  have hRHS :
      covGradModelEquiv (E := E) r s
        ((trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
          ⟨b, Φ⟩).2) D v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            Φ ((trivializationAt E (TangentSpace I) α).symmL ℝ b (v 0))) Dr)
        (fun j : Fin s =>
          (trivializationAt E (TangentSpace I) α).symmL ℝ b
            (Matrix.vecTail v j)) := by
    rw [covGradModelEquiv_apply]
    rw [hG_fibre]
    change ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (Φ ((trivializationAt E (TangentSpace I) α).symmL ℝ b (v 0))))
        D (Matrix.vecTail v) = _
    rw [hclmAt_RS, hRS_fibre]
    change ((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).continuousLinearMapAt ℝ b)
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            Φ ((trivializationAt E (TangentSpace I) α).symmL ℝ b (v 0))) Dr)
          (Matrix.vecTail v) = _
    rw [hclmAt_s, tensor0S_trivFibre_apply (I := I) (M := M) s α hb_s]
  rw [hLHS, hRHS]
  congr 1

theorem covGradBundleEquiv_symm_trivializationAt_eq (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSSpace r (s + 1) I b) :
    (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) α
        ⟨b, (covGradBundleEquiv (I := I) (M := M) r s b).symm T⟩).2 =
      (covGradModelEquiv (E := E) r s).symm
        ((trivializationAt (TensorRSModel r (s + 1) ℝ E)
          (fun y : M => TensorRSSpace r (s + 1) I y) α ⟨b, T⟩).2) := by
  have hforward := covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s α hb
    ((covGradBundleEquiv (I := I) (M := M) r s b).symm T)
  rw [(covGradBundleEquiv (I := I) (M := M) r s b).apply_symm_apply T] at hforward
  rw [hforward, ContinuousLinearEquiv.symm_apply_apply]

end Trivialisation

section SmoothEquiv

set_option maxHeartbeats 1600000 in

theorem covGradBundleEquiv_contMDiff_totalSpace (r s : ℕ) :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
      (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun p : TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) =>
        (⟨p.1, covGradBundleEquiv (I := I) (M := M) r s p.1 p.2⟩ :
          TotalSpace (TensorRSModel r (s + 1) ℝ E)
            (fun y : M => TensorRSSpace r (s + 1) I y))) := by
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E))
        𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E) ∞
        (fun p => (trivializationAt (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := (covGradModelEquiv (E := E) r s).toContinuousLinearMap)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt E (TangentSpace I) p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj (E →L[ℝ] TensorRSModel r s ℝ E)
          (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y))).mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) p₀.proj)
    ] with p hp
    exact covGradBundleEquiv_trivializationAt_eq (I := I) (M := M) r s p₀.proj hp
      p.snd

set_option maxHeartbeats 1600000 in

theorem covGradBundleEquiv_symm_contMDiff_totalSpace (r s : ℕ) :
    ContMDiff (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E))
      (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun p : TotalSpace (TensorRSModel r (s + 1) ℝ E)
          (fun y : M => TensorRSSpace r (s + 1) I y) =>
        (⟨p.1, (covGradBundleEquiv (I := I) (M := M) r s p.1).symm p.2⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y))) := by
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundle_topology r (s + 1)
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun y : M => TensorRSSpace r (s + 1) I y)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E))
        𝓘(ℝ, TensorRSModel r (s + 1) ℝ E) ∞
        (fun p => (trivializationAt (TensorRSModel r (s + 1) ℝ E)
          (fun y : M => TensorRSSpace r (s + 1) I y) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const
      (c := (covGradModelEquiv (E := E) r s).symm.toContinuousLinearMap)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt E (TangentSpace I) p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj (TensorRSModel r (s + 1) ℝ E)
          (fun y : M => TensorRSSpace r (s + 1) I y))).mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) p₀.proj)
    ] with p hp
    exact covGradBundleEquiv_symm_trivializationAt_eq (I := I) (M := M) r s p₀.proj hp
      p.snd

noncomputable def covGradBundleSmoothEquiv (r s : ℕ) :=
  letI : NormedAddCommGroup (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (s + 1)
  letI : NormedSpace ℝ (TensorRSModel r (s + 1) ℝ E) :=
    tensorRSModel_normedSpace r (s + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y)) :=
    tensorRSBundle_topology r (s + 1)
  letI : FiberBundle (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_fiber r (s + 1)
  letI : VectorBundle ℝ (TensorRSModel r (s + 1) ℝ E)
      (fun y : M => TensorRSSpace r (s + 1) I y) :=
    tensorRSBundle_vector r (s + 1)
  (ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => (covGradBundleEquiv (I := I) (M := M) r s x).toLinearEquiv)
    (covGradBundleEquiv_contMDiff_totalSpace (I := I) (M := M) r s)
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r s) :
      ContMDiffVectorBundleEquiv ℝ I ∞
        (E →L[ℝ] TensorRSModel r s ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)
        (TensorRSModel r (s + 1) ℝ E)
        (fun y : M => TensorRSSpace r (s + 1) I y))

theorem covGradBundleSmoothEquiv_baseMap (r s : ℕ) :
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).baseMap = id :=
  rfl

theorem covGradBundleSmoothEquiv_fiberLinearEquiv (r s : ℕ) (x : M) :
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).fiberLinearEquiv x =
      (covGradBundleEquiv (I := I) (M := M) r s x).toLinearEquiv :=
  rfl

theorem covGradBundleSmoothEquiv_toDiffeomorph_apply (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r s I x) :
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph ⟨x, Φ⟩ =
      ⟨x, covGradBundleEquiv (I := I) (M := M) r s x Φ⟩ :=
  rfl

end SmoothEquiv

end Tensor0SBundle

end
