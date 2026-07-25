import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculus

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem core_curry_reading (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s) (x : M) (v : E)
    (D : Tensor0SBundle.Tensor0SSpace (r + 1) I x) (v0 : E) :
    (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SBundle.Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
          Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ (r + 1) (s + 1)
            (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ) x v) D)) v0 =
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ r s Φ x v)
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D v0) := by
  classical
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (r + 1) ℝ E) (V := fun y : M => Tensor0SSpace (r + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  have hwcurry_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y
        ((Tensor0SNabla.curriedSection (I := I) (M := M) (fun z : M => w z) y) (Y y))) := by
    have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel r ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel r ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace r I z) y
          (Tensor0SNabla.curriedSection (I := I) (M := M) (fun z : M => w z) y)) :=
      fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
        (fun z : M => w z) y (w.contMDiff y)
    exact ContMDiff.clm_bundle_apply (b := id) hcurried Y.contMDiff
  let wcurry : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨fun y : M => (Tensor0SNabla.curriedSection (I := I) (M := M) (fun z : M => w z) y) (Y y), hwcurry_smooth⟩
  set SEΦ := Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ with hSEΦ
  have hU_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        ((show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SEΦ.toSection y) (w y))) :=
    ContMDiff.clm_bundle_apply (b := id) SEΦ.toSection.contMDiff w.contMDiff
  have hU_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SEΦ.toSection y) (w y)) x :=
    (hU_smooth x).mdifferentiableAt (by norm_num)
  have hw_at : TensorSectionMDiffAt (I := I) (r + 1) (fun y : M => w y) x :=
    (w.contMDiff x).mdifferentiableAt (by norm_num)
  have hCL_U := Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g₀ s
    (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SEΦ.toSection y) (w y))
    (x := x) hU_at Y v
  have hCL_w := Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g₀ r
    (fun y : M => w y) (x := x) hw_at Y v
  have hHL_Φ := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r s (LeviCivita (I := I) g₀)
    Φ.toSection wcurry x v
  have hHL_SE := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) (r + 1) (s + 1) (LeviCivita (I := I) g₀)
    SEΦ.toSection w x v
  have hfun : (fun y : M =>
        (Tensor0SNabla.curriedSection I M
            (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              SEΦ.toSection y) (w y)) y) (Y y)) =
      (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (wcurry y)) := by
    funext y
    change (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        ((show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SEΦ.toSection y) (w y))) (Y y) =
      (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y)
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r y (w y)) (Y y))
    rw [hSEΦ, Integral.Connection.slotExtend_toSection, Integral.Connection.slotExtendFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  rw [← hw, ← hY,
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) g₀ (r + 1) (s + 1) SEΦ x v,
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) g₀ r s Φ x v]
  rw [show ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (w x)) (Y x) = wcurry x from rfl]
  rw [hHL_Φ]
  rw [hHL_SE, map_sub, ContinuousLinearMap.sub_apply]
  rw [eq_sub_of_add_eq hCL_U.symm]
  rw [hfun]
  rw [hSEΦ, Integral.Connection.slotExtend_toSection, Integral.Connection.slotExtendFib_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  have hcurU_op : (Tensor0SNabla.curriedSection I M
        (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          SEΦ.toSection y) (w y)) x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        (Tensor0SNabla.curriedSection I M (fun y : M => w y) x) := by
    apply ContinuousLinearMap.ext
    intro t
    change (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from SEΦ.toSection x) (w x))) t =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x (w x)) t)
    rw [hSEΦ, Integral.Connection.slotExtend_toSection, Integral.Connection.slotExtendFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  rw [show (⇑wcurry) = (fun y : M => (Tensor0SNabla.curriedSection I M (fun z : M => w z) y) (Y y)) from rfl,
    hCL_w, map_add]
  rw [hcurU_op, ContinuousLinearMap.comp_apply]
  abel


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_slotExtend_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s) (x : M) (v : E) :
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ (r + 1) (s + 1)
        (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ) x v =
      (show Tensor0SBundle.Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
        Integral.Connection.slotExtendPointwise (I := I) (M := M) g₀ r s x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ r s Φ x v)) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [Integral.Connection.slotExtendFib_apply_eval (I := I) (M := M) g₀ r s x
    (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ r s Φ x v)
    D (m 0) (Matrix.vecTail m)]
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SBundle.Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ (r + 1) (s + 1)
        (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ) x v) D) (v0 := m 0) (vs := Matrix.vecTail m)]
  congr 1
  exact core_curry_reading (I := I) (M := M) g₀ r s Φ x v D (m 0)


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_slotExtend_eq_zero_of_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s)
    (hΦ : Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ r s Φ = 0) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ (r + 1) (s + 1)
        (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ) = 0 := by
  classical

  have hslotZero : ∀ (y : M),
      Integral.Connection.slotExtendPointwise (I := I) (M := M) g₀ r s y
          (0 : Tensor0SBundle.Tensor0SSpace r I y →L[ℝ] Tensor0SBundle.Tensor0SSpace s I y) =
        (0 : Tensor0SBundle.Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I y) := by
    intro y
    apply ContinuousLinearMap.ext
    intro D
    rw [Integral.Connection.slotExtendFib_apply, ContinuousLinearMap.zero_comp, map_zero,
      ContinuousLinearMap.zero_apply]

  have hdir : ∀ (x : M) (v : E),
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ r s Φ x v = 0 := by
    intro x v
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun m => ?_)

    have heval := Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval
      (I := I) (M := M) g₀ r s Φ x D (Fin.cons v m)
    rw [hΦ, Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply] at heval
    rw [Fin.cons_zero, show (Matrix.vecTail (Fin.cons v m)) = m from funext (fun j => by
      simp [Matrix.vecTail, Fin.cons_succ])] at heval
    beta_reduce
    rw [ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply]
    exact heval.symm

  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply,
    Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval
    (I := I) (M := M) g₀ (r + 1) (s + 1) (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ)
    x D m, tensorCovDerivAt_slotExtend_eq (I := I) (M := M) g₀ r s Φ x (m 0), hdir x (m 0),
    hslotZero x, ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
