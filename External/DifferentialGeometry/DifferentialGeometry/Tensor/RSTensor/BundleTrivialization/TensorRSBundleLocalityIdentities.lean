import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.Tensor0SBundleLocalityIdentities
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Hom

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Tensor

open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensorRS_trivAt_symmL_apply_eq_self_on_locality
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (D : TensorRSModel r s ℝ E)
    (α_input : Tensor0SSpace r I b) :
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).symmL ℝ b D) α_input =
      (show Tensor0SSpace s I b from
        D ((show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input))) := by
  classical
  set eRS := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) b₀ with heRS_def
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) b₀ with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) b₀ with hes_def

  have hb_tan : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact h_src

  have hb_r : b ∈ er.baseSet := hb_tan
  have hb_s : b ∈ es.baseSet := hb_tan

  have hb_RS : b ∈ eRS.baseSet := ⟨hb_r, hb_s⟩

  have hHomSymm : (eRS.symmL ℝ b D :
      Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      (es.symmL ℝ b).comp (D.comp (er.continuousLinearMapAt ℝ b)) := by
    have h := _root_.Bundle.Pretrivialization.continuousLinearMap_symm_apply'
      (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (F₂ := Tensor0SModel s ℝ E)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (e₁ := er) (e₂ := es) (b := b) hb_RS D

    change (eRS.symm b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) = _

    rw [show (eRS.symm b D : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
          ((_root_.Bundle.Pretrivialization.continuousLinearMap (𝕜₁ := ℝ) (𝕜₂ := ℝ)
            (σ := RingHom.id ℝ) (F₁ := Tensor0SModel r ℝ E)
            (E₁ := fun y : M => Tensor0SSpace r I y)
            (F₂ := Tensor0SModel s ℝ E)
            (E₂ := fun y : M => Tensor0SSpace s I y)
            er es).symm b D) from rfl]
    exact h

  rw [hHomSymm]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

  have h_r := tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality
    (I := I) (M := M) (s := r) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src) (T := α_input)

  have h_s := tensor0S_trivAt_symmL_eq_one_on_locality
    (I := I) (M := M) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src)
    (T := D ((show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input)))

  have h_r_id :
      (er.continuousLinearMapAt ℝ b α_input :
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input) := h_r

  have h_s_id :
      (es.symmL ℝ b
          (D (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
        D (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input)) := h_s

  have h_inner :
      D (er.continuousLinearMapAt ℝ b α_input) =
      D (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from α_input) := by
    exact congrArg D h_r_id
  rw [h_inner]

  exact h_s_id

theorem tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : TensorRSSpace r s I b)
    (D_α : Tensor0SModel r ℝ E) :
    (show Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E from
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T) D_α =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
          (show Tensor0SSpace r I b from D_α)) := by
  classical
  set eRS := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) b₀ with heRS_def
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) b₀ with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) b₀ with hes_def

  have hb_tan : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact h_src
  have hb_r : b ∈ er.baseSet := hb_tan
  have hb_s : b ∈ es.baseSet := hb_tan
  have hb_RS : b ∈ eRS.baseSet := ⟨hb_r, hb_s⟩

  have hcoeRS := eRS.coe_linearMapAt_of_mem (R := ℝ) hb_RS

  have hForward : (eRS.continuousLinearMapAt ℝ b T :
      Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) =
      (es.continuousLinearMapAt ℝ b).comp
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T).comp
          (er.symmL ℝ b)) := by
    have h := congrFun hcoeRS T

    have h_cLMA : (eRS.continuousLinearMapAt ℝ b T :
        Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) =
        (eRS ⟨b, T⟩).2 := by
      simpa [Bundle.Trivialization.continuousLinearMapAt_apply] using h
    rw [h_cLMA]

    rfl
  rw [hForward]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

  have h_r := tensor0S_trivAt_symmL_eq_one_on_locality
    (I := I) (M := M) (s := r) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src) (T := D_α)

  have h_s := tensor0S_trivAt_continuousLinearMapAt_eq_one_on_locality
    (I := I) (M := M) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src)
    (T :=
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
        (show Tensor0SSpace r I b from D_α))

  have h_r_id :
      (er.symmL ℝ b D_α :
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from
        (show Tensor0SSpace r I b from D_α)) := h_r

  have h_s_id :
      (es.continuousLinearMapAt ℝ b
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
            (show Tensor0SSpace r I b from D_α)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ from
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
          (show Tensor0SSpace r I b from D_α))) := h_s
  have h_inner :
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
          (er.symmL ℝ b D_α) =
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T)
          (show Tensor0SSpace r I b from D_α) :=
    congrArg (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T) h_r_id
  rw [h_inner]
  exact h_s_id

end Tensor
end DifferentialGeometry

end
