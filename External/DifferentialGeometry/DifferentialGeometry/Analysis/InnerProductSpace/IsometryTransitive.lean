import Mathlib.Analysis.InnerProductSpace.PiL2




















noncomputable section

open Module
open scoped RealInnerProductSpace

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]




theorem exists_linearIsometryEquiv_unit {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ e : E ≃ₗᵢ[ℝ] E, e u = v := by
  classical
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact one_ne_zero hu.symm
  haveI : Nontrivial E := nontrivial_of_ne u 0 hu_ne
  have hn : 0 < finrank ℝ E := finrank_pos
  let i0 : Fin (finrank ℝ E) := ⟨0, hn⟩
  have card_eq : finrank ℝ E = Fintype.card (Fin (finrank ℝ E)) :=
    (Fintype.card_fin _).symm

  have hsingle : ∀ (w : E), ‖w‖ = 1 →
      Orthonormal ℝ (({i0} : Set (Fin (finrank ℝ E))).restrict (fun _ => w)) := by
    intro w hw
    haveI : Subsingleton ↥({i0} : Set (Fin (finrank ℝ E))) :=
      ⟨fun a b => Subtype.ext
        ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)⟩
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl]
    simp only [Set.restrict_apply]
    rw [real_inner_self_eq_norm_mul_norm, hw, mul_one]
  obtain ⟨bu, hbu⟩ :=
    (hsingle u hu).exists_orthonormalBasis_extension_of_card_eq card_eq
  obtain ⟨bv, hbv⟩ :=
    (hsingle v hv).exists_orthonormalBasis_extension_of_card_eq card_eq
  have hbu0 : bu i0 = u := hbu i0 (by simp)
  have hbv0 : bv i0 = v := hbv i0 (by simp)
  refine ⟨bu.equiv bv (Equiv.refl (Fin (finrank ℝ E))), ?_⟩
  calc bu.equiv bv (Equiv.refl (Fin (finrank ℝ E))) u
      = bu.equiv bv (Equiv.refl (Fin (finrank ℝ E))) (bu i0) := by rw [hbu0]
    _ = bv ((Equiv.refl (Fin (finrank ℝ E))) i0) := by
          rw [OrthonormalBasis.equiv_apply_basis]
    _ = bv i0 := by rw [Equiv.refl_apply]
    _ = v := hbv0

end DifferentialGeometry
