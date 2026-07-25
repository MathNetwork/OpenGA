import DifferentialGeometry.Geometry.Metric.OpenSubtype
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false










noncomputable section

namespace DifferentialGeometry

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners Real F H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
variable {n : WithTop ℕ∞}

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in


theorem codRestr_contMDiffAt
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace H' N']
    {V : Opens N'} {f : M → N'} (hmem : ∀ y, f y ∈ V) {x : M}
    (hf : ContMDiffAt I J (∞ : WithTop ℕ∞) f x) :
    ContMDiffAt I J (∞ : WithTop ℕ∞)
      (fun y ↦ (⟨f y, hmem y⟩ : V)) x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨hcont, hdiff⟩ := hf
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (by simpa [Function.comp_def] using hcont), ?_⟩
  convert hdiff using 2

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in


theorem image_opens_isOpen
    (Φ : PartialDiffeomorph I J M N n)
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source) :
    IsOpen ((Φ : M → N) '' (U : Set M)) := by
  have himg : (Φ : M → N) '' (U : Set M) =
      Φ.target ∩ ((Φ.symm : N → M) ⁻¹' (U : Set M)) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨Φ.map_source' (hU hu), ?_⟩
      have hleft : (Φ.symm : N → M) ((Φ : M → N) u) = u :=
        Φ.left_inv' (hU hu)
      change (Φ.symm : N → M) ((Φ : M → N) u) ∈ (U : Set M)
      rw [hleft]
      exact hu
    · rintro ⟨hy, hu⟩
      exact ⟨(Φ.symm : N → M) y, hu, Φ.right_inv' hy⟩
  rw [himg]
  exact Φ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    Φ.open_target U.2

namespace PartialDiffeomorph



noncomputable def toOpensDiffeoCross
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source) :
    Diffeomorph I J U
      (⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩ : Opens N)
      (∞ : WithTop ℕ∞) where
  toFun p := ⟨(Φ : M → N) p.1, ⟨p.1, p.2, rfl⟩⟩
  invFun q := ⟨(Φ.symm : N → M) q.1, by
    obtain ⟨u, hu, hueq⟩ := q.2
    rw [← hueq]
    have hleft : (Φ.symm : N → M) ((Φ : M → N) u) = u :=
      Φ.left_inv' (hU hu)
    change (Φ.symm : N → M) ((Φ : M → N) u) ∈ U
    rw [hleft]
    exact hu⟩
  left_inv p := by
    apply Subtype.ext
    exact Φ.left_inv' (hU p.2)
  right_inv q := by
    apply Subtype.ext
    obtain ⟨u, hu, hueq⟩ := q.2
    apply Φ.right_inv'
    rw [← hueq]
    exact Φ.map_source' (hU hu)
  contMDiff_toFun := by
    intro p
    have hbase : ContMDiffAt I J (∞ : WithTop ℕ∞)
        (fun p : U ↦ (Φ : M → N) p.1) p := by
      rw [contMDiffAt_subtype_iff]
      exact Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hU p.2))
    exact codRestr_contMDiffAt
      (V := (⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩ : Opens N))
      (f := fun p : U ↦ (Φ : M → N) p.1)
      (fun y ↦ ⟨y.1, y.2, rfl⟩) hbase
  contMDiff_invFun := by
    intro q
    let V : Opens N :=
      ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
    have hmem : ∀ y : V, (Φ.symm : N → M) y.1 ∈ U := by
      intro y
      obtain ⟨u, hu, hueq⟩ := y.2
      rw [← hueq]
      have hleft : (Φ.symm : N → M) ((Φ : M → N) u) = u :=
        Φ.left_inv' (hU hu)
      change (Φ.symm : N → M) ((Φ : M → N) u) ∈ U
      rw [hleft]
      exact hu
    have hbase : ContMDiffAt J I (∞ : WithTop ℕ∞)
        (fun y : V ↦ (Φ.symm : N → M) y.1) q := by
      rw [contMDiffAt_subtype_iff]
      obtain ⟨u, hu, hueq⟩ := q.2
      have hqt : (q : N) ∈ Φ.target := by
        rw [← hueq]
        exact Φ.map_source' (hU hu)
      exact Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.open_target.mem_nhds hqt)
    exact codRestr_contMDiffAt (I := J) (J := I) hmem hbase

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in


theorem opensDiffeo_mfd
    (Φ : PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source)
    (p : U) (v : TangentSpace I p) :
    mfderiv I J
        (toOpensDiffeoCross Φ hU : U →
          (⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩ : Opens N)) p v =
      mfderiv I J (Φ : M → N) (p : M) v := by
  let V : Opens N :=
    ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let Ψ : Diffeomorph I J U V (∞ : WithTop ℕ∞) :=
    toOpensDiffeoCross Φ hU
  have hΨd : MDifferentiableAt I J (Ψ : U → V) p :=
    Ψ.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalV : MDifferentiableAt J J (Subtype.val : V → N) (Ψ p) :=
    ((contMDiff_subtype_val (I := J) (U := V)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalU : MDifferentiableAt I I (Subtype.val : U → M) p :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦd : MDifferentiableAt I J (Φ : M → N) (p : M) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU p.2))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hleft : mfderiv I J (fun y : U ↦ ((Ψ y : V) : N)) p =
      (mfderiv J J (Subtype.val : V → N) (Ψ p)).comp
        (mfderiv I J (Ψ : U → V) p) :=
    mfderiv_comp p hvalV hΨd
  have hright : mfderiv I J (fun y : U ↦ (Φ : M → N) (y : M)) p =
      (mfderiv I J (Φ : M → N) (p : M)).comp
        (mfderiv I I (Subtype.val : U → M) p) :=
    mfderiv_comp p hΦd hvalU
  have happ := DFunLike.congr_fun (hleft.symm.trans hright) v
  simpa only [Ψ, ContinuousLinearMap.comp_apply,
    mfderiv_subtype_val (I := J) V (Ψ p),
    mfderiv_subtype_val (I := I) U p] using happ

end PartialDiffeomorph
end DifferentialGeometry
