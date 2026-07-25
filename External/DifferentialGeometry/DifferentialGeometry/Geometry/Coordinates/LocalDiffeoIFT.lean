import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import DifferentialGeometry.Analysis.Calculus.CLMNeumann

set_option autoImplicit false
set_option linter.style.longLine false


























noncomputable section

open Set Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Coordinates

variable {n : WithTop ℕ∞}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]
variable {f : M → N} {x : M}



theorem isInvertible_of_norm_id_sub_lt {T : E →L[ℝ] E}
    (h : ‖ContinuousLinearMap.id ℝ E - T‖ < 1) : T.IsInvertible := by
  exact ContinuousLinearMap.invertible_of_id_sub h



























omit [CompleteSpace F] in
theorem isLocalDiffeomorphAt_of_contMDiffOn' (hn : 1 ≤ n) (hn' : n ≠ ∞) {U : Set M} (hU : IsOpen U)
    (hxU : x ∈ U) (hf : ContMDiffOn I J n f U)
    (hinv : (fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ Φ.source ⊆ U ∧ EqOn f Φ Φ.source := by
  classical
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'

  have hfx : ContMDiffAt I J n f x := hf.contMDiffAt (hU.mem_nhds hxU)
  have hG : ContDiffAt ℝ n (writtenInExtChartAt I J x f) (extChartAt I x x) := by
    have h := (contMDiffAt_iff.mp hfx).2
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at h
  obtain ⟨G', hG'⟩ := hinv
  have hGfd : HasFDerivAt (writtenInExtChartAt I J x f) (G' : E →L[ℝ] F) (extChartAt I x x) := by
    rw [hG']; exact (hG.differentiableAt hn0).hasFDerivAt

  set Ψ : OpenPartialHomeomorph E F :=
    hG.toOpenPartialHomeomorph (writtenInExtChartAt I J x f) hGfd hn0 with hΨdef
  have hΨcoe : (Ψ : E → F) = writtenInExtChartAt I J x f :=
    hG.toOpenPartialHomeomorph_coe hGfd hn0
  have ha₀ : extChartAt I x x ∈ Ψ.source := hG.mem_toOpenPartialHomeomorph_source hGfd hn0

  set cO : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I x
      open_source := isOpen_extChartAt_source x
      open_target := isOpen_extChartAt_target x
      continuousOn_toFun := continuousOn_extChartAt x
      continuousOn_invFun := continuousOn_extChartAt_symm x } with hcO
  set dO : OpenPartialHomeomorph N F :=
    { toPartialEquiv := extChartAt J (f x)
      open_source := isOpen_extChartAt_source (f x)
      open_target := isOpen_extChartAt_target (f x)
      continuousOn_toFun := continuousOn_extChartAt (f x)
      continuousOn_invFun := continuousOn_extChartAt_symm (f x) } with hdO
  set Θ : OpenPartialHomeomorph M N := (cO.trans Ψ).trans dO.symm with hΘ

  have hcz : (cO : M → E) = (extChartAt I x : M → E) := rfl
  have hdsz : (dO.symm : F → N) = ((extChartAt J (f x)).symm : F → N) := rfl
  have hEq : ∀ z : M, z ∈ (extChartAt I x).source → f z ∈ (extChartAt J (f x)).source →
      Θ z = f z := by
    intro z hz hfz
    rw [hΘ, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply, hcz,
      congrFun hΨcoe, hdsz]
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [PartialEquiv.left_inv (extChartAt I x) hz, PartialEquiv.left_inv (extChartAt J (f x)) hfz]
  have hxsrc : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hfxsrc : f x ∈ (extChartAt J (f x)).source := mem_extChartAt_source (f x)
  have hΘx : Θ x = f x := hEq x hxsrc hfxsrc

  have hxΘ : x ∈ Θ.source := by
    rw [hΘ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
    refine ⟨⟨hxsrc, ?_⟩, ?_⟩
    · exact ha₀
    · rw [Set.mem_preimage, OpenPartialHomeomorph.trans_apply, hcz, hΨcoe]
      simp only [writtenInExtChartAt, Function.comp_apply,
        PartialEquiv.left_inv (extChartAt I x) hxsrc]
      exact (extChartAt J (f x)).map_source hfxsrc

  have hΨinv : ContDiffAt ℝ n (Ψ.symm) (extChartAt J (f x) (f x)) := by
    have hGa : writtenInExtChartAt I J x f (extChartAt I x x) = extChartAt J (f x) (f x) := by
      simp only [writtenInExtChartAt, Function.comp_apply,
        PartialEquiv.left_inv (extChartAt I x) hxsrc]
    have hsymm_pt : Ψ.symm (extChartAt J (f x) (f x)) = extChartAt I x x := by
      rw [← hGa, ← congrFun hΨcoe]; exact Ψ.left_inv ha₀
    have htgt : extChartAt J (f x) (f x) ∈ Ψ.target := by
      rw [← hGa]; exact Ψ.map_source ha₀
    refine Ψ.contDiffAt_symm htgt (f₀' := G') ?_ ?_
    · rw [hsymm_pt]; exact (hΨcoe ▸ hGfd :)
    · rw [hsymm_pt]; exact (hΨcoe ▸ hG :)

  have hsymm_pt : Ψ.symm (extChartAt J (f x) (f x)) = extChartAt I x x := by
    have hGa : writtenInExtChartAt I J x f (extChartAt I x x) = extChartAt J (f x) (f x) := by
      simp only [writtenInExtChartAt, Function.comp_apply,
        PartialEquiv.left_inv (extChartAt I x) hxsrc]
    rw [← hGa, ← congrFun hΨcoe]; exact Ψ.left_inv ha₀
  have hΘsymm_at : ContMDiffAt J I n (Θ.symm : N → M) (f x) := by
    have hfn : (Θ.symm : N → M)
        = (fun y => (extChartAt I x).symm (Ψ.symm (extChartAt J (f x) y))) := by
      ext y
      rw [hΘ]
      simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
        Function.comp_apply]
      rfl
    rw [hfn]
    have h1 : ContMDiffAt J 𝓘(ℝ, F) n (extChartAt J (f x)) (f x) := contMDiffAt_extChartAt
    have h2 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) n (Ψ.symm) (extChartAt J (f x) (f x)) :=
      contMDiffAt_iff_contDiffAt.mpr hΨinv
    have h3 : ContMDiffAt 𝓘(ℝ, E) I n ((extChartAt I x).symm)
        (Ψ.symm (extChartAt J (f x) (f x))) := by
      rw [hsymm_pt]
      exact (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    exact h3.comp (f x) (h2.comp (f x) h1)
  obtain ⟨W, hWnhds, hΘsymmW⟩ := (contMDiffAt_iff_contMDiffOn_nhds hn').mp hΘsymm_at

  have hSnhds : Θ.source ∩ U ∩ f ⁻¹' (extChartAt J (f x)).source ∩ Θ ⁻¹' W ∈ nhds x := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_) ?_
    · exact Θ.open_source.mem_nhds hxΘ
    · exact hU.mem_nhds hxU
    · exact hfx.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (f x)).mem_nhds hfxsrc)
    · exact (Θ.continuousOn.continuousAt (Θ.open_source.mem_nhds hxΘ)).preimage_mem_nhds
        (by rw [hΘx]; exact hWnhds)
  obtain ⟨S, hSsub, hSopen, hxS⟩ := mem_nhds_iff.mp hSnhds

  have hEqS : ∀ z ∈ S, f z = Θ z := by
    intro z hz
    have hz' := hSsub hz
    have hzΘ : z ∈ Θ.source := hz'.1.1.1
    have hzc : z ∈ (extChartAt I x).source := by
      rw [hΘ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source] at hzΘ
      exact hzΘ.1.1
    exact (hEq z hzc hz'.1.2).symm
  have hsymmfz : ∀ z ∈ S, (Θ.symm : N → M) (f z) = z := fun z hz => by
    rw [hEqS z hz]; exact Θ.left_inv (hSsub hz).1.1.1

  refine ⟨{
    toFun := f
    invFun := (Θ.symm : N → M)
    source := S
    target := f '' S
    map_source' := fun z hz => Set.mem_image_of_mem f hz
    map_target' := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy; rw [hsymmfz z hz]; exact hz
    left_inv' := fun z hz => hsymmfz z hz
    right_inv' := fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy; rw [hsymmfz z hz]
    open_source := hSopen
    open_target := by
      rw [Set.image_congr hEqS]
      exact Θ.isOpen_image_of_subset_source hSopen (fun z hz => (hSsub hz).1.1.1)
    contMDiffOn_toFun := hf.mono (fun z hz => (hSsub hz).1.1.2)
    contMDiffOn_invFun := by
      rw [Set.image_congr hEqS]
      refine hΘsymmW.mono ?_
      rintro y ⟨z, hz, rfl⟩; exact (hSsub hz).2 }, hxS,
    fun z hz => (hSsub hz).1.1.2, fun z _ => rfl⟩




omit [CompleteSpace E] in
theorem norm_sub_le_of_fderiv_near_id {s : Set E} (hs : Convex ℝ s) {G : E → E} {ε : ℝ}
    (hG : ∀ z ∈ s, DifferentiableAt ℝ G z)
    (hbd : ∀ z ∈ s, ‖ContinuousLinearMap.id ℝ E - fderiv ℝ G z‖ ≤ ε)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (1 - ε) * ‖x - y‖ ≤ ‖G x - G y‖ := by
  have hh : ∀ z ∈ s, DifferentiableAt ℝ (fun w => w - G w) z := fun z hz =>
    differentiableAt_id.sub (hG z hz)
  have hbd' : ∀ z ∈ s, ‖fderiv ℝ (fun w => w - G w) z‖ ≤ ε := by
    intro z hz
    have hsub : HasFDerivAt (fun w => w - G w)
        (ContinuousLinearMap.id ℝ E - fderiv ℝ G z) z :=
      (hasFDerivAt_id z).sub (hG z hz).hasFDerivAt
    rw [hsub.fderiv]
    exact hbd z hz
  have hmvt : ‖(x - G x) - (y - G y)‖ ≤ ε * ‖x - y‖ :=
    hs.norm_image_sub_le_of_norm_fderiv_le hh hbd' hy hx
  have hdecomp : x - y = (G x - G y) + ((x - G x) - (y - G y)) := by abel
  have hkey : ‖x - y‖ ≤ ‖G x - G y‖ + ε * ‖x - y‖ := by
    calc ‖x - y‖ = ‖(G x - G y) + ((x - G x) - (y - G y))‖ := by rw [← hdecomp]
      _ ≤ ‖G x - G y‖ + ‖(x - G x) - (y - G y)‖ := norm_add_le _ _
      _ ≤ ‖G x - G y‖ + ε * ‖x - y‖ := by linarith
  linarith




omit [CompleteSpace E] in
theorem injOn_of_fderiv_near_id {s : Set E} (hs : Convex ℝ s) {G : E → E} {ε : ℝ} (hε : ε < 1)
    (hG : ∀ z ∈ s, DifferentiableAt ℝ G z)
    (hbd : ∀ z ∈ s, ‖ContinuousLinearMap.id ℝ E - fderiv ℝ G z‖ ≤ ε) :
    Set.InjOn G s := by
  intro x hx y hy hGxy
  have h := norm_sub_le_of_fderiv_near_id hs hG hbd hx hy
  rw [hGxy, sub_self, norm_zero] at h
  have hnorm : ‖x - y‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg (x - y)]) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)






omit [CompleteSpace E] [I.Boundaryless] [CompleteSpace F] [J.Boundaryless] in
theorem injOn_of_writtenInExtChart {f : M → N} {U : Set M} (x₀ : M)
    (hUsub : U ⊆ (extChartAt I x₀).source)
    (hinj : Set.InjOn (writtenInExtChartAt I J x₀ f) ((extChartAt I x₀) '' U)) :
    Set.InjOn f U := by
  intro a ha b hb hfab
  have hGa : writtenInExtChartAt I J x₀ f (extChartAt I x₀ a)
      = extChartAt J (f x₀) (f a) := by
    simp only [writtenInExtChartAt, Function.comp_apply,
      PartialEquiv.left_inv (extChartAt I x₀) (hUsub ha)]
  have hGb : writtenInExtChartAt I J x₀ f (extChartAt I x₀ b)
      = extChartAt J (f x₀) (f b) := by
    simp only [writtenInExtChartAt, Function.comp_apply,
      PartialEquiv.left_inv (extChartAt I x₀) (hUsub hb)]
  have hchart : extChartAt I x₀ a = extChartAt I x₀ b := by
    refine hinj (Set.mem_image_of_mem _ ha) (Set.mem_image_of_mem _ hb) ?_
    rw [hGa, hGb, hfab]
  have := congrArg (extChartAt I x₀).symm hchart
  rwa [PartialEquiv.left_inv _ (hUsub ha), PartialEquiv.left_inv _ (hUsub hb)] at this





omit [CompleteSpace F] in
theorem isLocalDiffeomorphAt_of_contMDiffOn (hn : 1 ≤ n) (hn' : n ≠ ∞) {U : Set M} (hU : IsOpen U)
    (hxU : x ∈ U) (hf : ContMDiffOn I J n f U)
    (hinv : (fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible) :
    IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨Φ, hx, -, hEq⟩ := isLocalDiffeomorphAt_of_contMDiffOn' hn hn' hU hxU hf hinv
  exact ⟨Φ, hx, hEq⟩




omit [CompleteSpace F] in
theorem contMDiffOn_isLocalDiffeomorphOn (hn : 1 ≤ n) (hn' : n ≠ ∞) {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I J n f U)
    (hinv : ∀ y ∈ U,
      (fderiv ℝ (writtenInExtChartAt I J y f) (extChartAt I y y)).IsInvertible) :
    IsLocalDiffeomorphOn I J n f U := by
  rintro ⟨y, hy⟩
  exact isLocalDiffeomorphAt_of_contMDiffOn hn hn' hU hy hf (hinv y hy)




omit [CompleteSpace F] in
theorem contMDiffAt_isLocalDiffeomorphAt (hn : 1 ≤ n) (hn' : n ≠ ∞)
    (hf : ContMDiffAt I J n f x)
    (hinv : (fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x)).IsInvertible) :
    IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨W, hW_nhds, hfW⟩ := (contMDiffAt_iff_contMDiffOn_nhds hn').mp hf
  obtain ⟨V, hVW, hV_open, hxV⟩ := mem_nhds_iff.mp hW_nhds
  exact isLocalDiffeomorphAt_of_contMDiffOn hn hn' hV_open hxV (hfW.mono hVW) hinv




omit [CompleteSpace F] in
theorem hlocAt_infty'
    [IsManifold I ∞ M] [IsManifold J ∞ N] {f : M → N} {U : Set M} (hU : IsOpen U)
    (hxU : x ∈ U) (hf : ContMDiffOn I J ∞ f U)
    (hinv : ∀ y ∈ U,
      (fderiv ℝ (writtenInExtChartAt I J y f) (extChartAt I y y)).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I J M N ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ EqOn f Φ Φ.source := by

  obtain ⟨Φ, hxΦ, hΦU, hEqΦ⟩ :=
    isLocalDiffeomorphAt_of_contMDiffOn' (n := 1) le_rfl
      (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤)) hU hxU
      (hf.of_le (by exact_mod_cast le_top)) (hinv x hxU)

  have hsymm_infty : ContMDiffOn J I ∞ (Φ.symm : N → M) Φ.target := by
    rw [contMDiffOn_infty]
    intro k y hy
    have hzsrc : (Φ.symm : N → M) y ∈ Φ.source := Φ.toPartialEquiv.map_target hy
    have hzU : (Φ.symm : N → M) y ∈ U := hΦU hzsrc
    have hfz : f ((Φ.symm : N → M) y) = y := by
      rw [hEqΦ hzsrc]; exact Φ.toPartialEquiv.right_inv hy

    obtain ⟨Ψ, hzΨ, hEqΨ⟩ :=
      isLocalDiffeomorphAt_of_contMDiffOn (n := ((max 1 k : ℕ) : WithTop ℕ∞))
        (by exact_mod_cast le_max_left 1 k) (by exact_mod_cast ENat.coe_ne_top (max 1 k))
        hU hzU (hf.of_le (by exact_mod_cast le_top)) (hinv _ hzU)

    have hWopen : IsOpen (Φ.target ∩ (Ψ.target ∩ (Ψ.symm : N → M) ⁻¹' Φ.source)) :=
      Φ.open_target.inter (Ψ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage
        Ψ.open_target Φ.open_source)
    have hyΨt : y ∈ Ψ.target := by
      rw [← hfz, hEqΨ hzΨ]; exact Ψ.toPartialEquiv.map_source hzΨ
    have hyW : y ∈ Φ.target ∩ (Ψ.target ∩ (Ψ.symm : N → M) ⁻¹' Φ.source) := by
      refine ⟨hy, hyΨt, ?_⟩
      have h1 : (Ψ : M → N) ((Φ.symm : N → M) y) = y := by rw [← hEqΨ hzΨ, hfz]
      have hΨsy : (Ψ.symm : N → M) y = (Φ.symm : N → M) y :=
        calc (Ψ.symm : N → M) y
            = (Ψ.symm : N → M) ((Ψ : M → N) ((Φ.symm : N → M) y)) := by rw [h1]
          _ = (Φ.symm : N → M) y := Ψ.toPartialEquiv.left_inv hzΨ
      rw [Set.mem_preimage, hΨsy]; exact hzsrc

    have hEqOn : EqOn (Φ.symm : N → M) (Ψ.symm : N → M)
        (Φ.target ∩ (Ψ.target ∩ (Ψ.symm : N → M) ⁻¹' Φ.source)) := by
      rintro y' ⟨hy'Φ, hy'Ψ, hy'pre⟩
      have ha : (Φ.symm : N → M) y' ∈ Φ.source := Φ.toPartialEquiv.map_target hy'Φ
      have hb : (Ψ.symm : N → M) y' ∈ Φ.source := hy'pre
      have hbΨ : (Ψ.symm : N → M) y' ∈ Ψ.source := Ψ.toPartialEquiv.map_target hy'Ψ
      refine Φ.toPartialEquiv.injOn ha hb ?_
      have h1 : (Φ : M → N) ((Φ.symm : N → M) y') = y' := Φ.toPartialEquiv.right_inv hy'Φ
      have h2 : (Φ : M → N) ((Ψ.symm : N → M) y') = y' := by
        rw [← hEqΦ hb, hEqΨ hbΨ]; exact Ψ.toPartialEquiv.right_inv hy'Ψ
      rw [show Φ.toPartialEquiv ((Φ.symm : N → M) y') = y' from h1,
        show Φ.toPartialEquiv ((Ψ.symm : N → M) y') = y' from h2]

    have hΨsm : ContMDiffAt J I (k : WithTop ℕ∞) (Ψ.symm : N → M) y :=
      (Ψ.symm.contMDiffOn.contMDiffAt (Ψ.open_target.mem_nhds hyΨt)).of_le
        (by exact_mod_cast le_max_right 1 k)
    exact ((hΨsm.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hWopen.mem_nhds hyW) hEqOn)).contMDiffWithinAt :)

  exact ⟨{ toPartialEquiv := Φ.toPartialEquiv
           open_source := Φ.open_source
           open_target := Φ.open_target
           contMDiffOn_toFun := (hf.mono hΦU).congr (fun z hz => (hEqΦ hz).symm)
           contMDiffOn_invFun := hsymm_infty }, hxΦ, hΦU, hEqΦ⟩











omit [CompleteSpace F] in
theorem contMDiffOn_isLocalDiffeomorphOn_infty
    [IsManifold I ∞ M] [IsManifold J ∞ N] {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I J ∞ f U)
    (hinv : ∀ y ∈ U,
      (fderiv ℝ (writtenInExtChartAt I J y f) (extChartAt I y y)).IsInvertible) :
    IsLocalDiffeomorphOn I J ∞ f U := by
  rintro ⟨x, hxU⟩
  obtain ⟨Φ, hxΦ, -, hEqΦ⟩ := hlocAt_infty' hU hxU hf hinv
  exact ⟨Φ, hxΦ, hEqΦ⟩

omit [I.Boundaryless] [J.Boundaryless] in




omit [CompleteSpace F] in
theorem hlocAt_of_coord
    [IsManifold I ∞ M] [IsManifold J ∞ N]
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (d : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : M → N} {x : M} {V : Set E} (hV : IsOpen V)
    (hxc : x ∈ c.source) (hcxV : c x ∈ V)
    (hmap : MapsTo (fun z => f (c.symm z)) V d.source)
    (hG : ContDiffOn ℝ ∞ (fun z => d (f (c.symm z))) V)
    (hinv : ∀ z ∈ V,
      (fderiv ℝ (fun w => d (f (c.symm w))) z).IsInvertible) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let G₀ : E → F := fun z => d (f (c.symm z))
  have hGm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ G₀ V := hG.contMDiffOn
  have hinvm : ∀ z ∈ V,
      (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, F) z G₀)
        (extChartAt 𝓘(ℝ, E) z z)).IsInvertible := by
    intro z hz
    simpa only [G₀, writtenInExtChartAt, extChartAt_self_eq, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq] using hinv z hz
  obtain ⟨Ψ, hcxΨ, hΨV, hEqΨ⟩ :=
    hlocAt_infty' (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, F)) hV hcxV hGm hinvm


  let cΨ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞ :=
    { toPartialEquiv := c.toPartialEquiv.trans Ψ.toPartialEquiv
      open_source := by
        have hsrc : (c.toPartialEquiv.trans Ψ.toPartialEquiv).source
            = c.source ∩ (c : M → E) ⁻¹' Ψ.source := rfl
        rw [hsrc]
        exact c.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_source Ψ.open_source
      open_target := by
        have htgt : (c.toPartialEquiv.trans Ψ.toPartialEquiv).target
            = Ψ.target ∩ (Ψ.symm : F → E) ⁻¹' c.target := by
          rw [PartialEquiv.trans_target]
          rfl
        rw [htgt]
        exact Ψ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Ψ.open_target
          c.open_target
      contMDiffOn_toFun := by
        have hsrc : (c.toPartialEquiv.trans Ψ.toPartialEquiv).source
            = c.source ∩ (c : M → E) ⁻¹' Ψ.source := rfl
        rw [hsrc]
        exact Ψ.contMDiffOn_toFun.comp
          (c.contMDiffOn_toFun.mono Set.inter_subset_left) (fun _ hz => hz.2)
      contMDiffOn_invFun := by
        have htgt : (c.toPartialEquiv.trans Ψ.toPartialEquiv).target
            = Ψ.target ∩ (Ψ.symm : F → E) ⁻¹' c.target := by
          rw [PartialEquiv.trans_target]
          rfl
        rw [htgt]
        exact c.symm.contMDiffOn_toFun.comp
          (Ψ.symm.contMDiffOn_toFun.mono Set.inter_subset_left) (fun _ hz => hz.2) }

  let Θ : PartialDiffeomorph I J M N ∞ :=
    { toPartialEquiv := cΨ.toPartialEquiv.trans d.symm.toPartialEquiv
      open_source := by
        have hsrc : (cΨ.toPartialEquiv.trans d.symm.toPartialEquiv).source
            = cΨ.source ∩ (cΨ : M → F) ⁻¹' d.symm.source := rfl
        rw [hsrc]
        exact cΨ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage cΨ.open_source
          d.symm.open_source
      open_target := by
        have htgt : (cΨ.toPartialEquiv.trans d.symm.toPartialEquiv).target
            = d.symm.target ∩ (d : N → F) ⁻¹' cΨ.target := by
          rw [PartialEquiv.trans_target]
          rfl
        rw [htgt]
        exact d.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.open_source cΨ.open_target
      contMDiffOn_toFun := by
        have hsrc : (cΨ.toPartialEquiv.trans d.symm.toPartialEquiv).source
            = cΨ.source ∩ (cΨ : M → F) ⁻¹' d.symm.source := rfl
        rw [hsrc]
        exact d.symm.contMDiffOn_toFun.comp
          (cΨ.contMDiffOn_toFun.mono Set.inter_subset_left) (fun _ hz => hz.2)
      contMDiffOn_invFun := by
        have htgt : (cΨ.toPartialEquiv.trans d.symm.toPartialEquiv).target
            = d.symm.target ∩ (d : N → F) ⁻¹' cΨ.target := by
          rw [PartialEquiv.trans_target]
          rfl
        rw [htgt]
        exact cΨ.symm.contMDiffOn_toFun.comp
          (d.contMDiffOn_toFun.mono Set.inter_subset_left) (fun _ hz => hz.2) }
  have hΨt : Ψ (c x) ∈ d.target := by
    rw [← hEqΨ hcxΨ]
    exact d.toPartialEquiv.map_source (hmap hcxV)
  refine ⟨Θ, ?_, ?_⟩
  · exact ⟨⟨hxc, hcxΨ⟩, hΨt⟩
  · intro z hz
    have hzc : z ∈ c.source := hz.1.1
    have hczΨ : c z ∈ Ψ.source := hz.1.2
    have hcz : (c.symm : E → M) (c z) = z := c.toPartialEquiv.left_inv hzc
    have hfzd : f z ∈ d.source := by
      have h := hmap (hΨV hczΨ)
      change f (c.symm (c z)) ∈ d.source at h
      rw [hcz] at h
      exact h
    simp only [Θ, cΨ, PartialEquiv.trans_apply]
    rw [← hEqΨ hczΨ]
    change f z = d.symm (d (f (c.symm (c z))))
    rw [hcz]
    exact (d.toPartialEquiv.left_inv hfzd).symm

end Coordinates
end DifferentialGeometry
