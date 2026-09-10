import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry

noncomputable abbrev vderiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) : M -> 𝕜 :=
  fun x => mvfderiv (I := I) f x (X x)

@[simp] theorem vderiv_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) (x : M) :
    vderiv (I := I) f X x = mvfderiv (I := I) f x (X x) := by
  rfl

 theorem _root_.DifferentialGeometry.mfderiv_eq_fderivWithin_chart_comp_closedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (f : M -> Real) (x : M) (z : M) (hz : z ∈ (extChartAt I x).source)
    (hg_diffWithin : DifferentiableWithinAt Real (f ∘ (extChartAt I x).symm)
      (Set.range I) ((extChartAt I x) z)) :
    mfderiv I 𝓘(Real, Real) f z =
      (fderivWithin Real (f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) z)).comp
        (mfderiv I 𝓘(Real, E) (extChartAt I x) z) := by
  set φ := extChartAt I x with hφ
  set s : Set E := Set.range I with hs
  set g : E -> Real := f ∘ φ.symm with hg
  have hφ_open : IsOpen φ.source := isOpen_extChartAt_source (I := I) x
  have hz_chart : z ∈ (chartAt H x).source := by
    simpa only [φ, extChartAt_source] using hz
  have hf_eq : f =ᶠ[𝓝 z] g ∘ φ := by
    filter_upwards [hφ_open.mem_nhds hz] with w hw
    simp only [g, Function.comp_apply, φ.left_inv hw]
  rw [hf_eq.mfderiv_eq]
  have hφ_diff : MDifferentiableAt I 𝓘(Real, E) φ z :=
    mdifferentiableAt_extChartAt (I := I) (x := x) hz_chart
  have hφ_diffWithin : MDifferentiableWithinAt I 𝓘(Real, E) φ φ.source z :=
    hφ_diff.mdifferentiableWithinAt
  have hg_mdiffWithin : MDifferentiableWithinAt 𝓘(Real, E) 𝓘(Real, Real) g s (φ z) :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hg_diffWithin
  have h_maps : φ.source ⊆ φ ⁻¹' s := fun w hw =>
    extChartAt_target_subset_range (I := I) x (φ.map_source hw)
  have hUniq : UniqueMDiffWithinAt I φ.source z :=
    hφ_open.uniqueMDiffWithinAt hz
  have hchain := mfderivWithin_comp z hg_mdiffWithin hφ_diffWithin h_maps hUniq
  rw [mfderivWithin_eq_mfderiv hUniq hφ_diff] at hchain
  have hgφ_diff : MDifferentiableAt I 𝓘(Real, Real) (g ∘ φ) z := by
    have hcomp : MDifferentiableWithinAt I 𝓘(Real, Real) (g ∘ φ) φ.source z :=
      hg_mdiffWithin.comp z hφ_diffWithin h_maps
    exact hcomp.mdifferentiableAt (hφ_open.mem_nhds hz)
  rw [mfderivWithin_eq_mfderiv hUniq hgφ_diff] at hchain
  rw [mfderivWithin_eq_fderivWithin] at hchain
  exact hchain

theorem vderiv_mlieBracket
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    vderiv (I := I) f (VectorField.mlieBracket I X Y) x =
      vderiv (I := I) (vderiv (I := I) f Y) X x -
        vderiv (I := I) (vderiv (I := I) f X) Y x := by
  change
    mvfderiv (I := I) f x (VectorField.mlieBracket I X Y x) =
      mvfderiv (I := I) (vderiv (I := I) f Y) x (X x) -
        mvfderiv (I := I) (vderiv (I := I) f X) x (Y x)
  let φ := extChartAt I x
  let y₀ : E := φ x
  let s : Set E := Set.range I
  let g : E -> Real := f ∘ φ.symm
  let V' : E -> E := VectorField.mpullbackWithin 𝓘(Real, E) I φ.symm X s
  let W' : E -> E := VectorField.mpullbackWithin 𝓘(Real, E) I φ.symm Y s
  let : NormedAddCommGroup (TangentSpace I x) := by
    change NormedAddCommGroup E
    infer_instance
  let : NormedSpace Real (TangentSpace I x) := by
    change NormedSpace Real E
    infer_instance
  let : ∀ y : E, NormedAddCommGroup (TangentSpace 𝓘(Real, E) y) := fun _ => by
    change NormedAddCommGroup E
    infer_instance
  let : ∀ y : E, Module Real (TangentSpace 𝓘(Real, E) y) := fun _ => by
    change Module Real E
    infer_instance
  let : ∀ y : E, NormedSpace Real (TangentSpace 𝓘(Real, E) y) := fun _ => by
    change NormedSpace Real E
    infer_instance
  let : ∀ r : Real, NormedAddCommGroup (TangentSpace 𝓘(Real, Real) r) := fun _ => by
    change NormedAddCommGroup Real
    infer_instance
  let : ∀ r : Real, Module Real (TangentSpace 𝓘(Real, Real) r) := fun _ => by
    change Module Real Real
    infer_instance
  let : ∀ r : Real, NormedSpace Real (TangentSpace 𝓘(Real, Real) r) := fun _ => by
    change NormedSpace Real Real
    infer_instance
  have hxmem : x ∈ φ.source := mem_extChartAt_source (I := I) x
  have hy₀tgt : y₀ ∈ φ.target := φ.map_source hxmem
  have hy₀s : y₀ ∈ s := extChartAt_target_subset_range (I := I) x hy₀tgt
  have huniq : UniqueDiffOn Real s := I.uniqueDiffOn
  have hy₀closure : y₀ ∈ closure (interior s) := by
    exact I.range_subset_closure_interior hy₀s
  have hmin : (minSmoothness Real 2 : WithTop ℕ∞) = 2 := by
    rw [minSmoothness_of_isRCLikeNormedField]
  have hn_ne_top : (minSmoothness Real 2 : WithTop ℕ∞) ≠ ∞ := by
    rw [hmin]; norm_num
  have hn_ne_zero : (minSmoothness Real 2 : WithTop ℕ∞) ≠ 0 := by
    rw [hmin]; norm_num
  have h_one_add_le :
      (1 : WithTop ℕ∞) + 1 ≤ (minSmoothness Real 2 : WithTop ℕ∞) := by
    rw [hmin]; norm_num
  have h_two_le : minSmoothness Real 2 ≤ (minSmoothness Real 2 : WithTop ℕ∞) := le_rfl
  have mvfderiv_eq :
      ∀ (h : M -> Real), MDifferentiableAt I 𝓘(Real, Real) h x ->
        ∀ v : TangentSpace I x,
          mvfderiv (I := I) h x v =
            fderivWithin Real (h ∘ φ.symm) s y₀ (show E from v) := by
    intro h hh v
    have hh_chart : DifferentiableWithinAt Real (h ∘ φ.symm) s y₀ := by
      have hh_model :=
        (mdifferentiableAt_iff_source_of_mem_source
          (I := I) (I' := 𝓘(Real, Real)) (f := h)
          (x := x) (x' := x) (mem_chart_source H x)).mp hh
      have hh_model' :
          MDifferentiableWithinAt 𝓘(Real, E) 𝓘(Real, Real)
            (h ∘ φ.symm) s y₀ := by
        simpa [φ, s, y₀] using hh_model
      exact hh_model'.differentiableWithinAt
    have hchain :=
      _root_.DifferentialGeometry.mfderiv_eq_fderivWithin_chart_comp_closedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic h x x hxmem hh_chart
    have happ := congrArg (fun L => L v) hchain
    erw [ContinuousLinearMap.comp_apply, mfderiv_extChartAt_self (I := I)] at happ
    have hid :
        (show E from (ContinuousLinearMap.id Real (TangentSpace I x)) v) =
          (show E from v) :=
      congrArg (fun w : TangentSpace I x => (show E from w))
        (ContinuousLinearMap.id_apply (R₁ := Real) v)
    let D := fderivWithin Real (h ∘ (extChartAt I x).symm) (Set.range I)
      ((extChartAt I x) x)
    have hfd := congrArg D hid
    have hscalar := congrArg
      (NormedSpace.fromTangentSpace (𝕜 := Real) (h x)) happ
    have hright := congrArg
      (NormedSpace.fromTangentSpace (𝕜 := Real) (h x)) hfd
    have hresult := hscalar.trans hright
    have hfrom :
        NormedSpace.fromTangentSpace (𝕜 := Real) (h x)
            (show TangentSpace 𝓘(Real, Real) (h x) from D (show E from v)) =
          D (show E from v) := by
      rfl
    have hfinal := hresult.trans hfrom
    simpa [mvfderiv, D, φ, s, y₀] using hfinal
  have hf_diff : MDifferentiableAt I 𝓘(Real, Real) f x :=
    hf.mdifferentiableAt hn_ne_zero
  rw [mvfderiv_eq f hf_diff]
  have bracket_eq :
      (VectorField.mlieBracket I X Y x : E) =
        VectorField.lieBracketWithin (E := E) Real V' W' s y₀ := by
    have h1 : VectorField.mlieBracket I X Y x =
        (mfderiv I 𝓘(Real, E) φ x).inverse
          (VectorField.lieBracketWithin (E := E) Real V' W'
            (φ.symm ⁻¹' Set.univ ∩ s) y₀) := by
      exact (VectorField.mlieBracketWithin_apply (I := I)
        (V := X) (W := Y) (s := Set.univ) (x₀ := x))
    rw [h1]
    apply (isInvertible_mfderiv_extChartAt (I := I) hxmem).inverse_apply_eq.mpr
    rw [mfderiv_extChartAt_self (I := I)]
    erw [ContinuousLinearMap.id_apply (R₁ := Real)]
    simp only [Set.preimage_univ, Set.univ_inter]
    rfl
  rw [bracket_eq]
  have hV'_y₀ : V' y₀ = X x := by
    simp only [V', VectorField.mpullbackWithin_apply, y₀]
    rw [φ.left_inv hxmem]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x) (X x)
  have hW'_y₀ : W' y₀ = Y x := by
    simp only [W', VectorField.mpullbackWithin_apply, y₀]
    rw [φ.left_inv hxmem]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x) (Y x)
  have hg_smooth : ContDiffWithinAt Real (minSmoothness Real 2) g s y₀ := by
    have hg_model := (contMDiffAt_iff.mp hf).2
    rw [extChartAt_self_eq] at hg_model
    simpa [g, s, φ, y₀] using hg_model
  have hX_mdiff : MDifferentiableWithinAt I (I.prod 𝓘(Real, E))
      (fun x => (X x : TangentBundle I M)) Set.univ x := by
    exact (hX.mdifferentiableAt hn_ne_zero).mdifferentiableWithinAt
  have hY_mdiff : MDifferentiableWithinAt I (I.prod 𝓘(Real, E))
      (fun x => (Y x : TangentBundle I M)) Set.univ x := by
    exact (hY.mdifferentiableAt hn_ne_zero).mdifferentiableWithinAt
  have hV'_diff : DifferentiableWithinAt Real V' s y₀ := by
    have h := hX_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simpa [V', s, y₀] using! h
  have hW'_diff : DifferentiableWithinAt Real W' s y₀ := by
    have h := hY_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simpa [W', s, y₀] using! h
  have hg_event :
      ∀ᶠ y in 𝓝[s] y₀,
        ContDiffWithinAt Real (minSmoothness Real 2) g s y := by
    simpa only [Set.insert_eq_of_mem hy₀s] using hg_smooth.eventually hn_ne_top
  have mfderiv_fderivWithin_chain :
      ∀ z ∈ φ.source, DifferentiableWithinAt Real g s (φ z) ->
        mfderiv I 𝓘(Real, Real) f z =
          (fderivWithin Real g s (φ z)).comp (mfderiv I 𝓘(Real, E) φ z) :=
    fun z hz hg_diffWithin =>
      _root_.DifferentialGeometry.mfderiv_eq_fderivWithin_chart_comp_closedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic f x z hz hg_diffWithin
  have pull_eq : ∀ (Z : (p : M) -> TangentSpace I p), ∀ y ∈ φ.target,
      VectorField.mpullbackWithin 𝓘(Real, E) I φ.symm Z s y =
        mfderiv I 𝓘(Real, E) φ (φ.symm y) (Z (φ.symm y)) := by
    intro Z y hy
    simp only [VectorField.mpullbackWithin_apply]
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  have hZf_eq : ∀ Z : (p : M) -> TangentSpace I p,
      ((fun p : M => mvfderiv (I := I) f p (Z p)) ∘ φ.symm)
        =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y
          (VectorField.mpullbackWithin 𝓘(Real, E) I φ.symm Z s y)) := by
    intro Z
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy₀tgt,
      hg_event] with y hy hgy
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have hgy_diff :
        DifferentiableWithinAt Real g s (φ (φ.symm y)) := by
      simpa [φ.right_inv hy] using hgy.differentiableWithinAt hn_ne_zero
    have h1 := mfderiv_fderivWithin_chain (φ.symm y) hy_src hgy_diff
    have h2raw := congrArg (fun L => L (Z (φ.symm y))) h1
    erw [ContinuousLinearMap.comp_apply] at h2raw
    have h2 : mvfderiv (I := I) f (φ.symm y) (Z (φ.symm y)) =
        fderivWithin Real g s (φ (φ.symm y))
          (mfderiv I 𝓘(Real, E) φ (φ.symm y) (Z (φ.symm y))) := by
      simpa [mvfderiv, NormedSpace.fromTangentSpace] using! h2raw
    simp only [Function.comp_def]
    rw [h2, φ.right_inv hy]
    congr 1
    exact (pull_eq Z y hy).symm
  have hYf_eq_v : ((vderiv (I := I) f Y) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (W' y)) := hZf_eq Y
  have hXf_eq_v : ((vderiv (I := I) f X) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (V' y)) := hZf_eq X
  have hfd_diff : DifferentiableWithinAt Real (fderivWithin Real g s) s y₀ :=
    (hg_smooth.fderivWithin_right huniq h_one_add_le hy₀s).differentiableWithinAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hmodelY_diff :
      DifferentiableWithinAt Real (fun y => fderivWithin Real g s y (W' y)) s y₀ :=
    hfd_diff.clm_apply hW'_diff
  have hmodelX_diff :
      DifferentiableWithinAt Real (fun y => fderivWithin Real g s y (V' y)) s y₀ :=
    hfd_diff.clm_apply hV'_diff
  have hYf_chart_diff :
      DifferentiableWithinAt Real
        ((vderiv (I := I) f Y) ∘ φ.symm)
        s y₀ :=
    (hYf_eq_v.differentiableWithinAt_iff_of_mem hy₀s).mpr hmodelY_diff
  have hXf_chart_diff :
      DifferentiableWithinAt Real
        ((vderiv (I := I) f X) ∘ φ.symm)
        s y₀ :=
    (hXf_eq_v.differentiableWithinAt_iff_of_mem hy₀s).mpr hmodelX_diff
  have hZf_diff : ∀ Z : (p : M) -> TangentSpace I p,
      DifferentiableWithinAt Real ((vderiv (I := I) f Z) ∘ φ.symm) s y₀ ->
      MDifferentiableAt I 𝓘(Real, Real) (vderiv (I := I) f Z) x := by
    intro Z hZ
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(Real, Real))
      (x := x) (x' := x) (mem_chart_source H x)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa only [writtenInExtChartAt, extChartAt, φ, y₀, s, Function.comp_def]
      using hZ
  have hYf_diff : MDifferentiableAt I 𝓘(Real, Real)
      (vderiv (I := I) f Y) x := hZf_diff Y hYf_chart_diff
  have hXf_diff : MDifferentiableAt I 𝓘(Real, Real)
      (vderiv (I := I) f X) x := hZf_diff X hXf_chart_diff
  rw [mvfderiv_eq _ hYf_diff, mvfderiv_eq _ hXf_diff]
  have hYf_fd :
      fderivWithin Real
          ((vderiv (I := I) f Y) ∘ φ.symm)
          s y₀ =
        fderivWithin Real (fun y => fderivWithin Real g s y (W' y)) s y₀ :=
    hYf_eq_v.fderivWithin_eq (hYf_eq_v.self_of_nhdsWithin hy₀s)
  have hXf_fd :
      fderivWithin Real
          ((vderiv (I := I) f X) ∘ φ.symm)
          s y₀ =
        fderivWithin Real (fun y => fderivWithin Real g s y (V' y)) s y₀ :=
    hXf_eq_v.fderivWithin_eq (hXf_eq_v.self_of_nhdsWithin hy₀s)
  have hmain := VectorField.fderivWithin_apply_lieBracket hg_smooth h_two_le huniq
    hy₀closure hy₀s hW'_diff hV'_diff
  rw [hV'_y₀, hW'_y₀] at hmain
  rw [hYf_fd, hXf_fd]
  exact hmain

theorem mvfderiv_apply_contMDiffAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M -> 𝕜} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(𝕜, 𝕜) ∞ f x₀)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun p : M => mvfderiv (I := I) f p (X p)) x₀ := by
  rw [contMDiffAt_infty]
  intro n
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt 𝕜 p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(𝕜, E) (n : WithTop ℕ∞) Xcoord x₀ := by
    have hXTop :
        ContMDiffAt I 𝓘(𝕜, E) ∞
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := fun p : M => X p)
          (x₀ := x₀)
          (by
            simp [e])).mp
          (X.contMDiff.contMDiffAt)
    refine (hXTop.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
    have hcoe : ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hp
    simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(𝕜, 𝕜) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.comp (x₀, x₀) contMDiffAt_snd).of_le
      (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(𝕜, 𝕜))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (n : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
  have hp_src : p ∈ (chartAt H x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : f p ∈ (chartAt 𝕜 (f x₀)).source := by
    rw [chartAt_self_eq]
    exact Set.mem_univ _
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(𝕜, 𝕜))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(𝕜, 𝕜) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(𝕜, 𝕜) 𝕜).coordChange
        (achart 𝕜 (f p)) (achart 𝕜 (f x₀)) (f p) = (1 : 𝕜 →L[𝕜] 𝕜) := by
    simp
  have hsource :=
    (TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := 𝕜) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL 𝕜 p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := 𝕜) hp (X p)
  rw [htarget]
  erw [hsource]
  change (mfderiv I 𝓘(𝕜, 𝕜) f p) (X p) =
    (mfderiv I 𝓘(𝕜, 𝕜) f p) (e.symmL 𝕜 p (Xcoord p))
  rw [hcancel]

end DifferentialGeometry
