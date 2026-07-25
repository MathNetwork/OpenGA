import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.VectorField







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry






noncomputable abbrev vderiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) : M -> 𝕜 :=
  fun x => extDerivFun (I := I) f x (X x)

@[simp] theorem vderiv_apply
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (f : M -> 𝕜) (X : (x : M) -> TangentSpace I x) (x : M) :
    vderiv (I := I) f X x = extDerivFun (I := I) f x (X x) := by
  rfl







set_option maxHeartbeats 250000 in
set_option backward.isDefEq.respectTransparency false in
theorem vderiv_mlieBracket
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    vderiv (I := I) f (VectorField.mlieBracket I X Y) x =
      vderiv (I := I) (vderiv (I := I) f Y) X x -
        vderiv (I := I) (vderiv (I := I) f X) Y x := by
  simp only [vderiv, extDerivFun, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk]
  let φ := extChartAt I x
  let y₀ : E := φ x
  let s : Set E := Set.range I
  let g : E -> Real := f ∘ φ.symm
  let V' : E -> E := VectorField.mpullbackWithin 𝓘(Real, E) I φ.symm X s
  let W' : E -> E := VectorField.mpullbackWithin 𝓘(Real, E) I φ.symm Y s
  letI : NormedAddCommGroup (TangentSpace I x) := by
    change NormedAddCommGroup E
    infer_instance
  letI : NormedSpace Real (TangentSpace I x) := by
    change NormedSpace Real E
    infer_instance
  letI : NormedAddCommGroup (TangentSpace 𝓘(Real, E) y₀) := by
    change NormedAddCommGroup E
    infer_instance
  letI : NormedSpace Real (TangentSpace 𝓘(Real, E) y₀) := by
    change NormedSpace Real E
    infer_instance
  have hxmem : x ∈ φ.source := by
    simp [φ]
  have hy₀tgt : y₀ ∈ φ.target := by
    simpa [y₀] using φ.map_source hxmem
  have hy₀s : y₀ ∈ s := by
    simp [s, φ, y₀]
  have huniq : UniqueDiffOn Real s := by
    simpa [s] using I.uniqueDiffOn
  have hy₀closure : y₀ ∈ closure (interior s) := by
    exact I.range_subset_closure_interior (by simpa [s] using hy₀s)
  have hn_ne_top : (minSmoothness Real 2 : WithTop ℕ∞) ≠ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  have hn_ne_zero : (minSmoothness Real 2 : WithTop ℕ∞) ≠ 0 := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  have h_one_add_le :
      (1 : WithTop ℕ∞) + 1 ≤ (minSmoothness Real 2 : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  have h_two_le : minSmoothness Real 2 ≤ (minSmoothness Real 2 : WithTop ℕ∞) := le_rfl
  have mfderiv_eq :
      ∀ (h : M -> Real), MDifferentiableAt I 𝓘(Real, Real) h x ->
        mfderiv I 𝓘(Real, Real) h x =
          fderivWithin Real (h ∘ φ.symm) s y₀ := by
    intro h hh
    simp only [mfderiv, if_pos hh]
    congr 1
  have hf_diff : MDifferentiableAt I 𝓘(Real, Real) f x :=
    hf.mdifferentiableAt hn_ne_zero
  rw [mfderiv_eq f hf_diff]
  have bracket_eq :
      VectorField.mlieBracket I X Y x =
        VectorField.lieBracketWithin Real V' W' s y₀ := by
    have h1 : VectorField.mlieBracket I X Y x =
        (mfderiv I 𝓘(Real, E) φ x).inverse
          (VectorField.lieBracketWithin Real V' W'
            (φ.symm ⁻¹' Set.univ ∩ s) y₀) := by
      exact (VectorField.mlieBracketWithin_apply (I := I)
        (V := X) (W := Y) (s := Set.univ) (x₀ := x))
    rw [h1, mfderiv_extChartAt_self (I := I)]
    erw [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]
    simp only [Set.preimage_univ, Set.univ_inter]
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
    simpa [g, s, φ, y₀] using (contMDiffAt_iff.mp hf).2
  have hX_mdiff : MDifferentiableWithinAt I (I.prod 𝓘(Real, E))
      (fun x => (X x : TangentBundle I M)) Set.univ x := by
    exact (hX.mdifferentiableAt hn_ne_zero).mdifferentiableWithinAt
  have hY_mdiff : MDifferentiableWithinAt I (I.prod 𝓘(Real, E))
      (fun x => (Y x : TangentBundle I M)) Set.univ x := by
    exact (hY.mdifferentiableAt hn_ne_zero).mdifferentiableWithinAt
  have hV'_diff : DifferentiableWithinAt Real V' s y₀ := by
    have h := hX_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simpa [V', s, y₀] using h
  have hW'_diff : DifferentiableWithinAt Real W' s y₀ := by
    have h := hY_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simpa [W', s, y₀] using h
  have hg_event :
      ∀ᶠ y in 𝓝[s] y₀,
        ContDiffWithinAt Real (minSmoothness Real 2) g s y := by
    simpa [Set.insert_eq_of_mem hy₀s] using hg_smooth.eventually hn_ne_top
  have mfderiv_fderivWithin_chain :
      ∀ z ∈ φ.source, DifferentiableWithinAt Real g s (φ z) ->
        mfderiv I 𝓘(Real, Real) f z =
          (fderivWithin Real g s (φ z)).comp (mfderiv I 𝓘(Real, E) φ z) := by
    intro z hz hg_diffWithin
    have hφ_open : IsOpen φ.source := by
      simpa [φ] using isOpen_extChartAt_source (I := I) x
    have hz_chart : z ∈ (chartAt H x).source := by
      simpa [φ, extChartAt_source] using hz
    have hφz_tgt : φ z ∈ φ.target := φ.map_source hz
    have hf_eq : f =ᶠ[𝓝 z] g ∘ φ := by
      filter_upwards [hφ_open.mem_nhds hz] with w hw
      simp [g, φ.left_inv hw]
    rw [hf_eq.mfderiv_eq]
    have hφ_diff : MDifferentiableAt I 𝓘(Real, E) φ z := by
      simpa [φ] using mdifferentiableAt_extChartAt (I := I) (x := x) hz_chart
    have hφ_diffWithin : MDifferentiableWithinAt I 𝓘(Real, E) φ φ.source z :=
      hφ_diff.mdifferentiableWithinAt
    have hg_mdiffWithin : MDifferentiableWithinAt 𝓘(Real, E) 𝓘(Real, Real) g s (φ z) :=
      mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hg_diffWithin
    have h_maps : φ.source ⊆ φ ⁻¹' s := fun w hw =>
      extChartAt_target_subset_range (I := I) x (by simpa [φ] using φ.map_source hw)
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
  have W'_eq : ∀ y ∈ φ.target,
      W' y = mfderiv I 𝓘(Real, E) φ (φ.symm y) (Y (φ.symm y)) := by
    intro y hy
    simp only [W', VectorField.mpullbackWithin_apply]
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  have V'_eq : ∀ y ∈ φ.target,
      V' y = mfderiv I 𝓘(Real, E) φ (φ.symm y) (X (φ.symm y)) := by
    intro y hy
    simp only [V', VectorField.mpullbackWithin_apply]
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  have hYf_eq : ((fun p : M => mfderiv I 𝓘(Real, Real) f p (Y p)) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (W' y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy₀tgt,
      hg_event] with y hy hgy
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have hgy_diff :
        DifferentiableWithinAt Real g s (φ (φ.symm y)) := by
      simpa [φ.right_inv hy] using hgy.differentiableWithinAt hn_ne_zero
    have h1 := mfderiv_fderivWithin_chain (φ.symm y) hy_src hgy_diff
    have h2 : mfderiv I 𝓘(Real, Real) f (φ.symm y) (Y (φ.symm y)) =
        fderivWithin Real g s (φ (φ.symm y))
          (mfderiv I 𝓘(Real, E) φ (φ.symm y) (Y (φ.symm y))) := by
      rw [h1]
      rfl
    simp only [Function.comp_def]
    rw [h2, φ.right_inv hy]
    congr 1
    exact (W'_eq y hy).symm
  have hXf_eq : ((fun p : M => mfderiv I 𝓘(Real, Real) f p (X p)) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (V' y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy₀tgt,
      hg_event] with y hy hgy
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    have hgy_diff :
        DifferentiableWithinAt Real g s (φ (φ.symm y)) := by
      simpa [φ.right_inv hy] using hgy.differentiableWithinAt hn_ne_zero
    have h1 := mfderiv_fderivWithin_chain (φ.symm y) hy_src hgy_diff
    have h2 : mfderiv I 𝓘(Real, Real) f (φ.symm y) (X (φ.symm y)) =
        fderivWithin Real g s (φ (φ.symm y))
          (mfderiv I 𝓘(Real, E) φ (φ.symm y) (X (φ.symm y))) := by
      rw [h1]
      rfl
    simp only [Function.comp_def]
    rw [h2, φ.right_inv hy]
    congr 1
    exact (V'_eq y hy).symm
  have hYf_eq_v : ((vderiv (I := I) f Y) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (W' y)) := by
    filter_upwards [hYf_eq] with y hy
    simpa [vderiv, extDerivFun, NormedSpace.fromTangentSpace] using hy
  have hXf_eq_v : ((vderiv (I := I) f X) ∘ φ.symm)
      =ᶠ[𝓝[s] y₀] (fun y => fderivWithin Real g s y (V' y)) := by
    filter_upwards [hXf_eq] with y hy
    simpa [vderiv, extDerivFun, NormedSpace.fromTangentSpace] using hy
  have hmodelY_diff :
      DifferentiableWithinAt Real (fun y => fderivWithin Real g s y (W' y)) s y₀ := by
    have hderiv :
        DifferentiableWithinAt Real (fderivWithin Real g s) s y₀ := by
      exact (hg_smooth.fderivWithin_right huniq h_one_add_le hy₀s).differentiableWithinAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact hderiv.clm_apply hW'_diff
  have hmodelX_diff :
      DifferentiableWithinAt Real (fun y => fderivWithin Real g s y (V' y)) s y₀ := by
    have hderiv :
        DifferentiableWithinAt Real (fderivWithin Real g s) s y₀ := by
      exact (hg_smooth.fderivWithin_right huniq h_one_add_le hy₀s).differentiableWithinAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    exact hderiv.clm_apply hV'_diff
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
  have hYf_diff : MDifferentiableAt I 𝓘(Real, Real)
      (vderiv (I := I) f Y) x := by
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(Real, Real))
      (x := x) (x' := x) (mem_chart_source H x)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa [writtenInExtChartAt, extChartAt, φ, y₀, s, Function.comp_def]
      using hYf_chart_diff
  have hXf_diff : MDifferentiableAt I 𝓘(Real, Real)
      (vderiv (I := I) f X) x := by
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(Real, Real))
      (x := x) (x' := x) (mem_chart_source H x)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa [writtenInExtChartAt, extChartAt, φ, y₀, s, Function.comp_def]
      using hXf_chart_diff
  rw [mfderiv_eq _ hYf_diff, mfderiv_eq _ hXf_diff]
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
  rw [hYf_fd, hXf_fd, ← hV'_y₀, ← hW'_y₀]
  exact VectorField.fderivWithin_apply_lieBracket hg_smooth h_two_le huniq
    hy₀closure hy₀s hW'_diff hV'_diff


theorem extDerivFun_apply_mlieBracket
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    (X Y : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2) (T% Y) x)
    (hf : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x) :
    extDerivFun (I := I) f x (VectorField.mlieBracket I X Y x) =
      extDerivFun (I := I)
          (fun y : M => extDerivFun (I := I) f y (Y y)) x (X x) -
        extDerivFun (I := I)
          (fun y : M => extDerivFun (I := I) f y (X y)) x (Y x) := by
  exact vderiv_mlieBracket (I := I) X Y f x hX hY hf



theorem contMDiff_partial_deriv_fst_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (F : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1) := by


  have hrw : (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1) =
      fun p : ℝ × M => (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t => F (t, p.2)) p.1) (1 : ℝ) := by
    funext p
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := fun t => F (t, p.2)) (x := p.1)).symm
  rw [hrw]

  rw [contMDiff_infty]
  intro n p₀

  have harg : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : (ℝ × M) × ℝ => (q.2, q.1.2)) :=
    ContMDiff.prodMk contMDiff_snd contMDiff_fst.snd
  have hF : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : (ℝ × M) × ℝ => F (q.2, q.1.2)) :=
    F.contMDiff.comp harg

  have h_apply :=
    ContMDiffAt.mfderiv_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : ℝ × M) (t : ℝ) => F (t, p.2))
      (g := fun p : ℝ × M => p.1)
      (g₁ := fun p : ℝ × M => p)
      (g₂ := fun _ : ℝ × M => (1 : ℝ))
      (x₀ := p₀)
      (m := (n : WithTop ℕ∞))
      ((hF.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)).contMDiffAt)
      contMDiffAt_fst
      contMDiffAt_id
      contMDiffAt_const
      le_rfl


  simpa [inTangentCoordinates_model_space] using h_apply



theorem timeDeriv_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Real × M -> Real} {p0 : Real × M} {m n : WithTop ℕ∞}
    (hF : ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) n F p0)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) m
      (fun p : Real × M => deriv (fun t => F (t, p.2)) p.1) p0 := by
  have hrw :
      (fun p : Real × M => deriv (fun t => F (t, p.2)) p.1) =
        fun p : Real × M =>
          (mfderiv (modelWithCornersSelf Real Real)
            (modelWithCornersSelf Real Real) (fun t => F (t, p.2)) p.1) (1 : Real) := by
    funext p
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := fun t => F (t, p.2)) (x := p.1)).symm
  rw [hrw]
  have harg :
      ContMDiffAt
        (((modelWithCornersSelf Real Real).prod I).prod
          (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real Real).prod I) n
        (fun q : (Real × M) × Real => (q.2, q.1.2)) (p0, p0.1) :=
    ContMDiffAt.prodMk contMDiffAt_snd contMDiffAt_fst.snd
  have hF' :
      ContMDiffAt
        (((modelWithCornersSelf Real Real).prod I).prod
          (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) n
        (fun q : (Real × M) × Real => F (q.2, q.1.2)) (p0, p0.1) :=
    hF.comp (p0, p0.1) harg
  have h_apply :=
    ContMDiffAt.mfderiv_apply
      (I := modelWithCornersSelf Real Real)
      (I' := modelWithCornersSelf Real Real)
      (f := fun (p : Real × M) (t : Real) => F (t, p.2))
      (g := fun p : Real × M => p.1)
      (g₁ := fun p : Real × M => p)
      (g₂ := fun _ : Real × M => (1 : Real))
      (x₀ := p0) (m := m) (n := n)
      hF' contMDiffAt_fst contMDiffAt_id contMDiffAt_const hmn
  simpa [inTangentCoordinates_model_space] using h_apply






theorem extDerivFun_const_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (c : ℝ) {f : M -> ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    extDerivFun (I := I) (fun y : M => c * f y) x =
      c • extDerivFun (I := I) f x := by
  change extDerivFun (I := I) (c • f) x =
    c • extDerivFun (I := I) f x
  ext v
  have hmul := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := fun _ : M => c) (g := f)
    (by exact mdifferentiableAt_const (c := c)) hf v
  simpa [extDerivFun] using hmul




theorem extDerivFun_mul_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f g : M -> ℝ} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v + g x * extDerivFun (I := I) f x v := by
  have hsmul : (fun y : M => f y * g y) = (f • g) := by
    funext y; simp [smul_eq_mul]
  rw [hsmul]
  have hmul := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  rw [show extDerivFun (I := I) (f • g) x v =
        f x * extDerivFun (I := I) g x v + extDerivFun (I := I) f x v * g x from by
      simpa [extDerivFun, smul_eq_mul] using hmul]
  ring




theorem extDerivFun_finset_sum_mul_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (U B : ι -> M -> ℝ)
    {x : M} (v : TangentSpace I x)
    (hU : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (U i) x)
    (hB : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (B i) x) :
    extDerivFun (I := I) (fun y : M => ∑ i ∈ t, U i y * B i y) x v =
      ∑ i ∈ t,
        (U i x * extDerivFun (I := I) (B i) x v +
          B i x * extDerivFun (I := I) (U i) x v) := by
  classical

  have hsumdiff :
      ∀ (s : Finset ι), (∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (U i) x) →
        (∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (B i) x) →
          MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y : M => ∑ i ∈ s, U i y * B i y) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ _; simpa using mdifferentiableAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (0 : ℝ))
    | insert a s has ih =>
        intro hUs hBs
        have hUa : MDifferentiableAt I 𝓘(ℝ, ℝ) (U a) x := hUs a (by simp)
        have hBa : MDifferentiableAt I 𝓘(ℝ, ℝ) (B a) x := hBs a (by simp)
        have htail := ih (fun i hi => hUs i (by simp [hi])) (fun i hi => hBs i (by simp [hi]))
        have heqfun :
            (fun y : M => ∑ i ∈ insert a s, U i y * B i y) =
              (fun y : M => U a y * B a y) + (fun y : M => ∑ i ∈ s, U i y * B i y) := by
          funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert has]
        rw [heqfun]
        exact (hUa.mul hBa).add htail
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
      have hUa : MDifferentiableAt I 𝓘(ℝ, ℝ) (U a) x := hU a (by simp)
      have hBa : MDifferentiableAt I 𝓘(ℝ, ℝ) (B a) x := hB a (by simp)
      have hUt : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (U i) x :=
        fun i hi => hU i (by simp [hi])
      have hBt : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (B i) x :=
        fun i hi => hB i (by simp [hi])
      have hsplit :
          (fun y : M => ∑ i ∈ insert a t, U i y * B i y) =
            (fun y : M => U a y * B a y) +
              (fun y : M => ∑ i ∈ t, U i y * B i y) := by
        funext y
        simp only [Pi.add_apply]
        rw [Finset.sum_insert hat]
      have hsummand_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y : M => U a y * B a y) x := hUa.mul hBa
      have hsumtail_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y : M => ∑ i ∈ t, U i y * B i y) x :=
        hsumdiff t hUt hBt
      rw [hsplit]
      have hadd := congr($(extDerivFun_add (I := I)
        (g := fun y : M => U a y * B a y)
        (g' := fun y : M => ∑ i ∈ t, U i y * B i y)
        (x := x) hsummand_diff hsumtail_diff) v)
      rw [show (extDerivFun (I := I)
            ((fun y : M => U a y * B a y) +
              fun y : M => ∑ i ∈ t, U i y * B i y) x) v =
          (extDerivFun (I := I) (fun y : M => U a y * B a y) x) v +
            (extDerivFun (I := I) (fun y : M => ∑ i ∈ t, U i y * B i y) x) v from by
        simpa [Pi.add_apply] using hadd]
      rw [extDerivFun_mul_at (I := I) v hUa hBa]
      rw [ih hUt hBt]
      rw [Finset.sum_insert hat]



theorem extDerivFun_finset_sum_at'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type*} (t : Finset ι) (F : ι -> M -> ℝ)
    {x : M} (v : TangentSpace I x)
    (hF : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) x) :
    extDerivFun (I := I) (fun y : M => ∑ i ∈ t, F i y) x v =
      ∑ i ∈ t, extDerivFun (I := I) (F i) x v := by
  classical
  have hsumdiff :
      ∀ (s : Finset ι), (∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) x) →
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => ∑ i ∈ s, F i y) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using mdifferentiableAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (0 : ℝ))
    | insert a s has ih =>
        intro hFs
        have hFa : MDifferentiableAt I 𝓘(ℝ, ℝ) (F a) x := hFs a (by simp)
        have htail := ih (fun i hi => hFs i (by simp [hi]))
        have heqfun :
            (fun y : M => ∑ i ∈ insert a s, F i y) =
              (fun y : M => F a y) + (fun y : M => ∑ i ∈ s, F i y) := by
          funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert has]
        rw [heqfun]
        exact hFa.add htail
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
      have hFa : MDifferentiableAt I 𝓘(ℝ, ℝ) (F a) x := hF a (by simp)
      have hFt : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) x :=
        fun i hi => hF i (by simp [hi])
      have hsplit :
          (fun y : M => ∑ i ∈ insert a t, F i y) =
            (fun y : M => F a y) + (fun y : M => ∑ i ∈ t, F i y) := by
        funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert hat]
      rw [hsplit]
      have hadd := congr($(extDerivFun_add (I := I)
        (g := fun y : M => F a y) (g' := fun y : M => ∑ i ∈ t, F i y)
        (x := x) hFa (hsumdiff t hFt)) v)
      rw [show (extDerivFun (I := I)
            ((fun y : M => F a y) + fun y : M => ∑ i ∈ t, F i y) x) v =
          (extDerivFun (I := I) (fun y : M => F a y) x) v +
            (extDerivFun (I := I) (fun y : M => ∑ i ∈ t, F i y) x) v from by
        simpa [Pi.add_apply] using hadd]
      rw [ih hFt]
      rw [Finset.sum_insert hat]




theorem extDerivFun_finset_sum_sum_mul_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (U B : ι -> κ -> M -> ℝ)
    {x : M} (v : TangentSpace I x)
    (hU : ∀ i ∈ s, ∀ j ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (U i j) x)
    (hB : ∀ i ∈ s, ∀ j ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (B i j) x) :
    extDerivFun (I := I) (fun y : M => ∑ i ∈ s, ∑ j ∈ t, U i j y * B i j y) x v =
      ∑ i ∈ s, ∑ j ∈ t,
        (U i j x * extDerivFun (I := I) (B i j) x v +
          B i j x * extDerivFun (I := I) (U i j) x v) := by
  classical

  have hinner_diff :
      ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun y : M => ∑ j ∈ t, U i j y * B i j y) x := by
    intro i hi
    have haux :
        ∀ (r : Finset κ), (∀ j ∈ r, MDifferentiableAt I 𝓘(ℝ, ℝ) (U i j) x) →
          (∀ j ∈ r, MDifferentiableAt I 𝓘(ℝ, ℝ) (B i j) x) →
            MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => ∑ j ∈ r, U i j y * B i j y) x := by
      intro r
      induction r using Finset.induction_on with
      | empty => intro _ _; simpa using mdifferentiableAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (0 : ℝ))
      | insert a r har ih =>
          intro hUr hBr
          have hUa := hUr a (by simp)
          have hBa := hBr a (by simp)
          have htail := ih (fun j hj => hUr j (by simp [hj])) (fun j hj => hBr j (by simp [hj]))
          have heqfun :
              (fun y : M => ∑ j ∈ insert a r, U i j y * B i j y) =
                (fun y : M => U i a y * B i a y) +
                  (fun y : M => ∑ j ∈ r, U i j y * B i j y) := by
            funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert har]
          rw [heqfun]
          exact (hUa.mul hBa).add htail
    exact haux t (fun j hj => hU i hi j hj) (fun j hj => hB i hi j hj)
  rw [extDerivFun_finset_sum_at' (I := I) s
    (fun i => fun y : M => ∑ j ∈ t, U i j y * B i j y) v hinner_diff]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [extDerivFun_finset_sum_mul_at (I := I) t (fun j => U i j) (fun j => B i j) v
    (fun j hj => hU i hi j hj) (fun j hj => hB i hi j hj)]





theorem extDerivFun_apply_contMDiff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : M -> 𝕜) (hf : ContMDiff I 𝓘(𝕜, 𝕜) ∞ f)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiff I 𝓘(𝕜, 𝕜) ∞
      (fun p : M => extDerivFun (I := I) f p (X p)) := by
  rw [contMDiff_infty]
  intro n x₀
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
    · filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
      have hcoe : ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
        e.coe_linearMapAt_of_mem (R := 𝕜) hp
      simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(𝕜, 𝕜) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.contMDiffAt.comp (x₀, x₀) contMDiffAt_snd).of_le
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
  · filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with p hp
    have hp_src : p ∈ (chartAt H x₀).source := by
      simpa [e, TangentBundle.trivializationAt_baseSet] using hp
    have hf_src : f p ∈ (chartAt 𝕜 (f x₀)).source := by
      simp
    rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(𝕜, 𝕜))
      (f := fun p : M => p) (g := f)
      (ϕ := fun p : M => mfderiv I 𝓘(𝕜, 𝕜) f p)
      hp_src hf_src]
    have htarget :
        (tangentBundleCore 𝓘(𝕜, 𝕜) 𝕜).coordChange
          (achart 𝕜 (f p)) (achart 𝕜 (f x₀)) (f p) = (1 : 𝕜 →L[𝕜] 𝕜) := by
      simp
    have hsource :
        (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
          e.symmL 𝕜 p := by
      simpa [e] using
        (TangentBundle.symmL_trivializationAt_eq_core
          (𝕜 := 𝕜) (I := I) (b₀ := x₀) (b := p) hp_src).symm
    have hcancel :
        e.symmL 𝕜 p (Xcoord p) = X p := by
      exact e.symmL_continuousLinearMapAt (R := 𝕜) hp (X p)
    rw [htarget, hsource]
    change (mfderiv I 𝓘(𝕜, 𝕜) f p) (X p) =
      (mfderiv I 𝓘(𝕜, 𝕜) f p) (e.symmL 𝕜 p (Xcoord p))
    rw [hcancel]





theorem extDerivFun_apply_contMDiffAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M -> 𝕜} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(𝕜, 𝕜) ∞ f x₀)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M -> Type _)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) ∞
      (fun p : M => extDerivFun (I := I) f p (X p)) x₀ := by
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
    simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(𝕜, 𝕜))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(𝕜, 𝕜) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(𝕜, 𝕜) 𝕜).coordChange
        (achart 𝕜 (f p)) (achart 𝕜 (f x₀)) (f p) = (1 : 𝕜 →L[𝕜] 𝕜) := by
    simp
  have hsource :
      (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
        e.symmL 𝕜 p := by
    simpa [e] using
      (TangentBundle.symmL_trivializationAt_eq_core
        (𝕜 := 𝕜) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL 𝕜 p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := 𝕜) hp (X p)
  rw [htarget, hsource]
  change (mfderiv I 𝓘(𝕜, 𝕜) f p) (X p) =
    (mfderiv I 𝓘(𝕜, 𝕜) f p) (e.symmL 𝕜 p (Xcoord p))
  rw [hcancel]






theorem prodExtDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Real × M -> Real} {X : (x : M) -> TangentSpace I x}
    {t : Real} {x : M}
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (3 : WithTop ℕ∞) F (t, x))
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E))
      (∞ : WithTop ℕ∞) (T% X) x) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun p : Real × M =>
        extDerivFun (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2))
      (t, x) := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x
  let XcoordM : M -> E := fun y => e.continuousLinearMapAt Real y (X y)
  let Xcoord : Real × M -> E := fun p => XcoordM p.2
  have hXcoordM :
      ContMDiffAt I 𝓘(Real, E) (2 : WithTop ℕ∞) XcoordM x := by
    have hXTopInf :
        ContMDiffAt I 𝓘(Real, E) (∞ : WithTop ℕ∞)
          (fun y : M => (e ⟨y, X y⟩).2) x := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := fun y : M => X y)
          (x₀ := x)
          (by
            simp [e])).mp hX
    have hXTop :
        ContMDiffAt I 𝓘(Real, E) (2 : WithTop ℕ∞)
          (fun y : M => (e ⟨y, X y⟩).2) x :=
      hXTopInf.of_le
        (by exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    refine hXTop.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with y hy
    have hcoe : ⇑(e.linearMapAt Real y) = fun z => (e ⟨y, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := Real) hy
    simp [XcoordM, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hXcoord :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, E)
        (2 : WithTop ℕ∞) Xcoord (t, x) := by
    exact hXcoordM.comp (t, x)
      (contMDiffAt_snd (I := 𝓘(Real, Real)) (J := I) (p := (t, x)))
  have harg :
      ContMDiffAt ((𝓘(Real, Real).prod I).prod I)
        (𝓘(Real, Real).prod I) (3 : WithTop ℕ∞)
        (fun q : (Real × M) × M => (q.1.1, q.2)) ((t, x), x) := by
    exact contMDiffAt_fst.fst.prodMk contMDiffAt_snd
  have hFprod :
      ContMDiffAt ((𝓘(Real, Real).prod I).prod I) 𝓘(Real, Real)
        (3 : WithTop ℕ∞)
        (fun q : (Real × M) × M => F (q.1.1, q.2)) ((t, x), x) :=
    hF.comp ((t, x), x) harg
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(Real, Real))
      (f := fun (p : Real × M) (y : M) => F (p.1, y))
      (g := fun p : Real × M => p.2)
      (g₁ := fun p : Real × M => p)
      (g₂ := Xcoord)
      (x₀ := (t, x))
      (m := (2 : WithTop ℕ∞))
      hFprod
      contMDiffAt_snd
      contMDiffAt_id
      hXcoord
      le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  have hbase :
      {p : Real × M | p.2 ∈ e.baseSet} ∈ 𝓝 (t, x) := by
    exact (continuous_snd.tendsto (t, x)).eventually
      (e.open_baseSet.mem_nhds (by simp [e]))
  filter_upwards [hbase] with p hp
  have hp_src : p.2 ∈ (chartAt H x).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : F (p.1, p.2) ∈ (chartAt Real (F (t, x))).source := by
    simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(Real, Real))
    (f := fun p : Real × M => p.2) (g := fun p : Real × M => F (p.1, p.2))
    (ϕ := fun p : Real × M =>
      mfderiv I 𝓘(Real, Real) (fun y : M => F (p.1, y)) p.2)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(Real, Real) Real).coordChange
        (achart Real (F (p.1, p.2))) (achart Real (F (t, x))) (F (p.1, p.2)) =
          (1 : Real →L[Real] Real) := by
    simp
  have hsource :
      (tangentBundleCore I M).coordChange (achart H x) (achart H p.2) p.2 =
        e.symmL Real p.2 := by
    simpa [e] using
      (TangentBundle.symmL_trivializationAt_eq_core
        (𝕜 := Real) (I := I) (b₀ := x) (b := p.2) hp_src).symm
  have hcancel :
      e.symmL Real p.2 (Xcoord p) = X p.2 := by
    exact e.symmL_continuousLinearMapAt (R := Real) hp (X p.2)
  rw [htarget, hsource]
  change
    (mfderiv I 𝓘(Real, Real) (fun y : M => F (p.1, y)) p.2) (X p.2) =
      (mfderiv I 𝓘(Real, Real) (fun y : M => F (p.1, y)) p.2)
        (e.symmL Real p.2 (Xcoord p))
  rw [hcancel]



theorem prodExtDerivAt_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Real × M -> Real} {X : (x : M) -> TangentSpace I x}
    {t : Real} {x : M} {m : WithTop ℕ∞} (hm : m ≤ (∞ : WithTop ℕ∞))
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (m + 1) F (t, x))
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E))
      (∞ : WithTop ℕ∞) (T% X) x) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) m
      (fun p : Real × M =>
        extDerivFun (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2))
      (t, x) := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x
  let XcoordM : M -> E := fun y => e.continuousLinearMapAt Real y (X y)
  let Xcoord : Real × M -> E := fun p => XcoordM p.2
  have hXcoordM :
      ContMDiffAt I 𝓘(Real, E) m XcoordM x := by
    have hXTopInf :
        ContMDiffAt I 𝓘(Real, E) (∞ : WithTop ℕ∞)
          (fun y : M => (e ⟨y, X y⟩).2) x := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := fun y : M => X y)
          (x₀ := x)
          (by
            simp [e])).mp hX
    have hXTop :
        ContMDiffAt I 𝓘(Real, E) m
          (fun y : M => (e ⟨y, X y⟩).2) x :=
      hXTopInf.of_le hm
    refine hXTop.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by
        simp [e])] with y hy
    have hcoe : ⇑(e.linearMapAt Real y) = fun z => (e ⟨y, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := Real) hy
    simp [XcoordM, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hXcoord :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, E) m Xcoord (t, x) := by
    exact hXcoordM.comp (t, x)
      (contMDiffAt_snd (I := 𝓘(Real, Real)) (J := I) (p := (t, x)))
  have harg :
      ContMDiffAt ((𝓘(Real, Real).prod I).prod I)
        (𝓘(Real, Real).prod I) (m + 1)
        (fun q : (Real × M) × M => (q.1.1, q.2)) ((t, x), x) := by
    exact contMDiffAt_fst.fst.prodMk contMDiffAt_snd
  have hFprod :
      ContMDiffAt ((𝓘(Real, Real).prod I).prod I) 𝓘(Real, Real)
        (m + 1)
        (fun q : (Real × M) × M => F (q.1.1, q.2)) ((t, x), x) :=
    hF.comp ((t, x), x) harg
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(Real, Real))
      (f := fun (p : Real × M) (y : M) => F (p.1, y))
      (g := fun p : Real × M => p.2)
      (g₁ := fun p : Real × M => p)
      (g₂ := Xcoord)
      (x₀ := (t, x))
      (m := m)
      hFprod
      contMDiffAt_snd
      contMDiffAt_id
      hXcoord
      le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  have hbase :
      {p : Real × M | p.2 ∈ e.baseSet} ∈ 𝓝 (t, x) := by
    exact (continuous_snd.tendsto (t, x)).eventually
      (e.open_baseSet.mem_nhds (by simp [e]))
  filter_upwards [hbase] with p hp
  have hp_src : p.2 ∈ (chartAt H x).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : F (p.1, p.2) ∈ (chartAt Real (F (t, x))).source := by
    simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(Real, Real))
    (f := fun p : Real × M => p.2) (g := fun p : Real × M => F (p.1, p.2))
    (ϕ := fun p : Real × M =>
      mfderiv I 𝓘(Real, Real) (fun y : M => F (p.1, y)) p.2)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(Real, Real) Real).coordChange
        (achart Real (F (p.1, p.2))) (achart Real (F (t, x))) (F (p.1, p.2)) =
          (1 : Real →L[Real] Real) := by
    simp
  have hsource :
      (tangentBundleCore I M).coordChange (achart H x) (achart H p.2) p.2 =
        e.symmL Real p.2 := by
    simpa [e] using
      (TangentBundle.symmL_trivializationAt_eq_core
        (𝕜 := Real) (I := I) (b₀ := x) (b := p.2) hp_src).symm
  have hcancel :
      e.symmL Real p.2 (Xcoord p) = X p.2 := by
    exact e.symmL_continuousLinearMapAt (R := Real) hp (X p.2)
  rw [htarget, hsource]
  change
    (mfderiv I 𝓘(Real, Real) (fun y : M => F (p.1, y)) p.2) (X p.2) =
      (mfderiv I 𝓘(Real, Real) (fun y : M => F (p.1, y)) p.2)
        (e.symmL Real p.2 (Xcoord p))
  rw [hcancel]




theorem prodExtDerivAt_inf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Real × M -> Real} {X : (x : M) -> TangentSpace I x}
    {t : Real} {x : M}
    (hF : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
      (∞ : WithTop ℕ∞) F (t, x))
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E))
      (∞ : WithTop ℕ∞) (T% X) x) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : Real × M =>
        extDerivFun (I := I) (fun y : M => F (p.1, y)) p.2 (X p.2))
      (t, x) := by
  rw [contMDiffAt_infty]
  intro n
  exact prodExtDerivAt_gen (m := (n : WithTop ℕ∞))
    (by exact_mod_cast le_top : ((n : WithTop ℕ∞)) ≤ ∞)
    (hF.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)) hX

end DifferentialGeometry
