import Mathlib.Geometry.Manifold.VectorField.LieBracket
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private lemma mpullbackWithin_extChartAt_symm_eq_chartE_repr_symm
    {x : M} (V : Π y : M, TangentSpace I y) {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) y =
      (chartE_section_repr (I := I) x V ∘ (extChartAt I x).symm) y := by
  classical
  set φ := extChartAt I x with hφ
  have hsymm_src : φ.symm y ∈ φ.source := φ.map_target hy
  have hsymm_chart : φ.symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I) (x := x)]; exact hsymm_src
  have hAB :
      (mfderiv I 𝓘(ℝ, E) φ (φ.symm y)).comp
          (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y) = ContinuousLinearMap.id ℝ _ :=
    mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x) hy
  have hBA :
      (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y).comp
          (mfderiv I 𝓘(ℝ, E) φ (φ.symm y)) = ContinuousLinearMap.id ℝ _ :=
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x) hy
  have hinv_eq :
      (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y).inverse =
        mfderiv I 𝓘(ℝ, E) φ (φ.symm y) :=
    ContinuousLinearMap.inverse_eq hBA hAB
  change (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y).inverse (V (φ.symm y)) =
       chartE_section_repr (I := I) x V (φ.symm y)
  rw [hinv_eq]
  rw [show (chartE_section_repr (I := I) x V (φ.symm y)) =
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ (φ.symm y) (V (φ.symm y))
      from rfl,
      ← TangentBundle.continuousLinearMapAt_trivializationAt
        (𝕜 := ℝ) (I := I) (x₀ := x) (x := φ.symm y) hsymm_chart]
  rfl

omit [FiniteDimensional ℝ E] in
private lemma mpullbackWithin_extChartAt_symm_eventuallyEq_chartE_repr_symm
    {x : M} (V : Π y : M, TangentSpace I y)
    (hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E)) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) =ᶠ[𝓝 (extChartAt I x x)]
      chartE_section_repr (I := I) x V ∘ (extChartAt I x).symm := by
  classical
  have htgt_nhds : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxint) interior_subset
  filter_upwards [htgt_nhds] with y hy
  exact mpullbackWithin_extChartAt_symm_eq_chartE_repr_symm V hy

set_option backward.isDefEq.respectTransparency false in

omit [FiniteDimensional ℝ E] in
theorem mlieBracket_eq_chart_fderiv_diff
    (x : M) (X Y : Π y : M, TangentSpace I y)
    (hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E))
    (_hX : MDiffAt (T% X) x) (_hY : MDiffAt (T% Y) x) :
    VectorField.mlieBracket I X Y x =
      fderiv ℝ (chartE_section_repr (I := I) x Y ∘ (extChartAt I x).symm)
          (extChartAt I x x) (X x)
        - fderiv ℝ (chartE_section_repr (I := I) x X ∘ (extChartAt I x).symm)
            (extChartAt I x x) (Y x) := by
  classical
  set φ := extChartAt I x with hφ
  have hrange_nhds : range I ∈ 𝓝 (extChartAt I x x) := by
    have hsubset : (extChartAt I x).target ⊆ range I := extChartAt_target_subset_range x
    exact Filter.mem_of_superset
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hxint) interior_subset)
      hsubset
  have hmfderiv_self :
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) x = ContinuousLinearMap.id ℝ _ :=
    mfderiv_extChartAt_self (𝕜 := ℝ) (I := I) (x := x)
  have hVE_at :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X (range I) (extChartAt I x x) = X x := by
    rw [VectorField.mpullbackWithin_apply]
    rw [show φ.symm (φ x) = x from extChartAt_to_inv (I := I) (x := x)]
    exact mfderivWithin_extChartAt_symm_inverse_apply (𝕜 := ℝ) (I := I) (x := x) (X x)
  have hWE_at :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm Y (range I) (extChartAt I x x) = Y x := by
    rw [VectorField.mpullbackWithin_apply]
    rw [show φ.symm (φ x) = x from extChartAt_to_inv (I := I) (x := x)]
    exact mfderivWithin_extChartAt_symm_inverse_apply (𝕜 := ℝ) (I := I) (x := x) (Y x)
  have hVE_eq :
      fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X (range I)) (extChartAt I x x) =
        fderiv ℝ (chartE_section_repr (I := I) x X ∘ (extChartAt I x).symm)
          (extChartAt I x x) :=
    Filter.EventuallyEq.fderiv_eq
      (mpullbackWithin_extChartAt_symm_eventuallyEq_chartE_repr_symm (x := x) X hxint)
  have hWE_eq :
      fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm Y (range I)) (extChartAt I x x) =
        fderiv ℝ (chartE_section_repr (I := I) x Y ∘ (extChartAt I x).symm)
          (extChartAt I x x) :=
    Filter.EventuallyEq.fderiv_eq
      (mpullbackWithin_extChartAt_symm_eventuallyEq_chartE_repr_symm (x := x) Y hxint)
  change VectorField.mlieBracketWithin I X Y univ x =
        fderiv ℝ (chartE_section_repr (I := I) x Y ∘ (extChartAt I x).symm)
            (extChartAt I x x) (X x)
          - fderiv ℝ (chartE_section_repr (I := I) x X ∘ (extChartAt I x).symm)
              (extChartAt I x x) (Y x)
  rw [VectorField.mlieBracketWithin_apply]
  rw [Set.preimage_univ, Set.univ_inter]
  rw [VectorField.lieBracketWithin_of_mem_nhds (𝕜 := ℝ) hrange_nhds]
  rw [hmfderiv_self]
  rw [ContinuousLinearMap.inverse_id]
  unfold VectorField.lieBracket
  rw [hVE_at, hWE_at, hVE_eq, hWE_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem mlieBracket_eq_chart_fderiv_diff_general
    (α x : M) (X Y : Π y : M, TangentSpace I y)
    (hx_src : x ∈ (extChartAt I α).source)
    (hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E))
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    VectorField.mlieBracket I X Y x =
      trivFromE (I := I) α x
        (fderiv ℝ (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (X x))
          - fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x (Y x))) := by
  classical
  set φ := extChartAt I α with hφ
  set y₀ : E := φ x with hy₀
  have hxsrc_chart : x ∈ (chartAt H α).source := by
    have := hx_src; rwa [extChartAt_source] at this
  have hxsymm : φ.symm y₀ = x := φ.left_inv hx_src
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have hrange_nhds : range I ∈ 𝓝 y₀ := by
    have hsubset : (extChartAt I α).target ⊆ range I := extChartAt_target_subset_range α
    exact Filter.mem_of_superset
      (Filter.mem_of_superset (hint_open.mem_nhds hx_int) interior_subset)
      hsubset
  have hytarget : y₀ ∈ φ.target := φ.map_source hx_src
  have hsymm_cmd_inf : ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have htgt_nhds : φ.target ∈ 𝓝 y₀ :=
    Filter.mem_of_superset (hint_open.mem_nhds hx_int) interior_subset
  have hsymm_cmd_at_inf : ContMDiffAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm y₀ := by
    have hopen_target_subset : ∃ u ∈ 𝓝 y₀, ∀ z ∈ u, z ∈ φ.target := by
      refine ⟨φ.target, htgt_nhds, fun z hz => hz⟩
    rcases hopen_target_subset with ⟨u, hu_nhds, hu_sub⟩
    have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target y₀ :=
      hsymm_cmd_inf y₀ hytarget
    exact hsymm_within.contMDiffAt htgt_nhds
  have h2le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
    (ENat.LEInfty.out (m := (2 : WithTop ℕ∞)))
  have hsymm_cmd_at : ContMDiffAt 𝓘(ℝ, E) I (2 : WithTop ℕ∞) φ.symm y₀ :=
    hsymm_cmd_at_inf.of_le h2le
  have hX_at : MDiffAt (T% X) (φ.symm y₀) := by rw [hxsymm]; exact hX
  have hY_at : MDiffAt (T% Y) (φ.symm y₀) := by rw [hxsymm]; exact hY
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField (𝕜 := ℝ)]
    infer_instance
  haveI : IsManifold (𝓘(ℝ, E)) (minSmoothness ℝ 2) E := by
    rw [minSmoothness_of_isRCLikeNormedField (𝕜 := ℝ)]
    infer_instance
  have hpb :=
    VectorField.mpullback_mlieBracket
      (𝕜 := ℝ) (I := 𝓘(ℝ, E)) (I' := I)
      (f := φ.symm)
      (V := X) (W := Y) (x₀ := y₀)
      (n := (2 : WithTop ℕ∞))
      hX_at hY_at hsymm_cmd_at
      (by rw [minSmoothness_of_isRCLikeNormedField])
  have hmf_symm_eq_within :
      mfderiv 𝓘(ℝ, E) I φ.symm y₀ = mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y₀ := by
    exact (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, E)) (I' := I) (f := φ.symm)
      (s := range I) (x := y₀) hrange_nhds).symm
  have hinv_eq_mfderiv_φ :
      (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y₀).inverse =
        mfderiv I 𝓘(ℝ, E) φ x := by
    have hAB :
        (mfderiv I 𝓘(ℝ, E) φ (φ.symm y₀)).comp
            (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y₀) = ContinuousLinearMap.id ℝ _ :=
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := α) hytarget
    have hBA :
        (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y₀).comp
            (mfderiv I 𝓘(ℝ, E) φ (φ.symm y₀)) = ContinuousLinearMap.id ℝ _ :=
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := α) hytarget
    have h_eq :
        (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y₀).inverse =
          mfderiv I 𝓘(ℝ, E) φ (φ.symm y₀) :=
      ContinuousLinearMap.inverse_eq hBA hAB
    rw [h_eq, hxsymm]
  have hmfderiv_φ_eq_triv :
      mfderiv I 𝓘(ℝ, E) φ x = trivToE (I := I) α x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt
      (𝕜 := ℝ) (I := I) (x₀ := α) (x := x) hxsrc_chart).symm
  have hinv_eq_trivToE :
      (mfderiv 𝓘(ℝ, E) I φ.symm y₀).inverse = trivToE (I := I) α x := by
    rw [hmf_symm_eq_within, hinv_eq_mfderiv_φ, hmfderiv_φ_eq_triv]
  have hLHS :
      VectorField.mpullback 𝓘(ℝ, E) I φ.symm
          (VectorField.mlieBracket I X Y) y₀ =
        trivToE (I := I) α x (VectorField.mlieBracket I X Y x) := by
    change (mfderiv 𝓘(ℝ, E) I φ.symm y₀).inverse
              (VectorField.mlieBracket I X Y (φ.symm y₀)) = _
    rw [hxsymm, hinv_eq_trivToE]
    rfl
  have hmpb_eq_mpbWithin (V : Π y : M, TangentSpace I y) :
      VectorField.mpullback 𝓘(ℝ, E) I φ.symm V =ᶠ[𝓝 y₀]
        VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm V (range I) := by
    have hint_nhds : interior ((extChartAt I α).target : Set E) ∈ 𝓝 y₀ :=
      hint_open.mem_nhds hx_int
    filter_upwards [hint_nhds] with z hz
    have hz_range : range I ∈ 𝓝 z :=
      Filter.mem_of_superset
        (Filter.mem_of_superset (hint_open.mem_nhds hz) interior_subset)
        (extChartAt_target_subset_range α)
    change (mfderiv 𝓘(ℝ, E) I φ.symm z).inverse (V (φ.symm z)) =
      (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) z).inverse (V (φ.symm z))
    have hmf_eq :
        mfderiv 𝓘(ℝ, E) I φ.symm z = mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) z :=
      (mfderivWithin_of_mem_nhds hz_range).symm
    rw [hmf_eq]
  have hmpbWithin_eq (V : Π y : M, TangentSpace I y) :
      VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm V (range I) =ᶠ[𝓝 y₀]
        chartE_section_repr (I := I) α V ∘ φ.symm := by
    have htgt_nhds : φ.target ∈ 𝓝 y₀ :=
      Filter.mem_of_superset (hint_open.mem_nhds hx_int) interior_subset
    filter_upwards [htgt_nhds] with z hz
    exact mpullbackWithin_extChartAt_symm_eq_chartE_repr_symm V hz
  have hmpb_eq_chartE (V : Π y : M, TangentSpace I y) :
      VectorField.mpullback 𝓘(ℝ, E) I φ.symm V =ᶠ[𝓝 y₀]
        chartE_section_repr (I := I) α V ∘ φ.symm :=
    (hmpb_eq_mpbWithin V).trans (hmpbWithin_eq V)
  set V_E : E → E := chartE_section_repr (I := I) α X ∘ φ.symm with hV_E
  set W_E : E → E := chartE_section_repr (I := I) α Y ∘ φ.symm with hW_E
  have hRHS_subst :
      VectorField.mlieBracket 𝓘(ℝ, E)
          (VectorField.mpullback 𝓘(ℝ, E) I φ.symm X)
          (VectorField.mpullback 𝓘(ℝ, E) I φ.symm Y) y₀ =
        VectorField.mlieBracket 𝓘(ℝ, E) V_E W_E y₀ := by
    have h1 : VectorField.mpullback 𝓘(ℝ, E) I φ.symm X =ᶠ[𝓝 y₀] V_E := hmpb_eq_chartE X
    have h2 : VectorField.mpullback 𝓘(ℝ, E) I φ.symm Y =ᶠ[𝓝 y₀] W_E := hmpb_eq_chartE Y
    exact (h1.mlieBracket_vectorField_eq h2)
  have hmL_eq_L :
      VectorField.mlieBracket 𝓘(ℝ, E) V_E W_E y₀ =
        VectorField.lieBracket ℝ V_E W_E y₀ := by
    have h1 : VectorField.mlieBracket 𝓘(ℝ, E) V_E W_E =
        VectorField.lieBracket ℝ V_E W_E := by
      have := VectorField.mlieBracketWithin_eq_lieBracketWithin
        (𝕜 := ℝ) (E := E) (V := V_E) (W := W_E) (s := univ)
      rw [VectorField.mlieBracketWithin_univ] at this
      rw [VectorField.lieBracketWithin_univ] at this
      exact this
    exact congrFun h1 y₀
  have hL_unfold :
      VectorField.lieBracket ℝ V_E W_E y₀ =
        fderiv ℝ W_E y₀ (V_E y₀) - fderiv ℝ V_E y₀ (W_E y₀) := rfl
  have hVE_y₀ : V_E y₀ = trivToE (I := I) α x (X x) := by
    change (chartE_section_repr (I := I) α X ∘ φ.symm) y₀ =
      trivToE (I := I) α x (X x)
    change chartE_section_repr (I := I) α X (φ.symm y₀) =
      trivToE (I := I) α x (X x)
    rw [hxsymm]
    exact chartE_section_repr_eq_trivToE (I := I) α X x
  have hWE_y₀ : W_E y₀ = trivToE (I := I) α x (Y x) := by
    change (chartE_section_repr (I := I) α Y ∘ φ.symm) y₀ =
      trivToE (I := I) α x (Y x)
    change chartE_section_repr (I := I) α Y (φ.symm y₀) =
      trivToE (I := I) α x (Y x)
    rw [hxsymm]
    exact chartE_section_repr_eq_trivToE (I := I) α Y x
  have hkey :
      trivToE (I := I) α x (VectorField.mlieBracket I X Y x) =
        fderiv ℝ W_E y₀ (trivToE (I := I) α x (X x))
          - fderiv ℝ V_E y₀ (trivToE (I := I) α x (Y x)) := by
    calc trivToE (I := I) α x (VectorField.mlieBracket I X Y x)
        = VectorField.mpullback 𝓘(ℝ, E) I φ.symm
            (VectorField.mlieBracket I X Y) y₀ := hLHS.symm
      _ = VectorField.mlieBracket 𝓘(ℝ, E)
            (VectorField.mpullback 𝓘(ℝ, E) I φ.symm X)
            (VectorField.mpullback 𝓘(ℝ, E) I φ.symm Y) y₀ := hpb
      _ = VectorField.mlieBracket 𝓘(ℝ, E) V_E W_E y₀ := hRHS_subst
      _ = VectorField.lieBracket ℝ V_E W_E y₀ := hmL_eq_L
      _ = fderiv ℝ W_E y₀ (V_E y₀) - fderiv ℝ V_E y₀ (W_E y₀) := hL_unfold
      _ = fderiv ℝ W_E y₀ (trivToE (I := I) α x (X x))
          - fderiv ℝ V_E y₀ (trivToE (I := I) α x (Y x)) := by
            rw [hVE_y₀, hWE_y₀]
  have hround : trivFromE (I := I) α x (trivToE (I := I) α x (VectorField.mlieBracket I X Y x)) =
      VectorField.mlieBracket I X Y x :=
    trivFromE_trivToE (I := I) α hx_base _
  rw [← hround, hkey]

omit [FiniteDimensional ℝ E] in
private lemma mfderiv_scalar_along_eventuallyEq_chart_fderiv
    (x : M) (f : M → ℝ) (Y : Π b : M, TangentSpace I b)
    (hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E))
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    (fun b : M => mfderiv I 𝓘(ℝ) f b (Y b)) =ᶠ[𝓝 x]
      (fun y : E => fderiv ℝ (f ∘ (extChartAt I x).symm) y
        (chartE_section_repr (I := I) x Y ((extChartAt I x).symm y))) ∘ (extChartAt I x) := by
  classical
  set φ := extChartAt I x with hφ
  have hint_open : IsOpen (interior ((extChartAt I x).target : Set E)) := isOpen_interior
  have hsrc_extChart : x ∈ φ.source := mem_extChartAt_source x
  have hsrc_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hφsrc_nhds : φ.source ∈ 𝓝 x :=
    extChartAt_source_mem_nhds' (I := I) hsrc_extChart
  have hφ_cont : ContinuousAt φ x := by
    apply (continuousAt_extChartAt' (I := I) (x := x) hsrc_extChart)
  have hφ_pre_nhds : φ ⁻¹' (interior φ.target) ∈ 𝓝 x :=
    hφ_cont.preimage_mem_nhds (hint_open.mem_nhds hx_int)
  have hf_eventually_cmd : ∀ᶠ b in 𝓝 x, ContMDiffAt I 𝓘(ℝ) 2 f b :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := (2 : WithTop ℕ∞))
      (by simp : (2 : WithTop ℕ∞) ≠ ∞)).mp hf
  have hf_eventually_mdiff : ∀ᶠ b in 𝓝 x, MDiffAt f b := by
    filter_upwards [hf_eventually_cmd] with b hb
    exact hb.mdifferentiableAt (by simp)
  filter_upwards [hφsrc_nhds, hφ_pre_nhds, hf_eventually_mdiff] with b hb_src hb_int hb_mdiff
  have hb_src_chart : b ∈ (chartAt H x).source := by
    rwa [extChartAt_source] at hb_src
  change mfderiv I 𝓘(ℝ) f b (Y b) =
    fderiv ℝ (f ∘ φ.symm) (φ b) (chartE_section_repr (I := I) x Y (φ.symm (φ b)))
  rw [show φ.symm (φ b) = b from φ.left_inv hb_src]
  rw [mfderiv_scalar_eq_chart_fderiv (I := I) (α := x) (f := f) (x := b)
      hb_src_chart hb_int hb_mdiff (Y b)]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [FiniteDimensional ℝ E] in
theorem mfderiv_scalar_along_eq_chart_fderiv
    {x : M} {X Y : Π b : M, TangentSpace I b}
    (hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E))
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hY : MDiffAt (T% Y) x) :
    mfderiv I 𝓘(ℝ) (fun b => mfderiv I 𝓘(ℝ) f b (Y b)) x (X x) =
      fderiv ℝ
        (fun y : E => fderiv ℝ (f ∘ (extChartAt I x).symm) y
          (chartE_section_repr (I := I) x Y ((extChartAt I x).symm y)))
        (extChartAt I x x) (X x) := by
  classical
  set φ := extChartAt I x with hφ
  set ftilde : E → ℝ := f ∘ φ.symm with hftilde
  set Ychart : E → E := chartE_section_repr (I := I) x Y ∘ φ.symm with hYchart
  set Gtilde : E → ℝ := fun y => fderiv ℝ ftilde y (Ychart y) with hGtilde
  have hsrc_extChart : x ∈ φ.source := mem_extChartAt_source x
  have hsrc_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hint_open : IsOpen (interior ((extChartAt I x).target : Set E)) := isOpen_interior
  have htgt_nhds : (extChartAt I x).target ∈ 𝓝 (φ x) :=
    Filter.mem_of_superset (hint_open.mem_nhds hx_int) interior_subset
  have hrange_nhds : range I ∈ 𝓝 (φ x) :=
    Filter.mem_of_superset htgt_nhds (extChartAt_target_subset_range x)
  have hLHS_eq : mfderiv I 𝓘(ℝ) (fun b => mfderiv I 𝓘(ℝ) f b (Y b)) x =
      mfderiv I 𝓘(ℝ) (Gtilde ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq
      (mfderiv_scalar_along_eventuallyEq_chart_fderiv x f Y hx_int hf)
  have hφ_mdiff : MDiffAt φ x := mdifferentiableAt_extChartAt (I := I) (x := x) hsrc_chart
  have hftilde_cmd : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ftilde (range I) (φ x) :=
    (contMDiffAt_iff_source_of_mem_source (n := (2 : WithTop ℕ∞))
      (x := x) (x' := x) (f := f) hsrc_chart).mp hf
  have hftilde_cmdAt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ftilde (φ x) :=
    hftilde_cmd.contMDiffAt hrange_nhds
  have hftilde_cda : ContDiffAt ℝ 2 ftilde (φ x) :=
    contMDiffAt_iff_contDiffAt.mp hftilde_cmdAt
  have h_one_le_two : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) := by norm_num
  have hfderiv_ftilde_cda : ContDiffAt ℝ 1 (fderiv ℝ ftilde) (φ x) :=
    hftilde_cda.fderiv_right (m := 1) h_one_le_two
  have hfderiv_ftilde_diff : DifferentiableAt ℝ (fderiv ℝ ftilde) (φ x) :=
    hfderiv_ftilde_cda.differentiableAt one_ne_zero
  have hYchart_diff : DifferentiableAt ℝ Ychart (φ x) :=
    (mdifferentiableAt_section_iff_chartE_fderiv (I := I) x Y hsrc_chart hxbase hx_int).mp hY
  have hGtilde_diff : DifferentiableAt ℝ Gtilde (φ x) :=
    hfderiv_ftilde_diff.clm_apply hYchart_diff
  have hGtilde_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) Gtilde (φ x) :=
    hGtilde_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ) (Gtilde ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) Gtilde (φ x)).comp (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hGtilde_mdiff hφ_mdiff
  have hmf_to_fderiv :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) Gtilde (φ x) = fderiv ℝ Gtilde (φ x) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := ℝ) (f := Gtilde) (x := φ x)
  have hφ_id : mfderiv I 𝓘(ℝ, E) (extChartAt I x) x = ContinuousLinearMap.id ℝ _ :=
    mfderiv_extChartAt_self (𝕜 := ℝ) (I := I) (x := x)
  rw [hLHS_eq, hchain, hmf_to_fderiv]
  change (fderiv ℝ Gtilde (φ x)) ((mfderiv I 𝓘(ℝ, E) (extChartAt I x) x) (X x)) =
    fderiv ℝ Gtilde (φ x) (X x)
  rw [hφ_id]
  rfl


omit [FiniteDimensional ℝ E] in
theorem extDerivFun_apply_mlieBracket
    {x : M} {X Y : Π b : M, TangentSpace I b}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E)) :
    extDerivFun f x (VectorField.mlieBracket I X Y x) =
      extDerivFun (fun b => extDerivFun f b (Y b)) x (X x) -
        extDerivFun (fun b => extDerivFun f b (X b)) x (Y x) := by
  classical
  set φ := extChartAt I x with hφ
  set ftilde : E → ℝ := f ∘ φ.symm with hftilde
  set Xchart : E → E := chartE_section_repr (I := I) x X ∘ φ.symm with hXchart
  set Ychart : E → E := chartE_section_repr (I := I) x Y ∘ φ.symm with hYchart
  have hsrc_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_extChart : x ∈ φ.source := mem_extChartAt_source x
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hint_open : IsOpen (interior ((extChartAt I x).target : Set E)) := isOpen_interior
  have htgt_nhds : (extChartAt I x).target ∈ 𝓝 (φ x) :=
    Filter.mem_of_superset (hint_open.mem_nhds hx_int) interior_subset
  have hrange_nhds : range I ∈ 𝓝 (φ x) :=
    Filter.mem_of_superset htgt_nhds (extChartAt_target_subset_range x)
  have hftilde_cmd : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ftilde (range I) (φ x) :=
    (contMDiffAt_iff_source_of_mem_source (n := (2 : WithTop ℕ∞))
      (x := x) (x' := x) (f := f) hsrc_chart).mp hf
  have hftilde_cmdAt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 ftilde (φ x) :=
    hftilde_cmd.contMDiffAt hrange_nhds
  have hftilde_cda : ContDiffAt ℝ 2 ftilde (φ x) :=
    contMDiffAt_iff_contDiffAt.mp hftilde_cmdAt
  have hXchart_diff : DifferentiableAt ℝ Xchart (φ x) :=
    (mdifferentiableAt_section_iff_chartE_fderiv (I := I) x X hsrc_chart hxbase hx_int).mp hX
  have hYchart_diff : DifferentiableAt ℝ Ychart (φ x) :=
    (mdifferentiableAt_section_iff_chartE_fderiv (I := I) x Y hsrc_chart hxbase hx_int).mp hY
  have hxsymm : φ.symm (φ x) = x := φ.left_inv hsrc_extChart
  have htriv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) x =
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt
      (𝕜 := ℝ) (I := I) (x₀ := x) (x := x) hsrc_chart).symm
  have hid : mfderiv I 𝓘(ℝ, E) (extChartAt I x) x = ContinuousLinearMap.id ℝ _ :=
    mfderiv_extChartAt_self (𝕜 := ℝ) (I := I) (x := x)
  have htriv_id : trivToE (I := I) x x = ContinuousLinearMap.id ℝ _ := by
    change (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x =
      ContinuousLinearMap.id ℝ _
    rw [← htriv_eq, hid]
  have hXchart_at : Xchart (φ x) = X x := by
    change chartE_section_repr (I := I) x X (φ.symm (φ x)) = X x
    rw [hxsymm]
    change trivToE (I := I) x x (X x) = X x
    rw [htriv_id]; rfl
  have hYchart_at : Ychart (φ x) = Y x := by
    change chartE_section_repr (I := I) x Y (φ.symm (φ x)) = Y x
    rw [hxsymm]
    change trivToE (I := I) x x (Y x) = Y x
    rw [htriv_id]; rfl
  have hbracket_chart :
      VectorField.mlieBracket I X Y x =
        fderiv ℝ Ychart (φ x) (X x) - fderiv ℝ Xchart (φ x) (Y x) :=
    mlieBracket_eq_chart_fderiv_diff x X Y hx_int hX hY
  have hsymm : IsSymmSndFDerivAt ℝ ftilde (φ x) :=
    hftilde_cda.isSymmSndFDerivAt (by simp)
  have hftilde_lieBracket :
      fderiv ℝ ftilde (φ x) (VectorField.lieBracket ℝ Xchart Ychart (φ x)) =
        fderiv ℝ (fun y => fderiv ℝ ftilde y (Ychart y)) (φ x) (Xchart (φ x)) -
          fderiv ℝ (fun y => fderiv ℝ ftilde y (Xchart y)) (φ x) (Ychart (φ x)) :=
    VectorField.fderiv_apply_lieBracket_of_isSymmSndFDerivAt hftilde_cda hsymm
      hYchart_diff hXchart_diff
  have hf_mdiff : MDiffAt f x := hf.mdifferentiableAt (by simp)
  have hsub_X : (X x : E) = Xchart (φ x) := hXchart_at.symm
  have hsub_Y : (Y x : E) = Ychart (φ x) := hYchart_at.symm
  have hLHS_chart :
      extDerivFun f x (VectorField.mlieBracket I X Y x) =
        fderiv ℝ ftilde (φ x) (VectorField.mlieBracket I X Y x) := by
    change (NormedSpace.fromTangentSpace (f x))
        (mfderiv I 𝓘(ℝ) f x (VectorField.mlieBracket I X Y x)) =
      fderiv ℝ ftilde (φ x) (VectorField.mlieBracket I X Y x)
    rw [mfderiv_scalar_eq_chart_fderiv (I := I) x f hsrc_chart hx_int hf_mdiff
        (VectorField.mlieBracket I X Y x), htriv_id]
    rfl
  have hg_eq_Y : (fun b => extDerivFun f b (Y b)) = (fun b => mfderiv I 𝓘(ℝ) f b (Y b)) := by
    funext b
    change (NormedSpace.fromTangentSpace _) (mfderiv I 𝓘(ℝ) f b (Y b)) = _
    rfl
  have hg_eq_X : (fun b => extDerivFun f b (X b)) = (fun b => mfderiv I 𝓘(ℝ) f b (X b)) := by
    funext b
    change (NormedSpace.fromTangentSpace _) (mfderiv I 𝓘(ℝ) f b (X b)) = _
    rfl
  have hRHS_chart_Y :
      extDerivFun (fun b => extDerivFun f b (Y b)) x (X x) =
        fderiv ℝ (fun y => fderiv ℝ ftilde y (Ychart y)) (φ x) (Xchart (φ x)) := by
    rw [hg_eq_Y]
    change (NormedSpace.fromTangentSpace _)
        (mfderiv I 𝓘(ℝ) (fun b => mfderiv I 𝓘(ℝ) f b (Y b)) x (X x)) = _
    have hkey := mfderiv_scalar_along_eq_chart_fderiv (X := X) (Y := Y) hx_int hf hY
    rw [hkey, hXchart_at]
    rfl
  have hRHS_chart_X :
      extDerivFun (fun b => extDerivFun f b (X b)) x (Y x) =
        fderiv ℝ (fun y => fderiv ℝ ftilde y (Xchart y)) (φ x) (Ychart (φ x)) := by
    rw [hg_eq_X]
    change (NormedSpace.fromTangentSpace _)
        (mfderiv I 𝓘(ℝ) (fun b => mfderiv I 𝓘(ℝ) f b (X b)) x (Y x)) = _
    have hkey := mfderiv_scalar_along_eq_chart_fderiv (X := Y) (Y := X) hx_int hf hX
    rw [hkey, hYchart_at]
    rfl
  rw [hLHS_chart, hbracket_chart, hRHS_chart_Y, hRHS_chart_X]
  have hlie_unfold :
      VectorField.lieBracket ℝ Xchart Ychart (φ x) =
        fderiv ℝ Ychart (φ x) (Xchart (φ x)) - fderiv ℝ Xchart (φ x) (Ychart (φ x)) := rfl
  rw [show fderiv ℝ Ychart (φ x) (X x) - fderiv ℝ Xchart (φ x) (Y x) =
        VectorField.lieBracket ℝ Xchart Ychart (φ x) by
        rw [hsub_X, hsub_Y]; exact hlie_unfold.symm]
  exact hftilde_lieBracket

end Connection
end Integral
end DifferentialGeometry
