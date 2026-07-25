import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrict

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem chartPushed_chartPullback_pointwise_identity
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (γ α : M) {K_α : Set M} (hK_compact : IsCompact K_α)
    (hK_α_in_α : K_α ⊆ (chartAt H α).source) :
    ∃ (Ω_γα Ω_αγ : Set EuclN) (_hΩ_γα_open : IsOpen Ω_γα)
      (_hΩ_αγ_open : IsOpen Ω_αγ)
      (_hΩ_γα_subset_target : Ω_γα ⊆ chartTargetEuclid (I := I) (M := M) γ)
      (_hΩ_αγ_subset_target : Ω_αγ ⊆ chartTargetEuclid (I := I) (M := M) α)
      (Φ : DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder
          (Module.finrank ℝ E) Ω_γα Ω_αγ 1)
      (ργ_pre : EuclN → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ργ_pre ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclN, ‖ργ_pre y‖ ≤ C ∧ ‖fderiv ℝ ργ_pre y‖ ≤ C) ∧
      (tsupport ργ_pre ⊆ Ω_γα ∩ chartTargetEuclid (I := I) (M := M) γ) ∧
      ((fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
          (K_α ∩ tsupport
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
              : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆ Ω_αγ) ∧
      (∀ y ∈ Ω_γα,
        Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y) ∧
      (∀ {v : EuclN → ℝ},
        tsupport v ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α →
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) γ,
          chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
              (chartPullback I α v) y =
            ργ_pre y * v (Φ.toFun y)) := by
  classical
  set K_M : Set M := K_α ∩ tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKM_def
  have hKM_compact : IsCompact K_M :=
    hK_compact.inter_right (isClosed_tsupport _)
  have hKM_in_α : K_M ⊆ (chartAt H α).source := fun x hx => hK_α_in_α hx.1
  have hKM_in_γ : K_M ⊆ (chartAt H γ).source := fun x hx =>
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M γ hx.2
  obtain ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target,
    hΩαγ_subset_target, hΩγα_subset_overlap, _hΩαγ_subset_overlap,
    hKM_image_in_Ωγα, Φ, hΦ_eq_on_Ωγα, _hΦ_inv_eq_on_Ωαγ⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      γ α hKM_compact hKM_in_γ hKM_in_α 1
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K_M
    with hKEγ_def
  have hKEγ_compact : IsCompact K_E_γ :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) γ hKM_compact hKM_in_γ
  have hKEγ_subset_target : K_E_γ ⊆ chartTargetEuclid (I := I) (M := M) γ := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    have hx_ext : x ∈ (extChartAt I γ).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I γ x ∈ (extChartAt I γ).target :=
      (extChartAt I γ).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I γ x, h_target, rfl⟩
  set Uγ : Set EuclN := Ω_γα ∩ chartTargetEuclid (I := I) (M := M) γ with hUγ_def
  have hUγ_open : IsOpen Uγ :=
    hΩγα_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) γ)
  have hKEγ_in_Uγ : K_E_γ ⊆ Uγ :=
    Set.subset_inter hKM_image_in_Ωγα hKEγ_subset_target
  obtain ⟨δ_γ, η_γ_loc, _hδ_γ_pos, _hδγ_subset, hη_γ_loc_smooth, hη_γ_loc_cpt,
    hη_γ_loc_range, hη_γ_loc_one, hη_γ_loc_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEγ_compact hUγ_open hKEγ_in_Uγ
  have hη_γ_loc_supp_Ωγα : tsupport η_γ_loc ⊆ Ω_γα :=
    fun y hy => (hη_γ_loc_supp hy).1
  set ρ_γ_M : M → ℝ :=
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_γ_M_def
  have hρ_γ_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ρ_γ_M :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯).contMDiff
  have hρ_γ_M_supp_in_chart : tsupport ρ_γ_M ⊆ (chartAt H γ).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M γ
  have hρ_γ_M_cpt : HasCompactSupport ρ_γ_M :=
    (isClosed_tsupport _).isCompact
  have hρ_γ_M_range : Set.range ρ_γ_M ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro v ⟨x, hx⟩
    rw [← hx]
    refine ⟨?_, ?_⟩
    · exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg γ x
    · exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one γ x
  set ργE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) γ ρ_γ_M with hργE_def
  have hργE_smooth : ContDiff ℝ (⊤ : ℕ∞) ργE :=
    contDiff_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth hρ_γ_M_cpt
      hρ_γ_M_supp_in_chart
  have hργE_range : Set.range ργE ⊆ Set.Icc (0 : ℝ) 1 :=
    etaEuclid_range_Icc (I := I) (M := M) γ ρ_γ_M hρ_γ_M_range
  have hργE_norm_one : ∀ y : EuclN, ‖ργE y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hργE_range
  obtain ⟨C_ργE_grad, _hC_ργE_pos, hC_ργE_grad⟩ :=
    exists_grad_bound_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth
      hρ_γ_M_cpt hρ_γ_M_supp_in_chart
  have hη_γ_loc_norm_one : ∀ y : EuclN, ‖η_γ_loc y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_γ_loc_range
  obtain ⟨C_η_γ_grad, _hC_η_γ_pos, hC_η_γ_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_γ_loc_smooth hη_γ_loc_cpt
  set ργ_pre : EuclN → ℝ := fun y => η_γ_loc y * ργE y with hργ_pre_def
  have hργ_pre_smooth : ContDiff ℝ (⊤ : ℕ∞) ργ_pre :=
    hη_γ_loc_smooth.mul hργE_smooth
  have hργ_pre_bound : ∀ y : EuclN, ‖ργ_pre y‖ ≤ 1 := by
    intro y
    have h := mul_le_mul (a := ‖η_γ_loc y‖) (b := 1) (c := ‖ργE y‖) (d := 1)
      (hη_γ_loc_norm_one y) (hργE_norm_one y) (norm_nonneg _) zero_le_one
    rw [show ργ_pre y = η_γ_loc y * ργE y from rfl, norm_mul, mul_one] at *
    exact h
  set C_combined_grad : ℝ := C_η_γ_grad + C_ργE_grad with hC_combined_grad_def
  have hC_combined_grad_bound : ∀ y : EuclN, ‖fderiv ℝ ργ_pre y‖ ≤ C_combined_grad := by
    intro y
    have h_eq : ργ_pre = fun y => η_γ_loc y * ργE y := rfl
    have hη_γ_loc_diff : DifferentiableAt ℝ η_γ_loc y :=
      (hη_γ_loc_smooth.differentiable (by simp)).differentiableAt
    have hργE_diff : DifferentiableAt ℝ ργE y :=
      (hργE_smooth.differentiable (by simp)).differentiableAt
    rw [h_eq]
    rw [fderiv_fun_mul hη_γ_loc_diff hργE_diff]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖η_γ_loc y • fderiv ℝ ργE y‖ ≤ C_ργE_grad := by
      rw [norm_smul]
      have : ‖η_γ_loc y‖ * ‖fderiv ℝ ργE y‖ ≤ 1 * C_ργE_grad :=
        mul_le_mul (hη_γ_loc_norm_one y) (hC_ργE_grad y) (norm_nonneg _) zero_le_one
      simpa using this
    have h2 : ‖ργE y • fderiv ℝ η_γ_loc y‖ ≤ C_η_γ_grad := by
      rw [norm_smul]
      have : ‖ργE y‖ * ‖fderiv ℝ η_γ_loc y‖ ≤ 1 * C_η_γ_grad :=
        mul_le_mul (hργE_norm_one y) (hC_η_γ_grad y) (norm_nonneg _) zero_le_one
      simpa using this
    linarith [h1, h2]
  set C : ℝ := max 1 C_combined_grad with hC_def
  have hC_nn : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
  have hC_norm : ∀ y : EuclN, ‖ργ_pre y‖ ≤ C := fun y =>
    (hργ_pre_bound y).trans (le_max_left _ _)
  have hC_grad : ∀ y : EuclN, ‖fderiv ℝ ργ_pre y‖ ≤ C := fun y =>
    (hC_combined_grad_bound y).trans (le_max_right _ _)
  have hΦ_eq_KM : ∀ x ∈ K_M, Φ.toFun ((toEuclidean (E := E)) (extChartAt I γ x)) =
      (toEuclidean (E := E)) (extChartAt I α x) := by
    intro x hxK
    set y := (toEuclidean (E := E)) (extChartAt I γ x) with hy_def
    have hy_in_KEγ : y ∈ K_E_γ := ⟨x, hxK, rfl⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy_in_KEγ
    have h1 : Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y :=
      hΦ_eq_on_Ωγα y hy_in_Ωγα
    rw [h1]
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    rw [hy_def]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hx_chart
  have hργ_pre_supp_in_Uγ : tsupport ργ_pre ⊆ Uγ := by
    refine subset_trans ?_ hη_γ_loc_supp
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_ne : η_γ_loc y ≠ 0 := by
      intro h0
      apply hy
      change η_γ_loc y * ργE y = 0
      rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hKEα_in_Ωαγ : (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M ⊆ Ω_αγ := by
    rintro w ⟨x, hxK, hxw⟩
    have hΦ_x := hΦ_eq_KM x hxK
    have h_y_in_Ωγα : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα :=
      hKM_image_in_Ωγα ⟨x, hxK, rfl⟩
    have h_w_eq : Φ.toFun ((toEuclidean (E := E)) (extChartAt I γ x)) = w := by
      rw [hΦ_x]; exact hxw
    rw [← h_w_eq]
    exact Φ.bijOn.mapsTo h_y_in_Ωγα
  refine ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
    Φ, ργ_pre, hργ_pre_smooth,
    ⟨C, hC_nn, fun y => ⟨hC_norm y, hC_grad y⟩⟩, hργ_pre_supp_in_Uγ,
    hKEα_in_Ωαγ, hΦ_eq_on_Ωγα, ?_⟩
  intro v hv_supp y hy_target
  set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I γ).target := by
    have := hy_target
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at this
    exact this
  have hz_source : z ∈ (extChartAt I γ).source :=
    (extChartAt I γ).map_target hsymm_target
  have hz_chartγ : z ∈ (chartAt H γ).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)] at hz_source
    exact hz_source
  have h_pushed_eq : chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
      (chartPullback I α v) y =
      ρ_γ_M z * chartPullback I α v z := by
    unfold chartPushed
    rfl
  rw [h_pushed_eq]
  have hργ_pre_y : ργ_pre y = η_γ_loc y * ργE y := rfl
  rw [hργ_pre_y]
  have hργE_y : ργE y = ρ_γ_M z := by
    rw [hργE_def]
    exact etaEuclid_apply_of_mem (I := I) (M := M) γ ρ_γ_M hy_target
  by_cases h_y_in_supp_η_γ : y ∈ tsupport η_γ_loc
  · have hy_in_Ωγα : y ∈ Ω_γα := hη_γ_loc_supp_Ωγα h_y_in_supp_η_γ
    by_cases hρ_zero : ρ_γ_M z = 0
    · rw [hρ_zero, hργE_y, hρ_zero]; ring
    · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M := by
        have h_in : z ∈ Function.support ρ_γ_M := by
          simp only [Function.mem_support, ne_eq]; exact hρ_zero
        exact subset_tsupport _ h_in
      by_cases hz_in_α : z ∈ (chartAt H α).source
      · rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_in_α]
        by_cases hz_in_Kα : z ∈ K_α
        · have hz_in_KM : z ∈ K_M := ⟨hz_in_Kα, hz_in_tsupp_ρ⟩
          have hy_in_KEγ : y ∈ K_E_γ := by
            refine ⟨z, hz_in_KM, ?_⟩
            change (toEuclidean (E := E)) (extChartAt I γ z) = y
            have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
              (extChartAt I γ).right_inv hsymm_target
            rw [h_z_chart]
            exact (toEuclidean (E := E)).apply_symm_apply y
          have hη_γ_loc_y : η_γ_loc y = 1 := by
            apply hη_γ_loc_one
            exact Metric.self_subset_cthickening K_E_γ hy_in_KEγ
          have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
            have h := hΦ_eq_KM z hz_in_KM
            have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
              (extChartAt I γ).right_inv hsymm_target
            have hy_eq : (toEuclidean (E := E)) (extChartAt I γ z) = y := by
              rw [h_z_chart]
              exact (toEuclidean (E := E)).apply_symm_apply y
            rw [← hy_eq]
            exact h
          rw [hΦ_y, hη_γ_loc_y, hργE_y]
          ring
        · have hvα_z_eq : (toEuclidean (E := E)) (extChartAt I α z) ∉ tsupport v := by
            intro hin
            have := hv_supp hin
            rcases this with ⟨x', hx'_K, hx'_eq⟩
            have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K
            have h_eq_chart_α : extChartAt I α x' = extChartAt I α z := by
              have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                  (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
              exact (toEuclidean (E := E)).injective h_eu
            have hz_in_α_ext : z ∈ (extChartAt I α).source := by
              rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
                (I := I) (M := M)]
              exact hz_in_α
            have hx'_α_ext : x' ∈ (extChartAt I α).source := by
              rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
                (I := I) (M := M)]
              exact hx'_chart
            have h_inj := (extChartAt I α).injOn hx'_α_ext hz_in_α_ext h_eq_chart_α
            have : z ∈ K_α := by rw [← h_inj]; exact hx'_K
            exact hz_in_Kα this
          have hv_z : v ((toEuclidean (E := E)) (extChartAt I α z)) = 0 :=
            image_eq_zero_of_notMem_tsupport hvα_z_eq
          have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
            rw [hΦ_eq_on_Ωγα y hy_in_Ωγα]
            have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
              (extChartAt I γ).right_inv hsymm_target
            have hy_eq : (toEuclidean (E := E)) (extChartAt I γ z) = y := by
              rw [h_z_chart]
              exact (toEuclidean (E := E)).apply_symm_apply y
            rw [← hy_eq]
            exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hz_chartγ
          rw [hΦ_y, hv_z]; ring
      · rw [chartPullback_apply_of_notMem (I := I) (M := M) α v hz_in_α]
        exfalso
        have hy_in_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
          hΩγα_subset_overlap hy_in_Ωγα
        unfold chartOverlapEuclid at hy_in_overlap
        rcases hy_in_overlap with ⟨z', ⟨w, hw_inter, hwz'⟩, hz'y⟩
        have hy_eq : (toEuclidean (E := E)) (extChartAt I γ w) = y := by
          rw [← hz'y, ← hwz']
        have h_w_chart_γ : w ∈ (extChartAt I γ).source := by
          rw [extChartAt_source]; exact hw_inter.1
        have h_z_eq_w : z = w := by
          have h_y_eq_chart : (toEuclidean (E := E)).symm y = extChartAt I γ w := by
            rw [← hy_eq, (toEuclidean (E := E)).symm_apply_apply]
          change (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) = w
          rw [h_y_eq_chart]
          exact (extChartAt I γ).left_inv h_w_chart_γ
        rw [h_z_eq_w] at hz_in_α
        exact hz_in_α hw_inter.2
  · have h_zero_η : η_γ_loc y = 0 := image_eq_zero_of_notMem_tsupport h_y_in_supp_η_γ
    rw [h_zero_η]
    simp only [zero_mul]
    by_cases hρ_zero : ρ_γ_M z = 0
    · rw [hρ_zero]; ring
    · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M := by
        have h_in : z ∈ Function.support ρ_γ_M := by
          simp only [Function.mem_support, ne_eq]; exact hρ_zero
        exact subset_tsupport _ h_in
      by_cases hpb_zero : chartPullback I α v z = 0
      · rw [hpb_zero]; ring
      · exfalso
        have hz_chartα : z ∈ (chartAt H α).source := by
          by_contra hcontra
          apply hpb_zero
          exact chartPullback_apply_of_notMem (I := I) (M := M) α v hcontra
        rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_chartα] at hpb_zero
        have h_arg_in_tsupp_v : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport v := by
          have : (toEuclidean (E := E)) (extChartAt I α z) ∈ Function.support v := by
            simp only [Function.mem_support, ne_eq]; exact hpb_zero
          exact subset_tsupport _ this
        have h_arg_in_image_K_α : (toEuclidean (E := E)) (extChartAt I α z) ∈
            (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
          hv_supp h_arg_in_tsupp_v
        obtain ⟨x', hx'_K_α, hx'_eq⟩ := h_arg_in_image_K_α
        have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K_α
        have h_eq_chart : extChartAt I α x' = extChartAt I α z := by
          have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
              (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
          exact (toEuclidean (E := E)).injective h_eu
        have hx'_α_ext : x' ∈ (extChartAt I α).source := by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]; exact hx'_chart
        have hz_α_ext : z ∈ (extChartAt I α).source := by
          rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]; exact hz_chartα
        have h_inj := (extChartAt I α).injOn hx'_α_ext hz_α_ext h_eq_chart
        have hz_in_K_α : z ∈ K_α := by rw [← h_inj]; exact hx'_K_α
        have hz_in_K_M : z ∈ K_M := ⟨hz_in_K_α, hz_in_tsupp_ρ⟩
        have hy_in_KEγ : y ∈ K_E_γ := by
          refine ⟨z, hz_in_K_M, ?_⟩
          change (toEuclidean (E := E)) (extChartAt I γ z) = y
          have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
            (extChartAt I γ).right_inv hsymm_target
          rw [h_z_chart]
          exact (toEuclidean (E := E)).apply_symm_apply y
        have hy_in_cthick : y ∈ Metric.cthickening δ_γ K_E_γ :=
          Metric.self_subset_cthickening K_E_γ hy_in_KEγ
        have h_η_y_one : η_γ_loc y = 1 := hη_γ_loc_one y hy_in_cthick
        have hy_in_supp : y ∈ Function.support η_γ_loc := by
          simp only [Function.mem_support, ne_eq, h_η_y_one]
          exact one_ne_zero
        exact h_y_in_supp_η_γ (subset_tsupport _ hy_in_supp)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
