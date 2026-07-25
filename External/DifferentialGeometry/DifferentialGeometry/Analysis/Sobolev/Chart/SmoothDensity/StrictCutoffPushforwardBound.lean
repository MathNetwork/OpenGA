import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrictMemWkpHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.StrictCutoff
import DifferentialGeometry.Analysis.Sobolev.Tools.StrictStrongSupport
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Integration.Measure.Rellich


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

private noncomputable def pou
    [T2Space M] [SigmaCompactSpace M] (γ : M) : M → ℝ :=
  ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
    : C^∞⟮I, M; ℝ⟯) : M → ℝ)

private lemma pou_smooth
    [T2Space M] [SigmaCompactSpace M] (γ : M) :
    ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (pou (I := I) (M := M) γ) :=
  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
    : C^∞⟮I, M; ℝ⟯).contMDiff

private lemma pou_tsupport_subset
    [T2Space M] [SigmaCompactSpace M] (γ : M) :
    tsupport (pou (I := I) (M := M) γ) ⊆ (chartAt H γ).source :=
  DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M γ

private lemma pou_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] (γ : M) :
    HasCompactSupport (pou (I := I) (M := M) γ) :=
  (isClosed_tsupport _).isCompact

private lemma hasCompactSupport_chartStrictCutoff
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] (α : M) :
    HasCompactSupport (chartStrictCutoff (I := I) (M := M) α) :=
  (isClosed_tsupport _).isCompact

private lemma prod_pou_strictCutoff_v_eq_zero_off
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (γ α : M) (v : M → ℝ) {x : M}
    (hx : x ∉ tsupport (pou (I := I) (M := M) γ) ∩
      tsupport (chartStrictCutoff (I := I) (M := M) α)) :
    pou (I := I) (M := M) γ x *
      (chartStrictCutoff (I := I) (M := M) α x * v x) = 0 := by
  classical
  rw [Set.mem_inter_iff, not_and_or] at hx
  rcases hx with hx_pou | hx_cut
  · have h0 : pou (I := I) (M := M) γ x = 0 :=
      image_eq_zero_of_notMem_tsupport hx_pou
    rw [h0]; ring
  · have h0 : chartStrictCutoff (I := I) (M := M) α x = 0 :=
      image_eq_zero_of_notMem_tsupport hx_cut
    rw [h0]; ring

private lemma strictCutoff_mul_v_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (α : M) (v : M → ℝ) (x : M) :
    chartStrictCutoff (I := I) (M := M) α x * v x =
      ∑ γ ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I) (M := M),
        pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x) := by
  classical
  have h_sum_one :
      ∑ γ ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I) (M := M),
        pou (I := I) (M := M) γ x = 1 := by
    unfold pou
    exact chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  calc
    chartStrictCutoff (I := I) (M := M) α x * v x =
        (∑ γ ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
                (I := I) (M := M),
          pou (I := I) (M := M) γ x) *
          (chartStrictCutoff (I := I) (M := M) α x * v x) := by
      rw [h_sum_one]; ring
    _ = ∑ γ ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I) (M := M),
          pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x) := by
      rw [Finset.sum_mul]

private lemma chartPushedRaw_strictCutoff_eq_finset_sum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (α : M) (v : M → ℝ) (y : EuclN) :
    chartPushedRaw (I := I) (M := M) α
        (fun x => chartStrictCutoff (I := I) (M := M) α x * v x) y =
      ∑ γ ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I) (M := M),
        chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)) y := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have h_sum_decomp : chartStrictCutoff (I := I) (M := M) α x * v x =
        ∑ γ ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
                (I := I) (M := M),
          pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x) :=
      strictCutoff_mul_v_eq_finset_sum (I := I) (M := M) α v x
    rw [h_sum_decomp]
    refine Finset.sum_congr rfl ?_
    intro γ _
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    have h_zero : ∀ γ : M,
        chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)) y = 0 := by
      intro γ
      exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy
    rw [Finset.sum_eq_zero (fun γ _ => h_zero γ)]

private lemma chartPushedRaw_pou_strictCutoff_v_zero_of_disjoint
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (γ α : M) (v : M → ℝ)
    (hKM_empty : tsupport (pou (I := I) (M := M) γ) ∩
      tsupport (chartStrictCutoff (I := I) (M := M) α) = ∅) :
    chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x)) =
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have hx_not_in :
        x ∉ tsupport (pou (I := I) (M := M) γ) ∩
            tsupport (chartStrictCutoff (I := I) (M := M) α) := by
      rw [hKM_empty]
      exact Set.notMem_empty x
    exact prod_pou_strictCutoff_v_eq_zero_off (I := I) (M := M) γ α v hx_not_in
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

private theorem cross_chart_strictCutoff_pushedRaw_joint
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (γ α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ {v : M → ℝ}, MemWkpChart (I := I) (M := M) g k p v →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)))
        (chartTargetEuclid (I := I) (M := M) α) ∧
      HasCompactSupport
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x))) ∧
      tsupport
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x))) ⊆
        chartTargetEuclid (I := I) (M := M) α ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ v)
          (chartTargetEuclid (I := I) (M := M) γ) := by
  classical
  let _ := g
  set K_M : Set M := tsupport (pou (I := I) (M := M) γ) ∩
    tsupport (chartStrictCutoff (I := I) (M := M) α) with hKM_def
  have hKM_compact : IsCompact K_M :=
    ((isClosed_tsupport _).isCompact).inter_right (isClosed_tsupport _)
  have hKM_in_γ : K_M ⊆ (chartAt H γ).source := fun x hx =>
    pou_tsupport_subset (I := I) (M := M) γ hx.1
  have hKM_in_α : K_M ⊆ (chartAt H α).source := fun x hx =>
    chartStrictCutoff_tsupport_subset (I := I) (M := M) α hx.2
  set Ωα_target : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩα_target_def
  set Ωγ_target : Set EuclN := chartTargetEuclid (I := I) (M := M) γ with hΩγ_target_def
  have hΩα_target_open : IsOpen Ωα_target := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩγ_target_open : IsOpen Ωγ_target := chartTargetEuclid_isOpen (I := I) (M := M) γ
  by_cases hKM_empty : K_M = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro v _
    have h_zero := chartPushedRaw_pou_strictCutoff_v_zero_of_disjoint
      (I := I) (M := M) γ α v hKM_empty
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_zero]
      exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
        (d := Module.finrank ℝ E) hp_one hΩα_target_open
    · rw [h_zero]
      exact HasCompactSupport.zero
    · rw [h_zero]
      have h_supp_eq : tsupport (fun _ : EuclN => (0 : ℝ)) = ∅ := by
        unfold tsupport
        rw [show (fun _ : EuclN => (0 : ℝ)) = (0 : EuclN → ℝ) from rfl,
          Function.support_zero, closure_empty]
      rw [h_supp_eq]
      exact Set.empty_subset _
    · rw [h_zero]
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
        (d := Module.finrank ℝ E) hp_one hΩα_target_open]
      exact zero_le _
  obtain ⟨Ω_α, Ω_γ, hΩα_open, hΩγ_open, hΩα_subset_target, hΩγ_subset_target,
    hΩα_subset_overlap, _hΩγ_subset_overlap, hKM_image_α_in_Ωα, Φ,
    hΦ_eq_on_Ωα, _hΦ_inv_eq_on_Ωγ⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      α γ hKM_compact hKM_in_α hKM_in_γ k
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M with hKEα_def
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K_M with hKEγ_def
  have hKEα_compact : IsCompact K_E_α :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKM_compact hKM_in_α
  have hKEγ_compact : IsCompact K_E_γ :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) γ hKM_compact hKM_in_γ
  have hKEα_subset_target : K_E_α ⊆ Ωα_target := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H α).source := hKM_in_α hxK
    have hx_ext : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I α x, h_target, rfl⟩
  have hKEγ_subset_target : K_E_γ ⊆ Ωγ_target := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    have hx_ext : x ∈ (extChartAt I γ).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I γ x ∈ (extChartAt I γ).target :=
      (extChartAt I γ).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I γ x, h_target, rfl⟩
  have hΦ_eq_KM : ∀ x ∈ K_M, Φ.toFun ((toEuclidean (E := E)) (extChartAt I α x)) =
      (toEuclidean (E := E)) (extChartAt I γ x) := by
    intro x hxK
    set y_α : EuclN := (toEuclidean (E := E)) (extChartAt I α x) with hy_α_def
    have hy_α_in_KEα : y_α ∈ K_E_α := ⟨x, hxK, rfl⟩
    have hy_α_in_Ωα : y_α ∈ Ω_α := hKM_image_α_in_Ωα hy_α_in_KEα
    have h1 : Φ.toFun y_α = chartTransitionEuclid (I := I) (M := M) α γ y_α :=
      hΦ_eq_on_Ωα y_α hy_α_in_Ωα
    rw [h1]
    have hx_chart_α : x ∈ (chartAt H α).source := hKM_in_α hxK
    rw [hy_α_def]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α γ hx_chart_α
  have hKEγ_eq_Φ_image : K_E_γ = Φ.toFun '' K_E_α := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hxK, hxz⟩
      refine ⟨(toEuclidean (E := E)) (extChartAt I α x), ?_, ?_⟩
      · exact ⟨x, hxK, rfl⟩
      · have := hΦ_eq_KM x hxK
        rw [this]; exact hxz
    · rintro ⟨y, hy, hyz⟩
      rcases hy with ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      have := hΦ_eq_KM x hxK
      rw [← hyz, ← hxy, this]
  have hKEγ_in_Ωγ : K_E_γ ⊆ Ω_γ := by
    rw [hKEγ_eq_Φ_image]
    intro z hz
    rcases hz with ⟨y, hy, hyz⟩
    have hy_in_Ωα : y ∈ Ω_α := hKM_image_α_in_Ωα hy
    rw [← hyz]; exact Φ.bijOn.mapsTo hy_in_Ωα
  set Uα : Set EuclN := Ω_α ∩ Ωα_target with hUα_def
  have hUα_open : IsOpen Uα := hΩα_open.inter hΩα_target_open
  have hKEα_in_Uα : K_E_α ⊆ Uα :=
    Set.subset_inter hKM_image_α_in_Ωα hKEα_subset_target
  obtain ⟨δ_α, η_α_loc, _hδ_α_pos, _hδα_subset, hη_α_loc_smooth, hη_α_loc_cpt,
    _hη_α_loc_range, hη_α_loc_one, hη_α_loc_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEα_compact hUα_open hKEα_in_Uα
  have hη_α_loc_supp_Ωα : tsupport η_α_loc ⊆ Ω_α :=
    fun y hy => (hη_α_loc_supp hy).1
  have hη_α_loc_supp_target : tsupport η_α_loc ⊆ Ωα_target :=
    fun y hy => (hη_α_loc_supp hy).2
  set Uγ : Set EuclN := Ω_γ ∩ Ωγ_target with hUγ_def
  have hUγ_open : IsOpen Uγ := hΩγ_open.inter hΩγ_target_open
  have hKEγ_in_Uγ : K_E_γ ⊆ Uγ :=
    Set.subset_inter hKEγ_in_Ωγ hKEγ_subset_target
  obtain ⟨_δ_γ, η_γ_loc, _hδ_γ_pos, _hδγ_subset, hη_γ_loc_smooth, hη_γ_loc_cpt,
    _hη_γ_loc_range, hη_γ_loc_one, hη_γ_loc_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEγ_compact hUγ_open hKEγ_in_Uγ
  have hη_γ_loc_supp_Ωγ : tsupport η_γ_loc ⊆ Ω_γ :=
    fun y hy => (hη_γ_loc_supp hy).1
  have hη_γ_loc_supp_target : tsupport η_γ_loc ⊆ Ωγ_target :=
    fun y hy => (hη_γ_loc_supp hy).2
  set η_α_E : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) α
    (chartStrictCutoff (I := I) (M := M) α) with hη_α_E_def
  have hη_α_E_smooth : ContDiff ℝ (⊤ : ℕ∞) η_α_E :=
    contDiff_etaEuclid (I := I) (M := M) α
      (chartStrictCutoff (I := I) (M := M) α)
      (chartStrictCutoff_contMDiff (I := I) (M := M) α)
      (hasCompactSupport_chartStrictCutoff (I := I) (M := M) α)
      (chartStrictCutoff_tsupport_subset (I := I) (M := M) α)
  have hη_α_E_cpt : HasCompactSupport η_α_E :=
    hasCompactSupport_etaEuclid (I := I) (M := M) α
      (chartStrictCutoff (I := I) (M := M) α)
      (hasCompactSupport_chartStrictCutoff (I := I) (M := M) α)
      (chartStrictCutoff_tsupport_subset (I := I) (M := M) α)
  set η_combined_α : EuclN → ℝ := fun y => η_α_loc y * η_α_E y with hηα_def
  have hη_combined_α_smooth : ContDiff ℝ (⊤ : ℕ∞) η_combined_α :=
    hη_α_loc_smooth.mul hη_α_E_smooth
  have hη_combined_α_cpt : HasCompactSupport η_combined_α := by
    refine hη_α_loc_cpt.of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_mono ?_
    intro y hy
    simp only [hηα_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_α_loc y ≠ 0 := by intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  have hη_combined_α_supp_Ωα : tsupport η_combined_α ⊆ Ω_α := by
    refine Set.Subset.trans ?_ hη_α_loc_supp_Ωα
    refine closure_mono ?_
    intro y hy
    simp only [hηα_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_α_loc y ≠ 0 := by intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  obtain ⟨C_combined_α, hC_combined_α_nn, hC_combined_α_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      hη_combined_α_smooth hη_combined_α_cpt k
  obtain ⟨C_η_γ_loc, hC_η_γ_loc_nn, hC_η_γ_loc_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      hη_γ_loc_smooth hη_γ_loc_cpt k
  have hη_combined_α_iter_bound :
      ∀ j ≤ k, ∀ y ∈ Ω_α, ‖iteratedFDeriv ℝ j η_combined_α y‖ ≤ C_combined_α := by
    intro j hj y _; exact hC_combined_α_bound y j hj
  obtain ⟨K_leib_α, hK_leib_α_pos, hK_leib_α_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      k hp_one hp_top hΩα_open hη_combined_α_smooth hC_combined_α_nn
      hη_combined_α_iter_bound
  have hη_γ_loc_iter_bound :
      ∀ j ≤ k, ∀ y ∈ Ωγ_target, ‖iteratedFDeriv ℝ j η_γ_loc y‖ ≤ C_η_γ_loc := by
    intro j hj y _; exact hC_η_γ_loc_bound y j hj
  obtain ⟨K_leib_γ, hK_leib_γ_pos, hK_leib_γ_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      k hp_one hp_top hΩγ_target_open hη_γ_loc_smooth hC_η_γ_loc_nn
      hη_γ_loc_iter_bound
  set K_chain : ℝ := Φ.wkpComp_const' k p with hK_chain_def
  have hK_chain_pos : 0 < K_chain := by
    have hp_zero : p ≠ 0 := by
      intro hpz; rw [hpz] at hp_one; exact absurd hp_one (by norm_num)
    have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
    have hjLB_pos : 0 < Φ.jacobian_lower_bound := Φ.jacobian_lower_bound_pos
    have hjLB_inv_pos : 0 < 1 / Φ.jacobian_lower_bound := by positivity
    have hKchg_pos : 0 < (1 / Φ.jacobian_lower_bound) ^ (1 / p.toReal) :=
      Real.rpow_pos_of_pos hjLB_inv_pos _
    rw [hK_chain_def]
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpComp_const'
    have h_zero_in : (0 : ℕ) ∈ Finset.range (k + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ _)
    have h_at_zero : (Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) : ℝ) = 1 := by
      have h_card : Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) = 1 := by
        rw [Fintype.card_fun]; simp
      exact_mod_cast h_card
    have h_card_pos : 0 < (Finset.range (k + 1)).sum
        (fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ)) := by
      have h_le := Finset.single_le_sum (s := Finset.range (k + 1))
        (f := fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ))
        (fun j _ => by positivity) h_zero_in
      rw [show ((fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ)) 0 : ℝ) =
          (Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) : ℝ) from rfl] at h_le
      rw [h_at_zero] at h_le
      linarith
    have h_kfact_D_pos : 0 < (k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k := by
      refine mul_pos ?_ ?_
      · exact_mod_cast Nat.factorial_pos k
      · exact pow_pos Φ.derivBoundMaxOne_pos k
    have h_k1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ k
    positivity
  set K_total : ℝ := K_leib_α * K_chain * K_leib_γ with hKtotal_def
  have hK_total_pos : 0 < K_total :=
    mul_pos (mul_pos hK_leib_α_pos hK_chain_pos) hK_leib_γ_pos
  refine ⟨K_total, hK_total_pos, ?_⟩
  intro v hv_mem
  set chartPushedγV : EuclN → ℝ :=
    chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ v
    with hchartPushedγV_def
  have hchartPushedγV_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p chartPushedγV Ωγ_target := hv_mem γ
  set ψ_γ_loc : EuclN → ℝ := fun y => η_γ_loc y * chartPushedγV y with hψγ_def
  have hψ_γ_loc_supp_in_η_γ : tsupport ψ_γ_loc ⊆ tsupport η_γ_loc := by
    refine closure_mono ?_
    intro y hy
    simp only [hψγ_def, Function.mem_support, ne_eq] at hy
    have h_η_ne : η_γ_loc y ≠ 0 := by
      intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hψ_γ_loc_supp_in_Ωγ : tsupport ψ_γ_loc ⊆ Ω_γ :=
    hψ_γ_loc_supp_in_η_γ.trans hη_γ_loc_supp_Ωγ
  have hψ_γ_loc_supp_in_Ωγ_target : tsupport ψ_γ_loc ⊆ Ωγ_target :=
    hψ_γ_loc_supp_in_η_γ.trans hη_γ_loc_supp_target
  have hψ_γ_loc_cpt : HasCompactSupport ψ_γ_loc :=
    hη_γ_loc_cpt.of_isClosed_subset (isClosed_tsupport _) hψ_γ_loc_supp_in_η_γ
  have hψ_γ_loc_mem_Ωγ_target : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p ψ_γ_loc Ωγ_target :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k hp_one hΩγ_target_open hη_γ_loc_smooth
      hη_γ_loc_iter_bound hchartPushedγV_mem
  have hψ_γ_loc_pair_Ωγ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_of_tsupport_subset_general
      (d := Module.finrank ℝ E) k hp_one hΩγ_target_open hΩγ_open
      hΩγ_subset_target hψ_γ_loc_mem_Ωγ_target hψ_γ_loc_supp_in_Ωγ
  have hψ_γ_loc_mem_Ωγ : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p ψ_γ_loc Ω_γ := hψ_γ_loc_pair_Ωγ.1
  have hψ_γ_loc_norm_target_eq_Ωγ :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p ψ_γ_loc Ωγ_target =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p ψ_γ_loc Ω_γ := hψ_γ_loc_pair_Ωγ.2
  set ψ_total : EuclN → ℝ := fun y => η_combined_α y * ψ_γ_loc (Φ.toFun y) with hψ_total_def
  have hψ_total_supp_in_η_combined_α : tsupport ψ_total ⊆ tsupport η_combined_α := by
    refine closure_mono ?_
    intro y hy
    simp only [hψ_total_def, Function.mem_support, ne_eq] at hy
    have h_η_ne : η_combined_α y ≠ 0 := by
      intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hψ_total_supp_Ωα : tsupport ψ_total ⊆ Ω_α :=
    hψ_total_supp_in_η_combined_α.trans hη_combined_α_supp_Ωα
  have hψ_total_supp_Ωα_target : tsupport ψ_total ⊆ Ωα_target :=
    hψ_total_supp_Ωα.trans hΩα_subset_target
  have hψ_total_cpt : HasCompactSupport ψ_total := by
    refine hη_combined_α_cpt.of_isClosed_subset (isClosed_tsupport _)
      hψ_total_supp_in_η_combined_α
  have h_ψγ_loc_comp_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p (fun y => ψ_γ_loc (Φ.toFun y)) Ω_α :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.comp_smoothDiffeoBoundedAtOrder
      (d := Module.finrank ℝ E) k (le_refl k) hp_one hp_top hΩα_open hΩγ_open Φ
      hψ_γ_loc_mem_Ωγ hψ_γ_loc_cpt hψ_γ_loc_supp_in_Ωγ
  have hψ_total_mem_Ωα :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p ψ_total Ω_α := by
    have h_bound : ∀ j ≤ k, ∀ y ∈ Ω_α,
        ‖iteratedFDeriv ℝ j η_combined_α y‖ ≤ C_combined_α :=
      hη_combined_α_iter_bound
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k hp_one hΩα_open hη_combined_α_smooth h_bound
      h_ψγ_loc_comp_mem
  have hψ_total_mem_Ωα_target :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p ψ_total Ωα_target :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) hp_one hp_top hΩα_open hΩα_target_open
      hΩα_subset_target hψ_total_mem_Ωα hψ_total_supp_Ωα hψ_total_cpt
  have h_pointwise_eq : ∀ y ∈ Ωα_target,
      chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)) y = ψ_total y := by
    intro y hy_target
    set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      have := hy_target
      rw [hΩα_target_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at this
      exact this
    have hz_source : z ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hsymm_target
    have hz_chartα : z ∈ (chartAt H α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hz_source
      exact hz_source
    have h_LHS_eq : chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x)) y =
        pou (I := I) (M := M) γ z *
          (chartStrictCutoff (I := I) (M := M) α z * v z) := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
    rw [h_LHS_eq]
    have hη_α_E_y : η_α_E y = chartStrictCutoff (I := I) (M := M) α z := by
      rw [hη_α_E_def]
      exact etaEuclid_apply_of_mem (I := I) (M := M) α
        (chartStrictCutoff (I := I) (M := M) α) hy_target
    have hψ_total_unfold : ψ_total y =
        η_α_loc y * η_α_E y * (η_γ_loc (Φ.toFun y) * chartPushedγV (Φ.toFun y)) := rfl
    rw [hψ_total_unfold, hη_α_E_y]
    by_cases hy_in_supp_η_α : y ∈ tsupport η_α_loc
    · have hy_in_Ωα : y ∈ Ω_α := hη_α_loc_supp_Ωα hy_in_supp_η_α
      by_cases hcutoff_zero : chartStrictCutoff (I := I) (M := M) α z = 0
      · rw [hcutoff_zero]; ring
      · have hz_in_tsupp_cut : z ∈ tsupport (chartStrictCutoff (I := I) (M := M) α) :=
          subset_tsupport _ (Function.mem_support.mpr hcutoff_zero)
        have hy_in_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) α γ :=
          hΩα_subset_overlap hy_in_Ωα
        have hz_chartγ : z ∈ (chartAt H γ).source := by
          rcases hy_in_overlap with ⟨w, ⟨x, hx_inter, hxw⟩, hwy⟩
          have hx_chart : x ∈ (chartAt H α).source := hx_inter.1
          have hx_chart_γ : x ∈ (chartAt H γ).source := hx_inter.2
          have hx_α_ext : x ∈ (extChartAt I α).source := by
            rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]
            exact hx_chart
          have hz_α_ext : z ∈ (extChartAt I α).source := by
            rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]
            exact hz_chartα
          have h_x_eq_chart : extChartAt I α x = (toEuclidean (E := E)).symm y := by
            rw [← hwy, ← hxw]
            exact ((toEuclidean (E := E)).symm_apply_apply (extChartAt I α x)).symm
          have h_z_eq_chart : extChartAt I α z = (toEuclidean (E := E)).symm y :=
            (extChartAt I α).right_inv hsymm_target
          have h_chart_eq : extChartAt I α x = extChartAt I α z := by
            rw [h_x_eq_chart, h_z_eq_chart]
          have h_x_eq_z := (extChartAt I α).injOn hx_α_ext hz_α_ext h_chart_eq
          rw [← h_x_eq_z]; exact hx_chart_γ
        have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I γ z) := by
          rw [hΦ_eq_on_Ωα y hy_in_Ωα]
          have h_z_chart : extChartAt I α z = (toEuclidean (E := E)).symm y :=
            (extChartAt I α).right_inv hsymm_target
          have hy_eq_α : (toEuclidean (E := E)) (extChartAt I α z) = y := by
            rw [h_z_chart]
            exact (toEuclidean (E := E)).apply_symm_apply y
          rw [← hy_eq_α]
          exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α γ hz_chartα
        rw [hΦ_y]
        have h_chartPushedγV_at_Φy :
            chartPushedγV ((toEuclidean (E := E)) (extChartAt I γ z)) =
              pou (I := I) (M := M) γ z * v z := by
          rw [hchartPushedγV_def]
          change ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M γ
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I γ).symm
              ((toEuclidean (E := E)).symm
                ((toEuclidean (E := E)) (extChartAt I γ z)))) *
            v ((extChartAt I γ).symm
              ((toEuclidean (E := E)).symm
                ((toEuclidean (E := E)) (extChartAt I γ z)))) = _
          rw [(toEuclidean (E := E)).symm_apply_apply]
          have hz_ext_γ : z ∈ (extChartAt I γ).source := by
            rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]
            exact hz_chartγ
          rw [(extChartAt I γ).left_inv hz_ext_γ]
          rfl
        rw [h_chartPushedγV_at_Φy]
        by_cases hpou_zero : pou (I := I) (M := M) γ z = 0
        · rw [hpou_zero]; ring
        · have hz_in_tsupp_pou : z ∈ tsupport (pou (I := I) (M := M) γ) :=
            subset_tsupport _ (Function.mem_support.mpr hpou_zero)
          have hz_in_KM : z ∈ K_M := ⟨hz_in_tsupp_pou, hz_in_tsupp_cut⟩
          have hy_in_KEα : y ∈ K_E_α := by
            refine ⟨z, hz_in_KM, ?_⟩
            change (toEuclidean (E := E)) (extChartAt I α z) = y
            have h_z_chart : extChartAt I α z = (toEuclidean (E := E)).symm y :=
              (extChartAt I α).right_inv hsymm_target
            rw [h_z_chart]
            exact (toEuclidean (E := E)).apply_symm_apply y
          have hη_α_loc_y : η_α_loc y = 1 := by
            apply hη_α_loc_one
            exact Metric.self_subset_cthickening K_E_α hy_in_KEα
          rw [hη_α_loc_y]
          have h_Φy_in_KEγ : (toEuclidean (E := E)) (extChartAt I γ z) ∈ K_E_γ :=
            ⟨z, hz_in_KM, rfl⟩
          have hη_γ_loc_Φy : η_γ_loc ((toEuclidean (E := E)) (extChartAt I γ z)) = 1 := by
            apply hη_γ_loc_one
            exact Metric.self_subset_cthickening K_E_γ h_Φy_in_KEγ
          rw [hη_γ_loc_Φy]
          ring
    · have h_zero : η_α_loc y = 0 := image_eq_zero_of_notMem_tsupport hy_in_supp_η_α
      rw [h_zero]; simp only [zero_mul]
      by_cases hpou_zero : pou (I := I) (M := M) γ z = 0
      · rw [hpou_zero]; ring
      · by_cases hcutoff_zero : chartStrictCutoff (I := I) (M := M) α z = 0
        · rw [hcutoff_zero]; ring
        · exfalso
          have hz_in_tsupp_pou : z ∈ tsupport (pou (I := I) (M := M) γ) :=
            subset_tsupport _ (Function.mem_support.mpr hpou_zero)
          have hz_in_tsupp_cut : z ∈ tsupport (chartStrictCutoff (I := I) (M := M) α) :=
            subset_tsupport _ (Function.mem_support.mpr hcutoff_zero)
          have hz_in_KM : z ∈ K_M := ⟨hz_in_tsupp_pou, hz_in_tsupp_cut⟩
          have hy_in_KEα : y ∈ K_E_α := by
            refine ⟨z, hz_in_KM, ?_⟩
            change (toEuclidean (E := E)) (extChartAt I α z) = y
            have h_z_chart : extChartAt I α z = (toEuclidean (E := E)).symm y :=
              (extChartAt I α).right_inv hsymm_target
            rw [h_z_chart]
            exact (toEuclidean (E := E)).apply_symm_apply y
          have hy_in_cthick : y ∈ Metric.cthickening δ_α K_E_α :=
            Metric.self_subset_cthickening K_E_α hy_in_KEα
          have h_η_y_one : η_α_loc y = 1 := hη_α_loc_one y hy_in_cthick
          have h_ne_zero : η_α_loc y ≠ 0 := by linarith
          have hy_in_supp : y ∈ Function.support η_α_loc := by
            simp only [Function.mem_support, ne_eq, h_ne_zero, not_false_eq_true]
          exact hy_in_supp_η_α (subset_tsupport _ hy_in_supp)
  have h_ae_eq : (chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x))) =ᵐ[volume.restrict Ωα_target]
      ψ_total := by
    refine (ae_restrict_iff' hΩα_target_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy; exact h_pointwise_eq y hy
  have h_pushed_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x)))
      Ωα_target := by
    refine (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp_one hΩα_target_open h_ae_eq.symm).mp ?_
    exact hψ_total_mem_Ωα_target
  have h_pushedRaw_supp_KE_α :
      tsupport (chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x))) ⊆ K_E_α := by
    have h_zero_off_KE_α :
        ∀ y : EuclN, y ∉ K_E_α →
        chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)) y = 0 := by
      intro y hy_off
      by_cases hy_target : y ∈ Ωα_target
      · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
        set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
        have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
          rw [hΩα_target_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
          exact hy_target
        have hz_not_in_KM : z ∉ K_M := by
          intro hz_in_KM
          apply hy_off
          refine ⟨z, hz_in_KM, ?_⟩
          change (toEuclidean (E := E)) (extChartAt I α z) = y
          have h_z_chart : extChartAt I α z = (toEuclidean (E := E)).symm y :=
            (extChartAt I α).right_inv hsymm_target
          rw [h_z_chart]
          exact (toEuclidean (E := E)).apply_symm_apply y
        exact prod_pou_strictCutoff_v_eq_zero_off γ α v hz_not_in_KM
      · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy_target
    have h_supp_sub : Function.support
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x))) ⊆ K_E_α := by
      intro y hy
      by_contra hy_off
      exact hy (h_zero_off_KE_α y hy_off)
    exact closure_minimal h_supp_sub hKEα_compact.isClosed
  have h_pushedRaw_cpt : HasCompactSupport
      (chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x))) :=
    hKEα_compact.of_isClosed_subset (isClosed_tsupport _) h_pushedRaw_supp_KE_α
  have h_pushedRaw_supp_Ωα_target :
      tsupport (chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x))) ⊆ Ωα_target :=
    h_pushedRaw_supp_KE_α.trans hKEα_subset_target
  refine ⟨h_pushed_mem, h_pushedRaw_cpt, h_pushedRaw_supp_Ωα_target, ?_⟩
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one hΩα_target_open h_ae_eq]
  have h_bridge_α :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p ψ_total Ωα_target ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p ψ_total Ω_α :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_le_of_tsupport_subset_mem_small_general
      (d := Module.finrank ℝ E) k hp_one hΩα_target_open hΩα_open
      hΩα_subset_target hψ_total_mem_Ωα hψ_total_supp_Ωα
  refine h_bridge_α.trans ?_
  have h_leib_step : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p ψ_total Ω_α ≤
      ENNReal.ofReal K_leib_α *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p (fun y => ψ_γ_loc (Φ.toFun y)) Ω_α :=
    hK_leib_α_bound h_ψγ_loc_comp_mem
  refine h_leib_step.trans ?_
  have h_chain_step :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p (fun y => ψ_γ_loc (Φ.toFun y)) Ω_α ≤
      ENNReal.ofReal K_chain *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p ψ_γ_loc Ω_γ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpNorm_comp_le
      hp_one hp_top hΩα_open hΩγ_open Φ k (le_refl k)
      hψ_γ_loc_mem_Ωγ hψ_γ_loc_cpt hψ_γ_loc_supp_in_Ωγ
  have h_chain_step_target :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p (fun y => ψ_γ_loc (Φ.toFun y)) Ω_α ≤
      ENNReal.ofReal K_chain *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p ψ_γ_loc Ωγ_target := by
    refine h_chain_step.trans ?_
    rw [hψ_γ_loc_norm_target_eq_Ωγ]
  have h_leib_γ_step :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p ψ_γ_loc Ωγ_target ≤
      ENNReal.ofReal K_leib_γ *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p chartPushedγV Ωγ_target := by
    have h_eq : ψ_γ_loc = (fun y => η_γ_loc y * chartPushedγV y) := rfl
    rw [h_eq]
    exact hK_leib_γ_bound hchartPushedγV_mem
  have h_chain_combined :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p (fun y => ψ_γ_loc (Φ.toFun y)) Ω_α ≤
      ENNReal.ofReal K_chain *
        (ENNReal.ofReal K_leib_γ *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p chartPushedγV Ωγ_target) := by
    refine h_chain_step_target.trans ?_
    exact mul_le_mul_of_nonneg_left h_leib_γ_step (zero_le _)
  refine (mul_le_mul_of_nonneg_left h_chain_combined (zero_le _)).trans ?_
  have h_K_eq : ENNReal.ofReal K_leib_α *
      (ENNReal.ofReal K_chain * (ENNReal.ofReal K_leib_γ *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p chartPushedγV Ωγ_target)) =
      ENNReal.ofReal K_total *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p chartPushedγV Ωγ_target := by
    rw [hKtotal_def]
    rw [ENNReal.ofReal_mul (mul_pos hK_leib_α_pos hK_chain_pos).le]
    rw [ENNReal.ofReal_mul hK_leib_α_pos.le]
    ring
  exact h_K_eq ▸ le_refl _

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
theorem memWkp_finset_sum
    [NeZero (Module.finrank ℝ E)]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set EuclN} (hΩ : IsOpen Ω)
    {S : Finset M} {f : M → EuclN → ℝ}
    (hf_mem : ∀ γ ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p (f γ) Ω) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p (fun y => ∑ γ ∈ S, f γ y) Ω := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
        (d := Module.finrank ℝ E) hp_one hΩ
  | insert δ T hδ ih =>
      have hf_δ_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p (f δ) Ω :=
        hf_mem δ (Finset.mem_insert_self δ T)
      have h_T_mem : ∀ ε ∈ T,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p (f ε) Ω := fun ε hε =>
        hf_mem ε (Finset.mem_insert_of_mem hε)
      have h_sumT_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p
          (fun y => ∑ ε ∈ T, f ε y) Ω := ih h_T_mem
      have h_eq : (fun y : EuclN => ∑ ε ∈ insert δ T, f ε y) =
          (fun y : EuclN => f δ y + ∑ ε ∈ T, f ε y) := by
        funext y; rw [Finset.sum_insert hδ]
      rw [h_eq]
      exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
        (d := Module.finrank ℝ E) hp_one hΩ hf_δ_mem h_sumT_mem

omit [IsManifold I ∞ M] in
theorem wkpNorm_finset_sum_le_chartTarget
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {S : Finset M} {f : M → EuclN → ℝ}
    (hf_mem : ∀ γ ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p (f γ) (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p (fun y => ∑ γ ∈ S, f γ y)
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑ γ ∈ S,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p (f γ) (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  induction S using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
        (d := Module.finrank ℝ E) hp_one hΩ_open]
  | insert γ S hγ ih =>
      have h_S_mem : ∀ δ ∈ S,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p (f δ) Ω := fun δ hδ =>
        hf_mem δ (Finset.mem_insert_of_mem hδ)
      have hf_γ_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p (f γ) Ω := hf_mem γ (Finset.mem_insert_self γ S)
      have h_sumS_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p
          (fun y => ∑ δ ∈ S, f δ y) Ω :=
        memWkp_finset_sum (k := k) hp_one hΩ_open h_S_mem
      have h_eq_sum : (fun y : EuclN => ∑ δ ∈ insert γ S, f δ y) =
          (fun y : EuclN => f γ y + ∑ δ ∈ S, f δ y) := by
        funext y; rw [Finset.sum_insert hγ]
      rw [h_eq_sum]
      have h_triangle :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
          (d := Module.finrank ℝ E) hp_one hΩ_open hf_γ_mem h_sumS_mem
      have h_ih := ih h_S_mem
      have h_RHS_eq : ∑ δ ∈ insert γ S,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p (f δ) Ω =
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p (f γ) Ω +
            ∑ δ ∈ S,
              DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := Module.finrank ℝ E) k p (f δ) Ω := by
        rw [Finset.sum_insert hγ]
      rw [h_RHS_eq]
      have h_step : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p (f γ) Ω +
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p (fun y => ∑ δ ∈ S, f δ y) Ω ≤
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p (f γ) Ω +
            ∑ δ ∈ S,
              DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := Module.finrank ℝ E) k p (f δ) Ω := by
        exact add_le_add le_rfl h_ih
      exact h_triangle.trans h_step

theorem wkpNorm_chartPushedRaw_strictCutoff_mul_le
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ {v : M → ℝ}, MemWkpChart (I := I) (M := M) g k p v →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x => chartStrictCutoff (I := I) (M := M) α x * v x))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C *
        wkpNormChart (I := I) (M := M) g k p v := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M)
    with hS_def
  have h_per_γ : ∀ γ : M, ∃ Cγ : ℝ, 0 < Cγ ∧
      ∀ {v : M → ℝ}, MemWkpChart (I := I) (M := M) g k p v →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p
          (chartPushedRaw (I := I) (M := M) α
            (fun x => pou (I := I) (M := M) γ x *
              (chartStrictCutoff (I := I) (M := M) α x * v x)))
          (chartTargetEuclid (I := I) (M := M) α) ∧
        HasCompactSupport
          (chartPushedRaw (I := I) (M := M) α
            (fun x => pou (I := I) (M := M) γ x *
              (chartStrictCutoff (I := I) (M := M) α x * v x))) ∧
        tsupport
          (chartPushedRaw (I := I) (M := M) α
            (fun x => pou (I := I) (M := M) γ x *
              (chartStrictCutoff (I := I) (M := M) α x * v x))) ⊆
          chartTargetEuclid (I := I) (M := M) α ∧
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushedRaw (I := I) (M := M) α
            (fun x => pou (I := I) (M := M) γ x *
              (chartStrictCutoff (I := I) (M := M) α x * v x)))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal Cγ *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ v)
            (chartTargetEuclid (I := I) (M := M) γ) := fun γ =>
    cross_chart_strictCutoff_pushedRaw_joint (I := I) (M := M) g k hp_one hp_top γ α
  let Cγ : M → ℝ := fun γ => (h_per_γ γ).choose
  have hCγ_pos : ∀ γ : M, 0 < Cγ γ := fun γ => (h_per_γ γ).choose_spec.1
  have hCγ_bound : ∀ γ : M, ∀ {v : M → ℝ}, MemWkpChart (I := I) (M := M) g k p v →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)))
        (chartTargetEuclid (I := I) (M := M) α) ∧
      HasCompactSupport _ ∧ tsupport _ ⊆ _ ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Cγ γ) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ v)
          (chartTargetEuclid (I := I) (M := M) γ) := fun γ => (h_per_γ γ).choose_spec.2
  by_cases hS_empty : S = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro v _
    exfalso
    have h_sum_one : ∑ γ ∈ S, pou (I := I) (M := M) γ α = 1 := by
      unfold pou
      rw [hS_def]
      exact chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) α
    rw [hS_empty, Finset.sum_empty] at h_sum_one
    exact absurd h_sum_one (by norm_num)
  have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  set Cmax : ℝ := S.sup' hS_nonempty Cγ with hCmax_def
  have hCmax_ge : ∀ γ ∈ S, Cγ γ ≤ Cmax := fun γ hγ => Finset.le_sup' Cγ hγ
  have hCmax_pos : 0 < Cmax := by
    obtain ⟨γ₀, hγ₀⟩ := hS_nonempty
    exact lt_of_lt_of_le (hCγ_pos γ₀) (hCmax_ge γ₀ hγ₀)
  refine ⟨Cmax, hCmax_pos, ?_⟩
  intro v hv
  have h_pw_sum : ∀ y : EuclN,
      chartPushedRaw (I := I) (M := M) α
          (fun x => chartStrictCutoff (I := I) (M := M) α x * v x) y =
      ∑ γ ∈ S,
        chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)) y :=
    fun y => chartPushedRaw_strictCutoff_eq_finset_sum (I := I) (M := M) α v y
  set Ωα_target : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩα_target_def
  have hΩα_target_open : IsOpen Ωα_target := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_pw_eq : (chartPushedRaw (I := I) (M := M) α
      (fun x => chartStrictCutoff (I := I) (M := M) α x * v x)) =
    (fun y : EuclN => ∑ γ ∈ S,
      chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x)) y) := funext h_pw_sum
  rw [h_pw_eq]
  have h_per_γ_mem : ∀ γ ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)))
        Ωα_target := fun γ _ => (hCγ_bound γ hv).1
  have h_triangle := wkpNorm_finset_sum_le_chartTarget (I := I) (M := M) (α := α)
    k hp_one (S := S) (f := fun γ y =>
      chartPushedRaw (I := I) (M := M) α
        (fun x => pou (I := I) (M := M) γ x *
          (chartStrictCutoff (I := I) (M := M) α x * v x)) y) h_per_γ_mem
  refine h_triangle.trans ?_
  have h_bound_each : ∀ γ ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)))
        Ωα_target ≤
      ENNReal.ofReal Cmax *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ v)
          (chartTargetEuclid (I := I) (M := M) γ) := by
    intro γ hγ
    refine (hCγ_bound γ hv).2.2.2.trans ?_
    have h_ofReal_le : ENNReal.ofReal (Cγ γ) ≤ ENNReal.ofReal Cmax :=
      ENNReal.ofReal_le_ofReal (hCmax_ge γ hγ)
    exact mul_le_mul_of_nonneg_right h_ofReal_le (zero_le _)
  have h_sum_bound : ∑ γ ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x => pou (I := I) (M := M) γ x *
            (chartStrictCutoff (I := I) (M := M) α x * v x)))
        Ωα_target ≤
      ∑ γ ∈ S,
        ENNReal.ofReal Cmax *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ v)
            (chartTargetEuclid (I := I) (M := M) γ) := Finset.sum_le_sum h_bound_each
  refine h_sum_bound.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  unfold wkpNormChart
  exact ENNReal.sum_le_tsum S

end Chart
end Sobolev
end Analysis
end DifferentialGeometry

end
