import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function Metric
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

omit [IsManifold I ∞ M] in
private lemma chartTransitionEuclid_comp_eq_id_on_overlap
    [I.Boundaryless]
    (γ α : M) {y : EuclN}
    (hy : y ∈ chartOverlapEuclid (I := I) (M := M) γ α) :
    (fun z => chartTransitionEuclid (I := I) (M := M) α γ
        (chartTransitionEuclid (I := I) (M := M) γ α z)) y = y :=
  chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy

omit [IsManifold I ∞ M] in
private lemma chartTransitionEuclid_comp_eventuallyEq_id
    [I.Boundaryless]
    (γ α : M) {y : EuclN}
    (hy : y ∈ chartOverlapEuclid (I := I) (M := M) γ α) :
    (fun z => chartTransitionEuclid (I := I) (M := M) α γ
        (chartTransitionEuclid (I := I) (M := M) γ α z))
      =ᶠ[𝓝 y] (fun z : EuclN => z) := by
  have h_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  refine Filter.eventually_of_mem (h_open.mem_nhds hy) ?_
  intro z hz
  exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hz

private lemma chartTransitionEuclid_differentiableAt_of_mem
    [I.Boundaryless]
    (γ α : M) {y : EuclN}
    (hy : y ∈ chartOverlapEuclid (I := I) (M := M) γ α) :
    DifferentiableAt ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y := by
  have h_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  have h_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α
  have h_diffOn : DifferentiableOn ℝ
      (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    h_smooth.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h_diffWithin : DifferentiableWithinAt ℝ
      (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) y :=
    h_diffOn y hy
  exact h_diffWithin.differentiableAt (h_open.mem_nhds hy)

private lemma chartTransitionEuclid_det_fderiv_ne_zero
    [I.Boundaryless]
    (γ α : M) {y : EuclN}
    (hy : y ∈ chartOverlapEuclid (I := I) (M := M) γ α) :
    (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det ≠ 0 := by
  classical
  have h_T_in : chartTransitionEuclid (I := I) (M := M) γ α y ∈
      chartOverlapEuclid (I := I) (M := M) α γ :=
    chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy
  have h_diff_T_γα : DifferentiableAt ℝ
      (chartTransitionEuclid (I := I) (M := M) γ α) y :=
    chartTransitionEuclid_differentiableAt_of_mem (I := I) (M := M) γ α hy
  have h_diff_T_αγ : DifferentiableAt ℝ
      (chartTransitionEuclid (I := I) (M := M) α γ)
      (chartTransitionEuclid (I := I) (M := M) γ α y) :=
    chartTransitionEuclid_differentiableAt_of_mem (I := I) (M := M) α γ h_T_in
  have h_fderiv_comp :
      fderiv ℝ (fun z => chartTransitionEuclid (I := I) (M := M) α γ
          (chartTransitionEuclid (I := I) (M := M) γ α z)) y =
        (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :=
    fderiv_comp y h_diff_T_αγ h_diff_T_γα
  have h_evt : (fun z => chartTransitionEuclid (I := I) (M := M) α γ
        (chartTransitionEuclid (I := I) (M := M) γ α z))
      =ᶠ[𝓝 y] (fun z : EuclN => z) :=
    chartTransitionEuclid_comp_eventuallyEq_id (I := I) (M := M) γ α hy
  have h_fderiv_id :
      fderiv ℝ (fun z => chartTransitionEuclid (I := I) (M := M) α γ
          (chartTransitionEuclid (I := I) (M := M) γ α z)) y =
        ContinuousLinearMap.id ℝ EuclN := by
    rw [h_evt.fderiv_eq]
    exact fderiv_id'
  have h_comp_eq :
      (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
          (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
        (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) =
      ContinuousLinearMap.id ℝ EuclN := by
    rw [← h_fderiv_comp]; exact h_fderiv_id
  have h_det_comp : (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
          (chartTransitionEuclid (I := I) (M := M) γ α y)).det *
      (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det = 1 := by
    have h_lin :
        ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
              EuclN →ₗ[ℝ] EuclN) =
        ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartTransitionEuclid (I := I) (M := M) γ α y) :
              EuclN →ₗ[ℝ] EuclN)).comp
          ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
              EuclN →ₗ[ℝ] EuclN) := rfl
    have h_det_id : ((ContinuousLinearMap.id ℝ EuclN) : EuclN →ₗ[ℝ] EuclN).det = 1 := by
      change LinearMap.det (LinearMap.id : EuclN →ₗ[ℝ] EuclN) = 1
      exact LinearMap.det_id
    have h_det_comp_lin :
        LinearMap.det
          (((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
              (chartTransitionEuclid (I := I) (M := M) γ α y)) :
                EuclN →ₗ[ℝ] EuclN).comp
            ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                EuclN →ₗ[ℝ] EuclN)) =
          LinearMap.det
            ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
              (chartTransitionEuclid (I := I) (M := M) γ α y)) :
                EuclN →ₗ[ℝ] EuclN) *
          LinearMap.det
            ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                EuclN →ₗ[ℝ] EuclN) :=
      LinearMap.det_comp _ _
    have hcomp_det :
        LinearMap.det
          (((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
              (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
            (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y)) :
              EuclN →ₗ[ℝ] EuclN) =
          LinearMap.det ((ContinuousLinearMap.id ℝ EuclN) : EuclN →ₗ[ℝ] EuclN) := by
      rw [h_comp_eq]
    rw [h_lin, h_det_comp_lin, h_det_id] at hcomp_det
    change (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
        (chartTransitionEuclid (I := I) (M := M) γ α y)).det *
        (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det = 1
    exact hcomp_det
  intro h_zero
  rw [h_zero, mul_zero] at h_det_comp
  exact zero_ne_one h_det_comp

private lemma abs_det_fderiv_chartTransitionEuclid_continuousOn
    [I.Boundaryless]
    (γ α : M) :
    ContinuousOn (fun y => |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det|)
      (chartOverlapEuclid (I := I) (M := M) γ α) := by
  have h_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  have h_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α
  have h_cont_fderiv : ContinuousOn
      (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α))
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
    h_smooth.continuousOn_fderiv_of_isOpen h_open
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have h_cont_det : Continuous (fun A : EuclN →L[ℝ] EuclN => A.det) :=
    ContinuousLinearMap.continuous_det
  have h_cont_abs : Continuous (fun r : ℝ => |r|) := continuous_abs
  exact (h_cont_abs.comp h_cont_det).continuousOn.comp h_cont_fderiv (Set.mapsTo_univ _ _)

private lemma chartTransitionEuclid_continuousOn_overlap
    [I.Boundaryless]
    (γ α : M) :
    ContinuousOn (chartTransitionEuclid (I := I) (M := M) γ α)
      (chartOverlapEuclid (I := I) (M := M) γ α) :=
  (chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α).continuousOn

theorem chartTransition_smoothDiffeoBoundedAtOrder
    [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (γ α : M)
    {K : Set M} (hK_compact : IsCompact K)
    (hK_γ : K ⊆ (chartAt H γ).source)
    (hK_α : K ⊆ (chartAt H α).source)
    (kmax : ℕ) :
    ∃ (Ω_γα Ω_αγ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (_hΩ_γα : IsOpen Ω_γα) (_hΩ_αγ : IsOpen Ω_αγ),
      ((toEuclidean : E ≃L[ℝ] _) ∘ extChartAt I γ) '' K ⊆ Ω_γα ∧
      ∃ (Φ : DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder
          (Module.finrank ℝ E) Ω_γα Ω_αγ kmax),
        ∀ x ∈ K,
          Φ.toFun ((toEuclidean ∘ extChartAt I γ) x) =
            (toEuclidean ∘ extChartAt I α) x := by
  classical
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K with hKEγ_def
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K with hKEα_def
  have hKEγ_compact : IsCompact K_E_γ :=
    kEuclid_compact (I := I) (M := M) γ hK_compact hK_γ
  have hKEγ_subset_overlap_γα : K_E_γ ⊆ chartOverlapEuclid (I := I) (M := M) γ α :=
    kEuclid_subset_overlap (I := I) (M := M) γ α hK_γ hK_α
  have hOverlap_γα_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  have hKEα_compact : IsCompact K_E_α :=
    kEuclid_compact (I := I) (M := M) α hK_compact hK_α
  have hKEα_subset_overlap_αγ : K_E_α ⊆ chartOverlapEuclid (I := I) (M := M) α γ :=
    kEuclid_subset_overlap (I := I) (M := M) α γ hK_α hK_γ
  have hOverlap_αγ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) α γ) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) α γ
  obtain ⟨δ_γ, η_γ, hδ_γ_pos, hδγ_subset, hη_γ_smooth, hη_γ_cpt, hη_γ_range,
      hη_γ_one, hη_γ_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E)
      hKEγ_compact hOverlap_γα_open hKEγ_subset_overlap_γα
  have hδ_γ_half_pos : 0 < δ_γ / 2 := by linarith
  set Ω_γα : Set EuclN := Metric.thickening (δ_γ / 2) K_E_γ with hΩγα_def
  have hΩγα_open : IsOpen Ω_γα := Metric.isOpen_thickening
  have hKEγ_subset_Ωγα : K_E_γ ⊆ Ω_γα := Metric.self_subset_thickening hδ_γ_half_pos K_E_γ
  have hΩγα_closure_subset_cthick_half :
      closure Ω_γα ⊆ Metric.cthickening (δ_γ / 2) K_E_γ :=
    Metric.closure_thickening_subset_cthickening (δ_γ / 2) K_E_γ
  have hcthick_half_subset_full :
      Metric.cthickening (δ_γ / 2) K_E_γ ⊆ Metric.cthickening δ_γ K_E_γ :=
    Metric.cthickening_mono (by linarith : δ_γ / 2 ≤ δ_γ) K_E_γ
  have hΩγα_closure_subset_cthick :
      closure Ω_γα ⊆ Metric.cthickening δ_γ K_E_γ :=
    hΩγα_closure_subset_cthick_half.trans hcthick_half_subset_full
  have hΩγα_closure_subset_overlap : closure Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α :=
    hΩγα_closure_subset_cthick.trans hδγ_subset
  have hcthick_compact : IsCompact (Metric.cthickening (δ_γ / 2) K_E_γ) :=
    hKEγ_compact.cthickening
  have hΩγα_closure_compact : IsCompact (closure Ω_γα) :=
    hcthick_compact.of_isClosed_subset isClosed_closure hΩγα_closure_subset_cthick_half
  have hΩγα_subset_cthick : Ω_γα ⊆ Metric.cthickening δ_γ K_E_γ := by
    refine subset_trans (Metric.thickening_subset_cthickening (δ_γ / 2) K_E_γ) ?_
    exact hcthick_half_subset_full
  set c_γ : EuclN := chartCenterEuclid (I := I) (M := M) α with hcγ_def
  set T_γα : EuclN → EuclN :=
    chartTransitionExtended (I := I) (M := M) γ α η_γ c_γ with hTγα_def
  have hT_γα_smooth : ContDiff ℝ (⊤ : ℕ∞) T_γα :=
    chartTransitionExtended_contDiff (I := I) (M := M) γ α
      hη_γ_smooth hη_γ_supp c_γ
  have hT_γα_eq_on_Ωγα : ∀ y ∈ Ω_γα,
      T_γα y = chartTransitionEuclid (I := I) (M := M) γ α y := by
    intro y hy
    have hy_cthick : y ∈ Metric.cthickening δ_γ K_E_γ := hΩγα_subset_cthick hy
    have hηy : η_γ y = 1 := hη_γ_one y hy_cthick
    exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
      (I := I) (M := M) γ α c_γ hηy
  have hT_γα_image_eq :
      T_γα '' Ω_γα = (chartTransitionEuclid (I := I) (M := M) γ α) '' Ω_γα := by
    apply Set.image_congr
    exact hT_γα_eq_on_Ωγα
  set Ω_αγ : Set EuclN :=
    (chartTransitionEuclid (I := I) (M := M) γ α) '' Ω_γα with hΩαγ_def
  have hΩαγ_subset_overlap_αγ : Ω_αγ ⊆ chartOverlapEuclid (I := I) (M := M) α γ := by
    intro z hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := by
      have : y ∈ closure Ω_γα := subset_closure hy_Ωγα
      exact hΩγα_closure_subset_overlap this
    rw [← hyz]
    exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy_overlap
  have hΩαγ_eq_preimage :
      Ω_αγ = (chartTransitionEuclid (I := I) (M := M) α γ ⁻¹' Ω_γα) ∩
              chartOverlapEuclid (I := I) (M := M) α γ := by
    ext z
    refine ⟨?_, ?_⟩
    · intro hz
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := by
        have hy_cl : y ∈ closure Ω_γα := subset_closure hy_Ωγα
        exact hΩγα_closure_subset_overlap hy_cl
      have hz_overlap : z ∈ chartOverlapEuclid (I := I) (M := M) α γ := by
        rw [← hyz]
        exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy_overlap
      refine ⟨?_, hz_overlap⟩
      have h_inv : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
        rw [← hyz]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
      simp only [Set.mem_preimage, h_inv]
      exact hy_Ωγα
    · rintro ⟨hz_pre, hz_overlap⟩
      simp only [Set.mem_preimage] at hz_pre
      have h_T_αγ_z_overlap : chartTransitionEuclid (I := I) (M := M) α γ z ∈
          chartOverlapEuclid (I := I) (M := M) γ α := by
        have : chartTransitionEuclid (I := I) (M := M) α γ z ∈ closure Ω_γα :=
          subset_closure hz_pre
        exact hΩγα_closure_subset_overlap this
      have h_left_inv :
          chartTransitionEuclid (I := I) (M := M) γ α
            (chartTransitionEuclid (I := I) (M := M) α γ z) = z :=
        chartTransitionEuclid_left_inv (I := I) (M := M) α γ hz_overlap
      refine ⟨chartTransitionEuclid (I := I) (M := M) α γ z, hz_pre, h_left_inv⟩
  have hT_αγ_continuousOn :
      ContinuousOn (chartTransitionEuclid (I := I) (M := M) α γ)
        (chartOverlapEuclid (I := I) (M := M) α γ) :=
    chartTransitionEuclid_continuousOn_overlap (I := I) (M := M) α γ
  have hΩαγ_open : IsOpen Ω_αγ := by
    rw [hΩαγ_eq_preimage]
    rw [Set.inter_comm]
    exact hT_αγ_continuousOn.isOpen_inter_preimage hOverlap_αγ_open hΩγα_open
  set L_αγ : Set EuclN :=
    (chartTransitionEuclid (I := I) (M := M) γ α) '' (closure Ω_γα) with hLαγ_def
  have hL_αγ_compact : IsCompact L_αγ :=
    hΩγα_closure_compact.image_of_continuousOn
      ((chartTransitionEuclid_continuousOn_overlap (I := I) (M := M) γ α).mono
        hΩγα_closure_subset_overlap)
  have hL_αγ_subset_overlap_αγ : L_αγ ⊆ chartOverlapEuclid (I := I) (M := M) α γ := by
    intro z hz
    rcases hz with ⟨y, hy_cl, hyz⟩
    rw [← hyz]
    exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α
      (hΩγα_closure_subset_overlap hy_cl)
  have hΩαγ_subset_Lαγ : Ω_αγ ⊆ L_αγ := by
    intro z hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    refine ⟨y, subset_closure hy_Ωγα, hyz⟩
  obtain ⟨δ_α, η_α, hδ_α_pos, hδα_subset, hη_α_smooth, hη_α_cpt, hη_α_range,
      hη_α_one, hη_α_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E)
      hL_αγ_compact hOverlap_αγ_open hL_αγ_subset_overlap_αγ
  have hL_αγ_subset_cthick_α : L_αγ ⊆ Metric.cthickening δ_α L_αγ :=
    Metric.self_subset_cthickening L_αγ
  have hΩαγ_subset_cthick_α : Ω_αγ ⊆ Metric.cthickening δ_α L_αγ :=
    hΩαγ_subset_Lαγ.trans hL_αγ_subset_cthick_α
  set c_α : EuclN := chartCenterEuclid (I := I) (M := M) γ with hcα_def
  set T_αγ : EuclN → EuclN :=
    chartTransitionExtended (I := I) (M := M) α γ η_α c_α with hTαγ_def
  have hT_αγ_smooth : ContDiff ℝ (⊤ : ℕ∞) T_αγ :=
    chartTransitionExtended_contDiff (I := I) (M := M) α γ
      hη_α_smooth hη_α_supp c_α
  have hT_αγ_eq_on_Ωαγ : ∀ z ∈ Ω_αγ,
      T_αγ z = chartTransitionEuclid (I := I) (M := M) α γ z := by
    intro z hz
    have hz_cthick : z ∈ Metric.cthickening δ_α L_αγ := hΩαγ_subset_cthick_α hz
    have hηz : η_α z = 1 := hη_α_one z hz_cthick
    exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
      (I := I) (M := M) α γ c_α hηz
  have hBijOn_T_γα : Set.BijOn T_γα Ω_γα Ω_αγ := by
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rw [hT_γα_eq_on_Ωγα y hy]
      exact ⟨y, hy, rfl⟩
    · intro y₁ hy₁ y₂ hy₂ heq
      rw [hT_γα_eq_on_Ωγα y₁ hy₁, hT_γα_eq_on_Ωγα y₂ hy₂] at heq
      have hy₁_overlap : y₁ ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy₁)
      have hy₂_overlap : y₂ ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy₂)
      exact chartTransitionEuclid_injOn_overlap (I := I) (M := M) γ α
        hy₁_overlap hy₂_overlap heq
    · intro z hz
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      refine ⟨y, hy_Ωγα, ?_⟩
      rw [hT_γα_eq_on_Ωγα y hy_Ωγα]; exact hyz
  have hBijOn_T_αγ : Set.BijOn T_αγ Ω_αγ Ω_γα := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [hT_αγ_eq_on_Ωαγ z hz]
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
      have h_inv : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
        rw [← hyz]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
      rw [h_inv]; exact hy_Ωγα
    · intro z₁ hz₁ z₂ hz₂ heq
      rw [hT_αγ_eq_on_Ωαγ z₁ hz₁, hT_αγ_eq_on_Ωαγ z₂ hz₂] at heq
      have hz₁_overlap : z₁ ∈ chartOverlapEuclid (I := I) (M := M) α γ :=
        hΩαγ_subset_overlap_αγ hz₁
      have hz₂_overlap : z₂ ∈ chartOverlapEuclid (I := I) (M := M) α γ :=
        hΩαγ_subset_overlap_αγ hz₂
      exact chartTransitionEuclid_injOn_overlap (I := I) (M := M) α γ
        hz₁_overlap hz₂_overlap heq
    · intro y hy_Ωγα
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
      refine ⟨chartTransitionEuclid (I := I) (M := M) γ α y, ?_, ?_⟩
      · exact ⟨y, hy_Ωγα, rfl⟩
      · have h_z_in_Ωαγ : chartTransitionEuclid (I := I) (M := M) γ α y ∈ Ω_αγ :=
          ⟨y, hy_Ωγα, rfl⟩
        rw [hT_αγ_eq_on_Ωαγ _ h_z_in_Ωαγ]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
  have hLeft_inv : Set.LeftInvOn T_αγ T_γα Ω_γα := by
    intro y hy
    rw [hT_γα_eq_on_Ωγα y hy]
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
      hΩγα_closure_subset_overlap (subset_closure hy)
    have h_T_γα_y_in_Ωαγ : chartTransitionEuclid (I := I) (M := M) γ α y ∈ Ω_αγ :=
      ⟨y, hy, rfl⟩
    rw [hT_αγ_eq_on_Ωαγ _ h_T_γα_y_in_Ωαγ]
    exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
  have hRight_inv : Set.RightInvOn T_αγ T_γα Ω_αγ := by
    intro z hz
    have hz_orig : z ∈ Ω_αγ := hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
      hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
    rw [hT_αγ_eq_on_Ωαγ _ hz_orig]
    have h_T_αγ_z_eq_y : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
      rw [← hyz]
      exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
    rw [h_T_αγ_z_eq_y]
    rw [hT_γα_eq_on_Ωγα y hy_Ωγα]
    exact hyz
  obtain ⟨B_γ, hBγ_pos, hBγ_bound⟩ :=
    chartTransitionExtended_iter_deriv_bound (I := I) (M := M) γ α
      hη_γ_smooth hη_γ_cpt hη_γ_supp c_γ kmax
  obtain ⟨B_α, hBα_pos, hBα_bound⟩ :=
    chartTransitionExtended_iter_deriv_bound (I := I) (M := M) α γ
      hη_α_smooth hη_α_cpt hη_α_supp c_α kmax
  set B : ℝ := max B_γ B_α with hB_def
  have hB_pos : 0 < B := lt_of_lt_of_le hBγ_pos (le_max_left _ _)
  have hB_γ_bound : ∀ i, i ≤ kmax → ∀ x : EuclN,
      ‖iteratedFDeriv ℝ i T_γα x‖ ≤ B := by
    intro i hi x
    exact (hBγ_bound i hi x).trans (le_max_left _ _)
  have hB_α_bound : ∀ i, i ≤ kmax → ∀ x : EuclN,
      ‖iteratedFDeriv ℝ i T_αγ x‖ ≤ B := by
    intro i hi x
    exact (hBα_bound i hi x).trans (le_max_right _ _)
  have hη_γ_eq_one_on_thick : ∀ y ∈ Metric.thickening δ_γ K_E_γ, η_γ y = 1 := by
    intro y hy
    have hy_cthick : y ∈ Metric.cthickening δ_γ K_E_γ :=
      Metric.thickening_subset_cthickening δ_γ K_E_γ hy
    exact hη_γ_one y hy_cthick
  have hΩγα_subset_thick_γ : Ω_γα ⊆ Metric.thickening δ_γ K_E_γ := by
    refine subset_trans ?_ (Metric.thickening_mono (by linarith : δ_γ / 2 ≤ δ_γ) K_E_γ)
    rfl
  have hT_γα_fderiv_eq : ∀ y ∈ Ω_γα,
      fderiv ℝ T_γα y = fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y := by
    intro y hy
    have h_evt : T_γα =ᶠ[𝓝 y] (chartTransitionEuclid (I := I) (M := M) γ α) := by
      have h_open_thick : IsOpen (Metric.thickening δ_γ K_E_γ) := Metric.isOpen_thickening
      have hy_thick : y ∈ Metric.thickening δ_γ K_E_γ := hΩγα_subset_thick_γ hy
      refine Filter.eventually_of_mem (h_open_thick.mem_nhds hy_thick) ?_
      intro y' hy'
      have hηy' : η_γ y' = 1 := hη_γ_eq_one_on_thick y' hy'
      exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
        (I := I) (M := M) γ α c_γ hηy'
    exact h_evt.fderiv_eq
  have h_abs_det_pos_on_overlap : ∀ y ∈ chartOverlapEuclid (I := I) (M := M) γ α,
      0 < |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det| := by
    intro y hy
    have h_ne_zero : (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det ≠ 0 :=
      chartTransitionEuclid_det_fderiv_ne_zero (I := I) (M := M) γ α hy
    exact abs_pos.mpr h_ne_zero
  have h_abs_det_continuousOn :
      ContinuousOn
        (fun y => |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det|)
        (closure Ω_γα) :=
    (abs_det_fderiv_chartTransitionEuclid_continuousOn (I := I) (M := M) γ α).mono
      hΩγα_closure_subset_overlap
  have h_abs_det_pos_on_closure : ∀ y ∈ closure Ω_γα,
      0 < |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det| := by
    intro y hy
    exact h_abs_det_pos_on_overlap y (hΩγα_closure_subset_overlap hy)
  by_cases hK_E_γ_empty : Ω_γα = ∅
  · refine ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, ?_, ?_⟩
    · intro z hz
      rcases hz with ⟨x, hx, hxz⟩
      simp only [Function.comp_apply] at hxz
      have hx_in : (toEuclidean (E := E)) (extChartAt I γ x) ∈ K_E_γ := ⟨x, hx, rfl⟩
      have : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα := hKEγ_subset_Ωγα hx_in
      rw [hxz] at this
      exact this
    refine ⟨{
      toFun := T_γα,
      invFun := T_αγ,
      toFun_smooth := hT_γα_smooth,
      invFun_smooth := hT_αγ_smooth,
      bijOn := hBijOn_T_γα,
      invFun_bijOn := hBijOn_T_αγ,
      left_inv := hLeft_inv,
      right_inv := hRight_inv,
      deriv_bound := B,
      deriv_bound_pos := hB_pos,
      iter_deriv_bounded_at := hB_γ_bound,
      iter_deriv_invFun_bounded_at := hB_α_bound,
      jacobian_lower_bound := 1,
      jacobian_lower_bound_pos := one_pos,
      jacobian_lower := ?_
    }, ?_⟩
    · intro x hx
      rw [hK_E_γ_empty] at hx
      exact (Set.notMem_empty x hx).elim
    · intro x hx
      simp only [Function.comp_apply]
      have hx_in_KEγ : (toEuclidean (E := E)) (extChartAt I γ x) ∈ K_E_γ := ⟨x, hx, rfl⟩
      have hx_in_Ωγα : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα :=
        hKEγ_subset_Ωγα hx_in_KEγ
      rw [hK_E_γ_empty] at hx_in_Ωγα
      exact (Set.notMem_empty _ hx_in_Ωγα).elim
  · have hΩγα_nonempty : Ω_γα.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_E_γ_empty
    have hclosure_nonempty : (closure Ω_γα).Nonempty := hΩγα_nonempty.mono subset_closure
    obtain ⟨y₀, hy₀_cl, hy₀_min⟩ :=
      hΩγα_closure_compact.exists_isMinOn hclosure_nonempty h_abs_det_continuousOn
    set J : ℝ := |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y₀).det| with hJ_def
    have hJ_pos : 0 < J := h_abs_det_pos_on_closure y₀ hy₀_cl
    have hJ_lower : ∀ y ∈ Ω_γα, J ≤
        |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det| := by
      intro y hy
      have hy_cl : y ∈ closure Ω_γα := subset_closure hy
      exact hy₀_min hy_cl
    have hJ_lower_T_γα : ∀ y ∈ Ω_γα, J ≤ |(fderiv ℝ T_γα y).det| := by
      intro y hy
      rw [hT_γα_fderiv_eq y hy]
      exact hJ_lower y hy
    refine ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, ?_, ?_⟩
    · intro z hz
      rcases hz with ⟨x, hx, hxz⟩
      simp only [Function.comp_apply] at hxz
      have hx_in : (toEuclidean (E := E)) (extChartAt I γ x) ∈ K_E_γ := ⟨x, hx, rfl⟩
      have h_in_Ωγα : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα :=
        hKEγ_subset_Ωγα hx_in
      rw [hxz] at h_in_Ωγα
      exact h_in_Ωγα
    refine ⟨{
      toFun := T_γα,
      invFun := T_αγ,
      toFun_smooth := hT_γα_smooth,
      invFun_smooth := hT_αγ_smooth,
      bijOn := hBijOn_T_γα,
      invFun_bijOn := hBijOn_T_αγ,
      left_inv := hLeft_inv,
      right_inv := hRight_inv,
      deriv_bound := B,
      deriv_bound_pos := hB_pos,
      iter_deriv_bounded_at := hB_γ_bound,
      iter_deriv_invFun_bounded_at := hB_α_bound,
      jacobian_lower_bound := J,
      jacobian_lower_bound_pos := hJ_pos,
      jacobian_lower := hJ_lower_T_γα
    }, ?_⟩
    intro x hx
    simp only [Function.comp_apply]
    have hx_in_KEγ : (toEuclidean (E := E)) (extChartAt I γ x) ∈ K_E_γ := ⟨x, hx, rfl⟩
    have hx_in_Ωγα : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα :=
      hKEγ_subset_Ωγα hx_in_KEγ
    rw [hT_γα_eq_on_Ωγα _ hx_in_Ωγα]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α (hK_γ hx)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
