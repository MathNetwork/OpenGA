import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBound
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotGTotalBound
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.ChartBilinearVariationalIdentity
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmooth

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartBilinearUniformDiffQuotBoundCanonical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBound
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear
open DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitutionNonSmooth
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

set_option maxHeartbeats 1200000 in

omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_v_test_sq_discharge
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set EuclN} (_hΩ'_open : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (_hΩ'_compact_closure : IsCompact (closure Ω'))
    (_hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω') :
    ∀ (k : Fin (Module.finrank ℝ E)), ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x,
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x)^2
        ∂(volume : Measure EuclN) ≤
        8 * N^2 *
          ∫ x in tsupport η,
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart x)^2
          ∂(volume : Measure EuclN) +
        2 * ∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial k) x)^2
          ∂(volume : Measure EuclN) := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_supp
  have h_cthickR0_compact : IsCompact (Metric.cthickening R₀ (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthickR0_in_Ω' : Metric.cthickening R₀ (tsupport η) ⊆ Ω' := by
    have h := hh_supp_in_Ω' (h := R₀) (by rw [abs_of_pos hR₀_pos])
    rw [abs_of_pos hR₀_pos] at h
    exact h
  have h_cthickR0_in_chart :
      Metric.cthickening R₀ (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
    h_cthickR0_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    h_cthickR0_compact.exists_cthickening_subset_open h_chart_open
      h_cthickR0_in_chart
  set r : ℝ := R₀ + δ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_gt_R0 : R₀ < r := by rw [hr_def]; linarith
  have hr_ge_R0 : R₀ ≤ r := hr_gt_R0.le
  have hr_le : r ≤ R₀ + δ := by rw [hr_def]; linarith
  have h_cthick_r_compact : IsCompact (Metric.cthickening r (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthick_r_in_chart :
      Metric.cthickening r (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    have hx' : x ∈ Metric.cthickening (R₀ + δ) (tsupport η) :=
      Metric.cthickening_mono hr_le _ hx
    have h_eq : Metric.cthickening (R₀ + δ) (tsupport η) =
        Metric.cthickening δ (Metric.cthickening R₀ (tsupport η)) := by
      have hδ_le : (0 : ℝ) ≤ δ := hδ_pos.le
      have hR0_le : (0 : ℝ) ≤ R₀ := hR₀_pos.le
      rw [show (R₀ + δ) = (δ + R₀) from by ring,
        ← cthickening_cthickening hδ_le hR0_le]
    rw [h_eq] at hx'
    exact hδ_in_chart hx'
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_range, hχ_one, hχ_tsupp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      (K := Metric.cthickening r (tsupport η))
      (Ω' := chartTargetEuclid (I := I) (M := M) α)
      h_cthick_r_compact h_chart_open h_cthick_r_in_chart
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact ⟨(hχ_range hx_range).1, (hχ_range hx_range).2⟩
  set u_g : EuclN → ℝ := fun x => χ x * D.u_chart x with hu_g_def
  set G : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.u_chart x +
    χ x * D.weak_partial i x with hG_def
  have hu_g_l2 : MemLp u_g 2 (volume : Measure EuclN) :=
    cutoff_uChart_memLp_two_univ (I := I) (M := M) D hχ_smooth hχ_cs hχ_tsupp
  have hG_l2 : ∀ i, MemLp (G i) 2 (volume : Measure EuclN) := fun i =>
    cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  have hG_isWP : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (G i) u_g Set.univ := fun i =>
    cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  have hu_g_locInt :
      LocallyIntegrable u_g ((volume : Measure EuclN).restrict Set.univ) := by
    have : LocallyIntegrable u_g (volume : Measure EuclN) :=
      hu_g_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [Measure.restrict_univ]; exact this
  have hG_locInt : ∀ i,
      LocallyIntegrable (G i) ((volume : Measure EuclN).restrict Set.univ) :=
    fun i => by
      have : LocallyIntegrable (G i) (volume : Measure EuclN) :=
        (hG_l2 i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      rw [Measure.restrict_univ]; exact this
  intro k h hh hh_le
  have hh_abs_pos : 0 < |h| := abs_pos.mpr hh
  have hh_abs_le : |h| ≤ R₀ := hh_le
  have hh_abs_lt_r : |h| < r := lt_of_le_of_lt hh_abs_le hr_gt_R0
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_abs_nh : |-h| = |h| := abs_neg h
  have h_inner_wp :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (fun y => (η y)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h (G k) y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g y)
        (fun y => (η y)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h u_g y)
        Set.univ :=
    DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction.hasWeakPartialDeriv_eta_sq_diffQuot
      (d := Module.finrank ℝ E) k k h hη hu_g_locInt (hG_locInt k) (hG_isWP k)
  have h_self_subset_cthick :
      tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    Metric.self_subset_cthickening _
  have h_cthick_h_subset_R0 :
      Metric.cthickening |h| (tsupport η) ⊆
        Metric.cthickening R₀ (tsupport η) :=
    Metric.cthickening_mono hh_abs_le _
  have h_cthick_R0_subset_r :
      Metric.cthickening R₀ (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.cthickening_mono hr_ge_R0 _
  have h_cthick_h_subset_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    h_cthick_h_subset_R0.trans h_cthick_R0_subset_r
  have h_cthick_h_subset_thick_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.thickening r (tsupport η) := by
    intro x hx
    have h_inf : Metric.infEDist x (tsupport η) ≤ ENNReal.ofReal |h| :=
      (Metric.mem_cthickening_iff).mp hx
    have h_ofReal_lt : ENNReal.ofReal |h| < ENNReal.ofReal r :=
      ENNReal.ofReal_lt_ofReal_iff hr_pos |>.mpr hh_abs_lt_r
    have h_inf_lt : Metric.infEDist x (tsupport η) < ENNReal.ofReal r :=
      lt_of_le_of_lt h_inf h_ofReal_lt
    exact (Metric.mem_thickening_iff_infEDist_lt).mpr h_inf_lt
  have h_tsupp_subset_thick_r : tsupport η ⊆ Metric.thickening r (tsupport η) :=
    Metric.self_subset_thickening hr_pos _
  have h_thick_r_open : IsOpen (Metric.thickening r (tsupport η)) :=
    Metric.isOpen_thickening
  have h_thick_r_subset_cthick_r :
      Metric.thickening r (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.thickening_subset_cthickening _ _
  have hχ_one_on_r : ∀ x ∈ Metric.cthickening r (tsupport η), χ x = 1 :=
    fun x hx => hχ_one x hx
  have h_fderiv_zero_on_thick_r : ∀ x ∈ Metric.thickening r (tsupport η),
      (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 := by
    intro x hx
    have hχ_eq_one_nhds : (fun y => χ y) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      refine Filter.eventually_of_mem (h_thick_r_open.mem_nhds hx) ?_
      intro y hy
      exact hχ_one y (h_thick_r_subset_cthick_r hy)
    have h_fderiv_eq : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclN => (1 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq hχ_eq_one_nhds
    rw [h_fderiv_eq]
    simp
  have h_u_g_eq_on_cthick_R0 : ∀ x ∈ Metric.cthickening R₀ (tsupport η),
      u_g x = D.u_chart x := by
    intro x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) :=
      h_cthick_R0_subset_r hx
    have hχx : χ x = 1 := hχ_one_on_r x hx_in_r
    change χ x * D.u_chart x = D.u_chart x
    rw [hχx, one_mul]
  have h_G_eq_on_thick_r : ∀ x ∈ Metric.thickening r (tsupport η),
      G k x = D.weak_partial k x := by
    intro x hx
    have hx_in_cthick_r : x ∈ Metric.cthickening r (tsupport η) :=
      h_thick_r_subset_cthick_r hx
    have hχx : χ x = 1 := hχ_one_on_r x hx_in_cthick_r
    have hdχx : (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 :=
      h_fderiv_zero_on_thick_r x hx
    change (fderiv ℝ χ x) (EuclideanSpace.single k 1) * D.u_chart x +
      χ x * D.weak_partial k x = D.weak_partial k x
    rw [hdχx, hχx, zero_mul, one_mul, zero_add]
  have h_diffQuot_u_eq_on_tsupport : ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart x := by
    intro x hx
    have hx_in_cthick_h : x ∈ Metric.cthickening |h| (tsupport η) :=
      h_self_subset_cthick hx
    have hx_in_cthick_R0 : x ∈ Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_R0 hx_in_cthick_h
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_cthick_R0 :
        x + h • EuclideanSpace.single k 1 ∈ Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_R0 h_shift_in_cthick_h
    have hux : u_g x = D.u_chart x :=
      h_u_g_eq_on_cthick_R0 x hx_in_cthick_R0
    have hux_shift : u_g (x + h • EuclideanSpace.single k 1) =
        D.u_chart (x + h • EuclideanSpace.single k 1) :=
      h_u_g_eq_on_cthick_R0 _ h_shift_in_cthick_R0
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      hux, hux_shift]
  have h_diffQuot_G_eq_on_tsupport : ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (G k) x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial k) x := by
    intro x hx
    have hx_in_thick_r : x ∈ Metric.thickening r (tsupport η) :=
      h_tsupp_subset_thick_r hx
    have hx_in_cthick_h : x ∈ Metric.cthickening |h| (tsupport η) :=
      h_self_subset_cthick hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_thick_r :
        x + h • EuclideanSpace.single k 1 ∈ Metric.thickening r (tsupport η) :=
      h_cthick_h_subset_thick_r h_shift_in_cthick_h
    have hGx : G k x = D.weak_partial k x := h_G_eq_on_thick_r x hx_in_thick_r
    have hGx_shift : G k (x + h • EuclideanSpace.single k 1) =
        D.weak_partial k (x + h • EuclideanSpace.single k 1) :=
      h_G_eq_on_thick_r _ h_shift_in_thick_r
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      hGx, hGx_shift]
  set F : EuclN → ℝ := fun y => (η y)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g y with hF_def
  set G_F : EuclN → ℝ := fun y => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) y +
      ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g y with hG_F_def
  have hF_wp : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k G_F F
      Set.univ := h_inner_wp
  have hη_sq_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => (η y)^2) :=
    hη.pow 2
  have hη_sq_cont : Continuous (fun y : EuclN => (η y)^2) :=
    hη_sq_smooth.continuous
  have hη_pt : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    hη_range (Set.mem_range_self x)
  have hη_nn : ∀ x, 0 ≤ η x := fun x => (hη_pt x).1
  have hη_le_one : ∀ x, η x ≤ 1 := fun x => (hη_pt x).2
  have hη_sq_nn : ∀ x, 0 ≤ (η x)^2 := fun x => sq_nonneg _
  have hη_sq_le_one : ∀ x, (η x)^2 ≤ 1 := fun x => by
    have h := hη_pt x
    nlinarith [h.1, h.2]
  have h_abs_eta_le_one : ∀ x, |η x| ≤ 1 := fun x =>
    abs_le.mpr ⟨by linarith [hη_nn x], hη_le_one x⟩
  have hη_sq_supp : HasCompactSupport (fun y : EuclN => (η y)^2) := by
    have heq : (fun y : EuclN => (η y)^2) = (fun y : EuclN => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_supp.mul_right
  have hF_cs : HasCompactSupport F := by
    rw [hF_def]; exact hη_sq_supp.mul_right
  have hF_supp_subset : tsupport F ⊆ tsupport η := by
    have h_supp_subset : Function.support F ⊆ Function.support η := by
      intro x hx
      change (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x ≠ 0 at hx
      have hη_x_ne : η x ≠ 0 := by
        intro hη_zero
        have hη_sq_zero : (η x)^2 = 0 := by rw [hη_zero]; ring
        apply hx; rw [hη_sq_zero, zero_mul]
      exact hη_x_ne
    exact (closure_mono h_supp_subset)
  have h_translate_u_g_l2 :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h u_g) 2 (volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.memLp_translate
      (d := Module.finrank ℝ E) k h hu_g_l2
  have h_diffQuot_u_g_l2 :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g) 2 (volume : Measure EuclN) := by
    have h_eq :
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g =
        fun x : EuclN =>
          h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h u_g x) + (-h⁻¹) * u_g x := by
      funext x
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      change (u_g (x + h • EuclideanSpace.single k 1) - u_g x) / h =
        h⁻¹ * u_g (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * u_g x
      field_simp; ring
    rw [h_eq]
    have h1 : MemLp
        (fun x : EuclN => h⁻¹ *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h u_g x) 2 (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => h⁻¹ *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h u_g x) =
          h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h u_g) := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact h_translate_u_g_l2.const_smul h⁻¹
    have h2 : MemLp (fun x : EuclN => (-h⁻¹) * u_g x) 2
        (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => (-h⁻¹) * u_g x) = (-h⁻¹) • u_g := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact hu_g_l2.const_smul (-h⁻¹)
    exact h1.add h2
  have h_translate_G_l2 :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h (G k)) 2 (volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.memLp_translate
      (d := Module.finrank ℝ E) k h (hG_l2 k)
  have h_diffQuot_G_l2 :
      MemLp
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k)) 2 (volume : Measure EuclN) := by
    have h_eq :
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) =
        fun x : EuclN =>
          h⁻¹ * (DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h (G k) x) + (-h⁻¹) * (G k) x := by
      funext x
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh]
      change ((G k) (x + h • EuclideanSpace.single k 1) - (G k) x) / h =
        h⁻¹ * (G k) (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * (G k) x
      field_simp; ring
    rw [h_eq]
    have h1 : MemLp
        (fun x : EuclN => h⁻¹ *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h (G k) x) 2
        (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => h⁻¹ *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h (G k) x) =
          h⁻¹ • (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h (G k)) := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact h_translate_G_l2.const_smul h⁻¹
    have h2 : MemLp (fun x : EuclN => (-h⁻¹) * (G k) x) 2
        (volume : Measure EuclN) := by
      have h_eq_smul : (fun x : EuclN => (-h⁻¹) * (G k) x) = (-h⁻¹) • (G k) := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq_smul]
      exact (hG_l2 k).const_smul (-h⁻¹)
    exact h1.add h2
  have hF_l2 : MemLp F 2 (volume : Measure EuclN) := by
    have h_aesm_F : AEStronglyMeasurable F (volume : Measure EuclN) := by
      have h_eta_sq_aesm :
          AEStronglyMeasurable (fun y : EuclN => (η y)^2)
            (volume : Measure EuclN) := hη_sq_cont.aestronglyMeasurable
      have h_diffQuot_aesm :
          AEStronglyMeasurable
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g) (volume : Measure EuclN) :=
        h_diffQuot_u_g_l2.aestronglyMeasurable
      exact h_eta_sq_aesm.mul h_diffQuot_aesm
    have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
        ‖F x‖ ≤ ‖DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      change ‖(η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x‖ ≤ _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hη_sq_nn x)]
      have h_le1 : (η x)^2 ≤ 1 := hη_sq_le_one x
      nlinarith [abs_nonneg
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x), hη_sq_nn x]
    exact MemLp.mono h_diffQuot_u_g_l2 h_aesm_F h_pt_le
  have h_eta_sq_fderiv_cont :
      Continuous (fun y : EuclN =>
        (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) := by
    have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
    exact (hη_sq_smooth.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_eta_sq_fderiv_cs : HasCompactSupport
      (fun y : EuclN =>
        (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) :=
    hη_sq_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  have h_eta_sq_fderiv_bound : ∀ y : EuclN,
      |(fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)| ≤ 2 * N := by
    intro y
    have h_eq : (fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1) =
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single k 1) := by
      have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
      rw [fderiv_fun_pow 2 (hη_diff y)]
      rw [ContinuousLinearMap.smul_apply]
      have h1 : (η y) ^ ((2 : ℕ) - 1) = η y := by norm_num
      rw [h1]
      have h_two : ((2 : ℕ) • η y) = 2 * η y := by rw [two_smul]; ring
      rw [h_two, smul_eq_mul]
    rw [h_eq, abs_mul, abs_mul]
    have h_eta_abs : |η y| ≤ 1 := h_abs_eta_le_one y
    have h_eta_partial_abs :
        |(fderiv ℝ η y) (EuclideanSpace.single k 1)| ≤ N := by
      have h_apply_le :
          ‖(fderiv ℝ η y) (EuclideanSpace.single k 1)‖ ≤
            ‖fderiv ℝ η y‖ * ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ :=
        (fderiv ℝ η y).le_opNorm (EuclideanSpace.single k 1)
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs] at h_apply_le
      exact h_apply_le.trans (h_fderiv_eta y)
    have h_2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h_2]
    have h_step1 : 2 * |η y| ≤ 2 := by linarith
    have h_step2 : 0 ≤ |(fderiv ℝ η y) (EuclideanSpace.single k 1)| :=
      abs_nonneg _
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (η y))]
  have hG_F_l2 : MemLp G_F 2 (volume : Measure EuclN) := by
    have h_T1_l2 : MemLp (fun y : EuclN => (η y)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) y) 2 (volume : Measure EuclN) := by
      have h_aesm : AEStronglyMeasurable (fun y : EuclN => (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) y)
          (volume : Measure EuclN) :=
        hη_sq_cont.aestronglyMeasurable.mul
          h_diffQuot_G_l2.aestronglyMeasurable
      have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
          ‖(η x)^2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x‖ ≤
            ‖DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x‖ := by
        refine Filter.Eventually.of_forall ?_
        intro x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (hη_sq_nn x)]
        have h_le1 : (η x)^2 ≤ 1 := hη_sq_le_one x
        nlinarith [abs_nonneg
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x), hη_sq_nn x]
      exact MemLp.mono h_diffQuot_G_l2 h_aesm h_pt_le
    have h_T2_l2 : MemLp (fun y : EuclN =>
        ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g y) 2 (volume : Measure EuclN) := by
      have h_aesm : AEStronglyMeasurable (fun y : EuclN =>
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single k 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g y)
          (volume : Measure EuclN) :=
        h_eta_sq_fderiv_cont.aestronglyMeasurable.mul
          h_diffQuot_u_g_l2.aestronglyMeasurable
      have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
          ‖((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x‖ ≤
            ‖(2 * N) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g x‖ := by
        refine Filter.Eventually.of_forall ?_
        intro x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
        have h_2N_nn : 0 ≤ 2 * N := by linarith
        rw [abs_of_nonneg h_2N_nn]
        exact mul_le_mul_of_nonneg_right (h_eta_sq_fderiv_bound x) (abs_nonneg _)
      exact MemLp.mono (h_diffQuot_u_g_l2.const_mul (2 * N)) h_aesm h_pt_le
    exact h_T1_l2.add h_T2_l2
  set Ω''_fk : Set EuclN := Metric.thickening (R₀ + 1) (tsupport η) with hΩ''_fk_def
  have hΩ''_fk_open : IsOpen Ω''_fk := Metric.isOpen_thickening
  have hΩ''_fk_meas : MeasurableSet Ω''_fk := hΩ''_fk_open.measurableSet
  have h_closure_Ω''_fk_compact : IsCompact (closure Ω''_fk) := by
    have h_le : closure Ω''_fk ⊆ Metric.cthickening (R₀ + 1) (tsupport η) := by
      rw [hΩ''_fk_def]
      exact Metric.closure_thickening_subset_cthickening _ _
    exact (hη_tsupp_compact.cthickening).of_isClosed_subset
      isClosed_closure h_le
  have hR0_plus_one_pos : 0 < R₀ + 1 := by linarith
  have hh_abs_le_R0_plus_one : |-h| ≤ R₀ + 1 := by
    rw [h_abs_nh]; linarith
  have hh_abs_pos_nh : 0 < |-h| := by rw [h_abs_nh]; exact hh_abs_pos
  have h_thick_outer :
      Metric.cthickening |-h| (closure Ω''_fk) ⊆ (Set.univ : Set EuclN) :=
    fun _ _ => trivial
  have h_FK_F : ∫ x in Ω''_fk,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) ≤
      ∫ x in (Set.univ : Set EuclN), (G_F x)^2 ∂(volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.integral_sq_diffQuot_le_integral_sq_weakPartial_meas
      (d := Module.finrank ℝ E)
      hF_l2 hG_F_l2 k hF_wp MeasurableSet.univ hΩ''_fk_meas
      h_closure_Ω''_fk_compact hh_abs_pos_nh h_thick_outer hnh (le_refl _)
  have h_v_eq_diffQuot : ∀ x,
      DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η u_g x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F x := by
    intro x
    rfl
  have h_support_diffQuot_F_subset_Ω''_fk : ∀ x,
      x ∉ Ω''_fk →
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F x = 0 := by
    intro x hx_notin
    have hx_far : Metric.infEDist x (tsupport η) ≥ ENNReal.ofReal (R₀ + 1) := by
      have : ¬ Metric.infEDist x (tsupport η) < ENNReal.ofReal (R₀ + 1) := by
        intro h_lt
        apply hx_notin
        rw [hΩ''_fk_def]
        exact (Metric.mem_thickening_iff_infEDist_lt).mpr h_lt
      exact not_lt.mp this
    have hx_notin_tsupp : x ∉ tsupport η := by
      intro hx_in
      have h_zero : Metric.infEDist x (tsupport η) = 0 :=
        Metric.infEDist_zero_of_mem hx_in
      rw [h_zero] at hx_far
      have h_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (R₀ + 1) :=
        ENNReal.ofReal_pos.mpr hR0_plus_one_pos
      exact absurd hx_far (not_le.mpr h_pos)
    have hF_x_zero : F x = 0 := by
      have hη_x_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_tsupp
      change (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x = 0
      rw [hη_x_zero]; ring
    have h_shift_notin_tsupp :
        x + (-h) • EuclideanSpace.single k 1 ∉ tsupport η := by
      intro h_in
      have h_dist_shift_x :
          dist (x + (-h) • EuclideanSpace.single k 1) x = |h| := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
        have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
        rw [hsing, mul_one, Real.norm_eq_abs, abs_neg]
      have h_inf_le : Metric.infEDist x (tsupport η) ≤
          edist x (x + (-h) • EuclideanSpace.single k 1) :=
        Metric.infEDist_le_edist_of_mem h_in
      have h_edist_eq : edist x (x + (-h) • EuclideanSpace.single k 1) =
          ENNReal.ofReal |h| := by
        rw [edist_dist]
        have : dist x (x + (-h) • EuclideanSpace.single k 1) = |h| := by
          rw [dist_comm]; exact h_dist_shift_x
        rw [this]
      rw [h_edist_eq] at h_inf_le
      have h_h_lt_R0_plus_one : ENNReal.ofReal |h| < ENNReal.ofReal (R₀ + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff hR0_plus_one_pos).mpr (by linarith)
      have h_inf_lt : Metric.infEDist x (tsupport η) < ENNReal.ofReal (R₀ + 1) :=
        lt_of_le_of_lt h_inf_le h_h_lt_R0_plus_one
      have h_inf_not_lt : ¬ Metric.infEDist x (tsupport η) < ENNReal.ofReal (R₀ + 1) :=
        not_lt.mpr hx_far
      exact absurd h_inf_lt h_inf_not_lt
    have hF_shift_zero : F (x + (-h) • EuclideanSpace.single k 1) = 0 := by
      have hη_shift_zero : η (x + (-h) • EuclideanSpace.single k 1) = 0 :=
        image_eq_zero_of_notMem_tsupport h_shift_notin_tsupp
      change (η (x + (-h) • EuclideanSpace.single k 1))^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g
            (x + (-h) • EuclideanSpace.single k 1) = 0
      rw [hη_shift_zero]; ring
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hnh,
      hF_shift_zero, hF_x_zero, sub_zero, zero_div]
  have h_int_univ_F :
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) F x)^2
          ∂(volume : Measure EuclN) =
      ∫ x in Ω''_fk,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ω''_fk) (μ := (volume : Measure EuclN)) ?_).symm
    intro x hx_notin
    have h_zero := h_support_diffQuot_F_subset_Ω''_fk x hx_notin
    rw [h_zero]; ring
  have h_F_eq_D : F = fun y => (η y)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y := by
    funext y
    by_cases hη_y : η y = 0
    · change (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g y =
        (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y
      rw [hη_y]; ring
    · have hy_in : y ∈ tsupport η := subset_tsupport η hη_y
      rw [hF_def]
      change (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g y =
        (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y
      rw [h_diffQuot_u_eq_on_tsupport y hy_in]
  have h_nb_test_eq : ∀ x,
      DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η D.u_chart x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) F x := by
    intro x
    change DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) (fun y => (η y)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y) x = _
    rw [← h_F_eq_D]
  have h_LHS_eq_FK :
      ∫ x, (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x)^2
          ∂(volume : Measure EuclN) =
      ∫ x in Ω''_fk,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) := by
    have h_eq :
        (fun x => (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x)^2) =
        (fun x =>
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) F x)^2) := by
      funext x; rw [h_nb_test_eq x]
    rw [h_eq, h_int_univ_F]
  have h_pointwise_G_F_sq : ∀ x : EuclN,
      (G_F x)^2 ≤
        8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 +
        2 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2 := by
    intro x
    set T1 : ℝ := (η x)^2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (G k) x with hT1_def
    set T2 : ℝ := ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x with hT2_def
    have hG_F_x : G_F x = T1 + T2 := rfl
    rw [hG_F_x]
    have h_sq_sum_le : (T1 + T2)^2 ≤ 2 * T1^2 + 2 * T2^2 := by
      have h_nn_diff : 0 ≤ (T1 - T2)^2 := sq_nonneg _
      nlinarith
    refine h_sq_sum_le.trans ?_
    have h_T1_sq_bound : 2 * T1^2 ≤ 2 * (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2 := by
      rw [hT1_def]
      have h_sq : ((η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2 =
          (η x)^4 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2 := by ring
      rw [h_sq]
      have h_eta_4_le_2 : (η x)^4 ≤ (η x)^2 := by
        have h1 : (η x)^4 = (η x)^2 * (η x)^2 := by ring
        rw [h1]
        have h_eta_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
        have h_eta_sq_le_one : (η x)^2 ≤ 1 := hη_sq_le_one x
        nlinarith
      have h_dq_sq_nn : 0 ≤ (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2 := sq_nonneg _
      nlinarith
    have h_T2_sq_bound : 2 * T2^2 ≤ 8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2 := by
      rw [hT2_def]
      by_cases hx_in : x ∈ tsupport η
      · rw [Set.indicator_of_mem hx_in]
        have h_bound := h_eta_sq_fderiv_bound x
        have h_sq_eq : (((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 =
            ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1))^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 := by ring
        rw [h_sq_eq]
        have h_partial_sq_le_4N2 :
            ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1))^2 ≤
              4 * N^2 := by
          have h_abs_le : |(fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)|
              ≤ 2 * N := h_bound
          have h_abs_nn : 0 ≤
              |(fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)| :=
            abs_nonneg _
          have h_2N_nn : 0 ≤ 2 * N := by linarith
          have h_sq_le : |(fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1)|^2 ≤
              (2 * N)^2 := by
            exact sq_le_sq' (by linarith) h_abs_le
          have h_sq_abs : |(fderiv ℝ (fun z => (η z)^2) x)
              (EuclideanSpace.single k 1)|^2 =
              ((fderiv ℝ (fun z => (η z)^2) x) (EuclideanSpace.single k 1))^2 := by
            rw [sq_abs]
          rw [← h_sq_abs]
          have : (2 * N)^2 = 4 * N^2 := by ring
          rw [this] at h_sq_le
          exact h_sq_le
        have h_dq_sq_nn : 0 ≤ (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 := sq_nonneg _
        nlinarith
      · rw [Set.indicator_of_notMem hx_in]
        have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx_in
        have h_tsupp_compl_open : IsOpen (tsupport η)ᶜ :=
          (isClosed_tsupport η).isOpen_compl
        have hx_in_compl : x ∈ (tsupport η)ᶜ := hx_in
        have h_eta_sq_eq_zero_nhds :
            (fun y : EuclN => (η y)^2) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
          refine Filter.eventually_of_mem (h_tsupp_compl_open.mem_nhds hx_in_compl) ?_
          intro y hy
          have hη_y_zero : η y = 0 := image_eq_zero_of_notMem_tsupport hy
          change (η y)^2 = 0
          rw [hη_y_zero]; ring
        have h_fderiv_eq : fderiv ℝ (fun y : EuclN => (η y)^2) x =
            fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x :=
          Filter.EventuallyEq.fderiv_eq h_eta_sq_eq_zero_nhds
        have h_partial_zero :
            (fderiv ℝ (fun y : EuclN => (η y)^2) x)
              (EuclideanSpace.single k 1) = 0 := by
          rw [h_fderiv_eq]; simp
        rw [h_partial_zero, zero_mul]
        have h_dq_sq_nn : 0 ≤ (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 := sq_nonneg _
        nlinarith
    linarith
  have h_eta_sq_dq_G_sq_integrable :
      Integrable (fun x : EuclN => (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) := by
    have h_dq_G_sq_int : Integrable (fun x : EuclN =>
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) :=
      h_diffQuot_G_l2.integrable_sq
    have h_aesm : AEStronglyMeasurable (fun x : EuclN => (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) := by
      have h1 : AEStronglyMeasurable (fun x : EuclN => (η x)^2)
          (volume : Measure EuclN) := hη_sq_cont.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun x : EuclN =>
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) :=
        h_dq_G_sq_int.aestronglyMeasurable
      exact h1.mul h2
    have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
        ‖(η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2‖ ≤
          ‖(DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hη_sq_nn x)]
      have h_le1 : (η x)^2 ≤ 1 := hη_sq_le_one x
      nlinarith [abs_nonneg
        ((DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2), hη_sq_nn x]
    exact h_dq_G_sq_int.mono h_aesm h_pt_le
  have h_dq_u_g_sq_int : Integrable (fun x : EuclN =>
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x)^2) (volume : Measure EuclN) :=
    h_diffQuot_u_g_l2.integrable_sq
  have h_indicator_dq_u_g_sq_int : Integrable (fun x : EuclN =>
      8 * N^2 *
      (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x)^2) (volume : Measure EuclN) := by
    have h_aesm : AEStronglyMeasurable (fun x : EuclN =>
        8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2) (volume : Measure EuclN) := by
      have h1 : AEStronglyMeasurable
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)))
          (volume : Measure EuclN) :=
        (aestronglyMeasurable_const).indicator
          (isClosed_tsupport η).measurableSet
      have h2 : AEStronglyMeasurable (fun x : EuclN =>
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2)
          (volume : Measure EuclN) := h_dq_u_g_sq_int.aestronglyMeasurable
      exact ((aestronglyMeasurable_const.mul h1).mul h2)
    have h_pt_le : ∀ᵐ x ∂(volume : Measure EuclN),
        ‖8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2‖ ≤
          ‖8 * N^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      have h_8N2_nn : 0 ≤ 8 * N^2 := by nlinarith
      have h_indicator_le : |Set.indicator (tsupport η)
          (fun _ : EuclN => (1 : ℝ)) x| ≤ 1 := by
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx]; simp
        · rw [Set.indicator_of_notMem hx]; simp
      have h_indicator_nn : 0 ≤ Set.indicator (tsupport η)
          (fun _ : EuclN => (1 : ℝ)) x := by
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx]; norm_num
        · rw [Set.indicator_of_notMem hx]
      have h_dq_sq_nn : 0 ≤ (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2 := sq_nonneg _
      have h_LHS_nn : 0 ≤ 8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 := by
        have : 0 ≤ 8 * N^2 * (Set.indicator (tsupport η)
            (fun _ : EuclN => (1 : ℝ)) x) :=
          mul_nonneg h_8N2_nn h_indicator_nn
        exact mul_nonneg this h_dq_sq_nn
      have h_RHS_nn : 0 ≤ 8 * N^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 :=
        mul_nonneg h_8N2_nn h_dq_sq_nn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_LHS_nn,
        abs_of_nonneg h_RHS_nn]
      have h_ind_le_1 : Set.indicator (tsupport η)
          (fun _ : EuclN => (1 : ℝ)) x ≤ 1 := by
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx]; norm_num
      have h_step : 8 * N^2 * (Set.indicator (tsupport η)
          (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 ≤
          8 * N^2 * 1 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_ind_le_1 h_8N2_nn)
          h_dq_sq_nn
      linarith
    exact (h_dq_u_g_sq_int.const_mul (8 * N^2)).mono h_aesm h_pt_le
  have hG_F_sq_int : Integrable (fun x : EuclN => (G_F x)^2)
      (volume : Measure EuclN) := hG_F_l2.integrable_sq
  have h_two_eta_sq_dq_int : Integrable (fun x : EuclN =>
      2 * (η x)^2 *
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) := by
    have h_const_mul := h_eta_sq_dq_G_sq_integrable.const_mul 2
    have heq : (fun x : EuclN => 2 *
        ((η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2)) =
        (fun x : EuclN => 2 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2) := by
      funext x; ring
    rw [heq] at h_const_mul
    exact h_const_mul
  have h_RHS_int : Integrable (fun x : EuclN =>
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2 +
      2 * (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) (volume : Measure EuclN) :=
    h_indicator_dq_u_g_sq_int.add h_two_eta_sq_dq_int
  have h_integral_G_F_le :
      ∫ x, (G_F x)^2 ∂(volume : Measure EuclN) ≤
        ∫ x, 8 * N^2 *
            (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 +
          2 * (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x)^2
          ∂(volume : Measure EuclN) := by
    exact integral_mono hG_F_sq_int h_RHS_int h_pointwise_G_F_sq
  have h_integral_split :
      ∫ x, 8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2 +
        2 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2
        ∂(volume : Measure EuclN) =
      (∫ x, 8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(volume : Measure EuclN)) +
      (∫ x, 2 * (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2
        ∂(volume : Measure EuclN)) :=
    integral_add h_indicator_dq_u_g_sq_int h_two_eta_sq_dq_int
  have h_t1_eq : ∫ x, 8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2
      ∂(volume : Measure EuclN) =
      8 * N^2 *
        ∫ x in tsupport η,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x)^2
        ∂(volume : Measure EuclN) := by
    have h_eq : (fun x : EuclN => 8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2) =
        (fun x : EuclN => (8 * N^2) *
          (Set.indicator (tsupport η)
            (fun y => (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g y)^2) x)) := by
      funext x
      by_cases hx : x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
    rw [h_eq, integral_const_mul]
    congr 1
    exact (MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet)
  have h_t2_eq : ∫ x, 2 * (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2
      ∂(volume : Measure EuclN) =
      2 * ∫ x, (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2
      ∂(volume : Measure EuclN) := by
    have heq : (fun x : EuclN => 2 * (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2) =
        (fun x : EuclN => 2 * ((η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G k) x)^2)) := by
      funext x; ring
    rw [heq, integral_const_mul]
  have h_FK_combined :
      ∫ x in Ω''_fk,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) ≤
        ∫ x in (Set.univ : Set EuclN), (G_F x)^2 ∂(volume : Measure EuclN) :=
    h_FK_F
  have h_int_univ_G_F :
      ∫ x in (Set.univ : Set EuclN), (G_F x)^2 ∂(volume : Measure EuclN) =
      ∫ x, (G_F x)^2 ∂(volume : Measure EuclN) :=
    MeasureTheory.setIntegral_univ
  have h_int_dq_u_g_eq : ∫ x in tsupport η,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g x)^2
      ∂(volume : Measure EuclN) =
      ∫ x in tsupport η,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart x)^2
      ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun (isClosed_tsupport η).measurableSet ?_
    intro x hx
    have h_eq := h_diffQuot_u_eq_on_tsupport x hx
    change (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x)^2 =
      (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart x)^2
    rw [h_eq]
  have h_int_eta_sq_dq_G_eq :
      ∫ x, (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G k) x)^2
      ∂(volume : Measure EuclN) =
      ∫ x, (η x)^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial k) x)^2
      ∂(volume : Measure EuclN) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    change (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (G k) x)^2 =
      (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weak_partial k) x)^2
    by_cases hx : x ∈ tsupport η
    · have h_eq := h_diffQuot_G_eq_on_tsupport x hx
      rw [h_eq]
    · have hη_x_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_x_zero]; ring
  calc ∫ x,
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x)^2
        ∂(volume : Measure EuclN)
      = ∫ x in Ω''_fk,
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) F x)^2
        ∂(volume : Measure EuclN) := h_LHS_eq_FK
    _ ≤ ∫ x in (Set.univ : Set EuclN), (G_F x)^2 ∂(volume : Measure EuclN) :=
        h_FK_combined
    _ = ∫ x, (G_F x)^2 ∂(volume : Measure EuclN) := h_int_univ_G_F
    _ ≤ ∫ x, 8 * N^2 *
            (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2 +
          2 * (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x)^2
          ∂(volume : Measure EuclN) := h_integral_G_F_le
    _ = (∫ x, 8 * N^2 *
            (Set.indicator (tsupport η) (fun _ : EuclN => (1 : ℝ)) x) *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2
          ∂(volume : Measure EuclN)) +
        (∫ x, 2 * (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x)^2
          ∂(volume : Measure EuclN)) := h_integral_split
    _ = 8 * N^2 *
          (∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g x)^2
            ∂(volume : Measure EuclN)) +
        2 * (∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G k) x)^2
          ∂(volume : Measure EuclN)) := by rw [h_t1_eq, h_t2_eq]
    _ = 8 * N^2 *
          (∫ x in tsupport η,
              (DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x)^2
            ∂(volume : Measure EuclN)) +
        2 * (∫ x, (η x)^2 *
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial k) x)^2
          ∂(volume : Measure EuclN)) := by
          rw [h_int_dq_u_g_eq, h_int_eta_sq_dq_G_eq]

end ChartBilinearUniformDiffQuotBoundCanonical

end Laplacian
end Analysis
end DifferentialGeometry
