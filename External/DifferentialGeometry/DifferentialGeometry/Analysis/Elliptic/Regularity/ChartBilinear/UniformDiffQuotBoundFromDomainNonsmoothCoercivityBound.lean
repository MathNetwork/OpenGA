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

set_option maxHeartbeats 4000000 in

theorem chartBilinear_master_nonsmooth_discharge
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (B : SmoothEllipticBilinearForm
      (Module.finrank ℝ E) (Set.univ : Set EuclN))
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {Ω' : Set EuclN} (_hΩ'_open : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (_hΩ'_compact_closure : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (h_B_a_match : ∀ y ∈ Metric.cthickening R₀ (tsupport η),
      ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y)
    (h_B_c_match : ∀ y ∈ Metric.cthickening R₀ (tsupport η),
      B.c y = densityOnEuclid (I := I) g α y) :
    ∀ (k : Fin (Module.finrank ℝ E)),
    ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial l) x ^ 2
        ∂(volume : Measure EuclN) ≤
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.translate
                (d := Module.finrank ℝ E) k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((D.weak_partial i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((D.weak_partial i) x) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x
            ∂(volume : Measure EuclN)| +
        |∫ x in (Set.univ : Set EuclN),
            (densityOnEuclid (I := I) g α x * D.f_chart x) *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x| +
        |∫ x in (Set.univ : Set EuclN), B.c x * D.u_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x
              ∂(volume : Measure EuclN)| := by
  classical
  intro k h hh hh_le
  have hh_abs_pos : 0 < |h| := abs_pos.mpr hh
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
  have hG_isWP : ∀ i, DeGiorgi.HasWeakPartialDeriv
      (d := Module.finrank ℝ E) i (G i) u_g Set.univ := fun i =>
    cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp i
  set Ω_principal : Set EuclN := Metric.thickening δ
    (Metric.cthickening R₀ (tsupport η)) with hΩ_principal_def
  have hΩ_principal_open : IsOpen Ω_principal := Metric.isOpen_thickening
  have hΩ_principal_compact_closure :
      IsCompact (closure Ω_principal) := by
    have h_subset : closure Ω_principal ⊆
        Metric.cthickening δ (Metric.cthickening R₀ (tsupport η)) :=
      Metric.closure_thickening_subset_cthickening _ _
    refine (h_cthickR0_compact.cthickening (r := δ)).of_isClosed_subset
      isClosed_closure h_subset
  have hΩ_principal_in_univ : closure Ω_principal ⊆ (Set.univ : Set EuclN) := by
    intro x _; exact Set.mem_univ _
  have hh_supp_in_Ω_principal :
      ∀ {h' : ℝ}, |h'| ≤ R₀ →
        Metric.cthickening |h'| (tsupport η) ⊆ Ω_principal := by
    intro h' hh'_le x hx
    have h_subset_cthickR0 :
        Metric.cthickening |h'| (tsupport η) ⊆
          Metric.cthickening R₀ (tsupport η) :=
      Metric.cthickening_mono hh'_le _
    have hx_in_cthickR0 :
        x ∈ Metric.cthickening R₀ (tsupport η) := h_subset_cthickR0 hx
    have h_self : Metric.cthickening R₀ (tsupport η) ⊆ Ω_principal := by
      rw [hΩ_principal_def]
      exact Metric.self_subset_thickening hδ_pos _
    exact h_self hx_in_cthickR0
  have h_principal_le :
      B.lam *
        ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G l) x)^2
          ∂(volume : Measure EuclN) ≤
      ∫ x, ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G j) x
        ∂(volume : Measure EuclN) := by
    exact principal_term_ge_lambda_norm_sq_nonsmooth
      (d := Module.finrank ℝ E) B hu_g_l2 hG_l2 hG_isWP
      hη hη_supp hη_range hΩ_principal_open
      hΩ_principal_compact_closure hΩ_principal_in_univ
      hh_supp_in_Ω_principal k hh hh_le
  have h_cthick_h_subset_r :
      Metric.cthickening |h| (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.cthickening_mono (hh_le.trans hr_ge_R0) _
  have h_cthick_h_subset_cthickR0 :
      Metric.cthickening |h| (tsupport η) ⊆
        Metric.cthickening R₀ (tsupport η) :=
    Metric.cthickening_mono hh_le _
  have h_cthickR0_subset_r :
      Metric.cthickening R₀ (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.cthickening_mono hr_ge_R0 _
  have h_self_subset_cthick_h :
      tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    Metric.self_subset_cthickening _
  have hh_abs_lt_r : |h| < r := by rw [hr_def]; linarith
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
  have h_thick_r_open : IsOpen (Metric.thickening r (tsupport η)) :=
    Metric.isOpen_thickening
  have h_thick_r_subset_cthick_r :
      Metric.thickening r (tsupport η) ⊆ Metric.cthickening r (tsupport η) :=
    Metric.thickening_subset_cthickening _ _
  have h_fderiv_zero_on_thick_r : ∀ x ∈ Metric.thickening r (tsupport η),
      ∀ l : Fin (Module.finrank ℝ E),
      (fderiv ℝ χ x) (EuclideanSpace.single l 1) = 0 := by
    intro x hx l
    have hχ_eq_one_nhds : (fun y => χ y) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      refine Filter.eventually_of_mem (h_thick_r_open.mem_nhds hx) ?_
      intro y hy
      exact hχ_one y (h_thick_r_subset_cthick_r hy)
    have h_fderiv_eq : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclN => (1 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq hχ_eq_one_nhds
    rw [h_fderiv_eq]
    simp
  have hG_eq_on_cthick_h : ∀ l : Fin (Module.finrank ℝ E),
      ∀ x ∈ Metric.cthickening |h| (tsupport η),
        G l x = D.weak_partial l x := by
    intro l x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) :=
      h_cthick_h_subset_r hx
    have hx_in_thick_r : x ∈ Metric.thickening r (tsupport η) :=
      h_cthick_h_subset_thick_r hx
    have hχx : χ x = 1 := hχ_one x hx_in_r
    have hdχx : (fderiv ℝ χ x) (EuclideanSpace.single l 1) = 0 :=
      h_fderiv_zero_on_thick_r x hx_in_thick_r l
    change (fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.u_chart x +
      χ x * D.weak_partial l x = D.weak_partial l x
    rw [hdχx, hχx, zero_mul, one_mul, zero_add]
  have hu_g_eq_on_cthick_h : ∀ x ∈ Metric.cthickening |h| (tsupport η),
      u_g x = D.u_chart x := by
    intro x hx
    have hx_in_r : x ∈ Metric.cthickening r (tsupport η) :=
      h_cthick_h_subset_r hx
    have hχx : χ x = 1 := hχ_one x hx_in_r
    change χ x * D.u_chart x = D.u_chart x
    rw [hχx, one_mul]
  have h_diffQuot_G_eq_on_tsupport : ∀ l : Fin (Module.finrank ℝ E),
      ∀ x ∈ tsupport η,
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (G l) x =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial l) x := by
    intro l x hx
    have hx_in_cthick_h : x ∈ Metric.cthickening |h| (tsupport η) :=
      h_self_subset_cthick_h hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have hG_at : G l x = D.weak_partial l x :=
      hG_eq_on_cthick_h l x hx_in_cthick_h
    have hG_shift : G l (x + h • EuclideanSpace.single k 1) =
        D.weak_partial l (x + h • EuclideanSpace.single k 1) :=
      hG_eq_on_cthick_h l _ h_shift_in_cthick_h
    change
      (if h = 0 then 0 else
        (G l (x + h • EuclideanSpace.single k 1) - G l x) / h) =
      (if h = 0 then 0 else
        (D.weak_partial l (x + h • EuclideanSpace.single k 1) -
          D.weak_partial l x) / h)
    rw [if_neg hh, if_neg hh, hG_at, hG_shift]
  have h_diffQuot_u_g_eq_on_tsupport : ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h u_g x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart x := by
    intro x hx
    have hx_in_cthick_h : x ∈ Metric.cthickening |h| (tsupport η) :=
      h_self_subset_cthick_h hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have hu_at : u_g x = D.u_chart x :=
      hu_g_eq_on_cthick_h x hx_in_cthick_h
    have hu_shift : u_g (x + h • EuclideanSpace.single k 1) =
        D.u_chart (x + h • EuclideanSpace.single k 1) :=
      hu_g_eq_on_cthick_h _ h_shift_in_cthick_h
    change
      (if h = 0 then 0 else
        (u_g (x + h • EuclideanSpace.single k 1) - u_g x) / h) =
      (if h = 0 then 0 else
        (D.u_chart (x + h • EuclideanSpace.single k 1) - D.u_chart x) / h)
    rw [if_neg hh, if_neg hh, hu_at, hu_shift]
  have h_LHS_pointwise :
      (fun x => (η x)^2 *
        ∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G l) x)^2) =
      (fun x => (η x)^2 *
        ∑ l : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial l) x)^2) := by
    funext x
    by_cases hx : x ∈ tsupport η
    · refine congrArg _ ?_
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [h_diffQuot_G_eq_on_tsupport l x hx]
    · have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_zero]; ring
  set K_0 : Set EuclN := tsupport η with hK_0_def
  have hK_0_compact : IsCompact K_0 := hη_tsupp_compact
  have hK_0_in_chart : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α := by
    rw [hK_0_def]
    exact hη_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  have h_thick_K_0_in_chart :
      Metric.cthickening |h| K_0 ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    rw [hK_0_def]
    exact h_cthick_h_subset_cthickR0.trans h_cthickR0_in_chart
  have h_translate_Ba_eq_on_tsupport : ∀ i j : Fin (Module.finrank ℝ E),
      ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun y : EuclN => B.a y i j) x =
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun y : EuclN => weightedInvGramOnEuclid (I := I) g α i j y) x := by
    intro i j x hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_cthickR0 :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_cthickR0 h_shift_in_cthick_h
    change B.a (x + h • EuclideanSpace.single k 1) i j =
      weightedInvGramOnEuclid (I := I) g α i j
        (x + h • EuclideanSpace.single k 1)
    exact h_B_a_match _ h_shift_in_cthickR0 i j
  have h_diffQuot_Ba_eq_on_tsupport : ∀ i j : Fin (Module.finrank ℝ E),
      ∀ x ∈ tsupport η,
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y : EuclN => B.a y i j) x =
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y : EuclN => weightedInvGramOnEuclid (I := I) g α i j y) x := by
    intro i j x hx
    have h_shift_in_cthick_h :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_cthickR0 :
        x + h • EuclideanSpace.single k 1 ∈
          Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_cthickR0 h_shift_in_cthick_h
    have hx_in_cthickR0 : x ∈ Metric.cthickening R₀ (tsupport η) :=
      h_cthick_h_subset_cthickR0 (h_self_subset_cthick_h hx)
    have hBa_x : B.a x i j = weightedInvGramOnEuclid (I := I) g α i j x :=
      h_B_a_match x hx_in_cthickR0 i j
    have hBa_shift :
        B.a (x + h • EuclideanSpace.single k 1) i j =
          weightedInvGramOnEuclid (I := I) g α i j
            (x + h • EuclideanSpace.single k 1) :=
      h_B_a_match _ h_shift_in_cthickR0 i j
    change
      (if h = 0 then 0 else
        (B.a (x + h • EuclideanSpace.single k 1) i j - B.a x i j) / h) =
      (if h = 0 then 0 else
        (weightedInvGramOnEuclid (I := I) g α i j
            (x + h • EuclideanSpace.single k 1) -
          weightedInvGramOnEuclid (I := I) g α i j x) / h)
    rw [if_neg hh, if_neg hh, hBa_x, hBa_shift]
  have h_RHS_principal_eq :
      ∫ x, ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G j) x
          ∂(volume : Measure EuclN) =
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h := by
    unfold principalTerm_chartBilinear
    have h_eq_on_tsupport : ∀ x ∈ tsupport η,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G j) x) =
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
          (η x) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial j) x) := by
      intro x hx
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_translate_Ba_eq_on_tsupport i j x hx,
          h_diffQuot_G_eq_on_tsupport i x hx,
          h_diffQuot_G_eq_on_tsupport j x hx]
    have h_eq_zero_off : ∀ x ∉ tsupport η,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G j) x) = 0 := by
      intro x hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [hη_zero]; ring
    have h_eq_zero_off_chartBilinear : ∀ x ∉ tsupport η,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
          (η x) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial j) x) = 0 := by
      intro x hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [hη_zero]; ring
    have h_compl_zero_LHS : ∀ x ∉ K_0,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (G j) x) = 0 := by
      intro x hx
      rw [hK_0_def] at hx
      exact h_eq_zero_off x hx
    have hK_0_meas : MeasurableSet K_0 := by
      rw [hK_0_def]
      exact (isClosed_tsupport η).measurableSet
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero_LHS]
    refine setIntegral_congr_fun hK_0_meas ?_
    intro x hx
    rw [hK_0_def] at hx
    exact h_eq_on_tsupport x hx
  have h_LHS_principal_eq :
      B.lam *
        ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G l) x)^2
          ∂(volume : Measure EuclN) =
      B.lam *
        ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial l) x ^ 2
          ∂(volume : Measure EuclN) := by
    have h_inner_eq :
        (fun x => (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (G l) x)^2) =
        (fun x => (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial l) x ^ 2) :=
      h_LHS_pointwise
    rw [h_inner_eq]
  have h_subst : chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
      chartBilinear_RHS (I := I) (M := M) D K_0 η k h :=
    chartBilinear_substitution_identity_holds (I := I) (M := M) D
      hK_0_compact hK_0_in_chart hη hη_supp (le_refl _) k hh hh_le
      h_thick_K_0_in_chart
  unfold chartBilinear_LHS chartBilinear_RHS at h_subst
  have h_principal_eq :
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h =
        c_term_chartBilinear (I := I) (M := M) D K_0 η k h
          - cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
          - cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
          - cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
          - f_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
    linarith

  have h_test_supp_in_cthick_h :
      Function.support
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart) ⊆
      Metric.cthickening |h| (tsupport η) := by
    intro x hx
    rw [Function.mem_support] at hx
    have h_unfold :
        DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart x =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun y : EuclN => η y ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart y) x := rfl
    rw [h_unfold] at hx
    have hh_neg : (-h) ≠ 0 := neg_ne_zero.mpr hh
    rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh_neg
        (fun y : EuclN => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart y) x] at hx
    have h_num_ne : (η (x + (-h) • EuclideanSpace.single k 1))^2 *
        (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart
            (x + (-h) • EuclideanSpace.single k 1)) -
        (η x)^2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart x) ≠ 0 := by
      intro h_zero
      apply hx
      rw [h_zero, zero_div]
    by_cases hηx : η x = 0
    · have hFx_zero : (η x)^2 *
          (DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x) = 0 := by
        rw [show (η x)^2 = 0 from by rw [hηx]; ring, zero_mul]
      rw [hFx_zero, sub_zero] at h_num_ne
      have hηy_ne : η (x + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
        intro h_zero
        apply h_num_ne
        rw [show (η (x + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
          rw [h_zero]; ring, zero_mul]
      have hy_in_supp :
          x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
        subset_tsupport η (Function.mem_support.mpr hηy_ne)
      refine Metric.mem_cthickening_of_dist_le _
        (x + (-h) • EuclideanSpace.single k 1) |h| (tsupport η) hy_in_supp ?_
      rw [dist_eq_norm]
      have h_diff_eq : x - (x + (-h) • EuclideanSpace.single k 1) =
          h • EuclideanSpace.single k 1 := by
        rw [sub_add_eq_sub_sub]
        rw [sub_self, zero_sub, neg_smul, neg_neg]
      rw [h_diff_eq]
      rw [norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    · have hx_in_supp : x ∈ tsupport η :=
        subset_tsupport η (Function.mem_support.mpr hηx)
      exact h_self_subset_cthick_h hx_in_supp
  have h_c_term_eq :
      c_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∫ x in (Set.univ : Set EuclN), B.c x * D.u_chart x *
        DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart x
        ∂(volume : Measure EuclN) := by
    unfold c_term_chartBilinear
    have h_supp_in_cthick_h_K_0 :
        Function.support
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart) ⊆
        Metric.cthickening |h| K_0 := by
      rw [hK_0_def]; exact h_test_supp_in_cthick_h
    have h_test_eq :
        (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          (d := Module.finrank ℝ E) k h η D.u_chart) =
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart) := rfl
    have h_cthick_h_K_0_subset_cthick1 :
        Metric.cthickening |h| K_0 ⊆ Metric.cthickening R₀ (tsupport η) := by
      rw [hK_0_def]; exact h_cthick_h_subset_cthickR0
    have h_Bc_match_on_supp : ∀ x ∈ Metric.cthickening |h| K_0,
        B.c x = densityOnEuclid (I := I) g α x := fun x hx =>
      h_B_c_match x (h_cthick_h_K_0_subset_cthick1 hx)
    have h_cthick_h_K_0_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
      Metric.isClosed_cthickening.measurableSet
    have h_F_zero_off : ∀ x ∉ Metric.cthickening |h| K_0,
        B.c x * D.u_chart x *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x) = 0 := by
      intro x hx
      have h_test_zero :
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x = 0 := by
        by_contra h_ne
        exact hx (h_supp_in_cthick_h_K_0 h_ne)
      rw [h_test_zero, mul_zero]
    have h_step_a :
        (∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.u_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
              (d := Module.finrank ℝ E) k h η D.u_chart x
            ∂(volume : Measure EuclN)) =
        (∫ x in Metric.cthickening |h| K_0,
          B.c x * D.u_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN)) := by
      refine setIntegral_congr_fun h_cthick_h_K_0_meas ?_
      intro x hx
      simp only
      rw [← h_Bc_match_on_supp x hx, h_test_eq]
    rw [h_step_a]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_F_zero_off,
        ← MeasureTheory.setIntegral_univ]
  have h_f_term_eq :
      f_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∫ x in (Set.univ : Set EuclN),
        (densityOnEuclid (I := I) g α x * D.f_chart x) *
        DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart x
        ∂(volume : Measure EuclN) := by
    unfold f_term_chartBilinear
    have h_supp_in_cthick_h_K_0 :
        Function.support
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart) ⊆
        Metric.cthickening |h| K_0 := by
      rw [hK_0_def]; exact h_test_supp_in_cthick_h
    have h_test_eq :
        (DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
          (d := Module.finrank ℝ E) k h η D.u_chart) =
        (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
          (d := Module.finrank ℝ E) k h η D.u_chart) := rfl
    have h_cthick_h_K_0_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
      Metric.isClosed_cthickening.measurableSet
    have h_F_zero_off : ∀ x ∉ Metric.cthickening |h| K_0,
        (densityOnEuclid (I := I) g α x * D.f_chart x) *
          (DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x) = 0 := by
      intro x hx
      have h_test_zero :
          DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.u_chart x = 0 := by
        by_contra h_ne
        exact hx (h_supp_in_cthick_h_K_0 h_ne)
      rw [h_test_zero, mul_zero]
    have h_step_a :
        (∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.f_chart x *
            DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest.standardNirenbergTest
              (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN)) =
        (∫ x in Metric.cthickening |h| K_0,
          (densityOnEuclid (I := I) g α x * D.f_chart x) *
            DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
              (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN)) := by
      refine setIntegral_congr_fun h_cthick_h_K_0_meas ?_
      intro x _hx
      simp only
      rw [h_test_eq]
    rw [h_step_a]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_F_zero_off,
        ← MeasureTheory.setIntegral_univ]
  have h_cross_1_eq :
      cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), ∫ x,
            2 * DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h
              (fun y : EuclN => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart x
          ∂(volume : Measure EuclN) := by
    unfold cross_1_term_chartBilinear
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_compl_zero : ∀ x ∉ K_0,
        2 * DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h
          (fun y : EuclN => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart x = 0 := by
      intro x hx
      rw [hK_0_def] at hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_zero]; ring
    have hK_0_meas : MeasurableSet K_0 := by
      rw [hK_0_def]; exact (isClosed_tsupport η).measurableSet
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero]
    refine setIntegral_congr_fun hK_0_meas ?_
    intro x hx
    rw [hK_0_def] at hx
    simp only
    rw [h_translate_Ba_eq_on_tsupport i j x hx]
  have h_cross_2_eq :
      cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), ∫ x,
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun y : EuclN => B.a y i j) x * (η x)^2 *
            ((D.weak_partial i) x) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) x
          ∂(volume : Measure EuclN) := by
    unfold cross_2_term_chartBilinear
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_compl_zero : ∀ x ∉ K_0,
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y : EuclN => B.a y i j) x * (η x)^2 *
        (D.weak_partial i x) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial j) x = 0 := by
      intro x hx
      rw [hK_0_def] at hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_zero]; ring
    have hK_0_meas : MeasurableSet K_0 := by
      rw [hK_0_def]; exact (isClosed_tsupport η).measurableSet
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero]
    refine setIntegral_congr_fun hK_0_meas ?_
    intro x hx
    rw [hK_0_def] at hx
    simp only
    rw [h_diffQuot_Ba_eq_on_tsupport i j x hx]
  have h_cross_3_eq :
      cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), ∫ x,
            2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun y : EuclN => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((D.weak_partial i) x) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart x
          ∂(volume : Measure EuclN) := by
    unfold cross_3_term_chartBilinear
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_compl_zero : ∀ x ∉ K_0,
        2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y : EuclN => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        (D.weak_partial i x) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.u_chart x = 0 := by
      intro x hx
      rw [hK_0_def] at hx
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hη_zero]; ring
    have hK_0_meas : MeasurableSet K_0 := by
      rw [hK_0_def]; exact (isClosed_tsupport η).measurableSet
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero]
    refine setIntegral_congr_fun hK_0_meas ?_
    intro x hx
    rw [hK_0_def] at hx
    simp only
    rw [h_diffQuot_Ba_eq_on_tsupport i j x hx]
  set A_1 : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E), ∫ x,
          2 * DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x
        ∂(volume : Measure EuclN) with hA_1_def
  set A_2 : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E), ∫ x,
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j) x * (η x)^2 *
          ((D.weak_partial i) x) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial j) x
        ∂(volume : Measure EuclN) with hA_2_def
  set A_3 : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E), ∫ x,
          2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y : EuclN => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((D.weak_partial i) x) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x
        ∂(volume : Measure EuclN) with hA_3_def
  set A_f : ℝ :=
    ∫ x in (Set.univ : Set EuclN),
      (densityOnEuclid (I := I) g α x * D.f_chart x) *
      DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η D.u_chart x
      ∂(volume : Measure EuclN) with hA_f_def
  set A_c : ℝ :=
    ∫ x in (Set.univ : Set EuclN), B.c x * D.u_chart x *
      DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η D.u_chart x
      ∂(volume : Measure EuclN) with hA_c_def
  have h_principal_in_A :
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h =
        A_c - A_1 - A_2 - A_3 - A_f := by
    rw [h_principal_eq, h_c_term_eq, h_cross_1_eq, h_cross_2_eq, h_cross_3_eq,
        h_f_term_eq]
  have h_LHS_le_principal_A :
      B.lam *
        ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial l) x ^ 2
          ∂(volume : Measure EuclN) ≤
      A_c - A_1 - A_2 - A_3 - A_f := by
    rw [← h_LHS_principal_eq, ← h_principal_in_A, ← h_RHS_principal_eq]
    exact h_principal_le
  have h_triangle :
      A_c - A_1 - A_2 - A_3 - A_f ≤
        |A_1| + |A_2| + |A_3| + |A_f| + |A_c| := by
    calc A_c - A_1 - A_2 - A_3 - A_f
        ≤ |A_c - A_1 - A_2 - A_3 - A_f| := le_abs_self _
      _ = |(- A_1) + (-A_2) + (-A_3) + (-A_f) + A_c| := by ring_nf
      _ ≤ |-A_1| + |-A_2| + |-A_3| + |-A_f| + |A_c| := by
          have h1 := abs_add_le ((- A_1) + (-A_2) + (-A_3) + (-A_f)) A_c
          have h2 := abs_add_le ((- A_1) + (-A_2) + (-A_3)) (-A_f)
          have h3 := abs_add_le ((- A_1) + (-A_2)) (-A_3)
          have h4 := abs_add_le (-A_1) (-A_2)
          linarith
      _ = |A_1| + |A_2| + |A_3| + |A_f| + |A_c| := by
          rw [abs_neg, abs_neg, abs_neg, abs_neg]
  exact h_LHS_le_principal_A.trans h_triangle

end ChartBilinearUniformDiffQuotBoundCanonical

end Laplacian
end Analysis
end DifferentialGeometry
