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

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem exists_cutoff_around_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M} {η : EuclN → ℝ} (hη_supp : HasCompactSupport η)
    (h_cthick_1_in_chart : Metric.cthickening 1 (tsupport η) ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∃ χ : EuclN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      (∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ Metric.cthickening 1 (tsupport η), χ x = 1) ∧
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_supp
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_cthick_1_compact : IsCompact (Metric.cthickening 1 (tsupport η)) :=
    hη_tsupp_compact.cthickening
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    h_cthick_1_compact.exists_cthickening_subset_open h_chart_open
      h_cthick_1_in_chart
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_range, hχ_one, hχ_tsupp⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff
      (d := Module.finrank ℝ E)
      h_cthick_1_compact
      (Metric.isOpen_thickening (δ := δ)
        (E := Metric.cthickening 1 (tsupport η)))
      (Metric.self_subset_thickening hδ_pos _)
  have hχ_tsupp_in_chart : tsupport χ ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    have h1 : x ∈ Metric.thickening δ (Metric.cthickening 1 (tsupport η)) :=
      hχ_tsupp hx
    have h2 : x ∈ Metric.cthickening δ (Metric.cthickening 1 (tsupport η)) :=
      Metric.thickening_subset_cthickening δ _ h1
    exact hδ_in_chart h2
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    have hx_mem := hχ_range hx_range
    exact ⟨hx_mem.1, hx_mem.2⟩
  exact ⟨χ, hχ_smooth, hχ_cs, hχ_nn, hχ_one, hχ_tsupp_in_chart⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem cutoff_fChart_memLp_two_univ
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_supp_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun x => χ x * D.f_chart x) 2 (volume : Measure EuclN) := by
  classical
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupp_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupp_empty hχ_cont.abs.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupp_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have h_supp_compact : IsCompact (tsupport χ) := hχ_cs
  have h_supp_meas : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  have hf_l2_supp : MemLp D.f_chart 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.f_chart_memLp_weighted h_supp_compact h_supp_meas hχ_supp_in
  have h_f_aesm_restrict : AEStronglyMeasurable D.f_chart
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hf_l2_supp.aestronglyMeasurable
  have h_pt_le : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
      ‖χ x * D.f_chart x‖ ≤ ‖M_χ * D.f_chart x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_χ_nn]
    exact mul_le_mul_of_nonneg_right (hM_χ_bd x) (abs_nonneg _)
  have h_prod_aesm_restrict :
      AEStronglyMeasurable (fun x => χ x * D.f_chart x)
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict.mul h_f_aesm_restrict
  have h_restrict_lp : MemLp (fun x => χ x * D.f_chart x) 2
      ((volume : Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hf_l2_supp.const_mul M_χ) h_prod_aesm_restrict h_pt_le
  have h_indicator_eq : (tsupport χ).indicator (fun x => χ x * D.f_chart x) =
      (fun x => χ x * D.f_chart x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hχx, zero_mul]
  have h_indicator_lp :
      MemLp ((tsupport χ).indicator (fun x => χ x * D.f_chart x)) 2
        (volume : Measure EuclN) :=
    (MeasureTheory.memLp_indicator_iff_restrict h_supp_meas).mpr h_restrict_lp
  rw [h_indicator_eq] at h_indicator_lp
  exact h_indicator_lp

end ChartBilinearUniformDiffQuotBoundCanonical

end Laplacian
end Analysis
end DifferentialGeometry
