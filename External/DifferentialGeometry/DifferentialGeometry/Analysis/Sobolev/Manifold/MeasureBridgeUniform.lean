import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma image_extChartAt_compact_subset_target_of_subset
    {K : Set M} {α : M}
    (hK_compact : IsCompact K) (hK_sub : K ⊆ (chartAt H α).source) :
    IsCompact ((extChartAt I α) '' K) ∧
      (extChartAt I α) '' K ⊆ (extChartAt I α).target := by
  refine ⟨?_, ?_⟩
  · have hsub : K ⊆ (extChartAt I α).source := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hK_sub hx
    have hcont : ContinuousOn (extChartAt I α) K :=
      (continuousOn_extChartAt α).mono hsub
    exact hK_compact.image_of_continuousOn hcont
  · rintro y ⟨x, hx, rfl⟩
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hK_sub hx
    exact (extChartAt I α).map_source hxsrc

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma image_extChartAt_tsupport_subset_image_K
    {u : M → ℝ} {K : Set M} {α : M}
    (hu_supp : tsupport u ⊆ K) :
    (extChartAt I α) '' (tsupport u) ⊆ (extChartAt I α) '' K := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, hu_supp hx, rfl⟩

theorem eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK_compact : IsCompact K) (hK_sub : K ⊆ (chartAt H α).source)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u : M → ℝ}, Measurable u → tsupport u ⊆ K →
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
          ≤ ENNReal.ofReal C *
              eLpNorm (chartPushedRaw I α u) p
                ((volume : Measure
                  (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                  (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  by_cases hK_ne : K.Nonempty
  · obtain ⟨hK_E_compact, hK_E_sub_target⟩ :=
      image_extChartAt_compact_subset_target_of_subset
        (I := I) (M := M) (K := K) (α := α) hK_compact hK_sub
    have hK_E_ne : ((extChartAt I α) '' K).Nonempty := hK_ne.image _
    obtain ⟨C, hC_pos, hC_bnd⟩ :=
      eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform
        (I := I) (M := M) g α hK_E_compact hK_E_ne hK_E_sub_target hp_one hp_top
    refine ⟨C, hC_pos, ?_⟩
    intro u hu_meas hu_supp
    have hu_chart_supp : tsupport u ⊆ (chartAt H α).source := hu_supp.trans hK_sub
    have hu_K_E : (extChartAt I α) '' (tsupport u) ⊆ (extChartAt I α) '' K :=
      image_extChartAt_tsupport_subset_image_K (I := I) (u := u) (K := K) (α := α)
        hu_supp
    exact hC_bnd hu_meas hu_chart_supp hu_K_E
  · rw [Set.not_nonempty_iff_eq_empty] at hK_ne
    refine ⟨1, one_pos, ?_⟩
    intro u _ hu_supp
    have hu_supp_empty : tsupport u ⊆ ∅ := by rw [← hK_ne]; exact hu_supp
    have hu_supp_eq : tsupport u = ∅ := Set.subset_empty_iff.mp hu_supp_empty
    have hu_zero : u = 0 := by
      funext x
      have hx_notsupp : x ∉ tsupport u := by rw [hu_supp_eq]; simp
      exact image_eq_zero_of_notMem_tsupport hx_notsupp
    rw [hu_zero, eLpNorm_zero]
    exact zero_le _

theorem eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {K : Set M} (hK_compact : IsCompact K) (hK_sub : K ⊆ (chartAt H α).source)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u : M → ℝ}, Measurable u → tsupport u ⊆ K →
        eLpNorm (chartPushedRaw I α u) p
            ((volume : Measure
              (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
              eLpNorm u p
                (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  by_cases hK_ne : K.Nonempty
  · obtain ⟨hK_E_compact, hK_E_sub_target⟩ :=
      image_extChartAt_compact_subset_target_of_subset
        (I := I) (M := M) (K := K) (α := α) hK_compact hK_sub
    have hK_E_ne : ((extChartAt I α) '' K).Nonempty := hK_ne.image _
    obtain ⟨C, hC_pos, hC_bnd⟩ :=
      eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform
        (I := I) (M := M) g α hK_E_compact hK_E_ne hK_E_sub_target hp_one hp_top
    refine ⟨C, hC_pos, ?_⟩
    intro u hu_meas hu_supp
    have hu_chart_supp : tsupport u ⊆ (chartAt H α).source := hu_supp.trans hK_sub
    have hu_K_E : (extChartAt I α) '' (tsupport u) ⊆ (extChartAt I α) '' K :=
      image_extChartAt_tsupport_subset_image_K (I := I) (u := u) (K := K) (α := α)
        hu_supp
    exact hC_bnd hu_meas hu_chart_supp hu_K_E
  · rw [Set.not_nonempty_iff_eq_empty] at hK_ne
    refine ⟨1, one_pos, ?_⟩
    intro u _ hu_supp
    have hu_supp_empty : tsupport u ⊆ ∅ := by rw [← hK_ne]; exact hu_supp
    have hu_supp_eq : tsupport u = ∅ := Set.subset_empty_iff.mp hu_supp_empty
    have hu_zero : u = 0 := by
      funext x
      have hx_notsupp : x ∉ tsupport u := by rw [hu_supp_eq]; simp
      exact image_eq_zero_of_notMem_tsupport hx_notsupp
    have hchartPushedRaw_zero :
        chartPushedRaw I α u = (fun _ => (0 : ℝ)) := by
      rw [hu_zero]
      funext y
      classical
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
      · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α (0 : M → ℝ) hy]
        rfl
      · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α (0 : M → ℝ) hy]
    rw [hchartPushedRaw_zero, eLpNorm_zero']
    exact zero_le _

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
