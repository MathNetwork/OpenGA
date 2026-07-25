import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Integration.Measure.Invariance


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem exists_pou_chartDensity_bound_on_chartTarget
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ M_α : ℝ, 0 ≤ M_α ∧
      ∀ y ∈ (extChartAt I α).target,
        (chartAtlasPOU I M α : M → ℝ) ((extChartAt I α).symm y) *
            chartDensity g α ((extChartAt I α).symm y) ≤ M_α := by
  classical
  set ρα : M → ℝ := fun x => (chartAtlasPOU I M α : M → ℝ) x with hρα_def
  set T : Set M := tsupport ρα with hT_def
  have hT_closed : IsClosed T := isClosed_tsupport _
  have hT_compact : IsCompact T := hT_closed.isCompact
  have hT_sub_chart : T ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate (I := I) (M := M) α)
  have hT_sub_extSrc : T ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I) (M := M)]
    exact hT_sub_chart hx
  have hext_contOn : ContinuousOn (extChartAt I α) T :=
    (continuousOn_extChartAt α).mono hT_sub_extSrc
  set K : Set E := (extChartAt I α) '' T with hK_def
  have hK_compact : IsCompact K := hT_compact.image_of_continuousOn hext_contOn
  have hK_sub_target : K ⊆ (extChartAt I α).target := by
    rintro y ⟨x, hxT, rfl⟩
    exact (extChartAt I α).map_source (hT_sub_extSrc hxT)
  have hρα_cont : Continuous ρα := ((chartAtlasPOU I M α)).contMDiff.continuous
  have hρα_le_one : ∀ x, ρα x ≤ 1 :=
    fun x => (chartAtlasPOU (I := I) (M := M)).le_one _ _
  have hρα_nonneg : ∀ x, 0 ≤ ρα x :=
    fun x => (chartAtlasPOU (I := I) (M := M)).nonneg _ _
  have hdens_contOn : ContinuousOn (chartDensity g α) (chartAt H α).source := by
    have := chartDensity_continuousOn (I := I) g α
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M)] using this
  by_cases hK_ne : K.Nonempty
  · obtain ⟨M_sup, hM_sup_pos, hM_sup_le⟩ :=
      (by
        have hdens_pos_target : ∀ y ∈ (extChartAt I α).target,
            0 < chartDensity g α ((extChartAt I α).symm y) := by
          intro y hy
          have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
            (extChartAt I α).map_target hy
          have hsource' : (extChartAt I α).symm y ∈ (chartAt H α).source := by
            rw [extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hsource
            exact hsource
          have hsymm_in_base :
              (extChartAt I α).symm y ∈
                (trivializationAt E (TangentSpace I) α).baseSet := by
            rw [trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M)]
            exact hsource'
          exact chartDensity_pos (I := I) g α hsymm_in_base
        have hdens_symm_contOn :
            ContinuousOn
              (fun y : E => chartDensity g α ((extChartAt I α).symm y))
              (extChartAt I α).target := by
          refine (hdens_contOn).comp (continuousOn_extChartAt_symm (I := I) α) ?_
          intro y hy
          have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
            (extChartAt I α).map_target hy
          rwa [extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hsource
        have hdens_symm_contOn_K :
            ContinuousOn
              (fun y : E => chartDensity g α ((extChartAt I α).symm y)) K :=
          hdens_symm_contOn.mono hK_sub_target
        obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
          hK_compact.exists_isMaxOn hK_ne hdens_symm_contOn_K
        refine ⟨chartDensity g α ((extChartAt I α).symm y₀),
          hdens_pos_target y₀ (hK_sub_target hy₀_mem), ?_⟩
        intro y hy
        exact hy₀_max hy : ∃ M_sup : ℝ, 0 < M_sup ∧ ∀ y ∈ K,
          chartDensity g α ((extChartAt I α).symm y) ≤ M_sup)
    refine ⟨M_sup, hM_sup_pos.le, ?_⟩
    intro y hy_target
    by_cases hy_K : y ∈ K
    · have hdens_le : chartDensity g α ((extChartAt I α).symm y) ≤ M_sup :=
        hM_sup_le y hy_K
      have hdens_nn : 0 ≤ chartDensity g α ((extChartAt I α).symm y) :=
        Real.sqrt_nonneg _
      have hρ_le : ρα ((extChartAt I α).symm y) ≤ 1 := hρα_le_one _
      have hρ_nn : 0 ≤ ρα ((extChartAt I α).symm y) := hρα_nonneg _
      have step₁ :
          ρα ((extChartAt I α).symm y) *
              chartDensity g α ((extChartAt I α).symm y)
            ≤ 1 * chartDensity g α ((extChartAt I α).symm y) :=
        mul_le_mul_of_nonneg_right hρ_le hdens_nn
      have step₂ :
          1 * chartDensity g α ((extChartAt I α).symm y) ≤ 1 * M_sup :=
        mul_le_mul_of_nonneg_left hdens_le zero_le_one
      have hM_sup_le' :
          ρα ((extChartAt I α).symm y) *
              chartDensity g α ((extChartAt I α).symm y) ≤ M_sup := by
        have h₁ : ρα ((extChartAt I α).symm y) *
              chartDensity g α ((extChartAt I α).symm y) ≤ 1 * M_sup :=
          le_trans step₁ step₂
        simpa using h₁
      exact hM_sup_le'
    · have hρα_zero : ρα ((extChartAt I α).symm y) = 0 := by
        by_contra h_ne
        have hmem : (extChartAt I α).symm y ∈ Function.support ρα :=
          Function.mem_support.mpr h_ne
        have hmem_T : (extChartAt I α).symm y ∈ T :=
          subset_tsupport _ hmem
        have hy_back : (extChartAt I α) ((extChartAt I α).symm y) = y :=
          (extChartAt I α).right_inv hy_target
        have : y ∈ K := ⟨(extChartAt I α).symm y, hmem_T, hy_back⟩
        exact hy_K this
      have : ρα ((extChartAt I α).symm y) *
            chartDensity g α ((extChartAt I α).symm y) = 0 := by
        rw [hρα_zero]; ring
      rw [this]
      exact hM_sup_pos.le
  · rw [Set.not_nonempty_iff_eq_empty] at hK_ne
    refine ⟨0, le_rfl, ?_⟩
    intro y hy_target
    have hρα_zero : ρα ((extChartAt I α).symm y) = 0 := by
      by_contra h_ne
      have hmem : (extChartAt I α).symm y ∈ Function.support ρα :=
        Function.mem_support.mpr h_ne
      have hmem_T : (extChartAt I α).symm y ∈ T :=
        subset_tsupport _ hmem
      have hy_back : (extChartAt I α) ((extChartAt I α).symm y) = y :=
        (extChartAt I α).right_inv hy_target
      have hyK : y ∈ K := ⟨(extChartAt I α).symm y, hmem_T, hy_back⟩
      rw [hK_ne] at hyK
      exact hyK
    have hprod_zero :
        ρα ((extChartAt I α).symm y) *
            chartDensity g α ((extChartAt I α).symm y) = 0 := by
      rw [hρα_zero]; ring
    rw [hprod_zero]

end Measure
end Integral
end DifferentialGeometry
