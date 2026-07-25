import DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Analysis.Integration.Measure.Family
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [IsManifold I ∞ M] in
private lemma chartPushed_eq_chartPushedRaw_pou_mul_on_target'
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α u y =
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y := by
  classical
  unfold chartPushed
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) hy]

omit [IsManifold I ∞ M] in
private lemma chartPushed_eq_chartPushedRaw_pou_ae'
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α u
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) := by
  filter_upwards [self_mem_ae_restrict
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)] with y hy
  exact chartPushed_eq_chartPushedRaw_pou_mul_on_target'
    (I := I) (M := M) ρ α u hy

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
private lemma tsupport_pou_mul_subset_tsupport_pou'
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport (ρ α : M → ℝ) := by
  have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by
    funext x; rfl
  rw [h_eq]
  exact tsupport_smul_subset_left
    (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
private lemma measurable_pou_mul
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    {u : M → ℝ} (hu : Measurable u) :
    Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) := by
  have hcont : Continuous (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x) :=
    (ρ α).contMDiff.continuous
  exact hcont.measurable.mul hu

private theorem chartAtlasPOU_pou_decomp
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (u : M → ℝ) (x : M) :
    u x = ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
      (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x * u x := by
  classical
  have hsum : ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
      (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x = 1 :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I) (M := M) x
  rw [← Finset.sum_mul, hsum, one_mul]

private theorem perChart_eLpNorm_le
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (hq_one : 1 ≤ q) (hq_top : q ≠ (⊤ : ℝ≥0∞)) (hqp : q ≤ p)
    (α : M) :
    ∃ K_α : ℝ≥0∞, K_α ≠ ⊤ ∧
      ∀ {u : M → ℝ}, Measurable u → MemWkpChart (I := I) (M := M) g 1 p u →
        eLpNorm
            (fun x : M =>
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x)
            q
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
          K_α * wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  set ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M with hρ_def
  set Kα : Set M := tsupport (ρ α : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα :=
    (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hq_ne_zero : q ≠ 0 := by
    intro h; rw [h] at hq_one; exact absurd hq_one (by norm_num)
  obtain ⟨C_α, hC_α_pos, hbridge⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hq_one hq_top
  have hKα_chart_decomp :=
    image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M) (u := (ρ α : M → ℝ)) (α := α) hKα_sub
  obtain ⟨hKα_chart_compact, hKα_chart_sub_target⟩ := hKα_chart_decomp
  set V_α : ℝ≥0∞ := MeasureTheory.volume
      (toEuclidean ''
        ((extChartAt I α) ''
          (tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ)))) with hV_α_def
  have hV_α_lt_top : V_α < ⊤ :=
    volume_chartImage_tsupport_lt_top (I := I) (M := M) ρ
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α
  have hV_α_ne_top : V_α ≠ ⊤ := ne_of_lt hV_α_lt_top
  set exp_diff : ℝ := 1 / q.toReal - 1 / p.toReal with hexp_diff_def
  set H_α : ℝ≥0∞ := V_α ^ exp_diff with hH_α_def
  have hp_toReal_pos : 0 < p.toReal := by
    have hp_lt_top : p < ⊤ := lt_top_iff_ne_top.mpr hp_top
    have hp_ne_zero : p ≠ 0 := by
      intro h; rw [h] at hp_one; exact absurd hp_one (by norm_num)
    exact ENNReal.toReal_pos hp_ne_zero hp_lt_top.ne
  have hq_toReal_pos : 0 < q.toReal := by
    have hq_lt_top : q < ⊤ := lt_top_iff_ne_top.mpr hq_top
    exact ENNReal.toReal_pos hq_ne_zero hq_lt_top.ne
  have hq_le_p_toReal : q.toReal ≤ p.toReal := ENNReal.toReal_mono hp_top hqp
  have hexp_diff_nonneg : 0 ≤ exp_diff := by
    rw [hexp_diff_def, sub_nonneg]
    rw [one_div, one_div, inv_le_inv₀ hp_toReal_pos hq_toReal_pos]
    exact hq_le_p_toReal
  have hH_α_ne_top : H_α ≠ ⊤ := by
    rw [hH_α_def]
    exact ENNReal.rpow_ne_top_of_nonneg hexp_diff_nonneg hV_α_ne_top
  set K_α : ℝ≥0∞ := ENNReal.ofReal C_α * H_α with hK_α_def
  have hK_α_ne_top : K_α ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH_α_ne_top
  refine ⟨K_α, hK_α_ne_top, ?_⟩
  intro u hu_meas hu
  have h_supp : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ Kα :=
    tsupport_pou_mul_subset_tsupport_pou' (I := I) (M := M) ρ α u
  have h_meas : Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) :=
    measurable_pou_mul (I := I) (M := M) ρ α hu_meas
  have h_bridge :
      eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) q
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C_α *
            eLpNorm (chartPushedRaw I α (fun x : M =>
              (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) q
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
    hbridge h_meas h_supp
  have h_eLpNorm_eq :
      eLpNorm (chartPushedRaw I α (fun x : M =>
          (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) q
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) =
        eLpNorm (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) q
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
    refine eLpNorm_congr_ae ?_
    have h_ae := chartPushed_eq_chartPushedRaw_pou_ae'
      (I := I) (M := M) ρ α u
    exact h_ae.symm
  rw [h_eLpNorm_eq] at h_bridge
  have h_holder :
      eLpNorm (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) q
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≤
        wkpNormChart (I := I) (M := M) g 1 p u * V_α ^ exp_diff :=
    eLpNorm_chartPushed_q_le_wkpNorm_one_subexp (I := I) (M := M) g
      hq_ne_zero hp_top hqp hu α
  calc eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) q
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
      ≤ ENNReal.ofReal C_α *
          eLpNorm (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) q
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := h_bridge
    _ ≤ ENNReal.ofReal C_α *
          (wkpNormChart (I := I) (M := M) g 1 p u * V_α ^ exp_diff) := by
        gcongr
    _ = K_α * wkpNormChart (I := I) (M := M) g 1 p u := by
        rw [hK_α_def, hH_α_def]
        ring

private noncomputable def perChartConst
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (hq_one : 1 ≤ q) (hq_top : q ≠ (⊤ : ℝ≥0∞)) (hqp : q ≤ p) : M → ℝ≥0∞ :=
  fun α =>
    Classical.choose (perChart_eLpNorm_le (I := I) (M := M) g
      hp_one hp_top hq_one hq_top hqp α)

private lemma perChartConst_ne_top
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (hq_one : 1 ≤ q) (hq_top : q ≠ (⊤ : ℝ≥0∞)) (hqp : q ≤ p) (α : M) :
    perChartConst (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α ≠ ⊤ :=
  (Classical.choose_spec (perChart_eLpNorm_le (I := I) (M := M) g
    hp_one hp_top hq_one hq_top hqp α)).1

private lemma perChartConst_bound
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (hq_one : 1 ≤ q) (hq_top : q ≠ (⊤ : ℝ≥0∞)) (hqp : q ≤ p) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) :
    eLpNorm
        (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)
        q
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
      perChartConst (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α *
        wkpNormChart (I := I) (M := M) g 1 p u :=
  (Classical.choose_spec (perChart_eLpNorm_le (I := I) (M := M) g
    hp_one hp_top hq_one hq_top hqp α)).2 hu_meas hu

private theorem perChart_memLp_riemannianMeasure
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (hq_one : 1 ≤ q) (hq_top : q ≠ (⊤ : ℝ≥0∞)) (hqp : q ≤ p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) (α : M) :
    MemLp
      (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)
      q
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  refine ⟨?_, ?_⟩
  · have h_meas : Measurable (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) :=
      measurable_pou_mul (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α hu_meas
    exact h_meas.aestronglyMeasurable
  · have h_bound :=
      perChartConst_bound (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α
        hu_meas hu
    have hK : perChartConst (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α ≠ ⊤ :=
      perChartConst_ne_top (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α
    have hN : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ :=
      ne_of_lt (wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_one hu)
    have hRHS_lt_top :
        perChartConst (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α *
          wkpNormChart (I := I) (M := M) g 1 p u < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact lt_top_iff_ne_top.mpr hK
      · exact lt_top_iff_ne_top.mpr hN
    exact lt_of_le_of_lt h_bound hRHS_lt_top

theorem MemWkpChart.memLp_riemannianMeasure_of_le_exponent
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hq_one : 1 ≤ q) (hq_top : q ≠ ⊤)
    (hqp : q ≤ p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g 1 p u) :
    MemLp u q
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  set S : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hS_def
  have hpointwise : ∀ x : M, u x =
      ∑ α ∈ S, (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x * u x :=
    fun x => chartAtlasPOU_pou_decomp (I := I) (M := M) u x
  have h_ae : u =ᵐ[DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)]
      (∑ α ∈ S, fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Finset.sum_apply]
    change u x = ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x * u x
    exact hpointwise x
  refine (memLp_congr_ae h_ae).mpr ?_
  refine memLp_finset_sum' (ε' := ℝ) S ?_
  intro α _
  exact perChart_memLp_riemannianMeasure (I := I) (M := M) g hp_one hp_top
    hq_one hq_top hqp hu_meas hu α

theorem eLpNorm_riemannianMeasure_le_const_mul_wkpNormChart_of_le_exponent
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p q : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (hq_one : 1 ≤ q) (hq_top : q ≠ (⊤ : ℝ≥0∞))
    (hqp : q ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u : M → ℝ}, Measurable u → MemWkpChart (I := I) (M := M) g 1 p u →
        eLpNorm u q
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
          ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  set S : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hS_def
  set D : ℝ≥0∞ :=
    ∑ α ∈ S, perChartConst (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α
    with hD_def
  have hD_ne_top : D ≠ ⊤ := by
    rw [hD_def]
    apply ENNReal.sum_ne_top.mpr
    intro α _
    exact perChartConst_ne_top (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α
  refine ⟨max 1 D.toReal, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro u hu_meas hu
  have hpointwise : ∀ x : M, u x =
      ∑ α ∈ S, (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x * u x :=
    fun x => chartAtlasPOU_pou_decomp (I := I) (M := M) u x
  have h_eLpNorm_eq :
      eLpNorm u q (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) =
        eLpNorm (∑ α ∈ S, fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) q
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
    refine eLpNorm_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Finset.sum_apply]
    change u x = ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x * u x
    exact hpointwise x
  rw [h_eLpNorm_eq]
  have h_aesm : ∀ α ∈ S,
      AEStronglyMeasurable
        (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
    intro α _
    have h_meas : Measurable (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) :=
      measurable_pou_mul (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α hu_meas
    exact h_meas.aestronglyMeasurable
  have h_minkowski :
      eLpNorm (∑ α ∈ S, fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) q
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
        ∑ α ∈ S, eLpNorm
          (fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) q
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) :=
    eLpNorm_sum_le h_aesm hq_one
  refine h_minkowski.trans ?_
  have h_each : ∀ α ∈ S,
      eLpNorm
          (fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) q
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≤
        perChartConst (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α *
          wkpNormChart (I := I) (M := M) g 1 p u := by
    intro α _
    exact perChartConst_bound (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α
      hu_meas hu
  have h_sum_le :
      (∑ α ∈ S, eLpNorm
          (fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) q
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))) ≤
        ∑ α ∈ S,
          perChartConst (I := I) (M := M) g hp_one hp_top hq_one hq_top hqp α *
            wkpNormChart (I := I) (M := M) g 1 p u :=
    Finset.sum_le_sum h_each
  refine h_sum_le.trans ?_
  rw [← Finset.sum_mul]
  change D * wkpNormChart (I := I) (M := M) g 1 p u ≤
    ENNReal.ofReal (max 1 D.toReal) * wkpNormChart (I := I) (M := M) g 1 p u
  gcongr
  have hD_eq : ENNReal.ofReal D.toReal = D := ENNReal.ofReal_toReal hD_ne_top
  have h_max_le :
      ENNReal.ofReal D.toReal ≤ ENNReal.ofReal (max 1 D.toReal) := by
    apply ENNReal.ofReal_le_ofReal
    exact le_max_right _ _
  rw [hD_eq] at h_max_le
  exact h_max_le

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
