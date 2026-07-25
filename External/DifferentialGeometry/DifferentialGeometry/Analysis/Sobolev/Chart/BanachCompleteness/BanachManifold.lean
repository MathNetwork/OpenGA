import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Banach
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Completeness
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.MeasurablePullback
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.UniformEmbedding


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

section
variable [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_cauchy_of_seminormCauchySeq
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (hf : CauchySeq f) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε := by
  intro ε hε_pos
  rw [Metric.cauchySeq_iff] at hf
  obtain ⟨N, hN⟩ := hf ε hε_pos
  refine ⟨N, ?_⟩
  intro m n hm hn
  have hdist := hN m hm n hn
  rw [dist_eq_norm] at hdist
  have h_norm_eq : ‖f m - f n‖ =
      (wkpNormChart (I := I) (M := M) g k p (wkpChartFun (f m - f n))).toReal := rfl
  rw [h_norm_eq] at hdist
  have h_sub_val :
      wkpChartFun (f m - f n) =
        fun x => wkpChartFun (f m) x - wkpChartFun (f n) x := by
    ext x; rfl
  rw [h_sub_val] at hdist
  have h_lt_top : wkpNormChart (I := I) (M := M) g k p
      (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp
      (MemWkpChart_sub (I := I) (M := M) g hp
        (wkpChartFun_memWkpChart (f m)) (wkpChartFun_memWkpChart (f n)))
  have h_ne_top : wkpNormChart (I := I) (M := M) g k p
      (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≠ ⊤ := h_lt_top.ne
  rw [← ENNReal.ofReal_toReal h_ne_top]
  exact ENNReal.ofReal_le_ofReal hdist.le

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_cauchy_of_wkpNormChart_cauchy
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f m)) y -
          chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f n)) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε := by
  intro ε hε_pos
  obtain ⟨N, hN⟩ := h_cauchy ε hε_pos
  refine ⟨N, ?_⟩
  intro m n hm hn
  have h_le := hN m n hm hn
  have h_chartPushed_eq : (fun y => chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (wkpChartFun (f m)) y -
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)) y) =
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) := by
    funext y
    unfold chartPushed
    ring
  rw [h_chartPushed_eq]
  unfold wkpNormChart at h_le
  have h_summand_le_tsum :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑' α' : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α'
            (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x))
          (chartTargetEuclid (I := I) (M := M) α') :=
    ENNReal.le_tsum α
  exact le_trans h_summand_le_tsum h_le

theorem exists_chart_limit
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    ∃ v_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p v_α
        (chartTargetEuclid (I := I) (M := M) α) ∧
      Tendsto
        (fun n =>
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (fun y => chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
              (wkpChartFun (f n)) y - v_α y)
            (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) := by
  have h_chart_cauchy := chartPushed_cauchy_of_wkpNormChart_cauchy
    (I := I) (M := M) (g := g) (hp := hp) h_cauchy α
  have h_chart_mem : ∀ n,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)))
        (chartTargetEuclid (I := I) (M := M) α) := fun n =>
    (wkpChartFun_memWkpChart (f n)) α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.exists_limit_of_wkpNorm_cauchy
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    k p hp_one hp_top h_chart_mem h_chart_cauchy

noncomputable def chartLimit
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  (exists_chart_limit (I := I) (M := M) g hp_one hp_top h_cauchy α).choose

lemma chartLimit_memWkp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartLimit (I := I) (M := M) hp_one hp_top h_cauchy α)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (exists_chart_limit (I := I) (M := M) g hp_one hp_top h_cauchy α).choose_spec.1

lemma chartLimit_tendsto
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    Tendsto
      (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f n)) y -
            chartLimit (I := I) (M := M) hp_one hp_top h_cauchy α y)
          (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝓝 0) :=
  (exists_chart_limit (I := I) (M := M) g hp_one hp_top h_cauchy α).choose_spec.2

noncomputable def manifoldLimitFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε) : M → ℝ :=
  fun x =>
    ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
      pullbackToManifold (I := I) β
        (chartLimit (I := I) (M := M) hp_one hp_top h_cauchy β) x

omit [NeZero (Module.finrank ℝ E)] in
lemma wkpChartFun_eq_finset_sum_pullback
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) g k p hp) :
    (fun x : M => wkpChartFun u x) =
      fun x =>
        ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
            (I := I) (M := M),
          pullbackToManifold (I := I) β
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
              (wkpChartFun u)) x := by
  classical
  funext x
  have h_eq : ∀ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M),
      pullbackToManifold (I := I) β
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
            (wkpChartFun u)) x =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x *
          wkpChartFun u x := by
    intro β _
    classical
    by_cases hxβ : x ∈ (chartAt H β).source
    · exact pullbackToManifold_chartPushed_apply_of_mem (I := I) β (wkpChartFun u) hxβ
    · rw [pullbackToManifold_apply_of_notMem (I := I) (α := β) _ hxβ]
      have h_subord :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate (I := I) (M := M)
      have h_tsupp : tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H β).source := h_subord β
      have h_x_notin : x ∉ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h => hxβ (h_tsupp h)
      have h_rho_zero :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport h_x_notin
      rw [h_rho_zero]; ring
  rw [Finset.sum_congr rfl h_eq]
  have h_factor :
      ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x *
          wkpChartFun u x =
      (∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) *
        wkpChartFun u x := by
    rw [Finset.sum_mul]
  rw [h_factor]
  rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x, one_mul]

end

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
