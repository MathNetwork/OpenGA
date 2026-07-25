import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Banach
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.UniformEmbedding


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section

variable [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E)] in
private theorem wkpNormChart_cauchy_of_seminormCauchySeq
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
private theorem chartPushed_cauchy_of_wkpNormChart_cauchy
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

private theorem exists_chart_limit
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

omit [NeZero (Module.finrank ℝ E)] in
private theorem chartPushed_tendstoInMeasure
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (α : M)
    {v_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (h_v_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p v_α
      (chartTargetEuclid (I := I) (M := M) α))
    (h_v : Tendsto
      (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f n)) y - v_α y)
          (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝓝 0)) :
    TendstoInMeasure
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      (fun n => chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (wkpChartFun (f n)))
      atTop v_α := by
  have h_eLp : Tendsto
      (fun n => eLpNorm
        (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)) y - v_α y)
        p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε_pos
    rw [ENNReal.tendsto_atTop_zero] at h_v
    obtain ⟨N, hN⟩ := h_v ε hε_pos
    refine ⟨N, ?_⟩
    intro n hn
    have h_eLp_le_wkp :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm
        (d := Module.finrank ℝ E) (k := k) p
        (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)) y - v_α y)
        (chartTargetEuclid (I := I) (M := M) α) 0 (Nat.zero_le _) ![]
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero] at h_eLp_le_wkp
    exact le_trans h_eLp_le_wkp (hN n hn)
  have hp_zero : p ≠ 0 := by
    intro h
    rw [h] at hp_one
    exact absurd hp_one (by norm_num : ¬ ((1 : ℝ≥0∞) ≤ 0))
  have h_aesm_seq : ∀ n, AEStronglyMeasurable
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (wkpChartFun (f n)))
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    ((wkpChartFun_memWkpChart (f n)) α).memLp.aestronglyMeasurable
  have h_aesm_lim : AEStronglyMeasurable v_α
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
    h_v_mem.memLp.aestronglyMeasurable
  exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_zero hp_top
    h_aesm_seq h_aesm_lim h_eLp

omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_subseq_chartPushed_ae_tendsto
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (α : M)
    {v_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (h_v_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p v_α
      (chartTargetEuclid (I := I) (M := M) α))
    (h_v : Tendsto
      (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f n)) y - v_α y)
          (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ y ∂(volume.restrict (chartTargetEuclid (I := I) (M := M) α)),
        Tendsto
          (fun i => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f (ns i))) y)
          atTop (𝓝 (v_α y)) := by
  have h_meas := chartPushed_tendstoInMeasure (I := I) (M := M) (g := g)
    (hp := hp) hp_one hp_top α h_v_mem h_v
  exact h_meas.exists_seq_tendsto_ae

end

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
