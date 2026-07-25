import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Banach
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Euclidean.IteratedSobolevBanach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.UniformEmbedding

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

theorem wkpNormChart_cauchy_of_seminormCauchySeq
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {f : ℕ → WkpChart (n := n) (M := M) g k p hp}
    (hf : CauchySeq f) :
    ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j →
      wkpNormChart (n := n) (M := M) g k p
        (fun x => wkpChartFun (f i) x - wkpChartFun (f j) x) ≤
        ENNReal.ofReal ε := by
  intro ε hε_pos
  rw [Metric.cauchySeq_iff] at hf
  obtain ⟨N, hN⟩ := hf ε hε_pos
  refine ⟨N, ?_⟩
  intro i j hi hj
  have hdist := hN i hi j hj
  rw [dist_eq_norm] at hdist
  have h_norm_eq : ‖f i - f j‖ =
      (wkpNormChart (n := n) (M := M) g k p (wkpChartFun (f i - f j))).toReal :=
    rfl
  rw [h_norm_eq] at hdist
  have h_sub_val :
      wkpChartFun (f i - f j) =
        fun x => wkpChartFun (f i) x - wkpChartFun (f j) x := by
    ext x; rfl
  rw [h_sub_val] at hdist
  have h_lt_top : wkpNormChart (n := n) (M := M) g k p
      (fun x => wkpChartFun (f i) x - wkpChartFun (f j) x) < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp
      (MemWkpChart_sub (n := n) (M := M) g hp
        (wkpChartFun_memWkpChart (f i)) (wkpChartFun_memWkpChart (f j)))
  have h_ne_top : wkpNormChart (n := n) (M := M) g k p
      (fun x => wkpChartFun (f i) x - wkpChartFun (f j) x) ≠ ⊤ := h_lt_top.ne
  rw [← ENNReal.ofReal_toReal h_ne_top]
  exact ENNReal.ofReal_le_ofReal hdist.le

theorem chartPushed_cauchy_of_wkpNormChart_cauchy
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {f : ℕ → WkpChart (n := n) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j →
      wkpNormChart (n := n) (M := M) g k p
        (fun x => wkpChartFun (f i) x - wkpChartFun (f j) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) k p
        (fun y => chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (wkpChartFun (f i)) y -
          chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α
            (wkpChartFun (f j)) y)
        (chartTargetEuclid (n := n) (M := M) α) ≤ ENNReal.ofReal ε := by
  intro ε hε_pos
  obtain ⟨N, hN⟩ := h_cauchy ε hε_pos
  refine ⟨N, ?_⟩
  intro i j hi hj
  have h_le := hN i j hi hj
  have h_chartPushed_eq : (fun y => chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α
        (wkpChartFun (f i)) y -
        chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (wkpChartFun (f j)) y) =
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α
        (fun x => wkpChartFun (f i) x - wkpChartFun (f j) x) := by
    funext y
    unfold chartPushed
    ring
  rw [h_chartPushed_eq]
  unfold wkpNormChart at h_le
  have h_summand_le_tsum :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) k p
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (fun x => wkpChartFun (f i) x - wkpChartFun (f j) x))
        (chartTargetEuclid (n := n) (M := M) α) ≤
      ∑' α' : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k p
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α'
            (fun x => wkpChartFun (f i) x - wkpChartFun (f j) x))
          (chartTargetEuclid (n := n) (M := M) α') :=
    ENNReal.le_tsum α
  exact le_trans h_summand_le_tsum h_le

theorem exists_chart_limit
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (n := n) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j →
      wkpNormChart (n := n) (M := M) g k p
        (fun x => wkpChartFun (f i) x - wkpChartFun (f j) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    ∃ v_α : EuclideanSpace ℝ (Fin n) → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := n) k p v_α
        (chartTargetEuclid (n := n) (M := M) α) ∧
      Tendsto
        (fun N =>
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
            (d := n) k p
            (fun y => chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α
              (wkpChartFun (f N)) y - v_α y)
            (chartTargetEuclid (n := n) (M := M) α))
        atTop (𝓝 0) := by
  have h_chart_cauchy := chartPushed_cauchy_of_wkpNormChart_cauchy
    (n := n) (M := M) (g := g) (hp := hp) h_cauchy α
  have h_chart_mem : ∀ N,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
        (d := n) k p
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (wkpChartFun (f N)))
        (chartTargetEuclid (n := n) (M := M) α) := fun N =>
    (wkpChartFun_memWkpChart (f N)) α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.exists_limit_of_wkpNormHalfSpace_cauchy
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    k p hp_one hp_top h_chart_mem h_chart_cauchy

theorem chartPushed_tendstoInMeasure
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (n := n) (M := M) g k p hp}
    (α : M)
    {v_α : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_v_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
      (d := n) k p v_α
      (chartTargetEuclid (n := n) (M := M) α))
    (h_v : Tendsto
      (fun N =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k p
          (fun y => chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α
            (wkpChartFun (f N)) y - v_α y)
          (chartTargetEuclid (n := n) (M := M) α))
      atTop (𝓝 0)) :
    TendstoInMeasure
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)))
      (fun N => chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α
        (wkpChartFun (f N)))
      atTop v_α := by
  have h_eLp : Tendsto
      (fun N => eLpNorm
        (fun y => chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (wkpChartFun (f N)) y - v_α y)
        p (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))))
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε_pos
    rw [ENNReal.tendsto_atTop_zero] at h_v
    obtain ⟨N, hN⟩ := h_v ε hε_pos
    refine ⟨N, ?_⟩
    intro N' hN'
    have h_eLp_le_wkp :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm
        (d := n) (k := k) p
        (fun y => chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (wkpChartFun (f N')) y - v_α y)
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) 0 (Nat.zero_le _) ![]
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
      at h_eLp_le_wkp
    change eLpNorm _ p _ ≤ ε
    exact le_trans h_eLp_le_wkp (hN N' hN')
  have hp_zero : p ≠ 0 := by
    intro h
    rw [h] at hp_one
    exact absurd hp_one (by norm_num : ¬ ((1 : ℝ≥0∞) ≤ 0))
  have h_aesm_seq : ∀ N, AEStronglyMeasurable
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α
        (wkpChartFun (f N)))
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) := fun N =>
    ((wkpChartFun_memWkpChart (f N)) α).memLp.aestronglyMeasurable
  have h_aesm_lim : AEStronglyMeasurable v_α
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) :=
    h_v_mem.memLp.aestronglyMeasurable
  exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_zero hp_top
    h_aesm_seq h_aesm_lim h_eLp

theorem exists_subseq_chartPushed_ae_tendsto
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (n := n) (M := M) g k p hp}
    (α : M)
    {v_α : EuclideanSpace ℝ (Fin n) → ℝ}
    (h_v_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
      (d := n) k p v_α
      (chartTargetEuclid (n := n) (M := M) α))
    (h_v : Tendsto
      (fun N =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k p
          (fun y => chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α
            (wkpChartFun (f N)) y - v_α y)
          (chartTargetEuclid (n := n) (M := M) α))
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ y ∂(volume.restrict
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
                (chartTargetEuclid (n := n) (M := M) α))),
        Tendsto
          (fun i => chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α
            (wkpChartFun (f (ns i))) y)
          atTop (𝓝 (v_α y)) := by
  have h_meas := chartPushed_tendstoInMeasure (n := n) (M := M) (g := g)
    (hp := hp) hp_one hp_top α h_v_mem h_v
  exact h_meas.exists_seq_tendsto_ae

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
