import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Embedding.Subcritical
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Euclidean.Morrey
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevHalfSpace

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

namespace EuclideanTowerStep

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Chart

abbrev pOne (d : ℕ) (p : ℝ) : ℝ := TowerStep.pOne d p

abbrev subcriticalConstant (k d : ℕ) [NeZero d] (p : ℝ) : ℝ :=
  TowerStep.subcriticalConstant k d p

lemma subcriticalConstant_nonneg (k : ℕ) (p : ℝ) :
    0 ≤ subcriticalConstant k d p :=
  TowerStep.subcriticalConstant_nonneg k d p

theorem MemWkpHalfSpace_subcritical_iterated
    (k : ℕ) {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {f : EuN → ℝ}
    (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ interiorHalfSpace Ω)
    (hf : MemWkpHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω) :
    MemWkpHalfSpace (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ∧
      wkpNormHalfSpace (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ≤
        ENNReal.ofReal (subcriticalConstant k d p) *
          wkpNormHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  have hΩ_int_open : IsOpen (interiorHalfSpace (d := d) Ω) :=
    interiorHalfSpace_isOpen hΩ
  have hf' : MemWkp (d := d) (k + 1) (ENNReal.ofReal p) f
      (interiorHalfSpace Ω) := hf
  exact TowerStep.MemWkp_subcritical_iterated (d := d) k hp_one hp_dim
    hΩ_int_open hf_compact hf_supp hf'

theorem MemWkpHalfSpace_succ_subcritical_step
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {f : EuN → ℝ}
    (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ interiorHalfSpace Ω)
    (hf : MemWkpHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω) :
    MemWkpHalfSpace (d := d) k
        (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormHalfSpace (d := d) k
            (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ≤
          ENNReal.ofReal C *
            wkpNormHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  obtain ⟨h_mem, h_norm⟩ :=
    MemWkpHalfSpace_subcritical_iterated (d := d) k hp_one hp_dim hΩ
      hf_compact hf_supp hf
  have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
  refine ⟨?_, ?_⟩
  · rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_mem
  · refine ⟨subcriticalConstant k d p, subcriticalConstant_nonneg k p, ?_⟩
    rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_norm

end EuclideanTowerStep

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

theorem wkpNormChart_succ_subcritical_step_withBoundary_perChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ},
        (∀ α : M,
          HasCompactSupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          tsupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) →
        MemWkpChart (n := n) (M := M) g (k + 1) (ENNReal.ofReal p) u →
          MemWkpChart (n := n) (M := M) g k
              (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ∧
            wkpNormChart (n := n) (M := M) g k
                (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ≤
              ENNReal.ofReal C *
                wkpNormChart (n := n) (M := M) g (k + 1) (ENNReal.ofReal p) u := by
  classical
  set C : ℝ := EuclideanTowerStep.subcriticalConstant k n p with hC_def
  have hC_nn : 0 ≤ C :=
    EuclideanTowerStep.subcriticalConstant_nonneg (d := n) k p
  refine ⟨C, hC_nn, ?_⟩
  intro u h_compact h_supp hu
  have h_per_chart : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
          (d := n) k (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) ≤
        ENNReal.ofReal C *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
            (d := n) (k + 1) (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)
            (chartTargetEuclid (n := n) (M := M) α) := by
    intro α
    have h_iter :=
      EuclideanTowerStep.MemWkpHalfSpace_subcritical_iterated (d := n) k
        hp_one hp_dim
        (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
        (h_compact α) (h_supp α) (hu α)
    obtain ⟨h_mem_p1, h_norm_p1⟩ := h_iter
    have h_pOne_eq : EuclideanTowerStep.pOne n p =
        (n : ℝ) * p / ((n : ℝ) - p) := rfl
    refine ⟨?_, ?_⟩
    · rw [show ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)) =
        ENNReal.ofReal (EuclideanTowerStep.pOne n p) from by rw [h_pOne_eq]]
      exact h_mem_p1
    · rw [show ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)) =
        ENNReal.ofReal (EuclideanTowerStep.pOne n p) from by rw [h_pOne_eq]]
      exact h_norm_p1
  refine ⟨fun α => (h_per_chart α).1, ?_⟩
  unfold wkpNormChart
  rw [show ENNReal.ofReal C * ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) (k + 1) (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) =
      ∑' α : M, ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) (k + 1) (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) from
    (ENNReal.tsum_mul_left).symm]
  exact ENNReal.tsum_le_tsum (fun α => (h_per_chart α).2)

theorem wkpNormChart_succ_subcritical_step_withBoundary_perChart_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ},
        (∀ α : M,
          ContDiff ℝ (⊤ : ℕ∞)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          HasCompactSupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          tsupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) →
        MemWkpChart (n := n) (M := M) g (k + 1) (ENNReal.ofReal p) u →
          MemWkpChart (n := n) (M := M) g k
              (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ∧
            wkpNormChart (n := n) (M := M) g k
                (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ≤
              ENNReal.ofReal C *
                wkpNormChart (n := n) (M := M) g (k + 1) (ENNReal.ofReal p) u := by
  obtain ⟨C, hC_nn, h⟩ :=
    wkpNormChart_succ_subcritical_step_withBoundary_perChart (n := n) (M := M)
      g (k := k) hp_one hp_dim
  refine ⟨C, hC_nn, ?_⟩
  intro u _hu_smooth h_compact h_supp hu
  exact h h_compact h_supp hu

theorem dim_lt_mul_sobolevConjugate_of_dim_lt_succ_mul
    (d : ℕ) (k : ℕ) (p : ℝ) (hp_pos : 0 < p) (hp_dim : p < (d : ℝ))
    (hkp : (d : ℝ) < (k + 1 : ℝ) * p) :
    (d : ℝ) < (k : ℝ) * ((d : ℝ) * p / ((d : ℝ) - p)) :=
  DifferentialGeometry.Analysis.Sobolev.Chart.IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
    d k p hp_pos hp_dim hkp

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
