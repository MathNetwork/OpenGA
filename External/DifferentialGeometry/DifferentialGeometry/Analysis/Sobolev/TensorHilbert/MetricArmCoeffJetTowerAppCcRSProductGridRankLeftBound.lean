import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma diagonalGrid_leftFactor_step_le (n : ℝ) (hn : 0 ≤ n) (j : ℕ) (cΦ cW : ℕ → ℝ)
    (hcΦ : ∀ i, 0 ≤ cΦ i) (hcW : ∀ l, 0 ≤ cW l) :
    (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
        n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) ≤
      (n + 1) * ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
  classical
  set D : ℝ := ∑ i ∈ Finset.range (j + 1 + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l
    with hD_def
  have hcell_nn : ∀ i, 0 ≤ cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
    intro i; exact mul_nonneg (hcΦ i) (Finset.sum_nonneg (fun l _ => hcW l))
  have hWshift : ∀ m : ℕ, (∑ l ∈ Finset.range m, cW (l + 1)) ≤ ∑ l ∈ Finset.range (m + 1), cW l := by
    intro m
    rw [Finset.sum_range_succ' (fun l => cW l) m]
    exact le_add_of_nonneg_right (hcW 0)
  have hA : (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) ≤ D := by
    rw [hD_def]
    rw [Finset.sum_range_succ' (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn 0))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (hcΦ (i + 1))
    rw [show j + 1 + 1 - (i + 1) = j + 1 - i from by omega]
  have hB : (∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) ≤ D := by
    rw [hD_def]
    rw [Finset.sum_range_succ (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn (j + 1)))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left ?_ (hcΦ i)
    refine le_trans (hWshift (j + 1 - i)) (le_of_eq ?_)
    rw [show j + 1 - i + 1 = j + 1 + 1 - i from by omega]
  calc (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
          n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
      ≤ D + n * D := by
        refine add_le_add hA ?_
        exact mul_le_mul_of_nonneg_left hB hn
    _ = (n + 1) * D := by ring

set_option maxHeartbeats 6400000 in
theorem riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (g : SmoothRiemannianMetric I M) :
    ∀ (j p a b : ℕ) (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g p a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g p (b + j) x
          ((iteratedCovGrad (I := I) g p b j
            (ccOperatorFieldComp (I := I) (M := M) g p a b Φ W)).toSection x) ≤
        diagonalGridGrowthFactor (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
                ((iteratedCovGrad (I := I) g a b i Φ).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g p (a + l) x
                  ((iteratedCovGrad (I := I) g p a l W).toSection x) := by
  intro j
  induction j with
  | zero =>
      intro p a b Φ W x
      rw [iteratedCovGrad_zero, diagonalGridGrowthFactor, pow_zero, one_mul]
      rw [Finset.sum_range_one, Finset.sum_range_one, iteratedCovGrad_zero, iteratedCovGrad_zero]
      rw [appCcRS_toSection (I := I) (M := M) g p a b Φ W x]
      have h := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g p a b x
        (show TensorRSSpace a b I x from Φ.toSection x)
        (show TensorRSSpace p a I x from W.toSection x)
      simpa using h
  | succ j ih =>
      intro p a b Φ W x
      classical
      rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g p b j
        (ccOperatorFieldComp (I := I) (M := M) g p a b Φ W) x]
      rw [covGrad_appCcRS_eq (I := I) (M := M) g p a b Φ W]
      rw [iteratedCovGrad_add]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g p ((b + 1) + j) x
        ((iteratedCovGrad (I := I) g p (b + 1) j
          (ccOperatorFieldComp (I := I) (M := M) g p a (b + 1)
            (covGrad (I := I) (M := M) g a b Φ) W)).toSection x)
        ((iteratedCovGrad (I := I) g p (b + 1) j
          (ccOperatorFieldComp (I := I) (M := M) g p (a + 1) (b + 1)
            (slotExtend (I := I) (M := M) g a b Φ)
            (covGrad (I := I) (M := M) g p a W))).toSection x)) ?_
      set cΦ : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
        ((iteratedCovGrad (I := I) g a b i Φ).toSection x) with hcΦ_def
      set cW : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g p (a + l) x
        ((iteratedCovGrad (I := I) g p a l W).toSection x) with hcW_def
      have hcΦ_nn : ∀ i, 0 ≤ cΦ i := fun i =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g a (b + i) x _
      have hcW_nn : ∀ l, 0 ≤ cW l := fun l =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g p (a + l) x _
      have hGj_nn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) j := appCcGdiag_nonneg (E := E) j
      have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      have hArmA : riemannianFiberNormSq (I := I) (M := M) g p ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g p (b + 1) j
              (ccOperatorFieldComp (I := I) (M := M) g p a (b + 1)
                (covGrad (I := I) (M := M) g a b Φ) W)).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j *
            ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l := by
        refine le_trans (ih p a (b + 1) (covGrad (I := I) (M := M) g a b Φ) W x) ?_
        refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) hGj_nn
        rw [hcΦ_def]
        dsimp only
        rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g a b i Φ x]
      have hArmB : riemannianFiberNormSq (I := I) (M := M) g p ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g p (b + 1) j
              (ccOperatorFieldComp (I := I) (M := M) g p (a + 1) (b + 1)
                (slotExtend (I := I) (M := M) g a b Φ)
                (covGrad (I := I) (M := M) g p a W))).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j *
            ((Module.finrank ℝ E : ℝ) *
              ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
        refine le_trans (ih p (a + 1) (b + 1) (slotExtend (I := I) (M := M) g a b Φ)
          (covGrad (I := I) (M := M) g p a W) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ hGj_nn
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hWinner : (∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g p ((a + 1) + l) x
                ((iteratedCovGrad (I := I) g p (a + 1) l
                  (covGrad (I := I) (M := M) g p a W)).toSection x)) =
            ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hcW_def]
          dsimp only
          rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g p a l W x]
        rw [hWinner]
        have hΦle : riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
              ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                (slotExtend (I := I) (M := M) g a b Φ)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) * cΦ i := by
          rw [hcΦ_def]
          dsimp only
          exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g a b Φ i x
        calc riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
                ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                  (slotExtend (I := I) (M := M) g a b Φ)).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
            ≤ ((Module.finrank ℝ E : ℝ) * cΦ i) * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) :=
                mul_le_mul_of_nonneg_right hΦle
                  (Finset.sum_nonneg (fun l _ => hcW_nn (l + 1)))
          _ = (Module.finrank ℝ E : ℝ) * (cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
                ring
      refine le_trans (add_le_add
        (mul_le_mul_of_nonneg_left hArmA (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hArmB (by norm_num : (0:ℝ) ≤ 2))) ?_
      set Gj : ℝ := diagonalGridGrowthFactor (E := E) j with hGj_def
      set SA : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l
        with hSA_def
      set SB : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
        with hSB_def
      set DG : ℝ := ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l with hDG_def
      have hstep : SA + (Module.finrank ℝ E : ℝ) * SB ≤ ((Module.finrank ℝ E : ℝ) + 1) * DG := by
        rw [hSA_def, hSB_def, hDG_def]
        exact diagonalGrid_leftFactor_step_le (Module.finrank ℝ E : ℝ) hn_nn j cΦ cW hcΦ_nn hcW_nn
      have hGdiag_succ : diagonalGridGrowthFactor (E := E) (j + 1) = (2 * ((Module.finrank ℝ E : ℝ) + 1)) * Gj := by
        rw [hGj_def, diagonalGridGrowthFactor, diagonalGridGrowthFactor, pow_succ]; ring
      rw [hGdiag_succ]
      have hGj_nn' : (0 : ℝ) ≤ Gj := hGj_nn
      nlinarith [mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 2 * Gj), hGj_nn',
        hstep]

end Connection
end Integral
end DifferentialGeometry

end
