import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpDualFrameParseval
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffCovDerivBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnDiffCovDeriv connDiff_pairing_mdiffAt connDiffCovDerivOp dLaCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet)
open DifferentialGeometry.Analysis.Laplacian (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one dLaBiContrFibFixedFrame_toModel)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

section DLaGridBrick

open Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

def antidiagonalTupleGridPartialSum (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k

lemma dLaGridWin_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m : ℕ) :
    0 ≤ antidiagonalTupleGridPartialSum b m :=
  Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k

private lemma dLaGridWin_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {m m' : ℕ} (h : m ≤ m') :
    antidiagonalTupleGridPartialSum b m ≤ antidiagonalTupleGridPartialSum b m' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun k _ _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)

lemma one_le_dLaGridWin (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ antidiagonalTupleGridPartialSum b m := by
  have h1 : Combinatorics.antidiagonalTupleGrid b 0 = 1 :=
    Combinatorics.antidiagonalTupleGrid_zero b
  calc (1 : ℝ) = antidiagonalTupleGridPartialSum b 1 := by
        rw [antidiagonalTupleGridPartialSum, Finset.sum_range_one, h1]
    _ ≤ antidiagonalTupleGridPartialSum b m := dLaGridWin_mono b hb hm

lemma grid_le_dLaGridWin (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {k m : ℕ} (h : k < m) :
    Combinatorics.antidiagonalTupleGrid b k ≤ antidiagonalTupleGridPartialSum b m :=
  Finset.single_le_sum
    (f := fun k' => Combinatorics.antidiagonalTupleGrid b k')
    (fun k' _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
    (Finset.mem_range.mpr h)

lemma single_le_grid_dla (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) (hj : 1 ≤ j) :
    b j ≤ Combinatorics.antidiagonalTupleGrid b j := by
  classical
  have hmem : (fun _ : Fin 1 => j) ∈ Finset.Nat.antidiagonalTuple 1 j := by
    rw [Finset.Nat.mem_antidiagonalTuple]
    simp
  have hprod : b j = ∏ m : Fin 1, b ((fun _ : Fin 1 => j) m) := by
    rw [Fin.prod_univ_one]
  rw [hprod, Combinatorics.antidiagonalTupleGrid]
  have h1 : (∏ m : Fin 1, b ((fun _ : Fin 1 => j) m)) ≤
      ∑ e ∈ Finset.Nat.antidiagonalTuple 1 j, ∏ m : Fin 1, b (e m) :=
    Finset.single_le_sum (f := fun e : Fin 1 → ℕ => ∏ m : Fin 1, b (e m))
      (fun e _ => Finset.prod_nonneg fun m _ => hb _) hmem
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n : ℕ => ∑ e ∈ Finset.Nat.antidiagonalTuple n j, ∏ m : Fin n, b (e m))
    (fun n _ => Finset.sum_nonneg fun e _ => Finset.prod_nonneg fun m _ => hb _)
    (Finset.mem_range.mpr (by omega : (1 : ℕ) < j + 1))

private def antidiagonalTupleTotalCount (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ)

private lemma dLaTGridCount_nonneg (j : ℕ) : 0 ≤ antidiagonalTupleTotalCount j :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

private lemma prodTerm_le_antidiagonalTupleGrid_dla (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (k n : ℕ) (hn : n < k + 1) (e : Fin n → ℕ)
    (he : e ∈ Finset.Nat.antidiagonalTuple n k) :
    (∏ m : Fin n, b (e m)) ≤ Combinatorics.antidiagonalTupleGrid b k := by
  rw [Combinatorics.antidiagonalTupleGrid]
  have h1 : (∏ m : Fin n, b (e m)) ≤
      ∑ e' ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e' m) :=
    Finset.single_le_sum (f := fun e' : Fin n → ℕ => ∏ m : Fin n, b (e' m))
      (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)) he
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n' : ℕ => ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k, ∏ m : Fin n', b (e' m))
    (fun n' _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)))
    (Finset.mem_range.mpr hn)

private lemma antidiagonalTupleGrid_mul_le_dla (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j k : ℕ) :
    Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k ≤
      (antidiagonalTupleTotalCount j * antidiagonalTupleTotalCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
  classical
  have hpair : ∀ n ∈ Finset.range (j + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n j,
      ∀ n' ∈ Finset.range (k + 1), ∀ e' ∈ Finset.Nat.antidiagonalTuple n' k,
      (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) ≤
        Combinatorics.antidiagonalTupleGrid b (j + k) := by
    intro n hn e he n' hn' e' he'
    have happend : (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) =
        ∏ m : Fin (n + n'), b (Fin.append e e' m) := by
      rw [Fin.prod_univ_add]
      congr 1
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_left])
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_right])
    rw [happend]
    have hmem : Fin.append e e' ∈ Finset.Nat.antidiagonalTuple (n + n') (j + k) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at he he' ⊢
      rw [Fin.sum_univ_add]
      have h1 : (∑ m : Fin n, Fin.append e e' (Fin.castAdd n' m)) = j := by
        rw [← he]
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_left])
      have h2 : (∑ m : Fin n', Fin.append e e' (Fin.natAdd n m)) = k := by
        rw [← he']
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_right])
      rw [h1, h2]
    have hnn' : n + n' < j + k + 1 := by
      rw [Finset.mem_range] at hn hn'
      omega
    exact prodTerm_le_antidiagonalTupleGrid_dla b hb (j + k) (n + n') hnn' _ hmem
  calc Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k
      = ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ((∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k) := by
        rw [Combinatorics.antidiagonalTupleGrid, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])
    _ ≤ ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          (antidiagonalTupleTotalCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        refine Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun e he => ?_))
        calc (∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k
            = ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                ((∏ m : Fin n, b (e m)) * ∏ m : Fin n', b (e' m)) := by
              rw [Combinatorics.antidiagonalTupleGrid, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n' _ => by rw [Finset.mul_sum])
          _ ≤ ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                Combinatorics.antidiagonalTupleGrid b (j + k) := by
              refine Finset.sum_le_sum (fun n' hn' => Finset.sum_le_sum (fun e' he' => ?_))
              exact hpair n hn e he n' hn' e' he'
          _ = antidiagonalTupleTotalCount k * Combinatorics.antidiagonalTupleGrid b (j + k) := by
              rw [antidiagonalTupleTotalCount, Finset.sum_mul]
              exact Finset.sum_congr rfl (fun n' _ => by
                rw [Finset.sum_const, nsmul_eq_mul])
    _ = ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ) *
          (antidiagonalTupleTotalCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ = (antidiagonalTupleTotalCount j * antidiagonalTupleTotalCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
        rw [show (antidiagonalTupleTotalCount j * antidiagonalTupleTotalCount k) *
            Combinatorics.antidiagonalTupleGrid b (j + k) =
            antidiagonalTupleTotalCount j *
              (antidiagonalTupleTotalCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) from by
          ring]
        rw [show antidiagonalTupleTotalCount j = ∑ n ∈ Finset.range (j + 1),
            ((Finset.Nat.antidiagonalTuple n j).card : ℝ) from rfl]
        rw [Finset.sum_mul]

def antidiagonalTuplePairCount (m1 m2 : ℕ) : ℝ :=
  ∑ k1 ∈ Finset.range m1, ∑ k2 ∈ Finset.range m2, antidiagonalTupleTotalCount k1 * antidiagonalTupleTotalCount k2

lemma dLaPairCount_nonneg (m1 m2 : ℕ) : 0 ≤ antidiagonalTuplePairCount m1 m2 :=
  Finset.sum_nonneg fun k1 _ => Finset.sum_nonneg fun k2 _ =>
    mul_nonneg (dLaTGridCount_nonneg k1) (dLaTGridCount_nonneg k2)

lemma dLaGridWin_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m1 m2 m3 : ℕ)
    (h3 : m1 + m2 ≤ m3 + 1) :
    antidiagonalTupleGridPartialSum b m1 * antidiagonalTupleGridPartialSum b m2 ≤ antidiagonalTuplePairCount m1 m2 * antidiagonalTupleGridPartialSum b m3 := by
  classical
  have hG_nn : ∀ k, 0 ≤ Combinatorics.antidiagonalTupleGrid b k :=
    fun k => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  rw [antidiagonalTupleGridPartialSum, antidiagonalTupleGridPartialSum, Finset.sum_mul]
  rw [antidiagonalTuplePairCount, Finset.sum_mul]
  refine Finset.sum_le_sum fun k1 hk1 => ?_
  calc Combinatorics.antidiagonalTupleGrid b k1 *
        ∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k2 ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k1 *
          Combinatorics.antidiagonalTupleGrid b k2 := by rw [Finset.mul_sum]
    _ ≤ ∑ k2 ∈ Finset.range m2, (antidiagonalTupleTotalCount k1 * antidiagonalTupleTotalCount k2) *
          antidiagonalTupleGridPartialSum b m3 := by
        refine Finset.sum_le_sum fun k2 hk2 => ?_
        refine le_trans (antidiagonalTupleGrid_mul_le_dla b hb k1 k2) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (dLaTGridCount_nonneg k1) (dLaTGridCount_nonneg k2))
        refine grid_le_dLaGridWin b hb ?_
        rw [Finset.mem_range] at hk1 hk2
        omega
    _ = (∑ k2 ∈ Finset.range m2, antidiagonalTupleTotalCount k1 * antidiagonalTupleTotalCount k2) *
          antidiagonalTupleGridPartialSum b m3 := by
        rw [Finset.sum_mul]

end DLaGridBrick

end DifferentialGeometry.Integral.Connection

end
