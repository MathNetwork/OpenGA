import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid

noncomputable section

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

def appCcLeibnizPsi (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) :
    ∀ (i k : ℕ), SmoothCcTensor g (b + k) (c + i)
  | 0, k => match k with
      | 0 => Φ
      | (_ + 1) => 0
  | (i + 1), k => match k with
      | 0 => covGrad (I := I) (M := M) g (b + 0) (c + i) (appCcLeibnizPsi g b c Φ i 0)
      | (j + 1) =>
          (if j + 1 < i + 1 then
              covGrad (I := I) (M := M) g (b + (j + 1)) (c + i) (appCcLeibnizPsi g b c Φ i (j + 1))
            else 0) +
            castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
              (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + j) (c + i) (appCcLeibnizPsi g b c Φ i j)))


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_appCcLeibniz_sum (g : SmoothRiemannianMetric I M) (a b c i : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g (b + k) (c + i)) (W : SmoothCcTensor g a b) :
    covGrad (I := I) (M := M) g a (c + i)
        (∑ k ∈ Finset.range (i + 1),
          ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + i) (Ψ k) (iteratedCovGrad g a b k W)) =
      ∑ k ∈ Finset.range (i + 1),
        (ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + (i + 1))
            (covGrad (I := I) (M := M) g (b + k) (c + i) (Ψ k)) (iteratedCovGrad g a b k W) +
          ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + k) (c + i) (Ψ k))
            (iteratedCovGrad g a b (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appCcRS_eq (I := I) (M := M) g a (b + k) (c + i) (Ψ k) (iteratedCovGrad g a b k W)]
  rw [show covGrad (I := I) (M := M) g a (b + k) (iteratedCovGrad g a b k W) =
      iteratedCovGrad g a b (k + 1) W from (iteratedCovGrad_succ g a b k W).symm]
  congr 1


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem appCcLeibnizPsi_succ_zero (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) 0 =
      covGrad (I := I) (M := M) g (b + 0) (c + i) (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0) :=
  rfl


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem appCcLeibnizPsi_succ_succ (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i j : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
          (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) :=
  rfl


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_appCcRS_eq (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (i : ℕ) :
    iteratedCovGrad (I := I) g a c i (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) =
      ∑ k ∈ Finset.range (i + 1),
        ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + i)
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k)
          (iteratedCovGrad (I := I) g a b k W) := by
  classical
  induction i with
  | zero =>
      rw [iteratedCovGrad_zero, Finset.sum_range_one, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      rw [iteratedCovGrad_succ, ih]
      rw [covGrad_appCcLeibniz_sum (I := I) (M := M) g a b c i
        (fun k => appCcLeibnizPsi (I := I) (M := M) g b c Φ i k) W]
      rw [show (∑ k ∈ Finset.range (i + 1),
            (ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + (i + 1))
                (covGrad (I := I) (M := M) g (b + k) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k))
                (iteratedCovGrad g a b k W) +
              ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + k) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k))
                (iteratedCovGrad g a b (k + 1) W))) =
          (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + (i + 1))
              (covGrad (I := I) (M := M) g (b + k) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k))
              (iteratedCovGrad g a b k W)) +
          (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (slotExtend (I := I) (M := M) g (b + k) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k))
              (iteratedCovGrad g a b (k + 1) W)) from Finset.sum_add_distrib]
      rw [Finset.sum_range_succ' (fun j =>
        ccOperatorFieldComp (I := I) (M := M) g a (b + j) (c + (i + 1))
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) j)
          (iteratedCovGrad g a b j W)) (i + 1)]
      rw [show (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (k + 1))
              (iteratedCovGrad g a b (k + 1) W)) =
          (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (if k + 1 < i + 1 then
                  covGrad (I := I) (M := M) g (b + (k + 1)) (c + i)
                    (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (k + 1))
                else 0)
              (iteratedCovGrad g a b (k + 1) W)) +
          (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (slotExtend (I := I) (M := M) g (b + k) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k))
              (iteratedCovGrad g a b (k + 1) W)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [appCcLeibnizPsi_succ_succ]
        rw [show castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + k) + 1 = b + (k + 1))
              (castCcTensorRank g ((b + k) + 1) (by omega : (c + i) + 1 = c + (i + 1))
                (slotExtend (I := I) (M := M) g (b + k) (c + i)
                  (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k))) =
            slotExtend (I := I) (M := M) g (b + k) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k) from by
          rw [castCcTensorRank, castCcTensorSourceRank]]
        rw [appCcRS_add_left]]
      rw [show (∑ k ∈ Finset.range (i + 1),
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (if k + 1 < i + 1 then
                  covGrad (I := I) (M := M) g (b + (k + 1)) (c + i)
                    (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (k + 1))
                else 0)
              (iteratedCovGrad g a b (k + 1) W)) =
          ∑ k ∈ Finset.range i,
            ccOperatorFieldComp (I := I) (M := M) g a (b + (k + 1)) (c + (i + 1))
              (covGrad (I := I) (M := M) g (b + (k + 1)) (c + i)
                (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (k + 1)))
              (iteratedCovGrad g a b (k + 1) W) from by
        rw [Finset.sum_range_succ]
        rw [if_neg (by omega : ¬ (i + 1 < i + 1)), appCcRS_zero_left, add_zero]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < i + 1)]]
      rw [Finset.sum_range_succ' (fun k =>
        ccOperatorFieldComp (I := I) (M := M) g a (b + k) (c + (i + 1))
          (covGrad (I := I) (M := M) g (b + k) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i k))
          (iteratedCovGrad g a b k W)) i]
      rw [appCcLeibnizPsi_succ_zero]
      abel


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_operatorFieldApply_eq (g : SmoothRiemannianMetric I M) (b s : ℕ)
    (Φ : SmoothCcTensor g b s) (W : SmoothCcTensor g 0 b) (i : ℕ) :
    iteratedCovGrad (I := I) g 0 s i (operatorFieldApply (I := I) (M := M) g b s Φ W) =
      ∑ k ∈ Finset.range (i + 1),
        ccOperatorFieldComp (I := I) (M := M) g 0 (b + k) (s + i)
          (appCcLeibnizPsi (I := I) (M := M) g b s Φ i k)
          (iteratedCovGrad (I := I) g 0 b k W) := by
  rw [← appCcRS_zero_eq_appCc (I := I) (M := M) g b s Φ W]
  exact iteratedCovGrad_appCcRS_eq (I := I) (M := M) g 0 b s Φ W i

end Connection
end Integral
end DifferentialGeometry

end
