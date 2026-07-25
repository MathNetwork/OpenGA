import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem appCcRS_zero_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (0 : SmoothCcTensor g a b) = 0 := by
  have h := appCcRS_add_right (I := I) (M := M) g a b c Φ 0 0
  rw [add_zero] at h
  have h0 : ccOperatorFieldComp (I := I) (M := M) g a b c Φ 0 + (0 : SmoothCcTensor g a c) =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ 0 +
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ 0 := by
    rw [add_zero]; exact h
  exact (add_left_cancel h0).symm

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_eq_zero_of_covGrad_eq_zero (g : SmoothRiemannianMetric I M) (a b : ℕ)
    (W : SmoothCcTensor g a b)
    (hW : covGrad (I := I) (M := M) g a b W = 0) :
    ∀ k : ℕ, iteratedCovGrad (I := I) g a b (k + 1) W = 0 := by
  intro k
  induction k with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact hW
  | succ k ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma appCcLeibnizPsi_order_zero (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0 =
      iteratedCovGrad (I := I) g b c i Φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change covGrad (I := I) (M := M) g b (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i 0) =
          iteratedCovGrad (I := I) g b c (i + 1) Φ
      rw [ih, iteratedCovGrad_succ]

omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_operatorFieldCompose_of_covGrad_right_eq_zero
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b)
    (hW : covGrad (I := I) (M := M) g a b W = 0) (i : ℕ) :
    iteratedCovGrad (I := I) g a c i
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g a b (c + i)
        (iteratedCovGrad (I := I) g b c i Φ) W := by
  classical
  rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g a b c Φ W i]
  rw [Finset.sum_eq_single 0]
  · rw [iteratedCovGrad_zero, appCcLeibnizPsi_order_zero]
    rfl
  · intro k _ hk0
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g a b W hW k',
      appCcRS_zero_right]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos i)) h0

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
