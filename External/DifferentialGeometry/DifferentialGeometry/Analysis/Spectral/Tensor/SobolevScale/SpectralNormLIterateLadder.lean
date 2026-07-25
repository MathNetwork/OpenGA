import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmEnergyPairing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.SobolevScaleSummable


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ladder_weight_natCast (g₀ : SmoothRiemannianMetric I M)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) (n : ℕ) :
    tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
  unfold tensorSobolevWeight
  rw [Real.rpow_natCast]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma tensorL2Inner_self_eq_norm_toL2_sq (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (X : SmoothCcTensor g₀ r s) :
    tensorL2Inner (I := I) (M := M) g₀ r s X.toFun X.toFun =
      ‖SmoothCcTensor.toL2 X‖ ^ 2 := by
  have h1 : (⟪SmoothCcTensor.toL2 X, SmoothCcTensor.toL2 X⟫_ℝ : ℝ) =
      tensorL2Inner (I := I) (M := M) g₀ r s X.toFun X.toFun := by
    rw [SmoothCcTensor.inner_toL2]
    exact SmoothCcTensor.inner_def X X
  rw [← h1, real_inner_self_eq_norm_sq]

theorem smoothCcToTensorHs_even_norm_eq_toL2_iter (g₀ : SmoothRiemannianMetric I M)
    (p : ℕ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p : ℕ) : ℝ) w‖ =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖ := by
  classical
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p : ℕ) : ℝ) w‖ ^ 2 =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum,
      ← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))]
    refine tsum_congr (fun i => ?_)
    rw [smoothCcToTensorHs_coeff,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) w i p,
      ladder_weight_natCast (I := I) (M := M) g₀ i (2 * p)]
    ring
  have h1 : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p : ℕ) : ℝ) w‖ :=
    norm_nonneg _
  have h2 : 0 ≤ ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖ :=
    norm_nonneg _
  nlinarith [hsq, h1, h2,
    sq_nonneg (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p : ℕ) : ℝ) w‖ -
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖)]

theorem smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) w‖ ^ 2 =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)‖ ^ 2 +
        ‖SmoothCcTensor.toL2 (covGrad (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))‖ ^ 2 := by
  classical
  have hterm : ∀ i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) i ((2 * p + 1 : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) w).coeff i) ^ 2 =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (oneMinusConnLapSmooth (I := I) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)) i := by
    intro i
    rw [smoothCcToTensorHs_coeff,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmooth (I := I) (M := M) g₀
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w) i,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) w i p,
      ladder_weight_natCast (I := I) (M := M) g₀ i (2 * p + 1)]
    ring
  have hcross := tensorL2Inner_eq_tsum_l2Coeff_cross_arm (I := I) (M := M) g₀
    (oneMinusConnLapSmooth (I := I) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)
  have hadd := oneMinusConnLapSmooth_l2Inner_eq_add_covGrad (I := I) (M := M) g₀ 0 2
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)
  have heq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) w‖ ^ 2 =
      tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmooth (I := I) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w)).toFun
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w).toFun := by
    rw [tensorHs.norm_sq_eq_tsum, hcross]
    exact tsum_congr hterm
  rw [heq, hadd,
    tensorL2Inner_self_eq_norm_toL2_sq (I := I) (M := M) g₀ 0 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w),
    tensorL2Inner_self_eq_norm_toL2_sq (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p w))]

theorem smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
    (g₀ : SmoothRiemannianMetric I M) (j : ℕ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 : ℕ) : ℝ) w‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
          (oneMinusConnLapSmooth (I := I) g₀ 0 2 w)‖ := by
  classical
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 : ℕ) : ℝ) w‖ ^ 2 =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
          (oneMinusConnLapSmooth (I := I) g₀ 0 2 w)‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    refine tsum_congr (fun i => ?_)
    rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmooth (I := I) (M := M) g₀
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) w i,
      ladder_weight_natCast (I := I) (M := M) g₀ i (j + 2),
      ladder_weight_natCast (I := I) (M := M) g₀ i j]
    ring
  have h1 : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 : ℕ) : ℝ) w‖ :=
    norm_nonneg _
  have h2 : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
      (oneMinusConnLapSmooth (I := I) g₀ 0 2 w)‖ := norm_nonneg _
  nlinarith [hsq, h1, h2,
    sq_nonneg (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 : ℕ) : ℝ) w‖ -
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j : ℕ) : ℝ)
        (oneMinusConnLapSmooth (I := I) g₀ 0 2 w)‖)]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
