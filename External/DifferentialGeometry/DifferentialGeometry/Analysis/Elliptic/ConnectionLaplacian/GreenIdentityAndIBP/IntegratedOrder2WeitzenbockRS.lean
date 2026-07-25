import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


lemma covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1 + 1)
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun =
      - tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
            (covGrad (I := I) (M := M) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (I := I) (M := M) g r (s + 1)
    (loweringIntertwinerRS_holds (I := I) (M := M) g r (s + 1))
    (covGrad (I := I) (M := M) g r s S)
    (covGrad (I := I) (M := M) g r s S)


lemma covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S)).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      - tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 := by
  set ΔS : SmoothCcTensor g r s := rawTensorConnLapSmooth (I := I) g r s S with hΔS_def
  rw [tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s ΔS).toFun
    (covGrad (I := I) (M := M) g r s S).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (I := I) (M := M) g r s
    (loweringIntertwinerRS_holds (I := I) (M := M) g r s) S ΔS]
  rw [hΔS_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s S)]


lemma rawTensorConnLap_l2Inner_covGrad_split_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (rawTensorConnLapSmooth (I := I) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      - tensorL2Norm (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 +
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
              (covGrad (I := I) (M := M) g r s S) -
            covGrad (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by
  classical
  set GS : SmoothCcTensor g r (s + 1) := covGrad (I := I) (M := M) g r s S with hGS_def
  set ΔGS : SmoothCcTensor g r (s + 1) :=
    rawTensorConnLapSmooth (I := I) g r (s + 1) GS with hΔGS_def
  set GΔ : SmoothCcTensor g r (s + 1) :=
    covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) with hGΔ_def
  have hcomm : ΔGS = GΔ + (ΔGS - GΔ) := by abel
  nth_rewrite 1 [hcomm]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g r (s + 1)
    GΔ.toFun (ΔGS - GΔ).toFun GS.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ GS)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (ΔGS - GΔ) GS)]
  rw [hGΔ_def, hGS_def]
  rw [covGrad_rawTensorConnLap_l2Inner_covGrad_eq_neg_normSq_rs (I := I) (M := M) g r s S]


theorem weitzenbock_integrated_covGrad_l2_normSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun ^ 2 =
      tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 -
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
              (covGrad (I := I) (M := M) g r s S) -
            covGrad (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g r (s + 1 + 1)
    (covGrad (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s S))]
  rw [covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs (I := I) (M := M) g r s S]
  rw [rawTensorConnLap_l2Inner_covGrad_split_rs (I := I) (M := M) g r s S]
  ring

end Connection
end Integral
end DifferentialGeometry

end
