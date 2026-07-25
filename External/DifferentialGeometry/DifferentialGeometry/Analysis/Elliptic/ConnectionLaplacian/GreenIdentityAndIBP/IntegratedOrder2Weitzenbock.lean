import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGradientL2Bound
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz

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


lemma covGrad_l2Inner_self_eq_neg_rawConnLap_inner_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1 + 1)
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen (I := I) (M := M) g (s + 1)
    (covGrad (I := I) (M := M) g 0 s S)
    (covGrad (I := I) (M := M) g 0 s S)


lemma covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 := by
  set ΔS : SmoothCcTensor g 0 s := rawTensorConnLapSmooth (I := I) g 0 s S with hΔS_def
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 (s + 1)
    (covGrad (I := I) (M := M) g 0 s ΔS).toFun
    (covGrad (I := I) (M := M) g 0 s S).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen (I := I) (M := M) g s S ΔS]
  rw [hΔS_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S)]


lemma rawConnLap_l2Inner_covGrad_split_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  set GS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hGS_def
  set ΔGS : SmoothCcTensor g 0 (s + 1) :=
    rawTensorConnLapSmooth (I := I) g 0 (s + 1) GS with hΔGS_def
  set GΔ : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) with hGΔ_def
  have hcomm : ΔGS = GΔ + (ΔGS - GΔ) := by abel
  nth_rewrite 1 [hcomm]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
    GΔ.toFun (ΔGS - GΔ).toFun GS.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ GS)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (ΔGS - GΔ) GS)]
  rw [hGΔ_def, hGS_def]
  rw [covGrad_rawConnLap_l2Inner_covGrad_eq_neg_normSq_gen (I := I) (M := M) g s S]


theorem weitzenbock_integrated_covGrad_l2_normSq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
        (covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S) -
            covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth (I := I) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (s + 1 + 1)
    (covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S))]
  rw [covGrad_l2Inner_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g s S]
  rw [rawConnLap_l2Inner_covGrad_split_gen (I := I) (M := M) g s S]
  ring

end Connection
end Integral
end DifferentialGeometry

end
