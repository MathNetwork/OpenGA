import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenDivergenceIdentityAnySection
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGradientL2Bound
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


lemma covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 2 T₀)
    (covGrad (I := I) (M := M) g 0 2 T₀)


theorem secondCovGrad_l2NormSq_le_rawConnLap_three_mul_covGrad
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun *
        tensorL2Norm (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun := by
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T₀ with hS_def
  set ΔS : SmoothCcTensor g 0 3 := rawTensorConnLapSmooth (I := I) g 0 3 S
    with hΔS_def
  change tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 3 ΔS.toFun *
        tensorL2Norm (I := I) (M := M) g 0 3 S.toFun
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (3 + 1)
      (covGrad (I := I) (M := M) g 0 3 S)]
    rw [hΔS_def, hS_def]
    exact covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner (I := I) (M := M) g T₀
  rw [hgreen]
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 3 ΔS.toFun S.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔS)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔS S)
  have hneg_le :
      - tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun ≤
        |tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun| :=
    neg_le_abs _
  exact le_trans hneg_le hcs


theorem covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toFun
        (covGrad (I := I) (M := M) g 0 2 T₀).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toFun ^ 2 := by
  set ΔT₀ : SmoothCcTensor g 0 2 := rawTensorConnLapSmooth (I := I) g 0 2 T₀
    with hΔT₀_def
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 (2 + 1)
    (covGrad (I := I) (M := M) g 0 2 ΔT₀).toFun
    (covGrad (I := I) (M := M) g 0 2 T₀).toFun]
  rw [green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed (I := I) (M := M) g T₀ ΔT₀]
  rw [hΔT₀_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T₀)]

end Connection
end Integral
end DifferentialGeometry

end
