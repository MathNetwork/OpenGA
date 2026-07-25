import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenDivergenceIdentity
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


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
lemma tensorL2Norm_sq_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
  rw [tensorL2Norm_def]
  exact Real.sq_sqrt (tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun)


lemma tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun
        (covGrad (I := I) (M := M) g 0 2 T).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun T.toFun :=
  green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed (I := I) (M := M) g T T


theorem covGrad_l2NormSq_le_rawConnLap_mul_self
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun *
        tensorL2Norm (I := I) (M := M) g 0 2 T.toFun := by
  set ΔT : SmoothCcTensor g 0 2 := rawTensorConnLapSmooth (I := I) g 0 2 T with hΔT_def
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (2 + 1)
      (covGrad (I := I) (M := M) g 0 2 T)]
    rw [hΔT_def]
    exact tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner (I := I) (M := M) g T
  rw [hgreen]
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 2 ΔT.toFun T.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔT)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) T)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔT T)
  have hneg_le :
      - tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun ≤
        |tensorL2Inner (I := I) (M := M) g 0 2 ΔT.toFun T.toFun| :=
    neg_le_abs _
  exact le_trans hneg_le hcs


theorem covGrad_l2Norm_le_geomMean
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun ≤
      Real.sqrt
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun *
          tensorL2Norm (I := I) (M := M) g 0 2 T.toFun) := by
  have hsq := covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  have hnn : 0 ≤ tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
      (covGrad (I := I) (M := M) g 0 2 T).toFun :=
    tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + 1) _
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hsq

end Connection
end Integral
end DifferentialGeometry

end
