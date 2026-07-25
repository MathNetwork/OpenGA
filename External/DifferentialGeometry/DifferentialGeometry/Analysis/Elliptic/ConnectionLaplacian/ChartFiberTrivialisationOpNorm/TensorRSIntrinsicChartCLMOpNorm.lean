import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.ChartJUniformBoundLocallyConstant

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma tensorRSIntrinsicChartCLM_pointwise_opNorm_le_factors
    (r s : ℕ) (α : M) (T : Π b' : M, TensorRSSpace r s I b') (b : M)
    {C_fib C_J : ℝ}
    (hC_fib : ∀ D : TensorRSModel r s ℝ E,
      ‖tensorRSChartFiberFromModel (I := I) r s α b D‖ ≤ C_fib * ‖D‖)
    (hC_fib_nn : 0 ≤ C_fib)
    (hC_J : ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ≤ C_J)
    (_hC_J_nn : 0 ≤ C_J)
    (X : TangentSpace I b) :
    ‖tensorRSIntrinsicChartCLM (I := I) r s α T b X‖ ≤
      C_fib * C_J *
        ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T ∘
          (extChartAt I α).symm) (extChartAt I α b)‖ * ‖X‖ := by
  classical
  set F : E → TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm with hF_def
  set p : E := extChartAt I α b with hp_def
  set D : TensorRSModel r s ℝ E := fderiv ℝ F p (trivToE (I := I) α b X) with hD_def
  have h_apply :
      tensorRSIntrinsicChartCLM (I := I) r s α T b X =
        tensorRSChartFiberFromModel (I := I) r s α b D := by
    rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α T b X]
  rw [h_apply]
  have h_fib_le : ‖tensorRSChartFiberFromModel (I := I) r s α b D‖ ≤ C_fib * ‖D‖ :=
    hC_fib D
  have h_D_le_fderiv :
      ‖D‖ ≤ ‖fderiv ℝ F p‖ * ‖trivToE (I := I) α b X‖ := by
    rw [hD_def]
    exact (fderiv ℝ F p).le_opNorm (trivToE (I := I) α b X)
  have h_trivToE_le :
      ‖trivToE (I := I) α b X‖ ≤ ‖trivToE (I := I) α b‖ * ‖X‖ :=
    (trivToE (I := I) α b).le_opNorm X
  have h_triv_J :
      ‖trivToE (I := I) α b‖ = ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ := rfl
  have h_X_nn : 0 ≤ ‖X‖ := norm_nonneg _
  have h_trivToE_le_CJ : ‖trivToE (I := I) α b X‖ ≤ C_J * ‖X‖ := by
    refine h_trivToE_le.trans ?_
    rw [h_triv_J]
    exact mul_le_mul_of_nonneg_right hC_J h_X_nn
  set N : ℝ := ‖fderiv ℝ F p‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have h_trivToE_nn : 0 ≤ ‖trivToE (I := I) α b X‖ := norm_nonneg _
  have h_D_le :
      ‖D‖ ≤ N * (C_J * ‖X‖) :=
    h_D_le_fderiv.trans (mul_le_mul_of_nonneg_left h_trivToE_le_CJ hN_nn)
  have h_D_nn : 0 ≤ ‖D‖ := norm_nonneg _
  have h_main_step :
      ‖tensorRSChartFiberFromModel (I := I) r s α b D‖ ≤ C_fib * (N * (C_J * ‖X‖)) :=
    h_fib_le.trans (mul_le_mul_of_nonneg_left h_D_le hC_fib_nn)
  have h_rearrange :
      C_fib * (N * (C_J * ‖X‖)) = C_fib * C_J * N * ‖X‖ := by ring
  rw [h_rearrange] at h_main_step
  exact h_main_step

end Connection
end Integral
end DifferentialGeometry

end
