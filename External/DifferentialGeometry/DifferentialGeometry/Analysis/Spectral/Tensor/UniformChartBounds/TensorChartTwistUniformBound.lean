import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.ChartJUniformBoundLocallyConstant
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import Mathlib.Analysis.Normed.Module.Multilinear.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap ContinuousMultilinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]


omit [T2Space M] in
lemma chartRSTwist_opNorm_le
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    ‖chartRSTwist (I := I) (M := M) α b r s T‖ ≤
      ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s *
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ r * ‖T‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · have : (0 : ℝ) ≤ ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s *
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ r * ‖T‖ := by positivity
    exact this
  intro α'
  rw [chartRSTwist_apply]
  have hA :
      ‖α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)‖ ≤
        ‖α'‖ * ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ r := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      α' (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  set u : Tensor0SModel r ℝ E :=
    α'.compContinuousLinearMap
      (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) with hu_def
  have hB : ‖T u‖ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
  have hC :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)‖ ≤
        ‖T u‖ * ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (T u) (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hCsorted :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)‖ ≤
        ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by
    calc
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)‖
          ≤ ‖T u‖ * ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s := hC
      _ = ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by ring
  have h_pow_nn : 0 ≤ ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s := by positivity
  have h_T_le : ‖T u‖ ≤ ‖T‖ * (‖α'‖ * ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ r) := by
    calc
      ‖T u‖ ≤ ‖T‖ * ‖u‖ := hB
      _ ≤ ‖T‖ * (‖α'‖ * ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ r) := by
            have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_left hA h_T_nn
  have h_combined :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)‖ ≤
        ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ r)) :=
    hCsorted.trans <| mul_le_mul_of_nonneg_left h_T_le h_pow_nn
  have h_final :
      ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ r)) =
        ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ s *
          ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ r * ‖T‖ * ‖α'‖ := by ring
  rw [h_final] at h_combined
  exact h_combined


omit [T2Space M] in
lemma chartRSTwistInv_opNorm_le
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    ‖chartRSTwistInv (I := I) (M := M) α b r s T‖ ≤
      ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s *
        ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ r * ‖T‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · have : (0 : ℝ) ≤ ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s *
        ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ r * ‖T‖ := by positivity
    exact this
  intro α'
  rw [chartRSTwistInv_apply]
  have hA :
      ‖α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)‖ ≤
        ‖α'‖ * ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ r := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      α' (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  set u : Tensor0SModel r ℝ E :=
    α'.compContinuousLinearMap
      (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) with hu_def
  have hB : ‖T u‖ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
  have hC :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)‖ ≤
        ‖T u‖ * ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s := by
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (T u) (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hCsorted :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)‖ ≤
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by
    calc
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)‖
          ≤ ‖T u‖ * ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s := hC
      _ = ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s * ‖T u‖ := by ring
  have h_pow_nn : 0 ≤ ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s := by positivity
  have h_T_le : ‖T u‖ ≤ ‖T‖ * (‖α'‖ * ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ r) := by
    calc
      ‖T u‖ ≤ ‖T‖ * ‖u‖ := hB
      _ ≤ ‖T‖ * (‖α'‖ * ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ r) := by
            have h_T_nn : 0 ≤ ‖T‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_left hA h_T_nn
  have h_combined :
      ‖(T u).compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b)‖ ≤
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ r)) :=
    hCsorted.trans <| mul_le_mul_of_nonneg_left h_T_le h_pow_nn
  have h_final :
      ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s *
          (‖T‖ * (‖α'‖ * ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ r)) =
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖ ^ s *
          ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ ^ r * ‖T‖ * ‖α'‖ := by ring
  rw [h_final] at h_combined
  exact h_combined

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
