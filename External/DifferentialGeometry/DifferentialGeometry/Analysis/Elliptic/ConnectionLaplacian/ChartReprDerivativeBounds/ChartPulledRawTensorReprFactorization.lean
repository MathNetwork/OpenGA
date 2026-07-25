import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.RawTensorConnLapNormSqChartPulledReprBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberForwardOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartReprNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma sum_sq_le_sq_sum_of_nonneg (V F I2 : ℝ)
    (hV : 0 ≤ V) (hF : 0 ≤ F) (hI2 : 0 ≤ I2) :
    V ^ 2 + F ^ 2 + I2 ^ 2 ≤ (V + F + I2) ^ 2 := by
  nlinarith [mul_nonneg hV hF, mul_nonneg hV hI2, mul_nonneg hF hI2]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma V_eq_iteratedFDeriv_zero_norm
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ‖tensorRSChartE_section_repr (I := I) r s α S b‖ =
      ‖iteratedFDeriv ℝ 0
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
  have hb_chart_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
  have hb_extsrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart_src
  have hsymm_eq : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_extsrc
  rw [norm_iteratedFDeriv_zero]
  change ‖tensorRSChartE_section_repr (I := I) r s α S b‖ =
    ‖tensorRSChartE_section_repr (I := I) r s α S
      ((extChartAt I α).symm (extChartAt I α b))‖
  rw [hsymm_eq]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma F_eq_iteratedFDeriv_one_norm
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) (b : M) :
    ‖fderiv ℝ
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ =
      ‖iteratedFDeriv ℝ 1
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
  rw [norm_iteratedFDeriv_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sum_VFI2_eq_finSum
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ‖tensorRSChartE_section_repr (I := I) r s α S b‖ +
      ‖fderiv ℝ
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ +
      ‖iteratedFDeriv ℝ 2
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ =
      ∑ j : Fin 3,
        ‖iteratedFDeriv ℝ j.val
          ((tensorRSChartE_section_repr (I := I) r s α S) ∘
              (extChartAt I α).symm)
          (extChartAt I α b)‖ := by
  rw [V_eq_iteratedFDeriv_zero_norm (I := I) (M := M) r s α S (b := b) hb_good]
  rw [F_eq_iteratedFDeriv_one_norm (I := I) (M := M) r s α S b]
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]

end Connection
end Integral
end DifferentialGeometry

end
