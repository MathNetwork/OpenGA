import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacianChart
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.RawTensorConnLap2ndApplicationOpNorm


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def chartFrameData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  (max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1) ^ (max r s) *
    (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀) ∘
        (extChartAt I α).symm) (extChartAt I α y)‖ *
      ‖smoothOrthoFrame (I := I) g y i y‖
      + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀ y‖)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartFrameData_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) :
    0 ≤ chartFrameData (I := I) g r s α T₀ y i := by
  classical
  unfold chartFrameData
  have h1 : 0 ≤ max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have h2 : 0 ≤ (max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1) ^ (max r s) :=
    pow_nonneg h1 _
  have h3 : 0 ≤
      ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀) ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖smoothOrthoFrame (I := I) g y i y‖
        + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀ y‖ := by
    have h_a : 0 ≤
        ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀) ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖smoothOrthoFrame (I := I) g y i y‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h_b : 0 ≤
        ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀ y‖ := norm_nonneg _
    linarith
  exact mul_nonneg h2 h3

noncomputable def secondAppChartData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  (max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1) ^ (max r s) *
    (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T₀ ∘
        (extChartAt I α).symm) (extChartAt I α y)‖ *
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖
      + ‖T₀ y‖)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma secondAppChartData_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) :
    0 ≤ secondAppChartData (I := I) g r s α T₀ y i := by
  classical
  unfold secondAppChartData
  have h1 : 0 ≤ max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have h2 : 0 ≤ (max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1) ^ (max r s) :=
    pow_nonneg h1 _
  have h3a : 0 ≤
      ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T₀ ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
          (smoothOrthoFrame (I := I) g y i y)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h3b : 0 ≤ ‖T₀ y‖ := norm_nonneg _
  exact mul_nonneg h2 (by linarith)

end Connection
end Integral
end DifferentialGeometry

end
