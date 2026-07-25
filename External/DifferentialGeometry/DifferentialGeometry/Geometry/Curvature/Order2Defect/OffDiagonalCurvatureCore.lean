import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

section DifferentialIdentities

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem covGradRoughLapCurv_toSection_eq_sub
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x := by
  rw [covGradRoughLapCurv]
  rw [SmoothCcTensor.toSection_sub]
  rfl

theorem rawTensorConnLap_gradTensor_toSection_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (rawTensorConnLapSmooth (I := I) g 0 3
        (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 3
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 3
    (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x

omit [NeZero (Module.finrank ℝ E)] in
theorem secondCovDeriv_gradTensor_antisymm_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    tensorSecondCovDeriv (I := I) g 0 3 X Y
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x -
      tensorSecondCovDeriv (I := I) g 0 3 Y X
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x =
      riemannOp (tensorCov (I := I) g 0 3) x (X x) (Y x)
        ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) :=
  tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 3
    (T := fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
    hX hY (covGrad_contMDiff_mk' (I := I) (M := M) g T₀)

end DifferentialIdentities

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_gradTensor_offDiag_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ v w : TangentSpace I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (riemannOp (tensorCov (I := I) g 0 3) x v w
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g 3 x
  refine ⟨Cx, hCx_nonneg, fun v w => ?_⟩
  exact hbound v w ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)

theorem riemannOp_gradTensor_offDiag_frame_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ i j : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
          Cx * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    riemannOp_gradTensor_offDiag_fiberNormSq_le (I := I) (M := M) g T₀ x
  refine ⟨Cx, hCx_nonneg, fun i j => ?_⟩
  have hii : g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    simpa using this
  have hjj : g.inner x (smoothOrthoFrame (I := I) g x j x)
      (smoothOrthoFrame (I := I) g x j x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x j j
    simpa using this
  have h := hbound (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
  rw [hii, hjj] at h
  simpa using h

end Connection

end Integral

end DifferentialGeometry

end
