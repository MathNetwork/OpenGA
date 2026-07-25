import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CurvatureDefect
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Bound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Tensor3rdCurvFiberNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge


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

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannSec_covApply_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} (x : M)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannSec (tensorCov (I := I) g 0 2) X Y
            (covApply (tensorCov (I := I) g 0 2) X (fun y : M => T₀.toSection y)) x) ≤
        Cx * g.inner x (X x) (X x) * g.inner x (Y x) (Y x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (covApply (tensorCov (I := I) g 0 2) X
              (fun y : M => T₀.toSection y) x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g 2 x
  refine ⟨Cx, hCx_nonneg, ?_⟩
  have hZ := covApplyRS_contMDiff (I := I) g 0 2 (T := fun y : M => T₀.toSection y)
    T₀.toSection.contMDiff (X := X) hX
  rw [riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 2) hX hY hZ]
  exact hbound (X x) (Y x) _

omit [CompactSpace M] [I.Boundaryless] in
theorem riemannSec_orthoFrame_covApply_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannSec (tensorCov (I := I) g 0 2)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => T₀.toSection y)) x) ≤
        Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => T₀.toSection y) x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    riemannSec_covApply_fiberNormSq_le (I := I) (M := M) g T₀
      (X := smoothOrthoFrame (I := I) g x i) (Y := smoothOrthoFrame (I := I) g x i) x
      (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i)
  refine ⟨Cx, hCx_nonneg, ?_⟩
  have hortho : g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    simpa using this
  rw [hortho] at hbound
  simpa using hbound

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem orthoFrame_pair_covApply_commutator
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (i a : Fin (Module.finrank ℝ E)) :
    covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
        (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x a)
          (fun y : M => T₀.toSection y)) =
      covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x a)
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => T₀.toSection y))
        + covApply (tensorCov (I := I) g 0 2)
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame (I := I) g x a)) (fun y : M => T₀.toSection y)
        + (fun b : M => riemannSec (tensorCov (I := I) g 0 2)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a)
            (fun y : M => T₀.toSection y) b) :=
  covApply_covApply_eq_section (tensorCov (I := I) g 0 2)
    (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a)
    (fun y : M => T₀.toSection y)

end Connection
end Integral
end DifferentialGeometry

end
