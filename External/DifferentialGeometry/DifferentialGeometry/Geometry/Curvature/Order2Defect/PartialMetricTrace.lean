import DifferentialGeometry.Geometry.Curvature.Order2Defect.OffDiagonalCurvatureCore
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
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

noncomputable def metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (H : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) →
      (Π b : M, TensorRSSpace r s I b) → (z : M) → TensorRSSpace r s I z)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    H (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in

lemma metricTrace2_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (H : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) →
      (Π b : M, TensorRSSpace r s I b) → (z : M) → TensorRSSpace r s I z)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s H T x =
      ∑ i : Fin (Module.finrank ℝ E),
        H (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricTrace2_secondCovDeriv_eq_metricTraceHessian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x =
      metricTraceHessian (I := I) g r s T x := by
  rw [metricTrace2_def, metricTraceHessian_def]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_eq_metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x := by
  rw [metricTrace2_secondCovDeriv_eq_metricTraceHessian]
  exact rawTensorConnLap_eq_metricTraceHessian (I := I) g r s T x

omit [CompactSpace M] [I.Boundaryless] in
theorem metricTrace2_eq_gWeighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x) := by
  rw [metricTrace2_secondCovDeriv_eq_metricTraceHessian]
  exact metricTraceHessian_eq_gWeighted_firstSlot (I := I) g r s T x

omit [CompactSpace M] [I.Boundaryless] in

omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem frame_pairing_locally_const
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x i y)
        (smoothOrthoFrame (I := I) g x j y)) =ᶠ[nhds x]
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) := by
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
  exact smoothOrthoFrame_orthonormal (I := I) g x hy i j

omit [CompactSpace M] [I.Boundaryless] in

omit [SigmaCompactSpace M] in
theorem cometric_skew_core
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x j x)
      + g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x j) x w) = 0 := by
  classical
  have hEi : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x i y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (by simp)
  have hEj : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x j y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x j).contMDiffAt.mdifferentiableAt (by simp)
  have hmfderiv0 : mfderiv I 𝓘(ℝ) (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x i y)
        (smoothOrthoFrame (I := I) g x j y)) x w = 0 := by
    rw [(frame_pairing_locally_const (I := I) g x i j).mfderiv_eq, mfderiv_const]
    rfl
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply
    (Y := fun y => smoothOrthoFrame (I := I) g x i y)
    (Z := fun y => smoothOrthoFrame (I := I) g x j y)
    (x := x) hEi hEj w
  rw [hmfderiv0] at hmc
  exact hmc.symm

omit [CompactSpace M] [I.Boundaryless] in

omit [SigmaCompactSpace M] in
theorem cometric_diagonal_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) (w : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x i x) = 0 := by
  have hcore := cometric_skew_core (I := I) g x i i w
  have hsymm : g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w) =
      g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x w)
        (smoothOrthoFrame (I := I) g x i x) := g.symm x _ _
  rw [hsymm] at hcore
  linarith

end Connection
end Integral
end DifferentialGeometry

end
