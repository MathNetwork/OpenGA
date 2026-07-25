import DifferentialGeometry.Geometry.Curvature.Order2Defect.PartialMetricTrace


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

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem firstSlotHessMap_eq_secondCovDeriv_field
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (y : M) :
    firstSlotHessMap (I := I) g r s Y T y (X y) =
      tensorSecondCovDeriv (I := I) g r s X Y T y := by
  rw [tensorSecondCovDeriv_eq_firstSlotHessMap]

noncomputable def frozenFrameTrace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    TensorRSSpace r s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    tensorSecondCovDeriv (I := I) g r s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma frozenFrameTrace_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    frozenFrameTrace (I := I) g r s T x y =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T y := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem frozenFrameTrace_self_eq_metricTrace2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    frozenFrameTrace (I := I) g r s T x x =
      metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x := by
  rw [frozenFrameTrace_def, metricTrace2_def]

omit [CompactSpace M] [I.Boundaryless] in
theorem frozenFrameTrace_eq_gWeighted_of_mem_nbhd
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    frozenFrameTrace (I := I) g r s T x y =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner y (smoothOrthoFrame (I := I) g x i y)
            (smoothOrthoFrame (I := I) g x j y) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y) := by
  classical
  rw [frozenFrameTrace_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_eq_firstSlotHessMap]
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        g.inner y (smoothOrthoFrame (I := I) g x i y)
            (smoothOrthoFrame (I := I) g x j y) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y)) =
      ∑ j : Fin (Module.finrank ℝ E),
        (if i = j then
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
            (smoothOrthoFrame (I := I) g x j y)
          else 0) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smoothOrthoFrame_orthonormal (I := I) g x hy i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, one_smul]
    · rw [if_neg hij, if_neg hij, zero_smul]]
  rw [Finset.sum_ite_eq (Finset.univ) i
    (fun j => firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T y
      (smoothOrthoFrame (I := I) g x j y))]
  rw [if_pos (Finset.mem_univ i)]

end Connection
end Integral
end DifferentialGeometry

end
