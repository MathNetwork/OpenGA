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
theorem tensorSecondCovDeriv_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {T T' : Π b : M, TensorRSSpace r s I b} {x : M}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hT' : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    tensorSecondCovDeriv (I := I) g r s X Y (fun y : M => T y + T' y) x =
      tensorSecondCovDeriv (I := I) g r s X Y T x +
        tensorSecondCovDeriv (I := I) g r s X Y T' x := by
  classical
  set cov := tensorCov (I := I) g r s with hcov_def
  have hcov_loc := cov.isCovariantDerivativeOn (s := (Set.univ : Set M))
  have hTd : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x :=
    (hT x).mdifferentiableAt (by simp)
  have hT'd : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y)) x :=
    (hT' x).mdifferentiableAt (by simp)
  have hcovT : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (covApply cov Y T y)) x :=
    (covApplyRS_contMDiff (I := I) g r s hT hY x).mdifferentiableAt (by simp)
  have hcovT' : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (covApply cov Y T' y)) x :=
    (covApplyRS_contMDiff (I := I) g r s hT' hY x).mdifferentiableAt (by simp)
  have hcovApply_add : covApply cov Y (fun y : M => T y + T' y) =
      fun y : M => covApply cov Y T y + covApply cov Y T' y := by
    funext y
    have hTy : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) z (T z)) y :=
      (hT y).mdifferentiableAt (by simp)
    have hT'y : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) z (T' z)) y :=
      (hT' y).mdifferentiableAt (by simp)
    have hadd_y : cov.toFun (fun z : M => T z + T' z) y = cov.toFun T y + cov.toFun T' y := by
      change cov.toFun (T + T') y = cov.toFun T y + cov.toFun T' y
      exact hcov_loc.add (σ := T) (σ' := T') hTy hT'y
    change cov.toFun (fun z : M => T z + T' z) y (Y y) = _
    rw [hadd_y]; rfl
  have hiter : cov.toFun (covApply cov Y (fun y : M => T y + T' y)) x =
      cov.toFun (covApply cov Y T) x + cov.toFun (covApply cov Y T') x := by
    rw [hcovApply_add]
    change cov.toFun ((covApply cov Y T) + (covApply cov Y T')) x = _
    exact hcov_loc.add (σ := covApply cov Y T) (σ' := covApply cov Y T') hcovT hcovT'
  have hchrist : cov.toFun (fun y : M => T y + T' y) x = cov.toFun T x + cov.toFun T' x := by
    change cov.toFun (T + T') x = cov.toFun T x + cov.toFun T' x
    exact hcov_loc.add (σ := T) (σ' := T') hTd hT'd
  rw [tensorSecondCovDeriv_def, tensorSecondCovDeriv_def, tensorSecondCovDeriv_def]
  rw [hiter, hchrist]
  simp only [ContinuousLinearMap.add_apply]
  abel

omit [CompactSpace M] [I.Boundaryless] in
theorem metricTrace2_secondCovDeriv_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T T' : Π b : M, TensorRSSpace r s I b} (x : M)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hT' : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y))) :
    metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
        (fun y : M => T y + T' y) x =
      metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x +
        metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T' x := by
  classical
  rw [metricTrace2_def, metricTrace2_def, metricTrace2_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact tensorSecondCovDeriv_add (I := I) g r s hT hT'
    (smoothOrthoFrame_smooth (I := I) g x i)

end Connection

end Integral

end DifferentialGeometry

end
