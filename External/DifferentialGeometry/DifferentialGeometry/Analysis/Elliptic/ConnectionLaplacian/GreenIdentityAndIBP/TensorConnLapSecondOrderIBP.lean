import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIdentity
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapLoweredIBP
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawTensorConnLapChartFrameTrace


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]   [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def covDerivAlongVFraw
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, TensorRSSpace 0 2 I y :=
  covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
    (fun y : M => B y) (fun y : M => T y)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covDerivAlongVFraw_apply
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFraw (I := I) (M := M) g T B y =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlongVFraw_contMDiff
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y
        (covDerivAlongVFraw (I := I) (M := M) g T B y)) := by
  classical
  set cov := tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) with hcov_def
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact T.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (B y)) :=
    B.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y
        (covApply cov (fun y : M => B y) (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT
  rw [← contMDiffOn_univ]
  exact hOn

def covDerivAlongVFSection
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covDerivAlongVFraw (I := I) (M := M) g T B y)
    (covDerivAlongVFraw_contMDiff (I := I) (M := M) g T B)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covDerivAlongVFSection_apply
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSection (I := I) (M := M) g T B y =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlongVFSection_lowered_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 2 y
        (TensorRSSpace.toModel (covDerivAlongVFSection (I := I) (M := M) g T B y)) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 2 T y (B y)) := by
  rw [(loweredCovDerivAt_eq_lower_tensorCovDerivAt
    (I := I) (M := M) g T y (B y))]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma toModel_liftedTensorSection_covDerivAlongVFSection
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T B) y) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 2 T y (B y)) := by
  rw [toModel_liftedTensorSection]
  exact covDerivAlongVFSection_lowered_eq (I := I) (M := M) g T B y

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_covDerivAlongVFSection_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T B) B y =
      tensorSecondCovDeriv (I := I) g 0 2
          (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) y +
        (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun b : M => T b) y
          ((LeviCivita (I := I) g).toFun (fun b : M => B b) y (B y)) := by
  rw [tensorSecondCovDeriv_def]
  change (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
      (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
        (fun b : M => B b) (fun b : M => T b)) y (B y) = _
  rw [show tensorCov (I := I) g 0 2 =
      tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) from rfl]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma toModel_loweredCovDerivAlongVF_covDerivAlongVFSection_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T B) B x) =
      lowerAllUpperIndices (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorSecondCovDeriv (I := I) g 0 2
            (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) x +
          (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
            (fun b : M => T b) x
            ((LeviCivita (I := I) g).toFun (fun b : M => B b) x (B x)))) := by
  rw [loweredCovDerivAlongVF_apply]
  rw [loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g
    (covDerivAlongVFSection (I := I) (M := M) g T B) x (B x)]
  congr 1
  exact congrArg TensorRSSpace.toModel
    (covDerivAlong_covDerivAlongVFSection_eq (I := I) (M := M) g T B x)

theorem integral_secondOrder_combined_eq_zero
    (g : SmoothRiemannianMetric I M)
    (T v : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T B) B x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2 v x))
          + covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T B) x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v B x))
          + tensorInnerScalar (I := I) (M := M) g 0 2
              (covDerivAlongVFSection (I := I) (M := M) g T B) v x
            * divergence_g (I := I) g B x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g T B) v B

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_secondOrder_eq_fixedFrame_summand
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T B) B b -
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) b
        (covApply (LeviCivita (I := I) g) (fun y : M => B y) (fun y : M => B y) b) =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
            (fun y : M => B y) (fun y : M => T y)) b (B b) -
        (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) := rfl

end Connection
end Integral
end DifferentialGeometry

end
