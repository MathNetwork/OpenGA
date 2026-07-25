import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]

omit [SigmaCompactSpace M] in
theorem riemannSec_eq_riemannOp_smooth
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    riemannSec cov X Y Z x = riemannOp cov x (X x) (Y x) (Z x) :=
  (riemannOp_apply_smooth (cov := cov) hX hY hZ).symm

omit [SigmaCompactSpace M] in
theorem cov_commutator_eq_riemannOp_smooth
    (cov : CovariantDerivative I F V)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% Z)) :
    cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
        - cov.toFun Z x (VectorField.mlieBracket I X Y x) =
      riemannOp cov x (X x) (Y x) (Z x) := by
  rw [← riemannSec_def cov X Y Z x]
  exact riemannSec_eq_riemannOp_smooth (cov := cov) hX hY hZ

end General

section TensorBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

noncomputable abbrev tensorCov (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    CovariantDerivative I (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRicciCommutator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
      (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) X T) x (Y x) -
      (tensorCov (I := I) g r s).toFun T x (VectorField.mlieBracket I X Y x) =
      riemannSec (tensorCov (I := I) g r s) X Y T x :=
  (riemannSec_def (tensorCov (I := I) g r s) X Y T x).symm

omit [NeZero (Module.finrank ℝ E)] in
theorem ricci_identity_tensor_commutator_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
      (tensorCov (I := I) g r s).toFun
        (covApply (tensorCov (I := I) g r s) X T) x (Y x) -
      (tensorCov (I := I) g r s).toFun T x (VectorField.mlieBracket I X Y x) =
      riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (T x) := by
  rw [tensorRicciCommutator (I := I) g r s X Y T x]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g r s) hX hY hT

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRicciCommutator_swap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    riemannSec (tensorCov (I := I) g r s) X Y T x =
      - riemannSec (tensorCov (I := I) g r s) Y X T x :=
  riemannSec_swap (tensorCov (I := I) g r s) X Y T x

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorRicciCommutator_self
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    riemannSec (tensorCov (I := I) g r s) X X T x = 0 :=
  riemannSec_self_eq_zero (tensorCov (I := I) g r s) X T x

noncomputable def tensorSecondCovDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
    (tensorCov (I := I) g r s).toFun T x ((LeviCivita (I := I) g).toFun Y x (X x))

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSecondCovDeriv_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    tensorSecondCovDeriv (I := I) g r s X Y T x =
      (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x (X x) -
        (tensorCov (I := I) g r s).toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorSecondCovDeriv_antisymm_eq_riemannSec
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} (T : Π b : M, TensorRSSpace r s I b) {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    tensorSecondCovDeriv (I := I) g r s X Y T x -
        tensorSecondCovDeriv (I := I) g r s Y X T x =
      riemannSec (tensorCov (I := I) g r s) X Y T x := by
  classical
  set cov := tensorCov (I := I) g r s with hcov_def
  have hbr : (LeviCivita (I := I) g).toFun Y x (X x) -
      (LeviCivita (I := I) g).toFun X x (Y x) = VectorField.mlieBracket I X Y x :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g)).mp
      (LeviCivita_torsion_eq_zero (I := I) g) hX hY
  rw [tensorSecondCovDeriv_def, tensorSecondCovDeriv_def, riemannSec_def]
  have hsub : (cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) -
        cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) =
      cov.toFun T x (VectorField.mlieBracket I X Y x) := by
    rw [← map_sub (cov.toFun T x), hbr]
  rw [show
      (cov.toFun (covApply cov Y T) x (X x) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x))) -
        (cov.toFun (covApply cov X T) x (Y x) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) =
      (cov.toFun (covApply cov Y T) x (X x) - cov.toFun (covApply cov X T) x (Y x)) -
        (cov.toFun T x ((LeviCivita (I := I) g).toFun Y x (X x)) -
          cov.toFun T x ((LeviCivita (I := I) g).toFun X x (Y x))) from by abel]
  rw [hsub]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorSecondCovDeriv_antisymm_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {T : Π b : M, TensorRSSpace r s I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) b (T b))) :
    tensorSecondCovDeriv (I := I) g r s X Y T x -
        tensorSecondCovDeriv (I := I) g r s Y X T x =
      riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (T x) := by
  rw [tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g r s T
        ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))]
  exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g r s) hX hY hT

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_eq_frame_trace_secondCovDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x := by
  rw [rawTensorConnLap_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_def]

end TensorBundle

end Connection
end Integral
end DifferentialGeometry
