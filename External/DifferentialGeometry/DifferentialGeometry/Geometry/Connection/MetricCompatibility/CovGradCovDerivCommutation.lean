import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

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

noncomputable def unitEvalSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    Π y : M, Tensor0SSpace s I y :=
  fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
      (unitZeroSec (I := I) (M := M) y)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma unitEvalSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (y : M) :
    unitEvalSection (I := I) (M := M) g s S y =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
        (unitZeroSec (I := I) (M := M) y) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensor0S_curry_covGradBundleEquiv_unit_genVal
    (s : ℕ) (x : M) (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x)
    (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
          (unitZeroSec (I := I) (M := M) x)) v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ v)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      covGradBundleEquiv (I := I) (M := M) 0 s x Φ)
      (unitZeroSec (I := I) (M := M) x)) (v0 := v) (vs := m)]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 s x Φ
    (unitZeroSec (I := I) (M := M) x) (Fin.cons v m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons v m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

omit [NeZero (Module.finrank ℝ E)] in
lemma curriedSection_unitGradFieldGen_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (w : TangentSpace I x) :
    Tensor0SNabla.curriedSection I M (unitGradFieldGen (I := I) (M := M) g s S) x w =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
        (unitEvalSection (I := I) (M := M) g s S) x w := by
  rw [curry_unitGradFieldGen_eq (I := I) (M := M) g s S x w]
  rw [tensorCovDerivAt_def (I := I) (M := M) g 0 s S x w]
  exact covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection x w

omit [NeZero (Module.finrank ℝ E)] in
lemma curriedSection_unitGradFieldGen_eq_covApply_abstract
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Z : Π b : M, TangentSpace I b) :
    (fun y : M => Tensor0SNabla.curriedSection I M
        (unitGradFieldGen (I := I) (M := M) g s S) y (Z y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Z
        (unitEvalSection (I := I) (M := M) g s S) := by
  funext y
  rw [curriedSection_unitGradFieldGen_apply (I := I) (M := M) g s S y (Z y), covApply_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSecondCovDeriv_unit_eval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorSecondCovDeriv (I := I) g 0 s B B
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s
              (LeviCivita (I := I) g)) B
            (unitEvalSection (I := I) (M := M) g s S)) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  rw [tensorSecondCovDeriv_def]
  rw [ContinuousLinearMap.sub_apply]
  congr 1
  · set σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
      ContMDiffSection.mk
        (fun y : M => covApply (tensorCov (I := I) g 0 s) B (fun z : M => S.toSection z) y)
        (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hB) with hσ
    have h1 := covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s σ x (B x)
    have hσapp : ∀ y, σ y =
        covApply (tensorCov (I := I) g 0 s) B (fun z : M => S.toSection z) y := fun y => rfl
    simp only [hσapp] at h1
    rw [h1]
    rw [covApply_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection B]
    rfl
  · rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection x
      ((LeviCivita (I := I) g).toFun B x (B x))]
    rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma contMDiff_unitEvalSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (unitEvalSection (I := I) (M := M) g s S y)) := by
  classical
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace s I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y))) :=
    S.toSection.contMDiff
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace s I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel s ℝ E) hϕ hv

omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_covDeriv_leadingSlot_eq_abstractHess
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (tensorCov (I := I) g 0 (s + 1)).toFun
            (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
          (unitZeroSec (I := I) (M := M) x)) (Z x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Z
            (unitEvalSection (I := I) (M := M) g s S)) x (Y x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun Z x (Y x)) := by
  classical

  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (tensorCov (I := I) g 0 (s + 1)).toFun
          (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldGen (I := I) (M := M) g s S) x (Y x) from
    covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s S).toSection x (Y x)]

  rw [curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection (I := I) (M := M) g s
    (unitGradFieldGen (I := I) (M := M) g s S) (Vfield := Y) (Y := Z) (x := x)
    ((contMDiff_curried_unitGradFieldGen (I := I) (M := M) g s S x).mdifferentiableAt (by simp))
    ((hY x).mdifferentiableAt (by simp)) ((hZ x).mdifferentiableAt (by simp))]

  rw [curriedSection_unitGradFieldGen_eq_covApply_abstract (I := I) (M := M) g s S Z]
  rw [curriedSection_unitGradFieldGen_apply (I := I) (M := M) g s S x
    ((LeviCivita (I := I) g).toFun Z x (Y x))]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_covDeriv_inner_leadingSlot_eq_abstractIter
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Y : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M) (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x))
          (unitZeroSec (I := I) (M := M) x)) w =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Y
            (unitEvalSection (I := I) (M := M) g s S)) x w := by
  classical

  rw [tensor0S_curry_covGradBundleEquiv_unit_genVal (I := I) (M := M) s x
    ((tensorCov (I := I) g 0 s).toFun
      (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x) w]

  set σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
    ContMDiffSection.mk
      (fun y : M => covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y)
      (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hY) with hσ
  have hσapp : ∀ y, σ y =
      covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y := fun y => rfl
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x w)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => σ y) x w)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [show (fun y : M => σ y) =
      (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) from
      funext (fun y => hσapp y)]]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s σ x w]

  rw [show (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Y
        (unitEvalSection (I := I) (M := M) g s S) from by
    funext y
    rw [hσapp y, covApply_apply, covApply_apply]
    rw [show (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          (tensorCov (I := I) g 0 s) (fun z : M => S.toSection z) y (Y y))
          (unitZeroSec (I := I) (M := M) y) =
        ((tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g))
          (fun z : M => S.toSection z) y (Y y))
          (unitZeroSec (I := I) (M := M) y) from rfl]
    rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s S.toSection y (Y y)]
    rfl]

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_covDeriv_leadingSlot_commutation
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Y Z : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (tensorCov (I := I) g 0 (s + 1)).toFun
            (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) x (Y x))
          (unitZeroSec (I := I) (M := M) x)) (Z x) -
      tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z)) x))
          (unitZeroSec (I := I) (M := M) x)) (Z x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) Y Z
          (unitEvalSection (I := I) (M := M) g s S) x -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun Y x (Z x)) := by
  classical
  set nab := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) with hnab
  set V := unitEvalSection (I := I) (M := M) g s S with hV

  rw [covGrad_covDeriv_leadingSlot_eq_abstractHess (I := I) (M := M) g s S hY hZ x]
  rw [covGrad_covDeriv_inner_leadingSlot_eq_abstractIter (I := I) (M := M) g s S hY x (Z x)]

  rw [riemannSec_def nab Y Z V x]

  have hbr : (LeviCivita (I := I) g).toFun Z x (Y x) -
      (LeviCivita (I := I) g).toFun Y x (Z x) = VectorField.mlieBracket I Y Z x :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := LeviCivita (I := I) g)).mp
      (LeviCivita_torsion_eq_zero (I := I) g)
      ((hY x).mdifferentiableAt (by simp)) ((hZ x).mdifferentiableAt (by simp))

  have hdir : (LeviCivita (I := I) g).toFun Z x (Y x) =
      VectorField.mlieBracket I Y Z x + (LeviCivita (I := I) g).toFun Y x (Z x) := by
    rw [← hbr]; abel

  rw [hdir, map_add]
  abel

end Connection
end Integral
end DifferentialGeometry

end
