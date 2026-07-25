import DifferentialGeometry.Geometry.Connection.TensorNabla.Slot0CurryCovariantLeibniz
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

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


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma secondCovDeriv_section_contMDiff' (g : SmoothRiemannianMetric I M) (k : ℕ)
    {T : Π b : M, TensorRSSpace 0 k I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 k ℝ E)
        (E := fun z : M => TensorRSSpace 0 k I z) y (T y)))
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, B b⟩ : TotalSpace E (TangentSpace I)))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 k ℝ E)
        (E := fun z : M => TensorRSSpace 0 k I z) y
        (tensorSecondCovDeriv (I := I) g 0 k B B T y)) := by
  have h1 := covApplyRS_contMDiff (I := I) g 0 k
    (covApplyRS_contMDiff (I := I) g 0 k hT hB) hB
  have h2 := covApplyRS_contMDiff (I := I) g 0 k hT
    (covApply_contMDiff (cov := LeviCivita (I := I) g) hB hB)
  refine (h1.sub_section h2).congr fun y => ?_
  rfl

def secondCovDerivCc (g : SmoothRiemannianMetric I M) (k : ℕ)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (T : SmoothCcTensor g 0 k) : SmoothCcTensor g 0 k where
  toSection :=
    { toFun := fun x : M => tensorSecondCovDeriv (I := I) g 0 k V V
        (fun y : M => T.toSection y) x
      contMDiff_toFun := secondCovDeriv_section_contMDiff' (I := I) (M := M) g k
        (T := fun y : M => T.toSection y) T.toSection.contMDiff hV }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma secondCovDerivCc_toSection_apply (g : SmoothRiemannianMetric I M) (k : ℕ)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (T : SmoothCcTensor g 0 k) (x : M) :
    (secondCovDerivCc (I := I) (M := M) g k hV T).toSection x =
      tensorSecondCovDeriv (I := I) g 0 k V V (fun y : M => T.toSection y) x := rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor00Scalar_unitZeroSec (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_eq_of_toModel_eq {t : ℕ} {x : M} {T T' : Tensor0SSpace t I x}
    (h : ∀ v : Fin t → E, Tensor0SSpace.toModel T v = Tensor0SSpace.toModel T' v) : T = T' :=
  Tensor0SSpace.toModel_injective (ContinuousMultilinearMap.ext h)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_zero_span (x : M) (τ : Tensor0SSpace 0 I x) :
    τ = tensor00Scalar (I := I) (M := M) x τ • unitZeroSec (I := I) (M := M) x := by
  apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
  intro v
  rw [show v = (fun k : Fin 0 => k.elim0) from funext (fun k => k.elim0)]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x)
      (fun k : Fin 0 => k.elim0) = 1 from by
    rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.constOfIsEmpty_apply]]
  rw [show Tensor0SSpace.toModel τ (fun k : Fin 0 => k.elim0) =
      tensor00Scalar (I := I) (M := M) x τ from
    (tensor00Scalar_apply (I := I) (M := M) x τ (fun k : Fin 0 => k.elim0)).symm]
  rw [smul_eq_mul, mul_one]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_rs_unit (t : ℕ) (x : M) (W : TensorRSSpace 0 t I x) :
    tensor0SToTensorRS (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) = W := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
            (unitZeroSec (I := I) (M := M) x))) τ =
      tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  conv_rhs => rw [tensor0S_zero_span (I := I) (M := M) x τ]
  rw [ContinuousLinearMap.map_smul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_sub (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SToTensorRS (I := I) (M := M) x (C - D) =
      tensor0SToTensorRS (I := I) (M := M) x C - tensor0SToTensorRS (I := I) (M := M) x D := by
  have h : (tensor0SToTensorRS (I := I) (M := M) x (C - D) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      (tensor0SToTensorRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) -
        (tensor0SToTensorRS (I := I) (M := M) x D :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (C - D) =
      tensor00Scalar (I := I) (M := M) x τ • C - tensor00Scalar (I := I) (M := M) x τ • D
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro v
    rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
      smul_eq_mul]
    ring
  exact h


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rs_sub_apply' {t : ℕ} {x : M} (A B : TensorRSSpace 0 t I x)
    (τ : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from A - B) τ =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from A) τ -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from B) τ := rfl


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rs_add_apply' {t : ℕ} {x : M} (A B : TensorRSSpace 0 t I x)
    (τ : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from A + B) τ =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from A) τ +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from B) τ := rfl


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorCov_toFun_sub (g : SmoothRiemannianMetric I M) (k : ℕ)
    {P Q : Π y : M, TensorRSSpace 0 k I y} {x : M}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 k ℝ E)
        (E := fun z : M => TensorRSSpace 0 k I z) y (P y)))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 k ℝ E)
        (E := fun z : M => TensorRSSpace 0 k I z) y (Q y))) :
    (tensorCov (I := I) g 0 k).toFun (fun y : M => P y - Q y) x =
      (tensorCov (I := I) g 0 k).toFun P x - (tensorCov (I := I) g 0 k).toFun Q x := by
  have hPQAt : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 k ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 k ℝ E)
        (E := fun z : M => TensorRSSpace 0 k I z) y (P y - Q y)) x :=
    ((hP.sub_section hQ) x).mdifferentiableAt (by simp)
  have hQAt : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 k ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 k ℝ E)
        (E := fun z : M => TensorRSSpace 0 k I z) y (Q y)) x :=
    (hQ x).mdifferentiableAt (by simp)
  have hadd := (tensorCov (I := I) g 0 k).isCovariantDerivativeOnUniv.add
    (σ := fun y : M => P y - Q y) (σ' := Q) hPQAt hQAt
  rw [show ((fun y : M => P y - Q y) + Q) = P from
    funext fun y => sub_add_cancel (P y) (Q y)] at hadd
  exact eq_sub_of_add_eq hadd.symm


omit [NeZero (Module.finrank ℝ E)] in
private lemma curry_covGrad_unit_read (g : SmoothRiemannianMetric I M) (k : ℕ)
    (P : SmoothCcTensor g 0 k) (y : M) (w : TangentSpace I y) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) k y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (k + 1) I y from
          (covGrad (I := I) (M := M) g 0 k P).toSection y)
          (unitZeroSec (I := I) (M := M) y))) w =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace k I y from
        (tensorCov (I := I) g 0 k).toFun (fun z : M => P.toSection z) y w)
        (unitZeroSec (I := I) (M := M) y) :=
  curry_unitGradFieldGen_eq (I := I) (M := M) g k P y w


omit [NeZero (Module.finrank ℝ E)] in
private lemma slotRead_covGrad_dir (g : SmoothRiemannianMetric I M) (k : ℕ)
    (P : SmoothCcTensor g 0 k) (y : M) (w : TangentSpace I y) :
    tensor0SToTensorRS (I := I) (M := M) y
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) k y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (k + 1) I y from
            (covGrad (I := I) (M := M) g 0 k P).toSection y)
            (unitZeroSec (I := I) (M := M) y))) w) =
      (tensorCov (I := I) g 0 k).toFun (fun z : M => P.toSection z) y w := by
  rw [curry_covGrad_unit_read (I := I) (M := M) g k P y w]
  exact tensor0SAsRS_rs_unit (I := I) (M := M) k y _


omit [NeZero (Module.finrank ℝ E)] in
private lemma slotRead_covGrad_section (g : SmoothRiemannianMetric I M) (k : ℕ)
    (P : SmoothCcTensor g 0 k) (B : Π b : M, TangentSpace I b) :
    (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) k y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (k + 1) I y from
            (covGrad (I := I) (M := M) g 0 k P).toSection y)
            (unitZeroSec (I := I) (M := M) y))) (B y))) =
      covApply (tensorCov (I := I) g 0 k) B (fun z : M => P.toSection z) := by
  funext y
  exact slotRead_covGrad_dir (I := I) (M := M) g k P y (B y)

private def covApplyCovGradCc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I)))) :
    SmoothCcTensor g 0 (s + 1) where
  toSection :=
    { toFun := fun y : M => covApply (tensorCov (I := I) g 0 (s + 1)) V
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) y
      contMDiff_toFun := covApplyRS_contMDiff (I := I) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff hV }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
theorem secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {V X : Π b : M, TangentSpace I b}
    (hVs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            tensorSecondCovDeriv (I := I) g 0 (s + 1) V V
              (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
            (unitZeroSec (I := I) (M := M) x))) (X x)) m -
      Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covGrad (I := I) (M := M) g 0 s
              (secondCovDerivCc (I := I) (M := M) g s hVs S)).toSection x)
            (unitZeroSec (I := I) (M := M) x))) (X x)) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            riemannSec (tensorCov (I := I) g 0 s) V X
              (covApply (tensorCov (I := I) g 0 s) V (fun y : M => S.toSection y)) x)
            (unitZeroSec (I := I) (M := M) x) +
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            covApply (tensorCov (I := I) g 0 s) V
              (fun y : M => riemannSec (tensorCov (I := I) g 0 s) V X
                (fun z : M => S.toSection z) y) x)
            (unitZeroSec (I := I) (M := M) x) +
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            riemannOp (tensorCov (I := I) g 0 s) x
              ((LeviCivita (I := I) g).toFun X x (V x)) (V x) (S.toSection x))
            (unitZeroSec (I := I) (M := M) x) +
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            riemannOp (tensorCov (I := I) g 0 s) x (X x)
              ((LeviCivita (I := I) g).toFun V x (V x)) (S.toSection x))
            (unitZeroSec (I := I) (M := M) x) -
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
              (riemannOp (LeviCivita (I := I) g) x (V x) (X x) (V x)))
            (unitZeroSec (I := I) (M := M) x) -
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensorSecondCovDeriv (I := I) g 0 s
              (fun y : M => (LeviCivita (I := I) g).toFun V y (X y)) V
              (fun y : M => S.toSection y) x)
            (unitZeroSec (I := I) (M := M) x) -
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensorSecondCovDeriv (I := I) g 0 s V
              (fun y : M => (LeviCivita (I := I) g).toFun V y (X y))
              (fun y : M => S.toSection y) x)
            (unitZeroSec (I := I) (M := M) x)) m := by
  classical
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  have hSAt := S.toSection.contMDiff
  have hW := covApply_contMDiff (cov := LeviCivita (I := I) g) hVs hVs
  have hXV := covApply_contMDiff (cov := LeviCivita (I := I) g) hVs hXs
  have hVX := covApply_contMDiff (cov := LeviCivita (I := I) g) hXs hVs

  have hbrx : VectorField.mlieBracket I V X x =
      covApply (LeviCivita (I := I) g) V X x - covApply (LeviCivita (I := I) g) X V x :=
    (covApply_sub_eq_mlieBracket (LeviCivita (I := I) g)
      (LeviCivita_torsion_eq_zero (I := I) g)
      ((hVs x).mdifferentiableAt (by simp)) ((hXs x).mdifferentiableAt (by simp))).symm
  have hbrsec : covApply (tensorCov (I := I) g 0 s) (VectorField.mlieBracket I V X)
      (fun z : M => S.toSection z) =
      fun y : M =>
        covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V X)
          (fun z : M => S.toSection z) y -
        covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) X V)
          (fun z : M => S.toSection z) y := by
    funext y
    have hbry : VectorField.mlieBracket I V X y =
        covApply (LeviCivita (I := I) g) V X y - covApply (LeviCivita (I := I) g) X V y :=
      (covApply_sub_eq_mlieBracket (LeviCivita (I := I) g)
        (LeviCivita_torsion_eq_zero (I := I) g)
        ((hVs y).mdifferentiableAt (by simp)) ((hXs y).mdifferentiableAt (by simp))).symm
    rw [covApply_apply, hbry, map_sub]
    rfl

  have hρ0 := slotRead_covGrad_section (I := I) (M := M) g s S X
  have hρ0' := slotRead_covGrad_section (I := I) (M := M) g s S
    (covApply (LeviCivita (I := I) g) V X)

  have hM3a := tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g s
    (covApplyCovGradCc (I := I) (M := M) g s S hVs) hVs hXs x
  have hM3b := tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g s
    (covGrad (I := I) (M := M) g 0 s S) hW hXs x
  have hM3c := tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g s
    (covGrad (I := I) (M := M) g 0 s S) hVs hXV x

  have hρ1 : (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          (covApplyCovGradCc (I := I) (M := M) g s S hVs).toSection y)
          (unitZeroSec (I := I) (M := M) y))) (X y))) =
      (fun y : M =>
        covApply (tensorCov (I := I) g 0 s) V
          (covApply (tensorCov (I := I) g 0 s) X (fun z : M => S.toSection z)) y -
        covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V X)
          (fun z : M => S.toSection z) y) := by
    funext y
    rw [show (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        (covApplyCovGradCc (I := I) (M := M) g s S hVs).toSection y) =
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          covApply (tensorCov (I := I) g 0 (s + 1)) V
            (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) y) from rfl]
    rw [tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g s
      (covGrad (I := I) (M := M) g 0 s S) hVs hXs y]
    rw [tensor0SAsRS_sub (I := I) (M := M) s y]
    rw [tensor0SAsRS_rs_unit (I := I) (M := M) s y]
    rw [show tensor0SToTensorRS (I := I) (M := M) y
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            (covGrad (I := I) (M := M) g 0 s S).toSection y)
            (unitZeroSec (I := I) (M := M) y)))
          ((LeviCivita (I := I) g).toFun X y (V y))) =
        (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) y
          ((LeviCivita (I := I) g).toFun X y (V y)) from
      slotRead_covGrad_dir (I := I) (M := M) g s S y
        ((LeviCivita (I := I) g).toFun X y (V y))]
    rw [hρ0]
    rfl

  have hVAL : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) V V
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
        (unitZeroSec (I := I) (M := M) x))) (X x) -
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s
            (secondCovDerivCc (I := I) (M := M) g s hVs S)).toSection x)
          (unitZeroSec (I := I) (M := M) x))) (X x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannSec (tensorCov (I := I) g 0 s) V X
            (covApply (tensorCov (I := I) g 0 s) V (fun y : M => S.toSection y)) x)
          (unitZeroSec (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          covApply (tensorCov (I := I) g 0 s) V
            (fun y : M => riemannSec (tensorCov (I := I) g 0 s) V X
              (fun z : M => S.toSection z) y) x)
          (unitZeroSec (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannOp (tensorCov (I := I) g 0 s) x
            ((LeviCivita (I := I) g).toFun X x (V x)) (V x) (S.toSection x))
          (unitZeroSec (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannOp (tensorCov (I := I) g 0 s) x (X x)
            ((LeviCivita (I := I) g).toFun V x (V x)) (S.toSection x))
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (riemannOp (LeviCivita (I := I) g) x (V x) (X x) (V x)))
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g 0 s
            (fun y : M => (LeviCivita (I := I) g).toFun V y (X y)) V
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g 0 s V
            (fun y : M => (LeviCivita (I := I) g).toFun V y (X y))
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by

    have hD2split : tensorSecondCovDeriv (I := I) g 0 (s + 1) V V
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x =
        covApply (tensorCov (I := I) g 0 (s + 1)) V
          (fun y : M => (covApplyCovGradCc (I := I) (M := M) g s S hVs).toSection y) x -
        covApply (tensorCov (I := I) g 0 (s + 1)) (covApply (LeviCivita (I := I) g) V V)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x := by
      rw [tensorSecondCovDeriv_def]
      rfl

    have hL2a : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s
            (secondCovDerivCc (I := I) (M := M) g s hVs S)).toSection x)
          (unitZeroSec (I := I) (M := M) x))) (X x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun
            (fun z : M => (secondCovDerivCc (I := I) (M := M) g s hVs S).toSection z) x
            (X x))
          (unitZeroSec (I := I) (M := M) x) :=
      curry_covGrad_unit_read (I := I) (M := M) g s
        (secondCovDerivCc (I := I) (M := M) g s hVs S) x (X x)
    have hsecP : (fun z : M =>
        (secondCovDerivCc (I := I) (M := M) g s hVs S).toSection z) =
        (fun z : M =>
          covApply (tensorCov (I := I) g 0 s) V
            (covApply (tensorCov (I := I) g 0 s) V (fun y : M => S.toSection y)) z -
          covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V V)
            (fun y : M => S.toSection y) z) := by
      funext z
      rw [show (secondCovDerivCc (I := I) (M := M) g s hVs S).toSection z =
          tensorSecondCovDeriv (I := I) g 0 s V V (fun y : M => S.toSection y) z from rfl,
        tensorSecondCovDeriv_def]
      rfl
    have hL2b : (tensorCov (I := I) g 0 s).toFun
        (fun z : M => (secondCovDerivCc (I := I) (M := M) g s hVs S).toSection z) x =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) V
            (covApply (tensorCov (I := I) g 0 s) V (fun y : M => S.toSection y))) x -
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V V)
            (fun y : M => S.toSection y)) x := by
      rw [hsecP]
      exact tensorCov_toFun_sub (I := I) (M := M) g s
        (covApplyRS_contMDiff (I := I) g 0 s
          (covApplyRS_contMDiff (I := I) g 0 s hSAt hVs) hVs)
        (covApplyRS_contMDiff (I := I) g 0 s hSAt hW)

    have hT1 : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        covApply (tensorCov (I := I) g 0 s) V
          (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
              ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                (covApplyCovGradCc (I := I) (M := M) g s S hVs).toSection y)
                (unitZeroSec (I := I) (M := M) y))) (X y))) x)
        (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) V
              (covApply (tensorCov (I := I) g 0 s) X (fun z : M => S.toSection z))) x
            (V x))
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V X)
              (fun z : M => S.toSection z)) x (V x))
          (unitZeroSec (I := I) (M := M) x) := by
      rw [show covApply (tensorCov (I := I) g 0 s) V
          (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
              ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                (covApplyCovGradCc (I := I) (M := M) g s S hVs).toSection y)
                (unitZeroSec (I := I) (M := M) y))) (X y))) x =
          (tensorCov (I := I) g 0 s).toFun
            (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
                ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                  (covApplyCovGradCc (I := I) (M := M) g s S hVs).toSection y)
                  (unitZeroSec (I := I) (M := M) y))) (X y))) x (V x) from rfl]
      rw [hρ1]
      rw [tensorCov_toFun_sub (I := I) (M := M) g s
        (P := covApply (tensorCov (I := I) g 0 s) V
          (covApply (tensorCov (I := I) g 0 s) X (fun z : M => S.toSection z)))
        (Q := covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V X)
          (fun z : M => S.toSection z))
        (covApplyRS_contMDiff (I := I) g 0 s
          (covApplyRS_contMDiff (I := I) g 0 s hSAt hXs) hVs)
        (covApplyRS_contMDiff (I := I) g 0 s hSAt hXV)]
      rfl

    have hT3 : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V V)
          (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
              ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                (covGrad (I := I) (M := M) g 0 s S).toSection y)
                (unitZeroSec (I := I) (M := M) y))) (X y))) x)
        (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) X (fun z : M => S.toSection z)) x
            (covApply (LeviCivita (I := I) g) V V x))
          (unitZeroSec (I := I) (M := M) x) := by
      rw [show covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V V)
          (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
              ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                (covGrad (I := I) (M := M) g 0 s S).toSection y)
                (unitZeroSec (I := I) (M := M) y))) (X y))) x =
          (tensorCov (I := I) g 0 s).toFun
            (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
                ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                  (covGrad (I := I) (M := M) g 0 s S).toSection y)
                  (unitZeroSec (I := I) (M := M) y))) (X y))) x
            (covApply (LeviCivita (I := I) g) V V x) from rfl]
      rw [hρ0]

    have hq2 : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covApplyCovGradCc (I := I) (M := M) g s S hVs).toSection x)
          (unitZeroSec (I := I) (M := M) x)))
        ((LeviCivita (I := I) g).toFun X x (V x)) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V X)
              (fun z : M => S.toSection z)) x (V x))
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
            ((LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) V X) x
              (V x)))
          (unitZeroSec (I := I) (M := M) x) := by
      have hq2pre : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covApplyCovGradCc (I := I) (M := M) g s S hVs).toSection x)
            (unitZeroSec (I := I) (M := M) x)))
          ((LeviCivita (I := I) g).toFun X x (V x)) =
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              covApply (tensorCov (I := I) g 0 (s + 1)) V
                (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
              (unitZeroSec (I := I) (M := M) x)))
            (covApply (LeviCivita (I := I) g) V X x) := rfl
      rw [hq2pre, hM3c]
      rw [show covApply (tensorCov (I := I) g 0 s) V
          (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
            ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
              ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
                (covGrad (I := I) (M := M) g 0 s S).toSection y)
                (unitZeroSec (I := I) (M := M) y)))
              (covApply (LeviCivita (I := I) g) V X y))) x =
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s)
              (covApply (LeviCivita (I := I) g) V X)
              (fun z : M => S.toSection z)) x (V x) from by
        rw [covApply_apply, hρ0']]
      rw [show (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covGrad (I := I) (M := M) g 0 s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)))
          ((LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) V X) x
            (V x)) =
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
              ((LeviCivita (I := I) g).toFun
                (covApply (LeviCivita (I := I) g) V X) x (V x)))
            (unitZeroSec (I := I) (M := M) x) from
        curry_covGrad_unit_read (I := I) (M := M) g s S x
          ((LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) V X) x
            (V x))]
    have hq4 : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)))
        ((LeviCivita (I := I) g).toFun X x (covApply (LeviCivita (I := I) g) V V x)) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
            ((LeviCivita (I := I) g).toFun X x (covApply (LeviCivita (I := I) g) V V x)))
          (unitZeroSec (I := I) (M := M) x) :=
      curry_covGrad_unit_read (I := I) (M := M) g s S x
        ((LeviCivita (I := I) g).toFun X x (covApply (LeviCivita (I := I) g) V V x))

    have hswap := secondCovDeriv_swap_outer (cov := tensorCov (I := I) g 0 s)
      (B := V) (W := X) (T := fun z : M => S.toSection z) (x := x) hVs hXs hSAt
    have hsw2 : (tensorCov (I := I) g 0 s).toFun
        (covApply (tensorCov (I := I) g 0 s) V (fun z : M => S.toSection z)) x
        (VectorField.mlieBracket I V X x) =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) V (fun z : M => S.toSection z)) x
          (covApply (LeviCivita (I := I) g) V X x) -
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) V (fun z : M => S.toSection z)) x
          (covApply (LeviCivita (I := I) g) X V x) := by
      rw [hbrx, map_sub]
    have hsw4 : (tensorCov (I := I) g 0 s).toFun
        (covApply (tensorCov (I := I) g 0 s) (VectorField.mlieBracket I V X)
          (fun z : M => S.toSection z)) x (V x) =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V X)
            (fun z : M => S.toSection z)) x (V x) -
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) X V)
            (fun z : M => S.toSection z)) x (V x) := by
      rw [hbrsec]
      rw [tensorCov_toFun_sub (I := I) (M := M) g s
        (P := covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V X)
          (fun z : M => S.toSection z))
        (Q := covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) X V)
          (fun z : M => S.toSection z))
        (covApplyRS_contMDiff (I := I) g 0 s hSAt hXV)
        (covApplyRS_contMDiff (I := I) g 0 s hSAt hVX)]
      rfl

    have hanti1 : tensorSecondCovDeriv (I := I) g 0 s
        (covApply (LeviCivita (I := I) g) V X) V (fun z : M => S.toSection z) x -
        tensorSecondCovDeriv (I := I) g 0 s V
          (covApply (LeviCivita (I := I) g) V X) (fun z : M => S.toSection z) x =
        riemannOp (tensorCov (I := I) g 0 s) x
          (covApply (LeviCivita (I := I) g) V X x) (V x) (S.toSection x) :=
      tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 s hXV hVs hSAt
    have hanti2 : tensorSecondCovDeriv (I := I) g 0 s X
        (covApply (LeviCivita (I := I) g) V V) (fun z : M => S.toSection z) x -
        tensorSecondCovDeriv (I := I) g 0 s
          (covApply (LeviCivita (I := I) g) V V) X (fun z : M => S.toSection z) x =
        riemannOp (tensorCov (I := I) g 0 s) x (X x)
          (covApply (LeviCivita (I := I) g) V V x) (S.toSection x) :=
      tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 s hXs hW hSAt

    have ht5dir : riemannOp (LeviCivita (I := I) g) x (V x) (X x) (V x) =
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) X V) x (V x) -
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) V V) x (X x) -
        ((LeviCivita (I := I) g).toFun V x (covApply (LeviCivita (I := I) g) V X x) -
          (LeviCivita (I := I) g).toFun V x (covApply (LeviCivita (I := I) g) X V x)) := by
      rw [← riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g) hVs hXs hVs]
      rw [riemannSec_def, hbrx, map_sub]

    have hd31 : tensorSecondCovDeriv (I := I) g 0 s
        (covApply (LeviCivita (I := I) g) V X) V (fun z : M => S.toSection z) x =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) V (fun z : M => S.toSection z)) x
          (covApply (LeviCivita (I := I) g) V X x) -
        (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
          ((LeviCivita (I := I) g).toFun V x
            (covApply (LeviCivita (I := I) g) V X x)) := by
      rw [tensorSecondCovDeriv_def]
    have hd32 : tensorSecondCovDeriv (I := I) g 0 s V
        (covApply (LeviCivita (I := I) g) V X) (fun z : M => S.toSection z) x =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V X)
            (fun z : M => S.toSection z)) x (V x) -
        (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
          ((LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) V X) x
            (V x)) := by
      rw [tensorSecondCovDeriv_def]
    have hd41 : tensorSecondCovDeriv (I := I) g 0 s X
        (covApply (LeviCivita (I := I) g) V V) (fun z : M => S.toSection z) x =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) V V)
            (fun z : M => S.toSection z)) x (X x) -
        (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
          ((LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) V V) x
            (X x)) := by
      rw [tensorSecondCovDeriv_def]
    have hd42 : tensorSecondCovDeriv (I := I) g 0 s
        (covApply (LeviCivita (I := I) g) V V) X (fun z : M => S.toSection z) x =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) X (fun z : M => S.toSection z)) x
          (covApply (LeviCivita (I := I) g) V V x) -
        (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
          ((LeviCivita (I := I) g).toFun X x
            (covApply (LeviCivita (I := I) g) V V x)) := by
      rw [tensorSecondCovDeriv_def]
    have hd6 : tensorSecondCovDeriv (I := I) g 0 s
        (fun y : M => (LeviCivita (I := I) g).toFun V y (X y)) V
        (fun y : M => S.toSection y) x =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) V (fun z : M => S.toSection z)) x
          (covApply (LeviCivita (I := I) g) X V x) -
        (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
          ((LeviCivita (I := I) g).toFun V x
            (covApply (LeviCivita (I := I) g) X V x)) := by
      rw [tensorSecondCovDeriv_def]
      rfl
    have hd7 : tensorSecondCovDeriv (I := I) g 0 s V
        (fun y : M => (LeviCivita (I := I) g).toFun V y (X y))
        (fun y : M => S.toSection y) x =
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) X V)
            (fun z : M => S.toSection z)) x (V x) -
        (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
          ((LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) X V) x
            (V x)) := by
      rw [tensorSecondCovDeriv_def]
      rfl

    rw [hD2split, rs_sub_apply', map_sub, ContinuousLinearMap.sub_apply]
    rw [hM3a, hM3b]
    rw [hT1, hT3, hq2, hq4]
    rw [hL2a, hL2b, ContinuousLinearMap.sub_apply, rs_sub_apply']

    rw [hswap]
    simp only [rs_add_apply']
    rw [hsw2, hsw4]
    simp only [rs_sub_apply']

    rw [show riemannOp (tensorCov (I := I) g 0 s) x
        ((LeviCivita (I := I) g).toFun X x (V x)) (V x) (S.toSection x) =
        riemannOp (tensorCov (I := I) g 0 s) x
          (covApply (LeviCivita (I := I) g) V X x) (V x) (S.toSection x) from rfl]
    rw [show riemannOp (tensorCov (I := I) g 0 s) x (X x)
        ((LeviCivita (I := I) g).toFun V x (V x)) (S.toSection x) =
        riemannOp (tensorCov (I := I) g 0 s) x (X x)
          (covApply (LeviCivita (I := I) g) V V x) (S.toSection x) from rfl]
    rw [← hanti1, ← hanti2]
    rw [hd31, hd32, hd41, hd42, hd6, hd7, ht5dir]
    rw [show covApply (tensorCov (I := I) g 0 s) V
        (fun y : M => riemannSec (tensorCov (I := I) g 0 s) V X
          (fun z : M => S.toSection z) y) x =
        (tensorCov (I := I) g 0 s).toFun
          (fun y : M => riemannSec (tensorCov (I := I) g 0 s) V X
            (fun z : M => S.toSection z) y) x (V x) from rfl]
    simp only [map_sub]
    simp only [rs_sub_apply']
    abel

  have h := congrArg (fun t : Tensor0SSpace s I x => Tensor0SSpace.toModel t m) hVAL
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply] at h
  exact h

end Connection
end Integral
end DifferentialGeometry

end
