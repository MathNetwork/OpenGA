import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

section Generic

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
  [FiberBundle F V] [VectorBundle ℝ F V]

def nablaRiemannSec (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (covV : CovariantDerivative I F V)
    (X Y Z : Π b : M, TangentSpace I b) (A : Π b : M, V b) (x : M) : V x :=
  covV.toFun (fun b => riemannSec covV Y Z A b) x (X x)
    - riemannSec covV (covApply covT X Y) Z A x
    - riemannSec covV Y (covApply covT X Z) A x
    - riemannSec covV Y Z (covApply covV X A) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [VectorBundle ℝ F V] in

lemma nablaRiemannSec_def (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (covV : CovariantDerivative I F V)
    (X Y Z : Π b : M, TangentSpace I b) (A : Π b : M, V b) (x : M) :
    nablaRiemannSec covT covV X Y Z A x =
      covV.toFun (fun b => riemannSec covV Y Z A b) x (X x)
        - riemannSec covV (covApply covT X Y) Z A x
        - riemannSec covV Y (covApply covT X Z) A x
        - riemannSec covV Y Z (covApply covV X A) x := rfl

end Generic

section TangentCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in

lemma nablaCurvSec_eq_nablaRiemannSec
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z W : Π b : M, TangentSpace I b) (x : M) :
    nablaCurvSec cov X Y Z W x = nablaRiemannSec cov cov X Y Z W x := rfl

end TangentCase

section GenericNablaHomLeibniz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {E_U : Type*} [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]
  [FiniteDimensional ℝ E_U] [CompleteSpace E_U]
variable {U : M → Type*} [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)]
  [∀ x, TopologicalSpace (U x)]
  [TopologicalSpace (TotalSpace E_U U)] [FiberBundle E_U U] [VectorBundle ℝ E_U U]
  [∀ x, IsTopologicalAddGroup (U x)] [∀ x, ContinuousSMul ℝ (U x)]
  [ContMDiffVectorBundle ∞ E_U U I]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]
variable {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V I]

omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [CompleteSpace E_U] [CompleteSpace F] in
lemma nablaRiemannSec_homBundleGen_apply_eq
    (cov_U : CovariantDerivative I E_U U) [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov_V ∞]
    (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative covT ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x : M => U x →L[ℝ] V x)⟯)
    (W : Cₛ^∞⟮I; E_U, U⟯) (x : M) :
    (nablaRiemannSec covT (HomConnectionGen.homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V)
        (fun b => X b) (fun b => Y b) (fun b => Z b) (fun b => τ b) x) (W x) =
      nablaRiemannSec covT cov_V (fun b => X b) (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) x
        - τ x (nablaRiemannSec covT cov_U (fun b => X b) (fun b => Y b) (fun b => Z b)
            (fun b => W b) x) := by
  classical
  set covHom := HomConnectionGen.homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V with hcovHom

  set BXY : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (covApply covT (fun b => X b) (fun b => Y b))
      (covApply_contMDiff (cov := covT) X.contMDiff Y.contMDiff) with hBXY
  set BXZ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (covApply covT (fun b => X b) (fun b => Z b))
      (covApply_contMDiff (cov := covT) X.contMDiff Z.contMDiff) with hBXZ
  set RUW : Cₛ^∞⟮I; E_U, U⟯ :=
    ContMDiffSection.mk (fun b => riemannSec cov_U (fun b => Y b) (fun b => Z b) (fun b => W b) b)
      (riemannSec_contMDiff (cov := cov_U) Y.contMDiff Z.contMDiff W.contMDiff) with hRUW
  set DXW : Cₛ^∞⟮I; E_U, U⟯ :=
    ContMDiffSection.mk (covApply cov_U (fun b => X b) (fun b => W b))
      (covApply_contMDiff (cov := cov_U) X.contMDiff W.contMDiff) with hDXW
  set Dτ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x : M => U x →L[ℝ] V x)⟯ :=
    ContMDiffSection.mk (covApply covHom (fun b => X b) (fun b => τ b))
      (covApply_contMDiff (cov := covHom) X.contMDiff τ.contMDiff) with hDτ

  have hτat : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun y : M => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) y (τ y)) x :=
    (τ.contMDiff x).mdifferentiableAt (by simp)
  have hWat : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y : M => TotalSpace.mk' E_U (E := U) y (W y)) x :=
    (W.contMDiff x).mdifferentiableAt (by simp)
  have hXat : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (X y)) x :=
    (X.contMDiff x).mdifferentiableAt (by simp)
  have hRHτ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E_U →L[ℝ] F)) ∞
      (fun b => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) b
          (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)) :=
    riemannSec_contMDiff (cov := covHom) Y.contMDiff Z.contMDiff τ.contMDiff
  have hRHτ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun b => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) b
          (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)) x :=
    (hRHτ_smooth x).mdifferentiableAt (by simp)
  have hRUW_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y : M => TotalSpace.mk' E_U (E := U) y (RUW y)) x :=
    (RUW.contMDiff x).mdifferentiableAt (by simp)

  have hPsec : (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
        (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b) (fun b => W b)) =
      (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b)
        - (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b)
            (fun b => RUW b)) := by
    funext b
    have hstar := HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V
      Y Z τ W b
    simp only [HomConnectionGen.pairedSection, Pi.sub_apply]
    rw [show RUW b = riemannSec cov_U (fun b => Y b) (fun b => Z b) (fun b => W b) b from rfl]
    rw [hstar]

  have hsm1 : MDiffAt (T% (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
      (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b)) x := by
    have := riemannSec_contMDiff (cov := cov_V) Y.contMDiff Z.contMDiff
      (T := HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b))
      (ContMDiff.clm_bundle_apply (b := id) τ.contMDiff W.contMDiff)
    exact (this x).mdifferentiableAt (by simp)
  have hsm2 : MDiffAt (T% (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
      (fun b => τ b) (fun b => RUW b))) x :=
    ((ContMDiff.clm_bundle_apply (b := id) τ.contMDiff RUW.contMDiff) x).mdifferentiableAt (by simp)

  have hVadd : cov_V.toFun (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b)
          x (X x) =
      cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
          (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)
          (fun b => W b)) x (X x)
        + cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
            (fun b => τ b) (fun b => RUW b)) x (X x) := by
    have hsplit : (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b) =
        HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
            (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b) (fun b => W b)
          + HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => RUW b) := by
      rw [hPsec]; abel
    have hsmσW : MDiffAt (T% (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
        (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b) (fun b => W b))) x :=
      ((ContMDiff.clm_bundle_apply (b := id) hRHτ_smooth W.contMDiff) x).mdifferentiableAt (by simp)
    rw [hsplit, cov_V.isCovariantDerivativeOnUniv.add hsmσW hsm2]
    rfl

  rw [nablaRiemannSec_def]
  simp only [ContinuousLinearMap.sub_apply]

  rw [show covHom.toFun
        (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b) x (X x) (W x) =
      cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
          (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)
          (fun b => W b)) x (X x)
        - (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) x)
            (cov_U.toFun (fun b => W b) x (X x)) from by
    have h := HomConnectionGen.cov_V_toFun_pairedSection_apply I M E_U U F V cov_U cov_V
      (σ := fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)
      (Y := fun b => W b) hRHτ_at hWat (X x)
    rw [← hcovHom] at h
    rw [h]
    abel]
  rw [show cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
          (fun b => τ b) (fun b => RUW b)) x (X x) =
      (covHom.toFun (fun b => τ b) x (X x)) (RUW x)
        + τ x (cov_U.toFun (fun b => RUW b) x (X x)) from by
    have h := HomConnectionGen.cov_V_toFun_pairedSection_apply I M E_U U F V cov_U cov_V
      (σ := fun b => τ b) (Y := fun b => RUW b) hτat hRUW_at (X x)
    rw [← hcovHom] at h
    exact h] at hVadd

  rw [show cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
          (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)
          (fun b => W b)) x (X x) =
      cov_V.toFun (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b)
          x (X x)
        - ((covHom.toFun (fun b => τ b) x (X x)) (RUW x)
            + τ x (cov_U.toFun (fun b => RUW b) x (X x))) from
    (eq_sub_of_add_eq hVadd.symm)]

  rw [show riemannSec covHom (covApply covT (fun b => X b) (fun b => Y b)) (fun b => Z b)
        (fun b => τ b) x (W x) =
      (riemannSec covHom (fun b => BXY b) (fun b => Z b) (fun b => τ b) x) (W x) from rfl,
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V BXY Z τ W x]
  rw [show riemannSec covHom (fun b => Y b) (covApply covT (fun b => X b) (fun b => Z b))
        (fun b => τ b) x (W x) =
      (riemannSec covHom (fun b => Y b) (fun b => BXZ b) (fun b => τ b) x) (W x) from rfl,
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V Y BXZ τ W x]
  rw [show riemannSec covHom (fun b => Y b) (fun b => Z b)
        (covApply covHom (fun b => X b) (fun b => τ b)) x (W x) =
      (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => Dτ b) x) (W x) from rfl,
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V Y Z Dτ W x]

  rw [show (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) x)
        (cov_U.toFun (fun b => W b) x (X x)) =
      (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) x) (DXW x) from rfl,
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V Y Z τ DXW x]

  rw [nablaRiemannSec_def, nablaRiemannSec_def, map_sub, map_sub, map_sub]

  rw [show covApply cov_V (fun b => X b)
        (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) =
      HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => Dτ b) (fun b => W b)
        + HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => DXW b) from by
    have h := HomConnectionGen.covApply_cov_V_pairedSection_eq I M E_U U F V cov_U cov_V X τ W
    rw [← hcovHom] at h
    rw [h]
    rfl]

  rw [show riemannSec cov_V (fun b => Y b) (fun b => Z b)
        (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => Dτ b) (fun b => W b)
          + HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => DXW b))
        x =
      riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => Dτ b) (fun b => W b)) x
        + riemannSec cov_V (fun b => Y b) (fun b => Z b)
            (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => DXW b)) x
      from by
    have hP1sm : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (HomConnectionGen.pairedSection
        (M := M) (U := U) (V := V) (fun b => Dτ b) (fun b => W b))) :=
      ContMDiff.clm_bundle_apply (b := id) Dτ.contMDiff W.contMDiff
    have hP2sm : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (HomConnectionGen.pairedSection
        (M := M) (U := U) (V := V) (fun b => τ b) (fun b => DXW b))) :=
      ContMDiff.clm_bundle_apply (b := id) τ.contMDiff DXW.contMDiff
    exact riemannSec_add_third (cov := cov_V)
      (Filter.Eventually.of_forall (fun b => (hP1sm b).mdifferentiableAt (by simp)))
      (Filter.Eventually.of_forall (fun b => (hP2sm b).mdifferentiableAt (by simp)))
      ((covApply_contMDiff (cov := cov_V) Z.contMDiff hP1sm x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Z.contMDiff hP2sm x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Z.contMDiff (hP1sm.add_section hP2sm) x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Y.contMDiff hP1sm x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Y.contMDiff hP2sm x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Y.contMDiff (hP1sm.add_section hP2sm) x).mdifferentiableAt (by simp))]

  simp only [hBXY, hBXZ, hDτ, hDXW, hRUW, ContMDiffSection.coeFn_mk]
  rw [show covApply covHom (fun b => X b) (fun b => τ b) x =
      covHom.toFun (fun b => τ b) x (X x) from rfl]
  abel

end GenericNablaHomLeibniz

section TensorTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

private abbrev TensorSmooth (s : ℕ) (A : Π b : M, Tensor0SSpace s I b) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
    (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) b (A b))

def nablaBaseSlotCurv
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    TangentSpace I x :=
  nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
    (fun b => smoothExtensionTangent (I := I) x u b) x

def nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) : Tensor0SSpace s I x :=
  nablaRiemannSec (LeviCivita (I := I) g)
    (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (fun b => X b) (fun b => Y b) (fun b => Z b) A x

omit [CompleteSpace E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma nablaTensor0SCurv_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    nablaTensor0SCurv (I := I) g s X Y Z A x =
      (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun b => riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b) A b) x (X x)
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b)) (fun b => Z b) A x
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b)) A x
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b)
            (covApply (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (fun b => X b) A) x :=
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannSec_tensor0SCov_zero_raw_eq_zero
    (g : SmoothRiemannianMetric I M)
    {P Q : Π b : M, TangentSpace I b}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Q))
    (A : Π b : M, Tensor0SSpace 0 I b) (hA : TensorSmooth (I := I) 0 A) (x : M) :
    riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)) P Q A x = 0 := by
  have hz := riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g
    (ContMDiffSection.mk P hP) (ContMDiffSection.mk Q hQ) A hA x
  simpa using hz

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_zero_eq_zero
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace 0 I b) (hA : TensorSmooth (I := I) 0 A) (x : M) :
    nablaTensor0SCurv (I := I) g 0 X Y Z A x = 0 := by
  classical
  rw [nablaTensor0SCurv_def]
  have hzero_sec : (fun b => riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (fun b => Y b) (fun b => Z b) A b) = (0 : Π b : M, Tensor0SSpace 0 I b) := by
    funext b
    exact riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g Y Z A hA b
  rw [hzero_sec]
  have hlead : (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).toFun
      (0 : Π b : M, Tensor0SSpace 0 I b) x (X x) = 0 := by
    rw [(tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).isCovariantDerivativeOnUniv.zero
      (Set.mem_univ x)]
    simp
  rw [hlead]
  have hXY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g)
      (fun b => X b) (fun b => Y b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Y.contMDiff
  have hXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g)
      (fun b => X b) (fun b => Z b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Z.contMDiff
  rw [riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g hXY Z.contMDiff A hA x,
    riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g Y.contMDiff hXZ A hA x]
  have hcXA : TensorSmooth (I := I) 0 (covApply
      (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)) (fun b => X b) A) :=
    covApply_contMDiff (cov := tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      X.contMDiff hA
  rw [riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g Y.contMDiff Z.contMDiff _ hcXA x]
  abel

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensor0S_curry_nablaTensor0SCurv_succ_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace (s + 1) I b) (hA : TensorSmooth (I := I) (s + 1) A) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        (nablaTensor0SCurv (I := I) g (s + 1) X Y Z A x) =
      nablaRiemannSec (LeviCivita (I := I) g) (homGenS (I := I) (M := M) g s)
        (fun b => X b) (fun b => Y b) (fun b => Z b) (curriedSection I M A) x := by
  classical

  have hA1 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ((∞ : WithTop ℕ∞) + 1)
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (A b)) := by
    rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]; exact hA
  have hAatAll : ∀ b : M, TensorSectionMDiffAt (I := I) (s + 1) A b := fun b =>
    (hA b).mdifferentiableAt (by simp)

  have hRYZ_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b) A b)) :=
    riemannSec_contMDiff (cov := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
      Y.contMDiff Z.contMDiff hA
  have hRYZ_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun b => riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (fun b => Z b) A b) x :=
    (hRYZ_smooth x).mdifferentiableAt (by simp)

  have hcovApply_at : ∀ (P : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      TensorSectionMDiffAt (I := I) (s + 1)
        (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => P b) A) x := by
    intro P
    have hsm := covApply_contMDiffOn (cov := tensor0SCovariantDerivative I M (s + 1)
      (LeviCivita (I := I) g)) P.contMDiff hA1
    exact (hsm.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)

  have hcurry_covApply : ∀ (P : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      curriedSection I M
          (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => P b) A) =
        covApply (homGenS (I := I) (M := M) g s) (fun b => P b) (curriedSection I M A) := by
    intro P
    funext b
    rw [curriedSection_apply, covApply_apply, covApply_apply,
      tensor0S_curry_tensor0SCov_succ_eq_homGenS (I := I) (M := M) g s A (hAatAll b) (P b)]

  have hcurry_RYZ :
      curriedSection I M
          (fun b => riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b) A b) =
        (fun b => riemannSec (homGenS (I := I) (M := M) g s)
          (fun b => Y b) (fun b => Z b) (curriedSection I M A) b) := by
    funext b
    rw [curriedSection_apply,
      tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s Y Z A hA b]

  rw [nablaTensor0SCurv_def, nablaRiemannSec_def]
  rw [map_sub, map_sub, map_sub]

  rw [tensor0S_curry_tensor0SCov_succ_eq_homGenS (I := I) (M := M) g s
      (fun b => riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (fun b => Z b) A b) hRYZ_at (X x), hcurry_RYZ]

  rw [show riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b)) (fun b => Z b) A x =
      riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => (ContMDiffSection.mk
          (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b))
          (covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Y.contMDiff) : Π b : M, TangentSpace I b) b)
        (fun b => Z b) A x from rfl,
    tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s
      (ContMDiffSection.mk (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b))
        (covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Y.contMDiff)) Z A hA x]
  rw [show riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b)) A x =
      riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b)
        (fun b => (ContMDiffSection.mk
          (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b))
          (covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Z.contMDiff) : Π b : M, TangentSpace I b) b)
        A x from rfl,
    tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s Y
      (ContMDiffSection.mk (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b))
        (covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Z.contMDiff)) A hA x]
  rw [show riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (fun b => Z b)
        (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => X b) A) x =
      riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (fun b => Z b)
        (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => X b) A) x from rfl]
  rw [tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s Y Z
      (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => X b) A)
      (covApply_contMDiff (cov := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        X.contMDiff hA) x,
    hcurry_covApply X]

  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_succ_consEval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace (s + 1) I b) (hA : TensorSmooth (I := I) (s + 1) A)
    (x : M) (u₀ : TangentSpace I x) (u' : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g (s + 1) X Y Z A x) (Fin.cons u₀ u') =
      Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s X Y Z
            (fun b => curriedSection I M A b
              (smoothExtensionTangent (I := I) x u₀ b)) x) u' -
        Tensor0SSpace.toModel (A x)
          (Fin.cons (nablaBaseSlotCurv (I := I) g X Y Z x u₀) u') := by
  classical
  set Y₀ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u₀)
      (smoothExtensionTangent_contMDiff (I := I) x u₀) with hY₀_def
  have hY₀x : (Y₀ : Π b : M, TangentSpace I b) x = u₀ := smoothExtensionTangent_eq (I := I) x u₀
  set Acurry : Cₛ^∞⟮I; E →L[ℝ] Tensor0SModel s ℝ E,
      (fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)⟯ :=
    ContMDiffSection.mk (curriedSection I M A)
      ((contMDiff_curriedSection_iff_section I M A).mp hA) with hAcurry_def

  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := nablaTensor0SCurv (I := I) g (s + 1) X Y Z A x) (v0 := u₀) (vs := u')]

  rw [tensor0S_curry_nablaTensor0SCurv_succ_eq (I := I) g s X Y Z A hA x]

  rw [show nablaRiemannSec (LeviCivita (I := I) g) (homGenS (I := I) (M := M) g s)
        (fun b => X b) (fun b => Y b) (fun b => Z b) (curriedSection I M A) x =
      nablaRiemannSec (LeviCivita (I := I) g)
          (HomConnectionGen.homBundleCovariantDerivativeGen I M E
            (TangentSpace I : M → Type _) (Tensor0SModel s ℝ E)
            (fun x : M => Tensor0SSpace s I x)
            (LeviCivita (I := I) g)
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)))
          (fun b => X b) (fun b => Y b) (fun b => Z b) (fun b => Acurry b) x from rfl]
  conv_lhs => rw [show (u₀ : TangentSpace I x) = (Y₀ : Π b : M, TangentSpace I b) x from hY₀x.symm]
  rw [nablaRiemannSec_homBundleGen_apply_eq (I := I) (M := M)
    (E_U := E) (U := (TangentSpace I : M → Type _)) (F := Tensor0SModel s ℝ E)
    (V := (fun x : M => Tensor0SSpace s I x))
    (cov_U := LeviCivita (I := I) g)
    (cov_V := tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (covT := LeviCivita (I := I) g) X Y Z Acurry Y₀ x]

  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

  rw [show (Acurry : Π b : M, TangentSpace I b →L[ℝ] Tensor0SSpace s I b) x =
      curriedSection I M A x from rfl, curriedSection_apply,
    show (nablaRiemannSec (LeviCivita (I := I) g) (LeviCivita (I := I) g)
        (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => (Y₀ : Π b : M, TangentSpace I b) b) x) =
      nablaBaseSlotCurv (I := I) g X Y Z x u₀ from rfl,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := A x) (v0 := nablaBaseSlotCurv (I := I) g X Y Z x u₀) (vs := u')]

  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_apply_eval
    (g : SmoothRiemannianMetric I M) (t : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ (A : Π b : M, Tensor0SSpace t I b), TensorSmooth (I := I) t A →
      ∀ (x : M) (u : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g t X Y Z A x) u =
        - ∑ k : Fin t,
            Tensor0SSpace.toModel (A x)
              (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))) := by
  induction t with
  | zero =>
      intro A hA x u
      rw [nablaTensor0SCurv_zero_eq_zero (I := I) g X Y Z A hA x]
      simp
  | succ s ih =>
      intro A hA x u
      classical
      have hpaired_smooth : TensorSmooth (I := I) s
          (fun b => curriedSection I M A b (smoothExtensionTangent (I := I) x (u 0) b)) :=
        ContMDiff.clm_bundle_apply (b := id)
          ((contMDiff_curriedSection_iff_section I M A).mp hA)
          (smoothExtensionTangent_contMDiff (I := I) x (u 0))
      rw [show u = Fin.cons (u 0) (Fin.tail u) from (Fin.cons_self_tail u).symm,
        nablaTensor0SCurv_succ_consEval (I := I) g s X Y Z A hA x (u 0) (Fin.tail u)]
      have hih := ih (fun b => curriedSection I M A b (smoothExtensionTangent (I := I) x (u 0) b))
        hpaired_smooth x (Fin.tail u)
      rw [hih]
      have hpx : ∀ v : Fin s → TangentSpace I x,
          Tensor0SSpace.toModel
              (curriedSection I M A x (smoothExtensionTangent (I := I) x (u 0) x)) v =
            Tensor0SSpace.toModel (A x) (Fin.cons (u 0) v) := by
        intro v
        rw [curriedSection_apply, smoothExtensionTangent_eq (I := I) x (u 0),
          TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := A x) (v0 := u 0) (vs := v)]
      rw [Finset.sum_congr rfl (fun k _ => by
        rw [hpx (Function.update (Fin.tail u) k (nablaBaseSlotCurv (I := I) g X Y Z x (Fin.tail u k)))])]
      have hcons_lead :
          Fin.cons (nablaBaseSlotCurv (I := I) g X Y Z x (u 0)) (Fin.tail u) =
            Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0)) := by
        rw [← Fin.update_cons_zero (x := u 0) (p := Fin.tail u)
          (z := nablaBaseSlotCurv (I := I) g X Y Z x (u 0)), Fin.cons_self_tail]
      have hcons_succ : ∀ (k : Fin s),
          Fin.cons (u 0) (Function.update (Fin.tail u) k
              (nablaBaseSlotCurv (I := I) g X Y Z x (Fin.tail u k))) =
            Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)) := by
        intro k
        have htk : Fin.tail u k = u k.succ := rfl
        rw [htk, Fin.cons_update (x := u 0) (p := Fin.tail u) (i := k)
          (y := nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)), Fin.cons_self_tail]
      rw [Finset.sum_congr rfl (fun k _ => by rw [hcons_succ k]), hcons_lead]
      rw [show (- ∑ k : Fin s,
            Tensor0SSpace.toModel (A x)
              (Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)))) -
          Tensor0SSpace.toModel (A x)
            (Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0))) =
          - (Tensor0SSpace.toModel (A x)
              (Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0))) +
              ∑ k : Fin s,
                Tensor0SSpace.toModel (A x)
                  (Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)))) from by
        ring]
      rw [Fin.cons_self_tail]
      congr 1
      rw [Fin.sum_univ_succ
        (f := fun k : Fin (s + 1) =>
          Tensor0SSpace.toModel (A x)
            (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))))]

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensorCov_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g s X Y Z A x) u =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (A x)
            (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))) :=
  nablaTensor0SCurv_apply_eval (I := I) g s X Y Z A hA x u

omit [CompleteSpace E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
lemma nablaBaseSlotCurv_eq_nablaCurvSec
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x u =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => smoothExtensionTangent (I := I) x u b) x := rfl

omit [CompleteSpace E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_cyclic_eq_zero
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x u
      + nablaBaseSlotCurv (I := I) g Y Z X x u
      + nablaBaseSlotCurv (I := I) g Z X Y x u = 0 := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec,
      nablaBaseSlotCurv_eq_nablaCurvSec]
  exact second_bianchi_levi_civita_metric (I := I) g X.contMDiff Y.contMDiff Z.contMDiff
    (smoothExtensionTangent_contMDiff (I := I) x u)

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensor0SCurv_cyclic_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s X Y Z A x
      + nablaTensor0SCurv (I := I) g s Y Z X A x
      + nablaTensor0SCurv (I := I) g s Z X Y A x = 0 := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_zero]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.zero_apply]
  rw [nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s Y Z X A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s Z X Y A hA x u]
  have hkey : ∀ k : Fin s,
      Tensor0SSpace.toModel (A x)
          (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k)))
        + Tensor0SSpace.toModel (A x)
          (Function.update u k (nablaBaseSlotCurv (I := I) g Y Z X x (u k)))
        + Tensor0SSpace.toModel (A x)
          (Function.update u k (nablaBaseSlotCurv (I := I) g Z X Y x (u k))) = 0 := by
    intro k
    rw [← (Tensor0SSpace.toModel (A x)).map_update_add u k
          (nablaBaseSlotCurv (I := I) g X Y Z x (u k))
          (nablaBaseSlotCurv (I := I) g Y Z X x (u k))]
    rw [← (Tensor0SSpace.toModel (A x)).map_update_add u k
          (nablaBaseSlotCurv (I := I) g X Y Z x (u k)
            + nablaBaseSlotCurv (I := I) g Y Z X x (u k))
          (nablaBaseSlotCurv (I := I) g Z X Y x (u k))]
    rw [nablaBaseSlotCurv_cyclic_eq_zero (I := I) g X Y Z x (u k)]
    exact (Tensor0SSpace.toModel (A x)).map_coord_zero k (by rw [Function.update_self])
  rw [← neg_add, ← neg_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_zero (fun k _ => hkey k), neg_zero]

omit [CompleteSpace E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaTensorCurv_frame_trace_eq_nablaRicci
    (g : SmoothRiemannianMetric I M)
    {X V : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) (w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (nablaCurvSec (LeviCivita (I := I) g) X
          (smoothOrthoFrame (I := I) g x i) V
          (fun b => smoothExtensionTangent (I := I) x w b) x)
          (smoothOrthoFrame (I := I) g x i x) =
      nablaRicci (I := I) g X V (fun b => smoothExtensionTangent (I := I) x w b) x := by
  have hext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => smoothExtensionTangent (I := I) x w b)) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  exact (nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hX hV hext).symm

theorem frame_sum_nablaTensor0SCurv_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (u : Fin s → TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s X
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i)) Z A x) u =
      - ∑ k : Fin s, ∑ i : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel (A x)
            (Function.update u k
              (nablaBaseSlotCurv (I := I) g X
                (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                  (smoothOrthoFrame_smooth (I := I) g x i)) Z x (u k))) := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => nablaTensorCov_baseSlot_eval (I := I) g s X
    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i)) Z A hA x u)]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]

omit [CompleteSpace E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub
    (g : SmoothRiemannianMetric I M)
    {Y W U : Π b : M, TangentSpace I b} {x : M}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U)) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (nablaCurvSec (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) Y W x) (U x) =
      nablaRicci (I := I) g U Y W x - nablaRicci (I := I) g W U Y x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hB_def
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)) :=
    fun i => smoothOrthoFrame_smooth (I := I) g x i

  have hconj : ∀ i,
      g.inner x (nablaCurvSec cov (B i) (B i) Y W x) (U x) =
        g.inner x (nablaCurvSec cov (B i) U W Y x) (B i x) := by
    intro i

    have hsk1 : g.inner x (nablaCurvSec cov (B i) (B i) Y W x) (U x) =
        - g.inner x (nablaCurvSec cov (B i) (B i) Y U x) (W x) := by
      have h := nablaCurvSec_metric_skew45 (I := I) g (X := B i) (Y := B i) (Z := Y) (W := W)
        (U := U) (x := x) (hBsm i) (hBsm i) hY hW hU
      linarith [h]

    have hps : g.inner x (nablaCurvSec cov (B i) (B i) Y U x) (W x) =
        g.inner x (nablaCurvSec cov (B i) U W (B i) x) (Y x) := by
      exact nablaCurvSec_inner_pair_symm (I := I) g (X := B i) (Y := B i) (Z := Y) (W := U)
        (U := W) (hBsm i) (hBsm i) hY hU hW

    have hsk2 : g.inner x (nablaCurvSec cov (B i) U W (B i) x) (Y x) =
        - g.inner x (nablaCurvSec cov (B i) U W Y x) (B i x) := by
      have h := nablaCurvSec_metric_skew45 (I := I) g (X := B i) (Y := U) (Z := W) (W := B i)
        (U := Y) (x := x) (hBsm i) hU hW (hBsm i) hY
      linarith [h]
    rw [hsk1, hps, hsk2]; ring
  rw [Finset.sum_congr rfl (fun i _ => hconj i)]

  have hbi : ∀ i,
      g.inner x (nablaCurvSec cov (B i) U W Y x) (B i x)
        + g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x)
        + g.inner x (nablaCurvSec cov W (B i) U Y x) (B i x) = 0 := by
    intro i
    exact nablaCurvSec_bianchi_paired (I := I) g (X := B i) (Y := U) (Z := W) (W := Y)
      (U := B i) (x := x) (hBsm i) hU hW hY

  have hrew : ∀ i,
      g.inner x (nablaCurvSec cov (B i) U W Y x) (B i x) =
        - g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x)
        - g.inner x (nablaCurvSec cov W (B i) U Y x) (B i x) := by
    intro i; linarith [hbi i]
  rw [Finset.sum_congr rfl (fun i _ => hrew i)]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

  have hterm3 : ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (nablaCurvSec cov W (B i) U Y x) (B i x) =
      nablaRicci (I := I) g W U Y x := by
    rw [nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hW hU hY]

  have hterm2 : ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x) =
      - nablaRicci (I := I) g U Y W x := by
    have hconv : ∀ i,
        g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x) =
          - g.inner x (nablaCurvSec cov U (B i) Y W x) (B i x) := by
      intro i

      have hps : g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x) =
          g.inner x (nablaCurvSec cov U Y (B i) W x) (B i x) :=
        nablaCurvSec_inner_pair_symm (I := I) g (X := U) (Y := W) (Z := B i) (W := Y)
          (U := B i) hU hW (hBsm i) hY (hBsm i)

      rw [hps, nablaCurvSec_swap23 (I := I) g (X := U) (Y := Y) (Z := B i) (W := W) (x := x)
        hY (hBsm i) hW, map_neg, ContinuousLinearMap.neg_apply]
    rw [Finset.sum_congr rfl (fun i _ => hconv i), Finset.sum_neg_distrib,
      nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hU hY hW]
  rw [hterm2, hterm3]
  ring

theorem frame_sum_nablaTensor0SCurv_diag_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (u : Fin s → TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i))
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i)) Y A x) u =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (A x)
            (Function.update u k
              (∑ i : Fin (Module.finrank ℝ E),
                nablaBaseSlotCurv (I := I) g
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i))
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i)) Y x (u k))) := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => nablaTensorCov_baseSlot_eval (I := I) g s
    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i))
    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i)) Y A hA x u)]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact ((Tensor0SSpace.toModel (A x)).toMultilinearMap.map_update_sum Finset.univ k
    (fun i => nablaBaseSlotCurv (I := I) g
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) Y x (u k)) u).symm

end TensorTransfer

end Connection
end Integral
end DifferentialGeometry

end
