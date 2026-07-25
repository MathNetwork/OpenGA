import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Curvature.Bochner.TensorWeitzenbockIdentity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField








noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unitModel_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - S') x =
      unitModel (I := I) (M := M) g s S x -
        unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - S').toSection x = S.toSection x - S'.toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (S - S').toSection x) (unitTensor (I := I) (M := M) x)) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
            (unitTensor (I := I) (M := M) x) -
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
            (unitTensor (I := I) (M := M) x) from by
      rw [hsec]
      rfl]
  rw [Tensor0SSpace.toModel_sub]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in


omit [NeZero (Module.finrank ℝ E)] in
theorem gradSlot_sub_eq_curv
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : SmoothCcTensor g₀ 2 4,
      ∀ S : SmoothCcTensor g₀ 0 2,
        iteratedCovGrad (I := I) g₀ 0 2 2 S -
            domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 C S := by
  classical
  refine ⟨⟨⟨fun y : M =>
      (show TensorRSSpace 2 4 I y from
        TensorRSSpace.ofCLM (curvatureOperatorOnTensorFib (I := I) (M := M) g₀ 2 y)),
      slotFreeCurvOpFib_contMDiff (I := I) (M := M) g₀ 2⟩,
    HasCompactSupport.of_compactSpace _⟩, ?_⟩
  intro S
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel_sub (I := I) g₀ 4 _ _ x, ContinuousMultilinearMap.sub_apply,
    domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (iteratedCovGrad (I := I) g₀ 0 2 2 S) x,
    ContinuousMultilinearMap.domDomCongr_apply]
  set Xs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 0),
      smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ with hXs_def
  set Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 1),
      smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩ with hYs_def
  have hXx : Xs x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hYx : Ys x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  set m : Fin 2 → TangentSpace I x := ![v 2, v 3] with hm_def
  have hv_eq : v = Fin.cons (Xs x) (Fin.cons (Ys x) m) := by
    rw [hXx, hYx, hm_def]
    funext i
    fin_cases i <;> rfl
  have hv_swap : (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      Fin.cons (Ys x) (Fin.cons (Xs x) m) := by
    rw [hXx, hYx, hm_def]
    funext i
    fin_cases i <;> rfl
  have h1 : unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m := by
    conv_lhs => rw [hv_eq]
    rw [unitModel]
    exact tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
      (I := I) (M := M) g₀ 2 S Xs.contMDiff Ys.contMDiff x m
  have h2 : unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m := by
    rw [hv_swap]
    rw [unitModel]
    exact tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
      (I := I) (M := M) g₀ 2 S Ys.contMDiff Xs.contMDiff x m
  have h3 : tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
        (fun y : M => S.toSection y) x -
      tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
        (fun y : M => S.toSection y) x =
      riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
        (fun y : M => S.toSection y) x :=
    tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g₀ 0 2
      (fun y : M => S.toSection y)
      ((Xs.contMDiff x).mdifferentiableAt (by simp))
      ((Ys.contMDiff x).mdifferentiableAt (by simp))
  have h4 : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m := by
    rw [← h3]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
          (fun y : M => S.toSection y) x -
        tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
          (fun y : M => S.toSection y) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
          (fun y : M => S.toSection y) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
          (fun y : M => S.toSection y) x) from rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  have h5 := riemannSec_tensorCov_apply_eval (I := I) (M := M) g₀ 0 2 Xs Ys
    S.toSection (unitZeroSec (I := I) (M := M)) x m
  have h6 : riemannSec
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀))
      (fun b => Xs b) (fun b => Ys b) (fun b => unitZeroSec (I := I) (M := M) b) x = 0 :=
    riemannSec_tensor0SCov_zero_eq_zero (I := I) g₀ Xs Ys
      (fun b => unitZeroSec (I := I) (M := M) b)
      (contMDiff_unitZeroSection (I := I) (M := M)) x
  have h7 := riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g₀ 2 Xs Ys
    (fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
      (unitZeroSec (I := I) (M := M) b))
    (contMDiff_unitEvalSection (I := I) (M := M) g₀ 2 S) x m
  have h8 : ∀ u : TangentSpace I x, baseSlotCurv (I := I) g₀ Xs Ys x u =
      riemannOp (LeviCivita (I := I) g₀) x (v 0) (v 1) u := by
    intro u
    rw [show baseSlotCurv (I := I) g₀ Xs Ys x u =
        riemannSec (LeviCivita (I := I) g₀) (fun b => Xs b) (fun b => Ys b)
          (fun b => smoothExtensionTangent (I := I) x u b) x from rfl]
    rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g₀)
      Xs.contMDiff Ys.contMDiff (smoothExtensionTangent_contMDiff (I := I) x u)]
    rw [smoothExtensionTangent_eq (I := I) x u, hXx, hYx]
  have h9 := slotFreeCurvOpFib_apply_eval (I := I) (M := M) g₀ 2 x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitZeroSec (I := I) (M := M) x)) (v 0) (v 1) m
  have hv0 : v = Fin.cons (v 0) (Fin.cons (v 1) m) := by
    rw [hm_def]
    funext i
    fin_cases i <;> rfl
  rw [h1, h2, h4, h5, h6, map_zero, Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply, sub_zero, h7]
  rw [Finset.sum_congr rfl (fun k _ => by rw [h8 (m k)])]
  rw [← h9]
  conv_rhs => rw [unitModel, hv0]
  rfl

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
