import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckTopCoeff
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffAppCcValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GradSlotCurvature








noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (unitModel unitTensor smoothCcTensor_ext_of_unitModel traceHessianCoeff
    ricciArmPrincipalCoeff)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricLmodel)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma unitModel_sub (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - S') x =
      unitModel (I := I) (M := M) g s S x - unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - S').toSection x = S.toSection x - S'.toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S - S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]
    rfl]
  rw [Tensor0SSpace.toModel_sub]

private lemma unitModel_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + S').toSection x = S.toSection x + S'.toSection x := by
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S + S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]
    rfl]
  rw [Tensor0SSpace.toModel_add]

private lemma unitModel_zero (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    unitModel (I := I) (M := M) g s (0 : SmoothCcTensor g 0 s) x = 0 := by
  have h := unitModel_sub (I := I) g s 0 0 x
  rw [sub_zero] at h
  calc
    unitModel (I := I) (M := M) g s (0 : SmoothCcTensor g 0 s) x =
        unitModel (I := I) (M := M) g s (0 : SmoothCcTensor g 0 s) x -
          unitModel (I := I) (M := M) g s (0 : SmoothCcTensor g 0 s) x := h
    _ = 0 := sub_self _

variable [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
theorem phiMet_symm_zero
    (g₀ g_bg g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (hWsymm : ∀ (x : M) (u₀ u₁ u₂ u₃ : TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 4 W x ![u₀, u₁, u₂, u₃] =
        unitModel (I := I) (M := M) g₀ 4 W x ![u₁, u₀, u₂, u₃]) :
    operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
              (I := I) (M := M) g₀ g) W = 0 := by
  classical
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel_zero, ContinuousMultilinearMap.zero_apply]
  rw [deTurckPhiMetTotal, appCc_sub_left, appCc_sub_left, appCc_add_left, appCc_add_left]
  rw [unitModel_sub, unitModel_sub, unitModel_add, unitModel_add,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_apply_eq
      (I := I) g₀ g g_bg W x v
  have hTHraw :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_apply_eq
      (I := I) (M := M) g₀ g W x v
  have hRACraw :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeff_appCc_eq_combinedTrace
      (I := I) (M := M) g₀ g W x v
  have hPure :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian
      (I := I) (M := M) g₀ g W x v
  have hTH : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![v 0, v 1,
            cometricLmodel (I := I) g x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k] := by
    rw [hTHraw]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
      (by funext i; fin_cases i <;> rfl)
  have hRAC : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g) W) x v =
      (1 / 2 : ℝ) *
        ((∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 W x
              ![cometricLmodel (I := I) g x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                v 0, v 1, (Module.finBasis ℝ E) k]
          + ∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 4 W x
                ![cometricLmodel (I := I) g x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)),
                  v 1, v 0, (Module.finBasis ℝ E) k])
        - ∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (cometricLmodel (I := I) g x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) v))) := by
    rw [hRACraw, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
    refine congrArg₂ (fun a b : ℝ => a - b) (congrArg₂ (fun a b : ℝ => a + b) ?_ ?_) rfl
    · refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
        (by funext i; fin_cases i <;> rfl)
    · refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
        (by funext i; fin_cases i <;> rfl)
  rw [hLie, hTH, hRAC, hPure]
  have hswapA : ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 W x
        ![v 0,
          cometricLmodel (I := I) g x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          v 1, (Module.finBasis ℝ E) k] =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![cometricLmodel (I := I) g x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            v 0, v 1, (Module.finBasis ℝ E) k] :=
    Finset.sum_congr rfl fun k _ => hWsymm x (v 0)
      (cometricLmodel (I := I) g x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      (v 1) ((Module.finBasis ℝ E) k)
  have hswapB : ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 W x
        ![v 1,
          cometricLmodel (I := I) g x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          v 0, (Module.finBasis ℝ E) k] =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![cometricLmodel (I := I) g x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            v 1, v 0, (Module.finBasis ℝ E) k] :=
    Finset.sum_congr rfl fun k _ => hWsymm x (v 1)
      (cometricLmodel (I := I) g x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      (v 0) ((Module.finBasis ℝ E) k)
  rw [hswapA, hswapB]
  ring



noncomputable def gradSwapCurvCoeff (g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 :=
  Classical.choose
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_sub_eq_curv
      (I := I) (M := M) g₀)



omit [NeZero (Module.finrank ℝ E)] in
theorem gradSwapCurv_spec (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    iteratedCovGrad (I := I) g₀ 0 2 2 S
        - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection (I := I)
            g₀ (Equiv.swap (0 : Fin 4) 1) (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (gradSwapCurvCoeff (I := I) g₀) S :=
  Classical.choose_spec
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.gradSlot_sub_eq_curv
      (I := I) (M := M) g₀) S



noncomputable def phiMetCurvCoeff
    (g₀ g_bg g : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 :=
  (1 / 2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g)
    (gradSwapCurvCoeff (I := I) g₀)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in



omit [NeZero (Module.finrank ℝ E)] in
theorem phiMet_curv_fold
    (g₀ g_bg g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
              (I := I) (M := M) g₀ g)
        (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 (phiMetCurvCoeff (I := I) g₀ g_bg g)
        (iteratedCovGrad (I := I) g₀ 0 2 0 S) := by
  classical
  set Φd : SmoothCcTensor g₀ 4 2 :=
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g with hΦd_def
  set W : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 S with hW_def
  set Wsw : SmoothCcTensor g₀ 0 4 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 1) W with hWsw_def
  have hsplit : W = (1 / 2 : ℝ) • (W + Wsw) + (1 / 2 : ℝ) • (W - Wsw) := by
    have h : (1 / 2 : ℝ) • (W + Wsw) + (1 / 2 : ℝ) • (W - Wsw) =
        ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • W +
          ((1 / 2 : ℝ) - (1 / 2 : ℝ)) • Wsw := by
      rw [smul_add, smul_sub, add_smul, sub_smul]
      abel
    rw [h]
    norm_num
  have hsym : ∀ (x : M) (u₀ u₁ u₂ u₃ : TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 4 (W + Wsw) x ![u₀, u₁, u₂, u₃] =
        unitModel (I := I) (M := M) g₀ 4 (W + Wsw) x ![u₁, u₀, u₂, u₃] := by
    intro x u₀ u₁ u₂ u₃
    have hv : ∀ a b : TangentSpace I x,
        (fun i => (![a, b, u₂, u₃] : Fin 4 → TangentSpace I x)
          ((Equiv.swap (0 : Fin 4) 1) i)) = ![b, a, u₂, u₃] := by
      intro a b
      funext i
      fin_cases i <;> rfl
    rw [unitModel_add (I := I) g₀ 4 W Wsw x,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
      hWsw_def,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel
        (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) W x,
      ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
      hv u₀ u₁, hv u₁ u₀]
    exact add_comm _ _
  have hkill : operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
      ((1 / 2 : ℝ) • (W + Wsw)) = 0 := by
    rw [appCc_smul_right, hΦd_def, phiMet_symm_zero (I := I) (M := M) g₀ g_bg g
      (W + Wsw) hsym, smul_zero]
  calc
    operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd W =
        operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
          ((1 / 2 : ℝ) • (W + Wsw) + (1 / 2 : ℝ) • (W - Wsw)) := by rw [← hsplit]
    _ = operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1 / 2 : ℝ) • (W + Wsw))
        + operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1 / 2 : ℝ) • (W - Wsw)) :=
      appCc_add_right (I := I) (M := M) g₀ 4 2 Φd _ _
    _ = operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1 / 2 : ℝ) • (W - Wsw)) := by
      rw [hkill, zero_add]
    _ = (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd (W - Wsw) :=
      appCc_smul_right (I := I) (M := M) g₀ 4 2 (1 / 2 : ℝ) Φd _
    _ = (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 (gradSwapCurvCoeff (I := I) g₀) S) := by
      rw [hW_def, hWsw_def, hW_def, gradSwapCurv_spec (I := I) (M := M) g₀ S]
    _ = (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φd
          (gradSwapCurvCoeff (I := I) g₀)) S := by
      rw [appCcRS_zero_eq_appCc, operatorFieldApply_assoc]
    _ = operatorFieldApply (I := I) (M := M) g₀ 2 2
        ((1 / 2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φd
          (gradSwapCurvCoeff (I := I) g₀)) S := by
      rw [appCc_smul_left]
    _ = operatorFieldApply (I := I) (M := M) g₀ 2 2 (phiMetCurvCoeff (I := I) g₀ g_bg g)
        (iteratedCovGrad (I := I) g₀ 0 2 0 S) := by
      rw [iteratedCovGrad_zero, phiMetCurvCoeff, hΦd_def]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
