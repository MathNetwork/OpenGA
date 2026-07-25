import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckCurvatureArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciArmPrincipalCoeffBackgroundJetBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartLieDeriv
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffAppCcValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RealizedGramDerivChartEvaluation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm2CoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmConnLapJetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzRicciArmCoeffBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLiePathValueDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieArmChartValue
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionL2JetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmDiffL2TameBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckTopCoeff


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField pathIntegralCoeffField_appCc_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_appCc linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff linearizedRicciArm1CorrField ricciArmPrincipalCoeff traceHessianCoeff linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff exists_arm1Koszul_realizedFam_rfns_ballUniform continuousBilinearMap_basis_expand unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local appCc_zero_left_local ccTensor02Symm symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedSmallSet realizedSmallSet_isOpen Icc_subset_realizedSmallSet linearizedRicciAt ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo realizedRicciChartSum jointContMDiff_toModel_continuous_slice hasDerivAt_realizedRicciChartSum_general realizedFam)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmAbsorbedCoeff symmAbsorbedCoeff_appCc_eq exists_iteratedCovGrad_unitModel_domDomCongrSection symmAbsorbedCoeff_riemannianFiberNormSq_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricLmodel)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_zero_fw (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    unitModel (I := I) (M := M) g s (0 : SmoothCcTensor g 0 s) x = 0 := by
  have h := unitModel_sub_local (I := I) g s 0 0 x
  rw [sub_zero] at h
  rw [h, sub_self]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
theorem deTurckPhiMetTotal_background_appCc_eq_zero_of_slot01Symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (hWsymm : ∀ (x : M) (u₀ u₁ u₂ u₃ : TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 4 W x ![u₀, u₁, u₂, u₃] =
        unitModel (I := I) (M := M) g₀ 4 W x ![u₁, u₀, u₂, u₃]) :
    operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
              (I := I) (M := M) g₀ g₀) W = 0 := by
  classical
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel_zero_fw, ContinuousMultilinearMap.zero_apply]
  rw [deTurckPhiMetTotal, appCc_sub_left, appCc_sub_left, appCc_add_left, appCc_add_left]
  rw [unitModel_sub_local, unitModel_sub_local, unitModel_add_local, unitModel_add_local,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_apply_eq
      (I := I) g₀ g₀ g_bg W x v
  have hTHraw :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_apply_eq
      (I := I) (M := M) g₀ g₀ W x v
  have hRACraw :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeff_appCc_eq_combinedTrace
      (I := I) (M := M) g₀ g₀ W x v
  have hPure :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian
      (I := I) (M := M) g₀ g₀ W x v
  have hTH : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2 (traceHessianCoeff (I := I) (M := M) g₀ g₀) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![v 0, v 1,
            cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k] := by
    rw [hTHraw]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
      (by funext i; fin_cases i <;> rfl)
  have hRAC : unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) W) x v =
      (1 / 2 : ℝ) *
        ((∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 W x
              ![cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                v 0, v 1, (Module.finBasis ℝ E) k]
          + ∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 4 W x
                ![cometricLmodel (I := I) g₀ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)),
                  v 1, v 0, (Module.finBasis ℝ E) k])
        - ∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (cometricLmodel (I := I) g₀ x
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
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          v 1, (Module.finBasis ℝ E) k] =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            v 0, v 1, (Module.finBasis ℝ E) k] :=
    Finset.sum_congr rfl fun k _ => hWsymm x (v 0)
      (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      (v 1) ((Module.finBasis ℝ E) k)
  have hswapB : ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 W x
        ![v 1,
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          v 0, (Module.finBasis ℝ E) k] =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            v 1, v 0, (Module.finBasis ℝ E) k] :=
    Finset.sum_congr rfl fun k _ => hWsymm x (v 1)
      (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      (v 0) ((Module.finBasis ℝ E) k)
  rw [hswapA, hswapB]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
private lemma deTurckPhiMetTotal_realizedFam_eq_lieArm2PrincipalCoeff_sub_twoLichnerowicz
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
          (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        - (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckPhiMetTotal, linearizedRicciArm2FieldLichnerowicz]
  set X : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hX
  set Y : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hY
  have hhalf : (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y = Y := by
    rw [← add_smul]
    norm_num
  have hgrp : (X - (1 / 2 : ℝ) • Y) + (X - (1 / 2 : ℝ) • Y) =
      (X + X) - ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y) := by abel
  rw [hgrp, hhalf]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem jointTotalSpaceRS_sub_fw {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem jointTotalSpaceRS_add_fw {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiMetTotal_realizedFam_jointSmooth
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') := by
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth
      (I := I) g₀ T T' hδ hδ' g_bg
  have hLich := linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add_fw (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLich hLich
  have hsub := jointTotalSpaceRS_sub_fw (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
        (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1
        + (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLie hadd
  refine hsub.congr (fun p _ => ?_)
  beta_reduce
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [deTurckPhiMetTotal_realizedFam_eq_lieArm2PrincipalCoeff_sub_twoLichnerowicz (I := I) (M := M) g₀ g_bg T T' hδ hδ' p.2,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
def deTurckPhiTotPathIntegral (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
    (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
      (realizedFam (I := I) g₀ T T' hδ hδ' s))
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by rw [Set.uIcc_of_le zero_le_one]; exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (deTurckPhiMetTotal_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T T' hδ hδ')

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilin_sub_fw (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w =
      smoothCcTensorBilinForm (I := I) g₀ T x v w - smoothCcTensorBilinForm (I := I) g₀ T' x v w := by
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ (T - T') x v w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x v w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T' x v w,
    unitModel_sub_local, ContinuousMultilinearMap.sub_apply]

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth)

lemma sq_bound_of_sqrt_le_fw {r Λv : ℝ} (hr : 0 ≤ r) (h : Real.sqrt r ≤ Λv) :
    r ≤ Λv ^ 2 := by
  nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma symmS_eq_self_of_symm_fw (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x u w = smoothCcTensorBilinForm (I := I) g₀ S x w u) :
    ccTensor02Symm (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  rw [ccTensor02Symm, hswap, ← two_smul ℝ S, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem threeArmHjoint_neg_two_smul_add_fw (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => (-2 : ℝ) • A s + B s) (δ := δ) (δ' := δ') := by
  have hsmul := lieArm_jointRS_const_smul_local (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (-2 : ℝ)
    (fun p : M × ℝ => (A p.2).toSection p.1) hA
  have hadd := jointTotalSpaceRS_add_fw (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (-2 : ℝ) • (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hsmul hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
lemma deTurckPhiMetTotal_realizedFam_eq_neg_two_smul_fw
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      (-2 : ℝ) • linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
        + deTurckLieArm2PrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg := by
  rw [deTurckPhiMetTotal_realizedFam_eq_lieArm2PrincipalCoeff_sub_twoLichnerowicz (I := I) (M := M) g₀ g_bg T T' hδ hδ' s]
  rw [show (-2 : ℝ) • linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s =
      -(linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
        + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) from by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, neg_smul, two_smul]]
  abel

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem linearizedDeTurckLieAt_eq_threeArm_plain_of_symm_fw
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w = smoothCcTensorBilinForm (I := I) g₀ (T - T') x w v)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → TangentSpace I x) :
    linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  have hSsymmS : ccTensor02Symm (I := I) (M := M) g₀ (T - T') = T - T' :=
    symmS_eq_self_of_symm_fw (I := I) (M := M) g₀ (T - T') hSsymm
  rw [linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) hs]
  rw [(hasDerivAt_realizedDeTurckLieChartSum_general (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) hs).deriv]
  have hcomp : ∀ i j : Fin (Module.finrank ℝ E),
      deriv (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro i j
    rw [deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i j hs]
    have h := lieArm_chartSlope_center_value_eq_threeArm (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' s x i j
    rw [hSsymmS] at h
    exact h
  set Wbase : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      + operatorFieldApply (I := I) (M := M) g₀ 3 2
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      + operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckLieArm2PrincipalCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hWbase
  calc (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
        deriv (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s)
      = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
            deriv (fun s : ℝ =>
              DeTurckCoefficients.chartLieDeTurckComp (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s :=
        Finset.sum_comm
    _ = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
            unitModel (I := I) (M := M) g₀ 2 Wbase x
              ![(chartModelBasis E) i, (chartModelBasis E) j] := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [hcomp i j]
    _ = unitModel (I := I) (M := M) g₀ 2 Wbase x v :=
        unitModel_basis_expand_two (I := I) (M := M) g₀ Wbase x v

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckRHSArmDiff_threeArm_canonicalTop_coeffC0_jetL2_ballUniform_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        (_hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2
                (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨ΛCr, hΛCr_nn, hC0r⟩ :=
    uniform_C0_bound_concrete_lichnerowicz_coeffFields (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Br, hBr_nn, hJr⟩ :=
    linearizedRicciArm_concreteField_jetL2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨ΛL0, hΛL0_nn, hL0r⟩ :=
    deTurckLieCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨ΛLc, hΛLc_nn, hLcr⟩ :=
    lieCorr0Field_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨ΛL1, hΛL1_nn, hL1r⟩ :=
    deTurckLieArm1Coeff_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨P0, hP0_nn, hP0j⟩ :=
    deTurckLieCoeffField_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨PL, hPL_nn, hPLj⟩ :=
    lieCorr0Field_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨P1, hP1_nn, hP1j⟩ :=
    deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨max (Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc)) (Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1)),
    max (Real.sqrt (8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)))
      (Real.sqrt (8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i)),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') x v w = smoothCcTensorBilinForm (I := I) g₀ (T - T') x w v := by
    intro x v w
    rw [ccTensorBilin_sub_fw (I := I) (M := M) g₀ T T' x v w,
      ccTensorBilin_sub_fw (I := I) (M := M) g₀ T T' x w v, hTsymm x v w, hT'symm x v w]
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set Ψ₀ : ℝ → SmoothCcTensor g₀ 2 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s
      + (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        + lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) with hΨ₀def
  set Ψ₁ : ℝ → SmoothCcTensor g₀ 3 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s
      + deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg with hΨ₁def
  set Ψ₂ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
      (realizedFam (I := I) g₀ T T' hδ hδ' s) with hΨ₂def
  have hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Ψ₀ (δ := δ) (δ' := δ') := by
    rw [hΨ₀def]
    exact threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 2 _ _
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ')
      (deTurckLieCoeffField_add_deTurckLieRemainderField_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)
  have hj1 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Ψ₁ (δ := δ) (δ' := δ') := by
    rw [hΨ₁def]
    exact threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 3 _ _
      (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ')
      (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)
  have hj2 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Ψ₂ (δ := δ) (δ' := δ') := by
    rw [hΨ₂def]
    exact deTurckPhiMetTotal_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hc0 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₀ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Ψ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hj0 x
  have hc1 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₁ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Ψ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hj1 x
  have hc2 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₂ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Ψ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hj2 x
  set C₀ : SmoothCcTensor g₀ 2 2 := pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Ψ₀
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 with hC₀def
  set C₁ : SmoothCcTensor g₀ 3 2 := pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 with hC₁def
  have hPitop : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
      (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Ψ₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 := rfl
  refine ⟨C₀, C₁, ?_, ?_, ?_, ?_, ?_⟩
  · apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    rw [hPitop]
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
    set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'
    rw [unitModel_sub_local (I := I) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply]
    rw [show (unitModel (I := I) (M := M) g₀ 2
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ) x) v =
        deTurckRicciRHS (I := I) g_bg g₁ x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ
        (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ) rfl x v]
    rw [show (unitModel (I := I) (M := M) g₀ 2
          (deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x) v =
        deTurckRicciRHS (I := I) g_bg g₁' x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') rfl x v]
    have hsplit : ∀ (g : SmoothRiemannianMetric I M),
        deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) =
          ((-2 : ℝ) • ricciTensor (I := I) g x (v 0) (v 1)) +
            lieDerivMetricClm (I := I) g
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) := by
      intro g
      rw [deTurckRicciRHS, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
      rfl
    rw [hsplit g₁, hsplit g₁']
    rw [show ((-2 : ℝ) • ricciTensor (I := I) g₁ x (v 0) (v 1) +
            lieDerivMetricClm (I := I) g₁
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) -
          ((-2 : ℝ) • ricciTensor (I := I) g₁' x (v 0) (v 1) +
            lieDerivMetricClm (I := I) g₁'
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) =
        ((-2 : ℝ) • (ricciTensor (I := I) g₁ x (v 0) (v 1) -
            ricciTensor (I := I) g₁' x (v 0) (v 1))) +
          (lieDerivMetricClm (I := I) g₁
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
            lieDerivMetricClm (I := I) g₁'
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) from by
      simp only [smul_sub]; ring]
    rw [hg₁, hg₁']
    rw [ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)]
    rw [lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)]
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add
      ((DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt_intervalIntegrable
        (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)).const_mul (-2 : ℝ))
      (linearizedDeTurckLieAt_intervalIntegrable (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1))]
    have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
        (-2 : ℝ) * linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s
          + linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
      rw [MeasureTheory.ae_iff]
      have hnull : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
      refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
      rw [Set.mem_setOf_eq, Classical.not_imp] at hs
      obtain ⟨hsmem, hsneq⟩ := hs
      rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
      rw [Set.mem_singleton_iff]
      by_contra hne
      have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
      refine hsneq ?_
      have hRid : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2
                (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 3 2
                (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 4 2
                (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        obtain ⟨_, _, _, hident, _, _⟩ :=
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
            (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
        exact hident hTsymm hT'symm s hsIoo x v hδ_lt hδ'_lt
      have hLid := linearizedDeTurckLieAt_eq_threeArm_plain_of_symm_fw (I := I) (M := M)
        g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' hSsymm hsIoo x v
      have hRid' : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        rw [hRid, unitModel_add2_apply_tame, unitModel_add2_apply_tame]
      have hLid' : linearizedDeTurckLieAt (I := I) g₀ g_bg T T'
            hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                + lieCorr0Field (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        rw [hLid, unitModel_add2_apply_tame, unitModel_add2_apply_tame]
      have e0 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                + lieCorr0Field (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v := by
        simp only [hΨ₀def]
        rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
      have e1 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v := by
        simp only [hΨ₁def]
        rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
      have e2 : unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        simp only [hΨ₂def]
        rw [deTurckPhiMetTotal_realizedFam_eq_neg_two_smul_fw (I := I) (M := M)
          g₀ g_bg T T' hδ hδ' s]
        rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
      rw [hRid', hLid', e0, e1, e2]
      ring
    rw [intervalIntegral.integral_congr_ae hintegrand]
    have hI0 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 2 Ψ₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) hSI hc0 x v
    have hI1 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 3 Ψ₁
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) hSI hc1 x v
    have hI2 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 4 Ψ₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) hSI hc2 x v
    rw [intervalIntegral.integral_add (hI0.add hI1) hI2, intervalIntegral.integral_add hI0 hI1]
    have he0 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Ψ₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0 x v
    have he1 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 3 2 Ψ₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1 x v
    have he2 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 Ψ₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2 x v
    rw [← hC₀def] at he0
    rw [← hC₁def] at he1
    rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame, he0, he1, he2]
  · intro x
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Ψ₀ t).toSection x)) ≤
          Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc) := by
      intro t ht
      refine Real.sqrt_le_sqrt ?_
      simp only [hΨ₀def]
      have hadd := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
        ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t)
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) := by
        rw [show (((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
            (-2 : ℝ) • ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hR := sq_bound_of_sqrt_le_fw
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _)
        ((hC0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x).1)
      have haddL := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg)
        (lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hL0 := hL0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      have hLc := hLcr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      linarith
    have htrans := riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 2 2 Ψ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 x
      (Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc)) (Real.sqrt_nonneg _)
      ((hc0 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)) hsup
    rw [← hC₀def] at htrans
    refine le_trans htrans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2)
  · intro x
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Ψ₁ t).toSection x)) ≤
          Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1) := by
      intro t ht
      refine Real.sqrt_le_sqrt ?_
      simp only [hΨ₁def]
      have hadd := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 3 2
        ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t)
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          (((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) := by
        rw [show (((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
            (-2 : ℝ) • ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hR := sq_bound_of_sqrt_le_fw
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 2 x _)
        ((hC0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x).2.1)
      have hL1 := hL1r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      linarith
    have htrans := riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 3 2 Ψ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 x
      (Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1)) (Real.sqrt_nonneg _)
      ((hc1 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)) hsup
    rw [← hC₁def] at htrans
    refine le_trans htrans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2)
  · have hnn : (0 : ℝ) ≤ 8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i) := by
      have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i) :=
        Finset.sum_nonneg fun i _ => by
          have := hP0_nn i; have := hPL_nn i; linarith
      nlinarith [sq_nonneg Br]
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Ψ₀ s)‖ ^ 2) ≤
          Real.sqrt (8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hnn]
      simp only [hΨ₀def]
      have htow := jetTowerSum_add_le (I := I) g₀ 2 2 (a + 1)
        ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hsc : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) =
          4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [iteratedCovGrad_smul', norm_smul]
        rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
        ring
      have hRj := (hJr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball).1 s hs
      have htowL := jetTowerSum_add_le (I := I) g₀ 2 2 (a + 1)
        (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hLsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), P0 i :=
        Finset.sum_le_sum fun i hi =>
          hP0j T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      have hcsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), PL i :=
        Finset.sum_le_sum fun i hi =>
          hPLj T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      have hexpand : (∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)) =
          4 * (∑ i ∈ Finset.range (a + 1), P0 i) + 4 * (∑ i ∈ Finset.range (a + 1), PL i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      linarith
    have htower := pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 2 a Ψ₀ hSI hSopen hj0
      (Real.sqrt_nonneg _) hjet
    rw [← hC₀def] at htower
    refine le_trans htower (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2)
  · have hnn : (0 : ℝ) ≤ 8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i := by
      have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (a + 1), P1 i :=
        Finset.sum_nonneg fun i _ => hP1_nn i
      nlinarith [sq_nonneg Br]
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Ψ₁ s)‖ ^ 2) ≤
          Real.sqrt (8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hnn]
      simp only [hΨ₁def]
      have htow := jetTowerSum_add_le (I := I) g₀ 3 2 (a + 1)
        ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hsc : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
          ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) =
          4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [iteratedCovGrad_smul', norm_smul]
        rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
        ring
      have hRj := (hJr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball).2.1 s hs
      have hLsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), P1 i :=
        Finset.sum_le_sum fun i hi =>
          hP1j T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      linarith
    have htower := pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 3 a Ψ₁ hSI hSopen hj1
      (Real.sqrt_nonneg _) hjet
    rw [← hC₁def] at htower
    refine le_trans htower (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_iteratedCovGradTwo_gradSlotAntisym_curvatureCoeff
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : SmoothCcTensor g₀ 2 4,
      ∀ S : SmoothCcTensor g₀ 0 2,
        iteratedCovGrad (I := I) g₀ 0 2 2 S
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection (I := I)
                g₀ (Equiv.swap (0 : Fin 4) 1) (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 C S := by
  classical
  refine ⟨⟨⟨fun y : M =>
      (show Tensor0SBundle.TensorRSSpace 2 4 I y from
        TensorRSSpace.ofCLM (curvatureOperatorOnTensorFib (I := I) (M := M) g₀ 2 y)),
      slotFreeCurvOpFib_contMDiff (I := I) (M := M) g₀ 2⟩,
    HasCompactSupport.of_compactSpace _⟩, ?_⟩
  intro S
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel_sub_local (I := I) g₀ 4 _ _ x, ContinuousMultilinearMap.sub_apply,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel (I := I)
      g₀ (Equiv.swap (0 : Fin 4) 1) (iteratedCovGrad (I := I) g₀ 0 2 2 S) x,
    ContinuousMultilinearMap.domDomCongr_apply]
  set Xs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 0), smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩
    with hXs_def
  set Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 1), smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩
    with hYs_def
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
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m := by
    conv_lhs => rw [hv_eq]
    rw [unitModel]
    exact tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M) g₀ 2 S
      Xs.contMDiff Ys.contMDiff x m
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m := by
    rw [hv_swap]
    rw [unitModel]
    exact tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M) g₀ 2 S
      Ys.contMDiff Xs.contMDiff x m
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
      (fun b => unitZeroSec (I := I) (M := M) b) (contMDiff_unitZeroSection (I := I) (M := M)) x
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
    rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g₀) Xs.contMDiff Ys.contMDiff
      (smoothExtensionTangent_contMDiff (I := I) x u)]
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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem appCc_appCcRS_assoc_fw (g₀ : SmoothRiemannianMetric I M)
    (Φ : SmoothCcTensor g₀ 4 2) (C : SmoothCcTensor g₀ 2 4) (S : SmoothCcTensor g₀ 0 2) :
    operatorFieldApply (I := I) (M := M) g₀ 4 2 Φ (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 C S) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φ C) S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, appCc_toSection, appCcRS_toSection, appCcRS_toSection,
    ContinuousLinearMap.comp_assoc]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem appCc_smul_left_fw (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (c : ℝ)
    (Φ : SmoothCcTensor g₀ r s) (W : SmoothCcTensor g₀ 0 r) :
    operatorFieldApply (I := I) (M := M) g₀ r s (c • Φ) W = c • operatorFieldApply (I := I) (M := M) g₀ r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g₀ r s Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g₀ r s Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : Tensor0SBundle.TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_deTurckPhiMetTotal_background_curvatureFold_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ K₀ : SmoothCcTensor g₀ 2 2,
      ∀ (S : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ S x v w = smoothCcTensorBilinForm (I := I) g₀ S x w v) →
        operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                  (I := I) (M := M) g₀ g₀)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          operatorFieldApply (I := I) (M := M) g₀ 2 2 K₀ (iteratedCovGrad (I := I) g₀ 0 2 0 S) := by
  classical
  obtain ⟨C24, hC24⟩ :=
    exists_iteratedCovGradTwo_gradSlotAntisym_curvatureCoeff (I := I) (M := M) g₀
  refine ⟨(1/2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀) C24, ?_⟩
  intro S hSsymm
  set Φd : SmoothCcTensor g₀ 4 2 :=
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀ with hΦd_def
  set W : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 S with hW_def
  set Wsw : SmoothCcTensor g₀ 0 4 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 1) W with hWsw_def
  have hsplit : W = (1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw) := by
    have h : (1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw) =
        ((1/2 : ℝ) + (1/2 : ℝ)) • W + ((1/2 : ℝ) - (1/2 : ℝ)) • Wsw := by
      rw [smul_add, smul_sub, add_smul, sub_smul]
      abel
    rw [h]
    norm_num
  have hsym : ∀ (x : M) (u₀ u₁ u₂ u₃ : TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 4 (W + Wsw) x ![u₀, u₁, u₂, u₃] =
        unitModel (I := I) (M := M) g₀ 4 (W + Wsw) x ![u₁, u₀, u₂, u₃] := by
    intro x u₀ u₁ u₂ u₃
    have hv : ∀ a b : TangentSpace I x,
        (fun i => (![a, b, u₂, u₃] : Fin 4 → TangentSpace I x) ((Equiv.swap (0 : Fin 4) 1) i)) =
          ![b, a, u₂, u₃] := by
      intro a b
      funext i
      fin_cases i <;> rfl
    rw [unitModel_add_local (I := I) (M := M) g₀ 4 W Wsw x,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
      hWsw_def,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel
        (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) W x,
      ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
      hv u₀ u₁, hv u₁ u₀]
    exact add_comm _ _
  have hkill : operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W + Wsw)) = 0 := by
    rw [appCc_smul_right, hΦd_def,
      deTurckPhiMetTotal_background_appCc_eq_zero_of_slot01Symm (I := I) (M := M) g₀ g_bg
        (W + Wsw) hsym, smul_zero]
  calc operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd W
      = operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
          ((1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw)) := by rw [← hsplit]
    _ = operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W + Wsw))
        + operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W - Wsw)) :=
      appCc_add_right (I := I) (M := M) g₀ 4 2 Φd _ _
    _ = operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W - Wsw)) := by
      rw [hkill, zero_add]
    _ = (1/2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd (W - Wsw) :=
      appCc_smul_right (I := I) (M := M) g₀ 4 2 (1/2 : ℝ) Φd _
    _ = (1/2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 4 2 Φd
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 C24 S) := by
      rw [hW_def, hWsw_def, hW_def, hC24 S]
    _ = (1/2 : ℝ) • operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φd C24) S := by
      rw [appCc_appCcRS_assoc_fw (I := I) (M := M) g₀ Φd C24 S]
    _ = operatorFieldApply (I := I) (M := M) g₀ 2 2
        ((1/2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φd C24) S := by
      rw [appCc_smul_left_fw (I := I) (M := M) g₀ 2 2 (1/2 : ℝ) _ S]
    _ = operatorFieldApply (I := I) (M := M) g₀ 2 2
        ((1/2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 Φd C24)
        (iteratedCovGrad (I := I) g₀ 0 2 0 S) := by
      rw [iteratedCovGrad_zero]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem traceHessianSlotPerm_inv_mul_apply_eq (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    traceHessianSlotPerm ((traceHessianSlotPerm⁻¹ * σ) j) = σ j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem lieTrace_eq_reindex_fw (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ ρ : Equiv.Perm (Fin 4))
    (hcomp : ∀ j : Fin 4, traceHessianSlotPerm (ρ j) = σ j) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection, traceHessianCoeff_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibPerm_apply, domDomCongrFib_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have harg : ContinuousMultilinearMap.domDomCongr σ
      (Tensor0SBundle.Tensor0SSpace.toModel D) =
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg _ (funext fun j => ?_)
    rw [hcomp j]
  rw [harg]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem reindexCoeffGen_sub_fw (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) :
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2 A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ 4 2 B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, ContinuousLinearMap.sub_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normSq_icg_sub_le_fw (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q (A - B)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g r s q A‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g r s q B‖ ^ 2 := by
  have htri : ‖iteratedCovGrad (I := I) g r s q (A - B)‖ ≤
      ‖iteratedCovGrad (I := I) g r s q A‖ + ‖iteratedCovGrad (I := I) g r s q B‖ := by
    rw [iteratedCovGrad_sub]
    exact norm_sub_le _ _
  nlinarith [htri, norm_nonneg (iteratedCovGrad (I := I) g r s q (A - B)),
    norm_nonneg (iteratedCovGrad (I := I) g r s q A),
    norm_nonneg (iteratedCovGrad (I := I) g r s q B),
    sq_nonneg (‖iteratedCovGrad (I := I) g r s q A‖ - ‖iteratedCovGrad (I := I) g r s q B‖)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_toSection_sub_le_fw (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((A - B).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x (B.toSection x) := by
  rw [show (A - B).toSection x = A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  exact riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x _ _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem normSq_icg_reindex_eq_fw (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i R‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral (I := I) (M := M) g₀ 4 (2 + i),
    lc0b_normSq_eq_integral (I := I) (M := M) g₀ 4 (2 + i)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2 R ρ i x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem gFibreOpBound_mono_fw (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ')
    (hb : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀ h δ' := by
  intro y a b
  refine le_trans (hb y a b) ?_
  have hnn : 0 ≤ Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc δ * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)
      = δ * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) := by ring
    _ ≤ δ' * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) :=
        mul_le_mul_of_nonneg_right hle hnn
    _ = δ' * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem gFibreOpBound_min_fw (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ₁ δ₂ : ℝ} (h₁ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ₁)
    (h₂ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ₂) :
    metricCauchySchwarzBound (I := I) (M := M) g₀ h (min δ₁ δ₂) := by
  intro x v w
  rcases le_total δ₁ δ₂ with hle | hle
  · rw [min_eq_left hle]
    exact h₁ x v w
  · rw [min_eq_right hle]
    exact h₂ x v w

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
theorem deTurckPhiMetTotal_eq_reindex_decomp_fw
    (g₀ g_bg g : SmoothRiemannianMetric I M) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
        - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g
            + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g) := by
  have hPhi : deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g =
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermA
        + deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermAT
        - traceHessianCoeff (I := I) (M := M) g₀ g)
      + traceHessianCoeff (I := I) (M := M) g₀ g
      - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g
          + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g) := rfl
  rw [hPhi,
    lieTrace_eq_reindex_fw (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermA
      (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
      (traceHessianSlotPerm_inv_mul_apply_eq deTurckLieArm2DivSlotPermA),
    lieTrace_eq_reindex_fw (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermAT
      (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
      (traceHessianSlotPerm_inv_mul_apply_eq deTurckLieArm2DivSlotPermAT)]
  abel

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
