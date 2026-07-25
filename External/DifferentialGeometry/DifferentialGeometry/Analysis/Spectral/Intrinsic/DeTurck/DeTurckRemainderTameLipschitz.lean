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
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzPhiMetTotalCurvatureFold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmOneAllOrderTameEnvelope
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzKernelRefoldTopSeparatedBounds


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open LieCorr0Core
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem)

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A - B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x -
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A - B) x) = A x - B x from by rw [ContMDiffSection.coe_sub]; rfl]
  rw [slotInsertEndoFib_sub_left, ContinuousLinearMap.sub_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma rsDomDomCongrSection_sub (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 2)) (X Y : SmoothCcTensor g₀ 2 2) :
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ (X - Y) =
      rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ X -
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hsub : ((X - Y).toSection x) = X.toSection x - Y.toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  have hsub2 : ((rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ X -
      rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ Y).toSection x) =
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ X).toSection x -
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ Y).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [rsDomDomCongrSection_toSection, hsub, hsub2]
  rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
  have hfib : ∀ (y : Tensor0SSpace 2 I x) (w : Fin 2 → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace 2 I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x - Y.toSection x) D m]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      tensorRS_domDomCongr σ (X.toSection x) - tensorRS_domDomCongr σ (Y.toSection x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (Y.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (X.toSection x - Y.toSection x : TensorRSSpace 2 2 I x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from X.toSection x) D -
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Y.toSection x) D from rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (Y.toSection x)) D : Tensor0SSpace 2 I x) m =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (X.toSection x)) D : Tensor0SSpace 2 I x) m -
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (Y.toSection x)) D : Tensor0SSpace 2 I x) m from rfl]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x) D m]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (Y.toSection x) D m]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma reindexCoeffGen_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 2 2) (ρ : Equiv.Perm (Fin 2)) :
    reindexCoeffGen (I := I) (M := M) g₀ 2 2 (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2 A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ 2 2 B ρ := by
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
private lemma lc0w_NEndoIns_diff_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
          lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀) =
      lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg := by
  rw [slotInsertEndoCc_sub (I := I) (M := M) g₀ 0,
    lc0b_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g_bg,
    lc0b_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g₀]
  abel

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0w_insertField_sub (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lc0InsertField (I := I) (M := M) g₀ g₁ g_bg -
        lc0InsertField (I := I) (M := M) g₀ g₁ g₀ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
            lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
                  lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1) := by
  rw [slotInsertEndoCc_sub (I := I) (M := M) g₀ 1,
    rsDomDomCongrSection_sub (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1),
    reindexCoeffGen_sub (I := I) (M := M) g₀]
  rw [show lc0InsertField (I := I) (M := M) g₀ g₁ g_bg =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1) from rfl]
  rw [show lc0InsertField (I := I) (M := M) g₀ g₁ g₀ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1) from rfl]
  abel

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieEndoArmField
  deTurckLieDLbFib deTurckLieDLbFib_toModel deTurckLieWEndo) in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lc0w_insertField_add_endoArmBase (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lc0InsertField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ =
      lc0InsertField (I := I) (M := M) g₀ g₁ g_bg -
        lc0InsertField (I := I) (M := M) g₀ g₁ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have hL : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀).toSection x)) D) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) +
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀).toSection x) D) := rfl
  have hR : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg -
        lc0InsertField (I := I) (M := M) g₀ g₁ g₀).toSection x)) D) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) -
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0InsertField (I := I) (M := M) g₀ g₁ g₀).toSection x) D) := rfl
  rw [hL, hR, Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply]
  rw [lc0b_insert_fiber (I := I) (M := M) g₀ g₁ g_bg x D m,
    lc0b_insert_fiber (I := I) (M := M) g₀ g₁ g₀ x D m]
  rw [lieCorr0InsertFib_toModel (I := I) g₀ g₁ g_bg x D m,
    lieCorr0InsertFib_toModel (I := I) g₀ g₁ g₀ x D m]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀).toSection x) D) =
      deTurckLieDLbFib (I := I) g₁ g₀ x D from rfl]
  rw [deTurckLieDLbFib_toModel (I := I) g₁ g₀ x D m]
  have hN0 : ∀ v : TangentSpace I x,
      lieCorr0NEndo (I := I) g₀ g₁ g₀ x v = -(deTurckLieWEndo (I := I) g₁ g₀ x v) := by
    intro v
    rw [show lieCorr0NEndo (I := I) g₀ g₁ g₀ x =
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)
          - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)
          - deTurckLieWEndo (I := I) g₁ g₀ x from rfl]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, sub_self, zero_sub]
  have e0 : Tensor0SSpace.toModel D
      (Function.update m 0 (lieCorr0NEndo (I := I) g₀ g₁ g₀ x (m 0))) =
      -(Tensor0SSpace.toModel D
        (Function.update m 0 (deTurckLieWEndo (I := I) g₁ g₀ x (m 0)))) := by
    rw [hN0 (m 0), show (-(deTurckLieWEndo (I := I) g₁ g₀ x (m 0))) =
        ((-1 : ℝ) • (deTurckLieWEndo (I := I) g₁ g₀ x (m 0))) from (neg_one_smul ℝ _).symm]
    rw [ContinuousMultilinearMap.map_update_smul]
    rw [neg_one_smul]
  have e1 : Tensor0SSpace.toModel D
      (Function.update m 1 (lieCorr0NEndo (I := I) g₀ g₁ g₀ x (m 1))) =
      -(Tensor0SSpace.toModel D
        (Function.update m 1 (deTurckLieWEndo (I := I) g₁ g₀ x (m 1)))) := by
    rw [hN0 (m 1), show (-(deTurckLieWEndo (I := I) g₁ g₀ x (m 1))) =
        ((-1 : ℝ) • (deTurckLieWEndo (I := I) g₁ g₀ x (m 1))) from (neg_one_smul ℝ _).symm]
    rw [ContinuousMultilinearMap.map_update_smul]
    rw [neg_one_smul]
  rw [e0, e1]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieEndoArmField) in

private theorem lc0w_lieCorr0_add_endoArmBase_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
            lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
                  lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1)
        + lc0VBField (I := I) (M := M) g₀ g₁
        + lc0AMixField (I := I) (M := M) g₀ g₁ g_bg
        + lc0RiemField (I := I) (M := M) g₀ g₁ := by
  have h1 := lc0b_total_decomp (I := I) (M := M) g₀ g₁ g_bg
  have h5 := lc0w_insertField_sub (I := I) (M := M) g₀ g₁ g_bg
  have h6 := lc0w_insertField_add_endoArmBase (I := I) (M := M) g₀ g₁ g_bg
  rw [h1, ← h5]
  rw [show lc0InsertField (I := I) (M := M) g₀ g₁ g_bg -
      lc0InsertField (I := I) (M := M) g₀ g₁ g₀ =
      lc0InsertField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ from h6.symm]
  abel

omit [BoundarylessManifold I M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private lemma one_le_l2JetWindow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (i : ℕ) :
    (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
  have h : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

omit [BoundarylessManifold I M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private lemma l2JetWindow_mono (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {q i : ℕ} (h : q ≤ i) :
    1 + ∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
      1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (pAO_range_subset (show q + 2 ≤ i + 2 by omega))
    (fun (j : ℕ) _ _ => sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖)
  linarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem appCcRS_l2JetWindow_le (g₀ : SmoothRiemannianMetric I M)
    (p a b : ℕ) (i : ℕ) (WinVal : ℝ) (_hWin1 : 1 ≤ WinVal)
    (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    (C2 : ℕ → ℝ) (hC2_nn : ∀ k, 0 ≤ C2 k)
    (htwo : ∀ k : ℕ,
      ∀ (S : SmoothCcTensor g₀ a b) (T : SmoothCcTensor g₀ p a)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
                  ((iteratedCovGrad (I := I) g₀ a b n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                      ((iteratedCovGrad (I := I) g₀ p a l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
                  ((iteratedCovGrad (I := I) g₀ a b n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                      ((iteratedCovGrad (I := I) g₀ p a l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2 k * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ a b n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ p a l T‖ ^ 2))
    (ΛΦ ΛW : ℝ) (KΦ KW : ℕ → ℝ) (hΛΦ : 0 ≤ ΛΦ) (hΛW : 0 ≤ ΛW)
    (hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) ≤ ΛΦ)
    (hW0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (W.toSection x) ≤ ΛW)
    (hKΦ : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ a b q' Φ‖ ^ 2 ≤ KΦ q * WinVal)
    (hKW : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ p a q' W‖ ^ 2 ≤ KW q * WinVal) :
    ∑ q ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ p b q (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W)‖ ^ 2 ≤
    (∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (ΛW * KΦ q + ΛΦ * KW q))) * WinVal := by
  obtain ⟨-, hL2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ p a b i Φ W C2 hC2_nn htwo
    ΛΦ ΛW (fun q => KΦ q * WinVal) (fun q => KW q * WinVal) hΛΦ hΛW hΦ0 hW0 hKΦ hKW
  refine le_trans (hL2 i le_rfl) (le_of_eq ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem exists_connDiffSection_coeffJetEnvelope (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((connDiffSection (I := I) g₁ g₀).toSection x) ≤ Λ) ∧
        (∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
  classical
  obtain ⟨Λ, F, hΛ_nn, hF_nn, hfeed⟩ :=
    lc0b_cds_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fw, hFw_nn, hFw⟩ :=
    pAO_connDiffSection_jetL2_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨Λ, fun i => ∑ q ∈ Finset.range (i + 1), Fw q, hΛ_nn,
    fun i => Finset.sum_nonneg fun q _ => hFw_nn q, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  refine ⟨(hfeed g₁ P htie hδ_le hδ0 hδ hPball).1, ?_⟩
  intro i
  have hterm : ∀ q ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
      Fw q * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro q hq
    refine le_trans (hFw g₁ P htie hδ_le hδ0 hδ hPball q) ?_
    exact mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P (by have := Finset.mem_range.mp hq; omega))
      (hFw_nn q)
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [Finset.sum_mul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem exists_perturbedMetricLoweredConnDiff_coeffJetEnvelope (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
  classical
  obtain ⟨Λ, F, hΛ_nn, hF_nn, hfeed⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨Fw, hFw_nn, hFw⟩ :=
    pAO_kappa_jetSum_tame (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  refine ⟨Λ, Fw, hΛ_nn, hFw_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  exact ⟨(hfeed g₁ P htie hδ_le hδ0 hδ hPball).1,
    fun i => hFw g₁ P htie hδ_le hδ0 hδ hPball i⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (sharpFlatEndoCc) in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceField) in
private theorem exists_pureDoubleTraceCoeff_coeffJetEnvelope (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) s x
            ((lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) ≤ Λ) ∧
        (∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ (s + 2) s q
              (lc0PureDT (I := I) (M := M) g₀ g₁ s)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
  classical
  obtain ⟨Λdt, Fdt, hΛdt_nn, hFdt_nn, hdt⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ s a ha_super hR hδ₀
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lc0b_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fsfw, hFsfw_nn, hsfw⟩ :=
    pAO_sharpFlat_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨c0, hc0_nn, hc0⟩ := lc0b_fixedField_rfns_jet (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ (s + 2) (s + 2) s (s + 2)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfrpow_nn : (0 : ℝ) ≤ fr ^ (s + 1) := by positivity
  set FcDT : ℕ → ℝ := fun q => ∑ q' ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ (s + 2) s q'
      (cometricDoubleTraceField (I := I) g₀ s)‖ ^ 2 with hFcDT_def
  have hFcDT_nn : ∀ q, 0 ≤ FcDT q := fun q => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨Λdt, fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * ((fr ^ (s + 1) * Λsf) * FcDT q +
        (c0 0) * (fr ^ (s + 1) * Fsfw q))),
    hΛdt_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg
        (mul_nonneg (mul_nonneg hfrpow_nn hΛsf_nn) (hFcDT_nn q))
        (mul_nonneg (hc0_nn 0) (mul_nonneg hfrpow_nn (hFsfw_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  refine ⟨(hdt g₁ P htie hδ_le hδ0 hδ hPball).1, ?_⟩
  intro i
  set Win : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWin_def
  have hWin1 : (1 : ℝ) ≤ Win := one_le_l2JetWindow (I := I) (M := M) g₀ P i
  have hWin0 : (0 : ℝ) ≤ Win := le_trans zero_le_one hWin1
  obtain ⟨hsfsup, -⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hsfw' := hsfw g₁ P htie hδ_le hδ0 hδ hPball
  set Wf : SmoothCcTensor g₀ (s + 2) (s + 2) :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) with hWf_def
  have hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) s x
      ((cometricDoubleTraceField (I := I) g₀ s).toSection x) ≤ c0 0 := by
    intro x
    have h := hc0 0 x
    simpa only [iteratedCovGrad_zero] using h
  have hFΦ : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (s + 2) s q'
          (cometricDoubleTraceField (I := I) g₀ s)‖ ^ 2 ≤ FcDT q * Win :=
    fun q _ => le_mul_of_one_le_right (hFcDT_nn q) hWin1
  have hWpt0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x
      (Wf.toSection x) ≤ fr ^ (s + 1) * Λsf := by
    intro x
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) 0 x
    simp only [iteratedCovGrad_zero] at h
    rw [← lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁] at h
    rw [← hfr_def] at h
    exact le_trans h (mul_le_mul_of_nonneg_left (hsfsup x) hfrpow_nn)
  have hKW : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) q' Wf‖ ^ 2 ≤
      (fr ^ (s + 1) * Fsfw q) * Win := by
    intro q hq
    have hterm : ∀ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l Wf‖ ^ 2 ≤
        fr ^ (s + 1) *
          ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 := by
      intro l _
      refine lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀
        (s + 2) ((s + 2) + l) 1 (1 + l)
        (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l Wf)
        (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁))
        (fr ^ (s + 1)) hfrpow_nn ?_
      intro x
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁) l x
      rw [← lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁] at h
      rw [← hfr_def] at h
      exact h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have h1 : fr ^ (s + 1) * (∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 q' (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2) ≤
        fr ^ (s + 1) * (Fsfw q * (1 + ∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (hsfw' q) hfrpow_nn
    refine le_trans h1 ?_
    have h2 : Fsfw q * (1 + ∑ j ∈ Finset.range (q + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ Fsfw q * Win :=
      mul_le_mul_of_nonneg_left (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hFsfw_nn q)
    refine le_trans (mul_le_mul_of_nonneg_left h2 hfrpow_nn) (le_of_eq (by ring))
  rw [show lc0PureDT (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s) Wf from
    lc0PureDT_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  exact appCcRS_l2JetWindow_le (I := I) (M := M) g₀ (s + 2) (s + 2) s i Win hWin1
    (cometricDoubleTraceField (I := I) g₀ s) Wf C2 hC2_nn hC2
    (c0 0) (fr ^ (s + 1) * Λsf) FcDT (fun q => fr ^ (s + 1) * Fsfw q)
    (hc0_nn 0) (mul_nonneg hfrpow_nn hΛsf_nn) hΦ0 hWpt0 hFΦ hKW

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_deTurckVectorFieldFlat_coeffJetEnvelope (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x
            ((lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 1 q
              (lc0VFlat (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
  classical
  obtain ⟨Λvf, Fvf, hΛvf_nn, hFvf_nn, hvf⟩ :=
    lc0b_vflat_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨Λdt, Kdt, hΛdt_nn, hKdt_nn, hdt⟩ :=
    exists_pureDoubleTraceCoeff_coeffJetEnvelope (I := I) (M := M) g₀ 1 a ha_super hR hδ₀
  obtain ⟨Λκ, Kκ, hΛκ_nn, hKκ_nn, hκ⟩ :=
    exists_perturbedMetricLoweredConnDiff_coeffJetEnvelope (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 0 1 3
  refine ⟨Λvf, fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λκ * Kdt q + Λdt * Kκ q)),
    hΛvf_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛκ_nn (hKdt_nn q))
        (mul_nonneg hΛdt_nn (hKκ_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  refine ⟨(hvf g₁ P htie hδ_le hδ0 hδ hPball).1, ?_⟩
  intro i
  set Win : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWin_def
  have hWin1 : (1 : ℝ) ≤ Win := one_le_l2JetWindow (I := I) (M := M) g₀ P i
  obtain ⟨hdt0, hdtK⟩ := hdt g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ0, hκK⟩ := hκ g₁ P htie hδ_le hδ0 hδ hPball
  have hKΦ : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 1 q'
          (lc0PureDT (I := I) (M := M) g₀ g₁ 1)‖ ^ 2 ≤ Kdt q * Win :=
    fun q hq => le_trans (hdtK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKdt_nn q))
  have hKW : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q'
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ Kκ q * Win :=
    fun q hq => le_trans (hκK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKκ_nn q))
  exact appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 0 3 1 i Win hWin1
    (lc0PureDT (I := I) (M := M) g₀ g₁ 1) (lc0Kappa (I := I) (M := M) g₀ g₁ gB)
    C2 hC2_nn hC2 Λdt Λκ Kdt Kκ hΛdt_nn hΛκ_nn
    (hdt0) (hκ0) hKΦ hKW

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_deTurckVectorFieldInteriorProduct_coeffJetEnvelope (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 1 x
            ((lc0IVField (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 1 q
              (lc0IVField (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
  classical
  obtain ⟨Λiv, Fiv, hΛiv_nn, hFiv_nn, hiv⟩ :=
    lc0b_iVField_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨Λdt, Kdt, hΛdt_nn, hKdt_nn, hdt⟩ :=
    exists_pureDoubleTraceCoeff_coeffJetEnvelope (I := I) (M := M) g₀ 1 a ha_super hR hδ₀
  obtain ⟨Λvf, Kvf, hΛvf_nn, hKvf_nn, hvf⟩ :=
    exists_deTurckVectorFieldFlat_coeffJetEnvelope (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 2 1 3
  set fr2 : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 with hfr2_def
  have hfr2_nn : (0 : ℝ) ≤ fr2 := by positivity
  refine ⟨Λiv, fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * ((fr2 * Λvf) * Kdt q + Λdt * (fr2 * Kvf q))),
    hΛiv_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg
        (mul_nonneg (mul_nonneg hfr2_nn hΛvf_nn) (hKdt_nn q))
        (mul_nonneg hΛdt_nn (mul_nonneg hfr2_nn (hKvf_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  refine ⟨(hiv g₁ P htie hδ_le hδ0 hδ hPball).1, ?_⟩
  intro i
  set Win : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWin_def
  have hWin1 : (1 : ℝ) ≤ Win := one_le_l2JetWindow (I := I) (M := M) g₀ P i
  obtain ⟨hdt0, hdtK⟩ := hdt g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hvf0, hvfK⟩ := hvf g₁ P htie hδ_le hδ0 hδ hPball
  have hdtWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 1 q'
          (lc0PureDT (I := I) (M := M) g₀ g₁ 1)‖ ^ 2 ≤ Kdt q * Win :=
    fun q hq => le_trans (hdtK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKdt_nn q))
  have hvfWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 1 q'
          (lc0VFlat (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ Kvf q * Win :=
    fun q hq => le_trans (hvfK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKvf_nn q))
  obtain ⟨hre0, hreL2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 3 1
    (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm Λdt (fun q => Kdt q * Win) i
    hdt0 hdtWin
  obtain ⟨hse0, hseL2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 1 2
    (lc0VFlat (I := I) (M := M) g₀ g₁ gB) Λvf (fun q => Kvf q * Win) i hvf0 hvfWin
  have hseWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (0 + 2) (1 + 2) q'
          (slotExtendIter (I := I) (M := M) g₀ 0 1 2
            (lc0VFlat (I := I) (M := M) g₀ g₁ gB))‖ ^ 2 ≤ (fr2 * Kvf q) * Win := by
    intro q hq
    refine le_trans (hseL2 q hq) (le_of_eq ?_)
    rw [hfr2_def]
    ring
  have hse0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (0 + 2) (1 + 2) x
      ((slotExtendIter (I := I) (M := M) g₀ 0 1 2
        (lc0VFlat (I := I) (M := M) g₀ g₁ gB)).toSection x) ≤ fr2 * Λvf := by
    intro x
    refine le_trans (hse0 x) (le_of_eq ?_)
    rw [hfr2_def]
  exact appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 3 1 i Win hWin1
    (reindexCoeffGen (I := I) (M := M) g₀ 3 1
      (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm)
    (slotExtendIter (I := I) (M := M) g₀ 0 1 2 (lc0VFlat (I := I) (M := M) g₀ g₁ gB))
    C2 hC2_nn hC2 Λdt (fr2 * Λvf) Kdt (fun q => fr2 * Kvf q)
    hΛdt_nn (mul_nonneg hfr2_nn hΛvf_nn) hre0 hse0' hreL2 hseWin

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_connDiffAppliedToDeTurckVectorField_coeffJetEnvelope (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q
              (lc0CdVField (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
  classical
  obtain ⟨Λcv, Fcv, hΛcv_nn, hFcv_nn, hcv⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨Λiv, Kiv, hΛiv_nn, hKiv_nn, hiv⟩ :=
    exists_deTurckVectorFieldInteriorProduct_coeffJetEnvelope (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨Λcd, Kcd, hΛcd_nn, hKcd_nn, hcd⟩ :=
    exists_connDiffSection_coeffJetEnvelope (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 2 1 1 2
  refine ⟨Λcv, fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λcd * Kiv q + Λiv * Kcd q)),
    hΛcv_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛcd_nn (hKiv_nn q))
        (mul_nonneg hΛiv_nn (hKcd_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  refine ⟨(hcv g₁ P htie hδ_le hδ0 hδ hPball).1, ?_⟩
  intro i
  set Win : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWin_def
  have hWin1 : (1 : ℝ) ≤ Win := one_le_l2JetWindow (I := I) (M := M) g₀ P i
  obtain ⟨hiv0, hivK⟩ := hiv g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hcd0, hcdK⟩ := hcd g₁ P htie hδ_le hδ0 hδ hPball
  have hivWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 1 q'
          (lc0IVField (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ Kiv q * Win :=
    fun q hq => le_trans (hivK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKiv_nn q))
  have hcdWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q'
          (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ Kcd q * Win :=
    fun q hq => le_trans (hcdK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKcd_nn q))
  exact appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 1 2 1 i Win hWin1
    (lc0IVField (I := I) (M := M) g₀ g₁ gB) (connDiffSection (I := I) g₁ g₀)
    C2 hC2_nn hC2 Λiv Λcd Kiv Kcd hΛiv_nn hΛcd_nn hiv0 hcd0 hivWin hcdWin

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem lc0w_comp_sup (g₀ : SmoothRiemannianMetric I M)
    (p a b : ℕ) (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a)
    (ΛΦ ΛW : ℝ) (hΛΦ : 0 ≤ ΛΦ)
    (hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) ≤ ΛΦ)
    (hW0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (W.toSection x) ≤ ΛW) :
    ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p b x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W).toSection x) ≤ ΛΦ * ΛW := by
  intro x
  rw [appCcRS_toSection]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ p a b x
    (show TensorRSSpace a b I x from Φ.toSection x)
    (show TensorRSSpace p a I x from W.toSection x)) ?_
  exact mul_le_mul (hΦ0 x) (hW0 x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ p a x _) hΛΦ

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lc0w_vb_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Λdt2, Kdt2, hΛdt2_nn, hKdt2_nn, hdt2⟩ :=
    exists_pureDoubleTraceCoeff_coeffJetEnvelope (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λκ, Kκ, hΛκ_nn, hKκ_nn, hκ⟩ :=
    exists_perturbedMetricLoweredConnDiff_coeffJetEnvelope (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Λiv, Kiv, hΛiv_nn, hKiv_nn, hiv⟩ :=
    exists_deTurckVectorFieldInteriorProduct_coeffJetEnvelope (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨C2i, hC2i_nn, hC2i⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 2 4 1
  obtain ⟨C2o, hC2o_nn, hC2o⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set ΛK : ℝ := fr ^ 1 * Λκ with hΛK_def
  have hΛK_nn : 0 ≤ ΛK := mul_nonneg (by positivity) hΛκ_nn
  set KK : ℕ → ℝ := fun q => fr ^ 1 * Kκ q with hKK_def
  have hKK_nn : ∀ q, 0 ≤ KK q := fun q => mul_nonneg (by positivity) (hKκ_nn q)
  set Λin : ℝ := ΛK * Λiv with hΛin_def
  have hΛin_nn : 0 ≤ Λin := mul_nonneg hΛK_nn hΛiv_nn
  set Kin : ℕ → ℝ := fun q => ∑ q' ∈ Finset.range (q + 1),
    diagonalGridGrowthFactor (E := E) q' * (C2i q' * (Λiv * KK q' + ΛK * Kiv q')) with hKin_def
  have hKin_nn : ∀ q, 0 ≤ Kin q := fun q =>
    Finset.sum_nonneg fun q' _ => mul_nonneg (appCcGdiag_nonneg (E := E) q')
      (mul_nonneg (hC2i_nn q') (add_nonneg (mul_nonneg hΛiv_nn (hKK_nn q'))
        (mul_nonneg hΛK_nn (hKiv_nn q'))))
  set Kout : ℕ → ℝ := fun q => ∑ q' ∈ Finset.range (q + 1),
    diagonalGridGrowthFactor (E := E) q' * (C2o q' * (Λin * Kdt2 q' + Λdt2 * Kin q')) with hKout_def
  have hKout_nn : ∀ q, 0 ≤ Kout q := fun q =>
    Finset.sum_nonneg fun q' _ => mul_nonneg (appCcGdiag_nonneg (E := E) q')
      (mul_nonneg (hC2o_nn q') (add_nonneg (mul_nonneg hΛin_nn (hKdt2_nn q'))
        (mul_nonneg hΛdt2_nn (hKin_nn q'))))
  refine ⟨fun i => (2 : ℝ) ^ 2 * Kout i,
    fun i => mul_nonneg (by norm_num) (hKout_nn i), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball i
  set Win : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWin_def
  have hWin1 : (1 : ℝ) ≤ Win := one_le_l2JetWindow (I := I) (M := M) g₀ P i
  obtain ⟨hdt20, hdt2K⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ0, hκK⟩ := hκ g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hiv0, hivK⟩ := hiv g₁ P htie hδ_le hδ0 hδ hPball
  have hdt2Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 q'
          (lc0PureDT (I := I) (M := M) g₀ g₁ 2)‖ ^ 2 ≤ Kdt2 q * Win :=
    fun q hq => le_trans (hdt2K q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKdt2_nn q))
  have hκWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q'
          (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤ Kκ q * Win :=
    fun q hq => le_trans (hκK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKκ_nn q))
  have hivWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 1 q'
          (lc0IVField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤ Kiv q * Win :=
    fun q hq => le_trans (hivK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKiv_nn q))
  obtain ⟨hK0raw, hKL2raw⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 1
    (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) Λκ (fun q => Kκ q * Win) i hκ0 hκWin
  have hK0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (0 + 1) (3 + 1) x
      ((slotExtendIter (I := I) (M := M) g₀ 0 3 1
        (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤ ΛK :=
    fun x => le_trans (hK0raw x) (le_of_eq (by rw [hΛK_def]))
  have hKWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (0 + 1) (3 + 1) q'
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))‖ ^ 2 ≤ KK q * Win :=
    fun q hq => le_trans (hKL2raw q hq) (le_of_eq (by rw [hKK_def]; ring))
  have hin0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
        (lc0IVField (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤ Λin :=
    lc0w_comp_sup (I := I) (M := M) g₀ 2 1 4
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
      (lc0IVField (I := I) (M := M) g₀ g₁ g₀) ΛK Λiv hΛK_nn hK0 hiv0
  have hinWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 4 q'
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
            (slotExtendIter (I := I) (M := M) g₀ 0 3 1
              (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
            (lc0IVField (I := I) (M := M) g₀ g₁ g₀))‖ ^ 2 ≤ Kin q * Win := by
    intro q hq
    refine le_trans (appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 1 4 q Win hWin1
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
      (lc0IVField (I := I) (M := M) g₀ g₁ g₀)
      C2i hC2i_nn hC2i ΛK Λiv KK Kiv hΛK_nn hΛiv_nn hK0 hiv0
      (fun q' hq' => hKWin q' (le_trans hq' hq))
      (fun q' hq' => hivWin q' (le_trans hq' hq))) (le_of_eq (by rw [hKin_def]))
  have htr0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm).toSection x) ≤ Λdt2 :=
    (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
      (lc0PureDT (I := I) (M := M) g₀ g₁ 2) lieCorr0VBPerm Λdt2
      (fun q => Kdt2 q * Win) i hdt20 hdt2Win).1
  have htrWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 q'
          (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)‖ ^ 2 ≤ Kdt2 q * Win :=
    fun q hq => (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
      (lc0PureDT (I := I) (M := M) g₀ g₁ 2) lieCorr0VBPerm Λdt2
      (fun q' => Kdt2 q' * Win) i hdt20 hdt2Win).2 q hq
  have hout0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
          (lc0IVField (I := I) (M := M) g₀ g₁ g₀))).toSection x) ≤ Λdt2 * Λin :=
    lc0w_comp_sup (I := I) (M := M) g₀ 2 4 2
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
        (lc0IVField (I := I) (M := M) g₀ g₁ g₀)) Λdt2 Λin hΛdt2_nn htr0 hin0
  have houtWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 q'
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
            (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
              (slotExtendIter (I := I) (M := M) g₀ 0 3 1
                (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
              (lc0IVField (I := I) (M := M) g₀ g₁ g₀)))‖ ^ 2 ≤ Kout q * Win := by
    intro q hq
    refine le_trans (appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 4 2 q Win hWin1
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
        (lc0IVField (I := I) (M := M) g₀ g₁ g₀))
      C2o hC2o_nn hC2o Λdt2 Λin Kdt2 Kin hΛdt2_nn hΛin_nn htr0 hin0
      (fun q' hq' => htrWin q' (le_trans hq' hq))
      (fun q' hq' => hinWin q' (le_trans hq' hq))) (le_of_eq (by rw [hKout_def]))
  obtain ⟨-, hsL2⟩ := lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (2 : ℝ)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
        (lc0IVField (I := I) (M := M) g₀ g₁ g₀)))
    (Λdt2 * Λin) (fun q => Kout q * Win) i hout0 houtWin
  exact le_trans (hsL2 i le_rfl) (le_of_eq (by ring))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lc0w_amixHalf_feed (g₀ g_bg : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg σlast).toSection x) ≤ Λ) ∧
        (∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg σlast)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
  classical
  obtain ⟨Λah, Fah, hΛah_nn, hFah_nn, hah⟩ :=
    lc0b_amixHalf_feed (I := I) (M := M) g₀ g_bg σlast a ha_super hR hδ₀
  obtain ⟨Λdt2, Kdt2, hΛdt2_nn, hKdt2_nn, hdt2⟩ :=
    exists_pureDoubleTraceCoeff_coeffJetEnvelope (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λdt3, Kdt3, hΛdt3_nn, hKdt3_nn, hdt3⟩ :=
    exists_pureDoubleTraceCoeff_coeffJetEnvelope (I := I) (M := M) g₀ 3 a ha_super hR hδ₀
  obtain ⟨Λdt4, Kdt4, hΛdt4_nn, hKdt4_nn, hdt4⟩ :=
    exists_pureDoubleTraceCoeff_coeffJetEnvelope (I := I) (M := M) g₀ 4 a ha_super hR hδ₀
  obtain ⟨Λκ0, Kκ0, hΛκ0_nn, hKκ0_nn, hκ0f⟩ :=
    exists_perturbedMetricLoweredConnDiff_coeffJetEnvelope (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Λκb, Kκb, hΛκb_nn, hKκb_nn, hκbf⟩ :=
    exists_perturbedMetricLoweredConnDiff_coeffJetEnvelope (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨C2a, hC2a_nn, hC2a⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 5 2 3 5
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 2 6 3
  obtain ⟨C2c, hC2c_nn, hC2c⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 6 2 4 6
  obtain ⟨C2d, hC2d_nn, hC2d⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set ΛK0 : ℝ := fr ^ 2 * Λκ0 with hΛK0_def
  have hΛK0_nn : 0 ≤ ΛK0 := mul_nonneg (by positivity) hΛκ0_nn
  set KK0 : ℕ → ℝ := fun q => fr ^ 2 * Kκ0 q with hKK0_def
  have hKK0_nn : ∀ q, 0 ≤ KK0 q := fun q => mul_nonneg (by positivity) (hKκ0_nn q)
  set ΛKb : ℝ := fr ^ 3 * Λκb with hΛKb_def
  have hΛKb_nn : 0 ≤ ΛKb := mul_nonneg (by positivity) hΛκb_nn
  set KKb : ℕ → ℝ := fun q => fr ^ 3 * Kκb q with hKKb_def
  have hKKb_nn : ∀ q, 0 ≤ KKb q := fun q => mul_nonneg (by positivity) (hKκb_nn q)
  set Λ1 : ℝ := Λdt3 * ΛK0 with hΛ1_def
  have hΛ1_nn : 0 ≤ Λ1 := mul_nonneg hΛdt3_nn hΛK0_nn
  set K1 : ℕ → ℝ := fun q => ∑ q' ∈ Finset.range (q + 1),
    diagonalGridGrowthFactor (E := E) q' * (C2a q' * (ΛK0 * Kdt3 q' + Λdt3 * KK0 q')) with hK1_def
  have hK1_nn : ∀ q, 0 ≤ K1 q := fun q =>
    Finset.sum_nonneg fun q' _ => mul_nonneg (appCcGdiag_nonneg (E := E) q')
      (mul_nonneg (hC2a_nn q') (add_nonneg (mul_nonneg hΛK0_nn (hKdt3_nn q'))
        (mul_nonneg hΛdt3_nn (hKK0_nn q'))))
  set Λ2 : ℝ := ΛKb * Λ1 with hΛ2_def
  have hΛ2_nn : 0 ≤ Λ2 := mul_nonneg hΛKb_nn hΛ1_nn
  set K2 : ℕ → ℝ := fun q => ∑ q' ∈ Finset.range (q + 1),
    diagonalGridGrowthFactor (E := E) q' * (C2b q' * (Λ1 * KKb q' + ΛKb * K1 q')) with hK2_def
  have hK2_nn : ∀ q, 0 ≤ K2 q := fun q =>
    Finset.sum_nonneg fun q' _ => mul_nonneg (appCcGdiag_nonneg (E := E) q')
      (mul_nonneg (hC2b_nn q') (add_nonneg (mul_nonneg hΛ1_nn (hKKb_nn q'))
        (mul_nonneg hΛKb_nn (hK1_nn q'))))
  set Λ3 : ℝ := Λdt4 * Λ2 with hΛ3_def
  have hΛ3_nn : 0 ≤ Λ3 := mul_nonneg hΛdt4_nn hΛ2_nn
  set K3 : ℕ → ℝ := fun q => ∑ q' ∈ Finset.range (q + 1),
    diagonalGridGrowthFactor (E := E) q' * (C2c q' * (Λ2 * Kdt4 q' + Λdt4 * K2 q')) with hK3_def
  have hK3_nn : ∀ q, 0 ≤ K3 q := fun q =>
    Finset.sum_nonneg fun q' _ => mul_nonneg (appCcGdiag_nonneg (E := E) q')
      (mul_nonneg (hC2c_nn q') (add_nonneg (mul_nonneg hΛ2_nn (hKdt4_nn q'))
        (mul_nonneg hΛdt4_nn (hK2_nn q'))))
  refine ⟨Λah, fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2d q * (Λ3 * Kdt2 q + Λdt2 * K3 q)),
    hΛah_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2d_nn q) (add_nonneg (mul_nonneg hΛ3_nn (hKdt2_nn q))
        (mul_nonneg hΛdt2_nn (hK3_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  refine ⟨(hah g₁ P htie hδ_le hδ0 hδ hPball).1, ?_⟩
  intro i
  set Win : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWin_def
  have hWin1 : (1 : ℝ) ≤ Win := one_le_l2JetWindow (I := I) (M := M) g₀ P i
  obtain ⟨hdt20, hdt2K⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hdt30, hdt3K⟩ := hdt3 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hdt40, hdt4K⟩ := hdt4 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ00, hκ0K⟩ := hκ0f g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκb0, hκbK⟩ := hκbf g₁ P htie hδ_le hδ0 hδ hPball
  have hdt2Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 q'
          (lc0PureDT (I := I) (M := M) g₀ g₁ 2)‖ ^ 2 ≤ Kdt2 q * Win :=
    fun q hq => le_trans (hdt2K q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKdt2_nn q))
  have hdt3Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 5 3 q'
          (lc0PureDT (I := I) (M := M) g₀ g₁ 3)‖ ^ 2 ≤ Kdt3 q * Win :=
    fun q hq => le_trans (hdt3K q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKdt3_nn q))
  have hdt4Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 6 4 q'
          (lc0PureDT (I := I) (M := M) g₀ g₁ 4)‖ ^ 2 ≤ Kdt4 q * Win :=
    fun q hq => le_trans (hdt4K q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKdt4_nn q))
  have hκ0Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q'
          (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤ Kκ0 q * Win :=
    fun q hq => le_trans (hκ0K q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKκ0_nn q))
  have hκbWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q'
          (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ Kκb q * Win :=
    fun q hq => le_trans (hκbK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKκb_nn q))
  obtain ⟨hK00raw, hK0L2raw⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 2
    (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) Λκ0 (fun q => Kκ0 q * Win) i hκ00 hκ0Win
  have hK00 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (0 + 2) (3 + 2) x
      ((slotExtendIter (I := I) (M := M) g₀ 0 3 2
        (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤ ΛK0 :=
    fun x => le_trans (hK00raw x) (le_of_eq (by rw [hΛK0_def]))
  have hK0Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (0 + 2) (3 + 2) q'
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))‖ ^ 2 ≤ KK0 q * Win :=
    fun q hq => le_trans (hK0L2raw q hq) (le_of_eq (by rw [hKK0_def]; ring))
  obtain ⟨hKb0raw, hKbL2raw⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 3
    (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg) Λκb (fun q => Kκb q * Win) i hκb0 hκbWin
  have hKb0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (0 + 3) (3 + 3) x
      ((slotExtendIter (I := I) (M := M) g₀ 0 3 3
        (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ ΛKb :=
    fun x => le_trans (hKb0raw x) (le_of_eq (by rw [hΛKb_def]))
  have hKbWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (0 + 3) (3 + 3) q'
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3
            (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤ KKb q * Win :=
    fun q hq => le_trans (hKbL2raw q hq) (le_of_eq (by rw [hKKb_def]; ring))
  have htr30 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 5 3 x
      ((lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ).toSection x) ≤ Λdt3 :=
    (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 5 3
      (lc0PureDT (I := I) (M := M) g₀ g₁ 3) lieCorr0AMixPermQ Λdt3
      (fun q => Kdt3 q * Win) i hdt30 hdt3Win).1
  have htr3Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 5 3 q'
          (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)‖ ^ 2 ≤ Kdt3 q * Win :=
    fun q hq => (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 5 3
      (lc0PureDT (I := I) (M := M) g₀ g₁ 3) lieCorr0AMixPermQ Λdt3
      (fun q' => Kdt3 q' * Win) i hdt30 hdt3Win).2 q hq
  have h10 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
        (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2
          (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))).toSection x) ≤ Λ1 :=
    lc0w_comp_sup (I := I) (M := M) g₀ 2 5 3
      (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
      Λdt3 ΛK0 hΛdt3_nn htr30 hK00
  have h1Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 3 q'
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
            (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2
              (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))‖ ^ 2 ≤ K1 q * Win := by
    intro q hq
    refine le_trans (appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 5 3 q Win hWin1
      (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
      C2a hC2a_nn hC2a Λdt3 ΛK0 Kdt3 KK0 hΛdt3_nn hΛK0_nn htr30 hK00
      (fun q' hq' => htr3Win q' (le_trans hq' hq))
      (fun q' hq' => hK0Win q' (le_trans hq' hq))) (le_of_eq (by rw [hK1_def]))
  have h20 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 6 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3
          (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))).toSection x) ≤ Λ2 :=
    lc0w_comp_sup (I := I) (M := M) g₀ 2 3 6
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
        (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))
      ΛKb Λ1 hΛKb_nn hKb0 h10
  have h2Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 6 q'
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
              (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
              (slotExtendIter (I := I) (M := M) g₀ 0 3 2
                (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))))‖ ^ 2 ≤ K2 q * Win := by
    intro q hq
    refine le_trans (appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 3 6 q Win hWin1
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
        (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))
      C2b hC2b_nn hC2b ΛKb Λ1 KKb K1 hΛKb_nn hΛ1_nn hKb0 h10
      (fun q' hq' => hKbWin q' (le_trans hq' hq))
      (fun q' hq' => h1Win q' (le_trans hq' hq))) (le_of_eq (by rw [hK2_def]))
  have htr40 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 6 4 x
      ((lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1).toSection x) ≤ Λdt4 :=
    (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 6 4
      (lc0PureDT (I := I) (M := M) g₀ g₁ 4) lieCorr0AMixPerm1 Λdt4
      (fun q => Kdt4 q * Win) i hdt40 hdt4Win).1
  have htr4Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 6 4 q'
          (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)‖ ^ 2 ≤ Kdt4 q * Win :=
    fun q hq => (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 6 4
      (lc0PureDT (I := I) (M := M) g₀ g₁ 4) lieCorr0AMixPerm1 Λdt4
      (fun q' => Kdt4 q' * Win) i hdt40 hdt4Win).2 q hq
  have h30 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
        (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3
            (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
            (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2
              (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))))).toSection x) ≤ Λ3 :=
    lc0w_comp_sup (I := I) (M := M) g₀ 2 6 4
      (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))))
      Λdt4 Λ2 hΛdt4_nn htr40 h20
  have h3Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 4 q'
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
            (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
                (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
                (slotExtendIter (I := I) (M := M) g₀ 0 3 2
                  (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))))‖ ^ 2 ≤ K3 q * Win := by
    intro q hq
    refine le_trans (appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 6 4 q Win hWin1
      (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))))
      C2c hC2c_nn hC2c Λdt4 Λ2 Kdt4 K2 hΛdt4_nn hΛ2_nn htr40 h20
      (fun q' hq' => htr4Win q' (le_trans hq' hq))
      (fun q' hq' => h2Win q' (le_trans hq' hq))) (le_of_eq (by rw [hK3_def]))
  have htr20 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((lc0Tr (I := I) (M := M) g₀ g₁ 2 σlast).toSection x) ≤ Λdt2 :=
    (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
      (lc0PureDT (I := I) (M := M) g₀ g₁ 2) σlast Λdt2
      (fun q => Kdt2 q * Win) i hdt20 hdt2Win).1
  have htr2Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 q'
          (lc0Tr (I := I) (M := M) g₀ g₁ 2 σlast)‖ ^ 2 ≤ Kdt2 q * Win :=
    fun q hq => (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
      (lc0PureDT (I := I) (M := M) g₀ g₁ 2) σlast Λdt2
      (fun q' => Kdt2 q' * Win) i hdt20 hdt2Win).2 q hq
  exact appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 4 2 i Win hWin1
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 σlast)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
      (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))))
    C2d hC2d_nn hC2d Λdt2 Λ3 Kdt2 K3 hΛdt2_nn hΛ3_nn htr20 h30 htr2Win h3Win

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lc0w_amix_feed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨ΛhA, KhA, hΛhA_nn, hKhA_nn, hhA⟩ :=
    lc0w_amixHalf_feed (I := I) (M := M) g₀ g_bg lieCorr0AMixPerm2 a ha_super hR hδ₀
  obtain ⟨ΛhB, KhB, hΛhB_nn, hKhB_nn, hhB⟩ :=
    lc0w_amixHalf_feed (I := I) (M := M) g₀ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2)
      a ha_super hR hδ₀
  refine ⟨fun i => (2 : ℝ) ^ 2 * (2 * KhA i + 2 * KhB i),
    fun i => mul_nonneg (by norm_num) (by
      have h1 := hKhA_nn i
      have h2 := hKhB_nn i
      linarith), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball i
  set Win : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWin_def
  have hWin1 : (1 : ℝ) ≤ Win := one_le_l2JetWindow (I := I) (M := M) g₀ P i
  obtain ⟨hhA0, hhAK⟩ := hhA g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hhB0, hhBK⟩ := hhB g₁ P htie hδ_le hδ0 hδ hPball
  have hhAWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 q'
          (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2)‖ ^ 2 ≤
      KhA q * Win :=
    fun q hq => le_trans (hhAK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKhA_nn q))
  have hhBWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 q'
          (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg
            (lc0SwapOutPerm * lieCorr0AMixPerm2))‖ ^ 2 ≤ KhB q * Win :=
    fun q hq => le_trans (hhBK q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKhB_nn q))
  obtain ⟨hadd0, haddL2⟩ := lc0b_add_feed_transfer (I := I) (M := M) g₀ 2 2
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2)
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2))
    ΛhA ΛhB (fun q => KhA q * Win) (fun q => KhB q * Win) i hhA0 hhB0 hhAWin hhBWin
  obtain ⟨-, hsL2⟩ := lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (2 : ℝ)
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2
      + lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg
        (lc0SwapOutPerm * lieCorr0AMixPerm2))
    (2 * ΛhA + 2 * ΛhB) (fun q => 2 * (KhA q * Win) + 2 * (KhB q * Win)) i hadd0 haddL2
  exact le_trans (hsL2 i le_rfl) (le_of_eq (by ring))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_lieDerivativeRiemannCoeff_coeffJetEnvelope (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ i : ℕ,
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
          K i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Λdt2, Kdt2, hΛdt2_nn, hKdt2_nn, hdt2⟩ :=
    exists_pureDoubleTraceCoeff_coeffJetEnvelope (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λrr, hΛrr_nn, hΛrr⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 4
      (lc0RiemRestField (I := I) (M := M) g₀)
  set Frr : ℕ → ℝ := fun q => ∑ q' ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ 2 4 q'
      (lc0RiemRestField (I := I) (M := M) g₀)‖ ^ 2 with hFrr_def
  have hFrr_nn : ∀ q, 0 ≤ Frr q := fun q => Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  refine ⟨fun i => (-1 : ℝ) ^ 2 * ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λrr * Kdt2 q + Λdt2 * Frr q)),
    fun i => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
        (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛrr_nn (hKdt2_nn q))
          (mul_nonneg hΛdt2_nn (hFrr_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball i
  set Win : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWin_def
  have hWin1 : (1 : ℝ) ≤ Win := one_le_l2JetWindow (I := I) (M := M) g₀ P i
  obtain ⟨hdt20, hdt2K⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  have hdt2Win : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 q'
          (lc0PureDT (I := I) (M := M) g₀ g₁ 2)‖ ^ 2 ≤ Kdt2 q * Win :=
    fun q hq => le_trans (hdt2K q) (mul_le_mul_of_nonneg_left
      (l2JetWindow_mono (I := I) (M := M) g₀ P hq) (hKdt2_nn q))
  have htr0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2).toSection x) ≤ Λdt2 :=
    (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
      (lc0PureDT (I := I) (M := M) g₀ g₁ 2) lieCorr0RiemPerm2 Λdt2
      (fun q => Kdt2 q * Win) i hdt20 hdt2Win).1
  have htrWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 q'
          (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)‖ ^ 2 ≤ Kdt2 q * Win :=
    fun q hq => (lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
      (lc0PureDT (I := I) (M := M) g₀ g₁ 2) lieCorr0RiemPerm2 Λdt2
      (fun q' => Kdt2 q' * Win) i hdt20 hdt2Win).2 q hq
  have hFrrWin : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 4 q'
          (lc0RiemRestField (I := I) (M := M) g₀)‖ ^ 2 ≤ Frr q * Win :=
    fun q _ => le_mul_of_one_le_right (hFrr_nn q) hWin1
  have hcompWin :
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
            (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
            (lc0RiemRestField (I := I) (M := M) g₀))‖ ^ 2 ≤
      (∑ q ∈ Finset.range (i + 1),
        diagonalGridGrowthFactor (E := E) q * (C2 q * (Λrr * Kdt2 q + Λdt2 * Frr q))) * Win :=
    appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 4 2 i Win hWin1
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
      (lc0RiemRestField (I := I) (M := M) g₀)
      C2 hC2_nn hC2 Λdt2 Λrr Kdt2 Frr hΛdt2_nn hΛrr_nn htr0 hΛrr htrWin hFrrWin
  have hcompWin' : ∀ q : ℕ, q ≤ i →
      ∑ q' ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 q'
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
            (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
            (lc0RiemRestField (I := I) (M := M) g₀))‖ ^ 2 ≤
      (∑ q' ∈ Finset.range (q + 1),
        diagonalGridGrowthFactor (E := E) q' * (C2 q' * (Λrr * Kdt2 q' + Λdt2 * Frr q'))) * Win := by
    intro q hq
    exact appCcRS_l2JetWindow_le (I := I) (M := M) g₀ 2 4 2 q Win hWin1
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
      (lc0RiemRestField (I := I) (M := M) g₀)
      C2 hC2_nn hC2 Λdt2 Λrr Kdt2 Frr hΛdt2_nn hΛrr_nn htr0 hΛrr
      (fun q' hq' => htrWin q' (le_trans hq' hq))
      (fun q' hq' => hFrrWin q' (le_trans hq' hq))
  have hcomp0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
        (lc0RiemRestField (I := I) (M := M) g₀)).toSection x) ≤ Λdt2 * Λrr :=
    lc0w_comp_sup (I := I) (M := M) g₀ 2 4 2
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
      (lc0RiemRestField (I := I) (M := M) g₀) Λdt2 Λrr hΛdt2_nn htr0 hΛrr
  obtain ⟨-, hsL2⟩ := lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (-1 : ℝ)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
      (lc0RiemRestField (I := I) (M := M) g₀))
    (Λdt2 * Λrr)
    (fun q => (∑ q' ∈ Finset.range (q + 1),
      diagonalGridGrowthFactor (E := E) q' * (C2 q' * (Λrr * Kdt2 q' + Λdt2 * Frr q'))) * Win)
    i hcomp0 hcompWin'
  exact le_trans (hsL2 i le_rfl) (le_of_eq (by ring))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieEndoArmField) in

private theorem lieDerivativeCorrectionPlusEndoArm_l2JetWindow
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              + deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Λc0, Kc0, hΛc0_nn, hKc0_nn, hc0⟩ :=
    exists_connDiffAppliedToDeTurckVectorField_coeffJetEnvelope (I := I) (M := M) g₀ g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λcb, Kcb, hΛcb_nn, hKcb_nn, hcb⟩ :=
    exists_connDiffAppliedToDeTurckVectorField_coeffJetEnvelope (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨Kvb, hKvb_nn, hvb⟩ := lc0w_vb_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Kam, hKam_nn, ham⟩ :=
    lc0w_amix_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨Kri, hKri_nn, hri⟩ := exists_lieDerivativeRiemannCoeff_coeffJetEnvelope (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 64 * (fr * (Kc0 i + Kcb i)) + 8 * Kvb i + 4 * Kam i + 2 * Kri i,
    fun i => by
      have h1 := hKc0_nn i
      have h2 := hKcb_nn i
      have h3 := hKvb_nn i
      have h4 := hKam_nn i
      have h5 := hKri_nn i
      have h6 : 0 ≤ fr * (Kc0 i + Kcb i) := mul_nonneg hfr_nn (by linarith)
      linarith, ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T 0 hδ hδZ s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T 0 s with hPc_def
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hzgrad : ∀ j : ℕ,
      iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    intro j
    have h := iteratedCovGrad_sub (I := I) (g := g₀) (r := 0) (s := 2) (j := j) T T
    rw [sub_self, sub_self] at h
    exact h
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ + |s| * δ) := by
    rw [hPc_def]
    exact DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation_gFibreOpBound_abs
      (I := I) g₀ T 0 hδ hδZ s
  set δP : ℝ := max (|1 - s| * δ + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ Pc) δP :=
    lc0b_gFibreOpBound_mono (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ
      (Icc_subset_realizedSmallSet hδ_lt hδ_lt hs) y v w
  have hPcT : ∀ j : ℕ, iteratedCovGrad (I := I) g₀ 0 2 j Pc =
      s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
    intro j
    rw [hPc_def]
    rw [show convexPerturbation (I := I) g₀ T 0 s =
        (1 - s) • (0 : SmoothCcTensor g₀ 0 2) + s • T from rfl,
      iteratedCovGrad_add, lc0b_icg_smul, lc0b_icg_smul, hzgrad, smul_zero, zero_add]
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    rw [hPcT j, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    calc s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ 1 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
          mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ = ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := one_mul _
      _ ≤ R := hball j hj
  have hPT2 : ∀ j : ℕ, ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by
    intro j
    rw [hPcT j, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hX := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖
    nlinarith [mul_nonneg (mul_nonneg h1ms (show (0 : ℝ) ≤ 1 + s by linarith)) hX]
  set WinT : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 with hWinT_def
  have hWinT_nn : (0 : ℝ) ≤ WinT := by
    rw [hWinT_def]
    have := one_le_l2JetWindow (I := I) (M := M) g₀ T i
    linarith
  have hWinPT : 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2 ≤ WinT := by
    rw [hWinT_def]
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (i + 2)) => hPT2 j)
    linarith
  have hc0K := (hc0 g₁ Pc htie hδP_le hδP_nn hδP_bound hPball).2 i
  have hcbK := (hcb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball).2 i
  have hvbK := hvb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball i
  have hamK := ham g₁ Pc htie hδP_le hδP_nn hδP_bound hPball i
  have hriK := hri g₁ Pc htie hδP_le hδP_nn hδP_bound hPball i
  rw [lc0w_lieCorr0_add_endoArmBase_decomp (I := I) (M := M) g₀ g₁ g_bg]
  set IΔ : SmoothCcTensor g₀ 2 2 := endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
    (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
      lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀) with hIΔ_def
  set IS : SmoothCcTensor g₀ 2 2 := reindexCoeffGen (I := I) (M := M) g₀ 2 2
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) IΔ)
    (Equiv.swap (0 : Fin 2) 1) with hIS_def
  have k1 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
    (IΔ + IS + lc0VBField (I := I) (M := M) g₀ g₁
      + lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)
    (lc0RiemField (I := I) (M := M) g₀ g₁)
  have k2 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
    (IΔ + IS + lc0VBField (I := I) (M := M) g₀ g₁)
    (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)
  have k3 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
    (IΔ + IS) (lc0VBField (I := I) (M := M) g₀ g₁)
  have k4 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i IΔ IS
  have hIΔ_le : ‖iteratedCovGrad (I := I) g₀ 2 2 i IΔ‖ ^ 2 ≤
      fr * ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
            lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀))‖ ^ 2 := by
    rw [hIΔ_def]
    refine lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀ 2 (2 + i) 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
            lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)))
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
            lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)))
      fr hfr_nn ?_
    intro x
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
      (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
        lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀) i x
    rw [pow_one] at h
    exact h
  have hIΔ_dec : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
          lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀))‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 +
      2 * ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := by
    rw [lc0w_NEndoIns_diff_decomp (I := I) (M := M) g₀ g₁ g_bg]
    exact lc0b_normSq_icg_sub_le (I := I) (M := M) g₀ 1 1 i
      (lc0CdVField (I := I) (M := M) g₀ g₁ g₀)
      (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)
  have hc0i : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (lc0CdVField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤ Kc0 i * WinT := by
    refine le_trans (Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 1 1 q (lc0CdVField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self i))) ?_
    exact le_trans hc0K (mul_le_mul_of_nonneg_left hWinPT (hKc0_nn i))
  have hcbi : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ Kcb i * WinT := by
    refine le_trans (Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 1 1 q (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self i))) ?_
    exact le_trans hcbK (mul_le_mul_of_nonneg_left hWinPT (hKcb_nn i))
  have hswap : ‖iteratedCovGrad (I := I) g₀ 2 2 i IS‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 2 2 i IΔ‖ ^ 2 := by
    rw [hIS_def, hIΔ_def]
    exact lc0b_normSq_icg_bothCongr_eq (I := I) (M := M) g₀ 2 2
      (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg -
          lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)) i
  have hvbi : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Kvb i * WinT := by
    refine le_trans (Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self i))) ?_
    exact le_trans hvbK (mul_le_mul_of_nonneg_left hWinPT (hKvb_nn i))
  have hami : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ Kam i * WinT := by
    refine le_trans (Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q
        (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self i))) ?_
    exact le_trans hamK (mul_le_mul_of_nonneg_left hWinPT (hKam_nn i))
  have hrii : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Kri i * WinT := by
    refine le_trans (Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_self i))) ?_
    exact le_trans hriK (mul_le_mul_of_nonneg_left hWinPT (hKri_nn i))
  have hIΔ_tot : ‖iteratedCovGrad (I := I) g₀ 2 2 i IΔ‖ ^ 2 ≤
      fr * (2 * (Kc0 i * WinT) + 2 * (Kcb i * WinT)) := by
    refine le_trans hIΔ_le (mul_le_mul_of_nonneg_left ?_ hfr_nn)
    linarith [hIΔ_dec, hc0i, hcbi]
  have hfrK : (0 : ℝ) ≤ fr * (Kc0 i + Kcb i) :=
    mul_nonneg hfr_nn (by linarith [hKc0_nn i, hKcb_nn i])
  nlinarith [k1, k2, k3, k4, hswap, hIΔ_tot, hvbi, hami, hrii,
    mul_nonneg hfrK hWinT_nn]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieEndoArmField) in

private theorem exists_lieDerivativeCorrectionPlusEndoArm_order0_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
          (fun s => lieCorr0Field (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            + deTurckLieEndoArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀) (δ := δ) (δ' := δ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              + deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤ Λ ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              + deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨ΛL, hΛL_nn, hsupL⟩ :=
    lieCorr0Field_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Λz, hΛz_nn, hsupz⟩ :=
    DifferentialGeometry.Integral.Connection.deTurckLieDLbCoeffField_realizedFam_rfns_order0_ballUniform
      (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨K, hK_nn, henv⟩ :=
    lieDerivativeCorrectionPlusEndoArm_l2JetWindow (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  have hS_nn : (0 : ℝ) ≤ 2 * ΛL + 2 * Λz := by linarith
  refine ⟨Real.sqrt (2 * ΛL + 2 * Λz), Real.sqrt_nonneg _, K, hK_nn, ?_⟩
  intro T δ hδ_le hδ hδZ hball
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    have hzero : iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := iteratedCovGrad_sub (I := I) (g := g₀) (r := 0) (s := 2) (j := j) T T
      rw [sub_self, sub_self] at h
      exact h
    rw [hzero, norm_zero]
    exact hR
  have hEndoEq : ∀ u : ℝ,
      deTurckLieEndoArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ u) g₀ =
      DifferentialGeometry.Integral.Connection.deTurckLieDLbCoeffField (I := I) (M := M)
        g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ u) g₀ := by
    intro u
    apply SmoothCcTensor.ext
    refine ContMDiffSection.ext (fun x => ?_)
    rfl
  refine ⟨?_, ?_, fun i s hs => henv T hδ_le hδ hδZ hball i s hs⟩
  · have hjA := lieCorr0_path_joint (I := I) g₀ T 0 hδ hδZ g_bg
    have hjC := deTurckLieCoeffField_realizedFam_jointSmooth (I := I) g₀ T 0 hδ hδZ g₀
    have hjD : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
        (fun u => DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCovDerivArmField
          (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ u) g₀)
        (δ := δ) (δ' := δ) := by
      have h :=
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.dLaBiContrFib_realizedFam_jointContMDiffOn
          (I := I) g₀ T 0 hδ hδZ g₀
      refine h.congr (fun p _ => ?_)
      rfl
    have hjB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
        (fun u => deTurckLieEndoArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ u) g₀) (δ := δ) (δ' := δ) := by
      have hsub := jointTotalSpaceRS_sub_fw (I := I) (r := 2) (s := 2)
        (S := realizedSmallSet (δ := δ) (δ' := δ))
        (fun p : M × ℝ => (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g₀).toSection p.1)
        (fun p : M × ℝ =>
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCovDerivArmField
            (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g₀).toSection p.1)
        hjC hjD
      refine hsub.congr (fun p _ => ?_)
      refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
      beta_reduce
      have hsplit : deTurckLieEndoArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g₀ =
          deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g₀
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCovDerivArmField
              (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g₀ := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField_eq_covDerivArm_add_endoArm
          (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g₀).symm
      rw [hsplit, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    exact linearizedRicciThreeArmHjoint_add (I := I) (M := M) g₀ 2 _ _ hjA hjB
  · intro s hs x
    try dsimp only
    rw [Real.sq_sqrt hS_nn]
    have h1 := hsupL T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieEndoArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤ Λz := by
      rw [hEndoEq s]
      exact hsupz T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    refine le_trans (lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (lieCorr0Field (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
      (deTurckLieEndoArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀) x) ?_
    linarith

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieEndoArmField
  deTurckLieCovDerivArmField deTurckLieCoeffField_eq_covDerivArm_add_endoArm
  exists_deTurckLieCovDerivArm_curvatureRefold_data
  exists_deTurckLieEndoArm_backgroundDifference_order0_data) in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

private theorem exists_lieDerivativeCorrection_curvatureRefold_armSplit_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_half : δ₀ ≤ 1 / 2) :
    ∃ Λlc : ℝ, 0 ≤ Λlc ∧ ∃ Klc : ℕ → ℝ, (∀ i, 0 ≤ Klc i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0lc : ℝ → SmoothCcTensor g₀ 2 2) (C2lc : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0lc (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2lc (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (deTurckLieCoeffField (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
                  + lieCorr0Field (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0lc s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 (C2lc s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0lc s).toSection x) ≤
              Λlc ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2lc s).toSection x) ≤
              (max (10 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0lc s)‖ ^ 2 ≤
              Klc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2lc s)‖ ^ 2 ≤
              Klc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λda, -, Kda, hKda_nn, hDA⟩ :=
    exists_deTurckLieCovDerivArm_curvatureRefold_data (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Λdf, -, Kdf, hKdf_nn, hDF⟩ :=
    exists_deTurckLieEndoArm_backgroundDifference_order0_data (I := I) (M := M) g₀ g_bg
      a ha_super hR hδ₀
  obtain ⟨Λrs, -, Krs, hKrs_nn, hRS⟩ :=
    exists_lieDerivativeCorrectionPlusEndoArm_order0_data (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  have hS_nn : (0 : ℝ) ≤ 4 * Λda ^ 2 + 4 * Λdf ^ 2 + 2 * Λrs ^ 2 := by positivity
  refine ⟨Real.sqrt (4 * Λda ^ 2 + 4 * Λdf ^ 2 + 2 * Λrs ^ 2), Real.sqrt_nonneg _,
    fun i => 3 * (Kda i + Kdf i + Krs i),
    fun i => by
      have h1 := hKda_nn i
      have h2 := hKdf_nn i
      have h3 := hKrs_nn i
      linarith, ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  obtain ⟨C0da, C2da, hj0da, hj2da, hidda, hsupda, hcapda, henv0da, henv2da⟩ :=
    hDA T hTsymm hδ_le hδ hδZ hball
  obtain ⟨hjdf, hsupdf, henvdf⟩ := hDF T hδ_le hδ hδZ hball
  obtain ⟨hjrs, hsuprs, henvrs⟩ := hRS T hδ_le hδ hδZ hball
  set fam := realizedFam (I := I) g₀ T 0 hδ hδZ
  refine ⟨fun s => C0da s
      + (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
        - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)
      + (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
        + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀),
    C2da, ?_, hj2da, ?_, ?_, ?_, ?_, ?_⟩
  · exact linearizedRicciThreeArmHjoint_add (I := I) (M := M) g₀ 2 _ _
      (linearizedRicciThreeArmHjoint_add (I := I) (M := M) g₀ 2 _ _ hj0da hjdf) hjrs
  · intro s hs
    have hsplit : deTurckLieCoeffField (I := I) (M := M) g₀ (fam s) g_bg
        + lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg =
        deTurckLieCovDerivArmField (I := I) (M := M) g₀ (fam s) g_bg
        + (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
          - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)
        + (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
          + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀) := by
      rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm (I := I) (M := M) g₀
        (fam s) g_bg]
      abel
    try dsimp only
    rw [hsplit]
    simp only [appCc_add_left]
    rw [hidda s hs]
    abel
  · intro s hs x
    have h1 := hsupda s hs x
    have h2 := hsupdf s hs x
    have h3 := hsuprs s hs x
    try dsimp only
    rw [Real.sq_sqrt hS_nn, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
      Pi.add_apply, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x _ _) ?_
    have h12 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
      ((C0da s).toSection x)
      ((deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
        - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀).toSection x)
    linarith [h1, h2, h3, h12]
  · intro s hs x
    refine le_trans (hcapda s hs x) ?_
    have hfC := deTurckArmFibreConst_nonneg (Module.finrank ℝ E)
    have hδ_half : δ ≤ 1 / 2 := hδ_le.trans hδ₀_half
    have h1mδ_pos : (0 : ℝ) < 1 - δ := by linarith
    refine pow_le_pow_left₀ (le_max_right _ _) ?_ 2
    refine max_le ?_ (le_max_right _ _)
    rcases le_or_gt δ 0 with hδ0 | hδ0
    · refine le_trans ?_ (le_max_right _ _)
      have hq : δ / (1 - δ) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hδ0 (sq_nonneg _)
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hfC)
        (neg_nonneg.mpr hq)]
    · refine le_trans ?_ (le_max_left _ _)
      rw [show (3 : ℝ) * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)
            = 3 * deTurckArmFibreConst (Module.finrank ℝ E) * δ / (1 - δ) ^ 2 from by
          ring,
        show (10 : ℝ) * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))
            = 10 * deTurckArmFibreConst (Module.finrank ℝ E) * δ / (1 - δ) from by
          ring,
        div_le_div_iff₀ (by positivity) h1mδ_pos]
      have hP : (0 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) * δ * (1 - δ) :=
        mul_nonneg (mul_nonneg hfC hδ0.le) h1mδ_pos.le
      have hQ : (0 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) * δ * (1 - δ)
          * (1 / 2 - δ) := mul_nonneg hP (by linarith)
      nlinarith [hP, hQ]
  · intro i s hs
    have ha := henv0da i s hs
    have hb := henvdf i s hs
    have hc := henvrs i s hs
    have hW : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
    try dsimp only
    have e1 := iteratedCovGrad_add (I := I) (g := g₀) (r := 2) (s := 2) (j := i)
      (C0da s
        + (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
          - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀))
      (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
        + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)
    have e2 := iteratedCovGrad_add (I := I) (g := g₀) (r := 2) (s := 2) (j := i)
      (C0da s)
      (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
        - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)
    rw [e1, e2]
    have htri : ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)
          + iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)
          + iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
              + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)‖
        ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖
          + ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
                - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)‖
          + ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
                + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)‖ := by
      have t1 := norm_add_le
        (iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)
          + iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀))
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
            + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀))
      have t2 := norm_add_le
        (iteratedCovGrad (I := I) g₀ 2 2 i (C0da s))
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
            - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀))
      linarith [t1, t2]
    refine le_trans (pow_le_pow_left₀ (norm_nonneg _) htri 2) ?_
    nlinarith [ha, hb, hc, mul_nonneg (hKda_nn i) hW, mul_nonneg (hKdf_nn i) hW,
      mul_nonneg (hKrs_nn i) hW,
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖
        - ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)‖),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)‖
        - ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
              + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)‖),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖
        - ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
              + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)‖),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g_bg
          - deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀)),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorr0Field (I := I) (M := M) g₀ (fam s) g_bg
          + deTurckLieEndoArmField (I := I) (M := M) g₀ (fam s) g₀))]
  · intro i s hs
    have hW : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
    refine le_trans (henv2da i s hs) ?_
    try dsimp only
    nlinarith [mul_nonneg (hKda_nn i) hW, mul_nonneg (hKdf_nn i) hW,
      mul_nonneg (hKrs_nn i) hW]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

private theorem exists_lieDerivativeCorrection_curvatureRefold_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_half : δ₀ ≤ 1 / 2) :
    ∃ Λlc : ℝ, 0 ≤ Λlc ∧ ∃ Klc : ℕ → ℝ, (∀ i, 0 ≤ Klc i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0lc : ℝ → SmoothCcTensor g₀ 2 2) (C2lc : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0lc (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2lc (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (deTurckLieCoeffField (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
                  + lieCorr0Field (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0lc s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 (C2lc s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0lc s).toSection x) ≤
              Λlc ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2lc s).toSection x) ≤
              (max (10 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0lc s)‖ ^ 2 ≤
              Klc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2lc s)‖ ^ 2 ≤
              Klc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  exists_lieDerivativeCorrection_curvatureRefold_armSplit_data (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
    hδ₀_half

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_riemannLieDerivativeCorrection_curvatureRefold_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_half : δ₀ ≤ 1 / 2) :
    ∃ Λrl : ℝ, 0 ≤ Λrl ∧ ∃ Krl : ℕ → ℝ, (∀ i, 0 ≤ Krl i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0f : ℝ → SmoothCcTensor g₀ 2 2) (C2f : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0f (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2f (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
            (fun s => linearizedRicciArm0CorrField (I := I) g₀ T 0 hδ hδZ s
              + (3 / 2 : ℝ) •
                DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                  (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                  (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)
                  + (deTurckLieCoeffField (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
                    + lieCorr0Field (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg))
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0f s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 (C2f s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0f s).toSection x) ≤
              Λrl ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ Λrl ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2f s).toSection x) ≤
              (max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0f s)‖ ^ 2 ≤
              Krl i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2f s)‖ ^ 2 ≤
              Krl i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λra, hΛra_nn, Kra, hKra_nn, hRA⟩ :=
    exists_riemannPalatini_curvatureRefold_data (I := I) (M := M) g₀ a ha_super hR hδ₀
      hδ₀_half
  obtain ⟨Λlc, hΛlc_nn, Klc, hKlc_nn, hLC⟩ :=
    exists_lieDerivativeCorrection_curvatureRefold_data (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
      hδ₀_half
  refine ⟨Real.sqrt (3 * Λra ^ 2 + 2 * Λlc ^ 2), Real.sqrt_nonneg _,
    fun i => 2 * Kra i + 2 * Klc i,
    fun i => by
      have h1 := hKra_nn i
      have h2 := hKlc_nn i
      linarith, ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hTjets
  obtain ⟨C0ra, C2ra, hjC0ra, hjC2ra, hidRA, hsupC0ra, hsupRm, hsupC2ra, henvC0ra, henvC2ra⟩ :=
    hRA T hTsymm hδ_le hδ hδZ hTjets
  obtain ⟨C0lc, C2lc, hjC0lc, hjC2lc, hidLC, hsupC0lc, hsupC2lc, henvC0lc, henvC2lc⟩ :=
    hLC T hTsymm hδ_le hδ hδZ hTjets
  have hsum_nn : (0 : ℝ) ≤ 3 * Λra ^ 2 + 2 * Λlc ^ 2 := by positivity
  refine ⟨fun s => C0ra s + C0lc s, fun s => C2ra s + C2lc s,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact linearizedRicciThreeArmHjoint_add (I := I) (M := M) g₀ 2 C0ra C0lc hjC0ra hjC0lc
  · exact linearizedRicciThreeArmHjoint_add (I := I) (M := M) g₀ 4 C2ra C2lc hjC2ra hjC2lc
  · have hfun : (fun s => linearizedRicciArm0CorrField (I := I) g₀ T 0 hδ hδZ s
        + (3 / 2 : ℝ) •
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
            (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)) =
        (fun s => linearizedRicciArm0Field (I := I) g₀ T 0 hδ hδZ s
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)) := by
      funext s
      rw [show linearizedRicciArm0Field (I := I) g₀ T 0 hδ hδZ s =
          linearizedRicciArm0BaseCoeff (I := I) g₀ T 0 hδ hδZ s
            + linearizedRicciArm0CorrField (I := I) g₀ T 0 hδ hδZ s from rfl]
      rw [show linearizedRicciArm0BaseCoeff (I := I) g₀ T 0 hδ hδZ s =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
              (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) from rfl]
      module
    rw [hfun]
    have hRmJ : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
        (fun s =>
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (δ := δ) (δ' := δ) :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff_realizedFam_jointContMDiff
        (I := I) (M := M) g₀ T 0 hδ hδZ
    exact linearizedRicciThreeArmHjoint_add_smul (I := I) (M := M) g₀ 2 (1 / 2 : ℝ) _ _
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T 0 hδ hδZ) hRmJ
  · intro s hs
    rw [appCc_add_left, hidRA s hs, hidLC s hs]
    try dsimp only
    rw [appCc_add_left, appCc_add_left]
    abel
  · intro s hs x
    try dsimp only
    have hadd := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2 (C0ra s) (C0lc s) x
    have h1 := hsupC0ra s hs x
    have h2 := hsupC0lc s hs x
    have h3 := sq_nonneg Λra
    rw [Real.sq_sqrt hsum_nn]
    linarith
  · intro s hs x
    have h := hsupRm s hs x
    have h2 := sq_nonneg Λra
    have h3 := sq_nonneg Λlc
    rw [Real.sq_sqrt hsum_nn]
    linarith
  · intro s hs x
    try dsimp only
    have hadd := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 4 2 (C2ra s) (C2lc s) x
    have h8 := hsupC2ra s hs x
    have h10 := hsupC2lc s hs x
    rcases le_or_gt 0 (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) with hu | hu
    · have e8 : max (8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 =
          8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
        max_eq_left (by nlinarith)
      have e10 : max (10 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 =
          10 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
        max_eq_left (by nlinarith)
      have e19 : max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 =
          19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
        max_eq_left (by nlinarith)
      rw [e19]
      rw [e8] at h8
      rw [e10] at h10
      nlinarith [hadd, h8, h10, hu,
        sq_nonneg (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)))]
    · have e8 : max (8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 = 0 :=
        max_eq_right (by nlinarith)
      have e10 : max (10 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 = 0 :=
        max_eq_right (by nlinarith)
      have e19 : max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 = 0 :=
        max_eq_right (by nlinarith)
      rw [e19]
      rw [e8] at h8
      rw [e10] at h10
      nlinarith [hadd, h8, h10]
  · intro i s hs
    try dsimp only
    have hadd := lc0b_normSq_icg_add_le (I := I) g₀ 2 2 i (C0ra s) (C0lc s)
    have h1 := henvC0ra i s hs
    have h2 := henvC0lc i s hs
    have hexp : (2 * Kra i + 2 * Klc i) * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) =
        2 * (Kra i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) +
        2 * (Klc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by ring
    rw [hexp]
    linarith
  · intro i s hs
    try dsimp only
    have hadd := lc0b_normSq_icg_add_le (I := I) g₀ 4 2 i (C2ra s) (C2lc s)
    have h1 := henvC2ra i s hs
    have h2 := henvC2lc i s hs
    have hexp : (2 * Kra i + 2 * Klc i) * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) =
        2 * (Kra i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) +
        2 * (Klc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by ring
    rw [hexp]
    linarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem sum_range_shift_two_sq_le (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (T₀ : SmoothCcTensor g₀ 0 2) :
    ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 2) T₀‖ ^ 2 ≤
      (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2 := by
  rw [Finset.sum_range_succ]
  have himg : ∑ q ∈ Finset.range i, ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 2) T₀‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
    set f : ℕ → ℝ := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 with hf_def
    have hinj : ∀ q₁ ∈ Finset.range i, ∀ q₂ ∈ Finset.range i, q₁ + 2 = q₂ + 2 → q₁ = q₂ :=
      fun q₁ _ q₂ _ h => by omega
    have hsub : (Finset.range i).image (fun q => q + 2) ⊆ Finset.range (i + 2) := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨q, hq, rfl⟩ := hj
      rw [Finset.mem_range] at hq ⊢
      omega
    calc ∑ q ∈ Finset.range i, f (q + 2)
        = ∑ j ∈ (Finset.range i).image (fun q => q + 2), f j :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ j ∈ Finset.range (i + 2), f j :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => sq_nonneg _)
  linarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

private theorem deTurckPhiZeroPathIntegral_zero_curvatureRefold_coeffSup_jetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧
    ∃ ε₀ : ℝ, 0 ≤ ε₀ ∧
      3 * Real.sqrt (Module.finrank ℝ E) * ε₀ ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ K₀c : ℕ → ℝ, (∀ i, 0 ≤ K₀c i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₂r : SmoothCcTensor g₀ 4 2),
          operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckPhiZeroPathIntegral (I := I) (M := M) g₀ g_bg T₀
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀)))
              (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) =
            operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂r (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ Λ₀ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂r.toSection x) ≤
              (max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
              K₀c i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                ε₀ ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂r‖ ^ 2 ≤
              K₀c i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨Cbr, hCbr_nn, hCbr⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (a + 2)
  have hR_nn : (0 : ℝ) ≤ Cbr * R₀ := mul_nonneg hCbr_nn hR₀
  have h13 : (1 : ℝ) / 3 < 1 := by norm_num
  obtain ⟨ΛC, hΛC_nn, hC0r⟩ :=
    uniform_C0_bound_concrete_lichnerowicz_coeffFields (I := I) (M := M) g₀ g_bg a
      ha_super hR_nn h13
  obtain ⟨Λrl, hΛrl_nn, Krl, hKrl_nn, hchild⟩ :=
    exists_riemannLieDerivativeCorrection_curvatureRefold_data (I := I) (M := M) g₀ g_bg a
      ha_super hR_nn h13 (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)
  obtain ⟨Kcb, hKcb_nn, ε, hε_nn, hε_cap, hKcb⟩ :=
    linearizedRicciArm0CorrField_allOrder_tameEnvelope_interface (I := I) (M := M) g₀ a
      ha_super hR_nn h13 (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)
  have hε₀_cap : 3 * Real.sqrt (Module.finrank ℝ E) * (3 * ε) ≤
      32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 := by
    have h23 : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
    have hcap18 : 18 * (Real.sqrt (Module.finrank ℝ E) * ε) ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) := by
      calc 18 * (Real.sqrt (Module.finrank ℝ E) * ε)
          = 27 * Real.sqrt (Module.finrank ℝ E) * ((1 : ℝ) - 1 / 3) * ε := by
            rw [h23]; ring
        _ ≤ 2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
            28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) := hε_cap
    calc 3 * Real.sqrt (Module.finrank ℝ E) * (3 * ε)
        = 9 * (Real.sqrt (Module.finrank ℝ E) * ε) := by ring
      _ ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 := by linarith
  refine ⟨Real.sqrt (8 * (2 * ΛC ^ 2 + 1 / 2 * Λrl ^ 2) + 4 * Λrl ^ 2), Real.sqrt_nonneg _,
    3 * ε, by linarith, hε₀_cap,
    fun i => (∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q)) + 8 * ε ^ 2,
    fun i => by
      have h1 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q) :=
        Finset.sum_nonneg fun q _ => by
          have h2 := hKcb_nn q
          have h3 := hKrl_nn q
          linarith
      have h4 : (0 : ℝ) ≤ 8 * ε ^ 2 := by positivity
      linarith, ?_⟩
  intro T₀ hsymm hball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hδT : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ :=
    hδ_fibre T₀ hball
  have hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ :=
    hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
      (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀)
  have hicg0 : ∀ j : ℕ,
      iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    intro j
    have h := iteratedCovGrad_smul' (I := I) g₀ 0 2 j (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2)
    rwa [zero_smul, zero_smul] at h
  have hTball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ Cbr * R₀ := by
    intro j hj
    have hCjT := hCbr T₀
    rw [show ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 by norm_cast] at hCjT
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        ∑ j' ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j' T₀‖ :=
      Finset.single_le_sum (f := fun j' => ‖iteratedCovGrad (I := I) g₀ 0 2 j' T₀‖)
        (fun j' _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    exact le_trans hsingle (le_trans hCjT (mul_le_mul_of_nonneg_left hball hCbr_nn))
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ Cbr * R₀ := by
    intro j _
    rw [hicg0 j, norm_zero]
    exact hR_nn
  have hpair : ∀ n : ℕ,
      (∑ j ∈ Finset.range n,
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ^ 2)) =
      ∑ j ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
    intro n
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hicg0 j, norm_zero]
    ring
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ)) := realizedSmallSet_isOpen
  obtain ⟨C0f, C2f, hjC0, hjC2, hjCombo, hids, hsupC0, hsupRm, hsupC2, henvC0, henvC2⟩ :=
    hchild T₀ hsymm hδ_le hδT hδZ hTball
  set Ψ₀ : ℝ → SmoothCcTensor g₀ 2 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s
      + (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) g_bg
        + lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) g_bg)
    with hΨ₀def
  have hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Ψ₀ (δ := δ) (δ' := δ) := by
    rw [hΨ₀def]
    exact deTurckPhiZero_jointSmooth_fw (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2) hδT hδZ
  have hc0 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₀ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Ψ₀
      (realizedSmallSet (δ := δ) (δ' := δ)) hj0 x
  set Φ₀ : ℝ → SmoothCcTensor g₀ 2 2 := fun s =>
    (-2 : ℝ) • (linearizedRicciArm0CorrField (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          hδT hδZ s
        + (3 / 2 : ℝ) •
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)
        - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
            (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s))
      + C0f s with hΦ₀def
  have hjΦ₀ : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
      (δ := δ) (δ' := δ) := by
    rw [hΦ₀def]
    exact threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 2 _ _ hjCombo hjC0
  have hcΦ : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Φ₀ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ)) hjΦ₀ x
  have hcC2 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((C2f t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 C2f
      (realizedSmallSet (δ := δ) (δ' := δ)) hjC2 x
  have hPi0 : deTurckPhiZeroPathIntegral (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀)) =
      pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Ψ₀
        (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj0 := rfl
  have halg : ∀ s : ℝ, Ψ₀ s =
      (-2 : ℝ) • (linearizedRicciArm0CorrField (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
            hδT hδZ s
          + (3 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
              (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s))
        + (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)
          + (deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) g_bg
            + lieCorr0Field (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) g_bg)) := by
    intro s
    simp only [hΨ₀def]
    rw [show linearizedRicciArm0Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s =
        linearizedRicciArm0BaseCoeff (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s
          + linearizedRicciArm0CorrField (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              hδT hδZ s from rfl]
    rw [show linearizedRicciArm0BaseCoeff (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          hδT hδZ s =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
            (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) from rfl]
    module
  refine ⟨pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjΦ₀,
    pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 C2f
      (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjC2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPi0]
    apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    rw [pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Ψ₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)
      (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj0 hc0 x v]
    rw [unitModel_add2_apply_tame]
    rw [pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Φ₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)
      (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjΦ₀ hcΦ x v]
    rw [pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 C2f
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)
      (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjC2 hcC2 x v]
    rw [← intervalIntegral.integral_add
      (threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 2 Φ₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) hSI hcΦ x v)
      (threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 4 C2f
        (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) hSI hcC2 x v)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    dsimp only
    have h1 : operatorFieldApply (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
        (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) =
        operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
          operatorFieldApply (I := I) (M := M) g₀ 4 2 (C2f s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) := by
      rw [halg s, appCc_add_left, hids s hs]
      simp only [hΦ₀def]
      rw [appCc_add_left]
      abel
    rw [h1, unitModel_add2_apply_tame]
  · intro x
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((Φ₀ t).toSection x)) ≤
          Real.sqrt (8 * (2 * ΛC ^ 2 + 1 / 2 * Λrl ^ 2) + 4 * Λrl ^ 2) := by
      intro t ht
      refine Real.sqrt_le_sqrt ?_
      have hΛrl_sq : (0 : ℝ) ≤ Λrl ^ 2 := sq_nonneg _
      have hadd1 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
        ((-2 : ℝ) • (linearizedRicciArm0CorrField (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
            hδT hδZ t
          + (3 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
              (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)))
        (C0f t) x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (((-2 : ℝ) • (linearizedRicciArm0CorrField (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t
            + (3 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t))).toSection
            x) =
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0CorrField (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t
              + (3 / 2 : ℝ) •
                DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                  (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                  (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)).toSection
              x) := by
        rw [show (((-2 : ℝ) • (linearizedRicciArm0CorrField (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t
            + (3 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t))).toSection
              x) =
            (-2 : ℝ) • ((linearizedRicciArm0CorrField (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t
              + (3 / 2 : ℝ) •
                DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                  (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                  (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)).toSection
                x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hcombo_eq : linearizedRicciArm0CorrField (I := I) g₀ T₀
            (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t
          + (3 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
              (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t) =
          linearizedRicciArm0Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t
            + (1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t) := by
        rw [show linearizedRicciArm0Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              hδT hδZ t =
            linearizedRicciArm0BaseCoeff (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                hδT hδZ t
              + linearizedRicciArm0CorrField (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                hδT hδZ t from rfl]
        rw [show linearizedRicciArm0BaseCoeff (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              hδT hδZ t =
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t) from rfl]
        module
      have hcombo_split : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((linearizedRicciArm0CorrField (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t
            + (3 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t)).toSection
            x) ≤
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              hδT hδZ t).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            (((1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  hδT hδZ t)).toSection x) := by
        rw [hcombo_eq]
        exact lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2 _ _ x
      have hsm2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (((1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                hδT hδZ t)).toSection x) =
          1 / 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                hδT hδZ t)).toSection x) := by
        rw [show (((1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  hδT hδZ t)).toSection x) =
            (1 / 2 : ℝ) •
              ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  hδT hδZ t)).toSection x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hArm0 := sq_bound_of_sqrt_le_fw
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _)
        ((hC0r T₀ (0 : SmoothCcTensor g₀ 0 2) hδ_le hδT hδ_le hδZ hTball hZball t ht x).1)
      have hRm := hsupRm t ht x
      have hC0fb := hsupC0 t ht x
      simp only [hΦ₀def]
      linarith [hadd1, hsm, hcombo_split, hsm2, hArm0, hRm, hC0fb]
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M)
      g₀ 2 2 Φ₀ (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjΦ₀ x
      (Real.sqrt (8 * (2 * ΛC ^ 2 + 1 / 2 * Λrl ^ 2) + 4 * Λrl ^ 2)) (Real.sqrt_nonneg _)
      ((hcΦ x).mono (Icc_subset_realizedSmallSet hδ_lt hδ_lt)) hsup
  · intro x
    have hb_nn : (0 : ℝ) ≤
        max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 :=
      le_max_right _ _
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((C2f t).toSection x)) ≤
          max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 := by
      intro t ht
      have h := hsupC2 t ht x
      calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((C2f t).toSection x))
          ≤ Real.sqrt ((max (19 * deTurckArmFibreConst (Module.finrank ℝ E) *
              (δ / (1 - δ))) 0) ^ 2) := Real.sqrt_le_sqrt h
        _ = max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 :=
            Real.sqrt_sq hb_nn
    have hPIle := riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M)
      g₀ 4 2 C2f (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjC2 x
      (max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) hb_nn
      ((hcC2 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ_lt)) hsup
    refine le_trans hPIle ?_
    refine pow_le_pow_left₀ hb_nn ?_ 2
    refine max_le ?_ (le_max_right _ _)
    rcases le_or_gt 0 (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) with h | h
    · calc 19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))
          = 19 * (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) := by ring
        _ ≤ 19 * (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) := by linarith
        _ = 19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) := by ring
        _ ≤ max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 :=
            le_max_left _ _
    · calc 19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))
          = 19 * (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) := by ring
        _ ≤ 0 := by linarith
        _ ≤ max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0 :=
            le_max_right _ _
  · intro i
    have hW_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have hs_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith
    have hKS_nn : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q) :=
      Finset.sum_nonneg fun q _ => by
        have h1 := hKcb_nn q
        have h2 := hKrl_nn q
        linarith
    have hX_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2 := sq_nonneg _
    have htotal_nn : (0 : ℝ) ≤
        ((∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q)) + 8 * ε ^ 2) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
          (3 * ε) ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2 := by
      have h8 : (0 : ℝ) ≤ 8 * ε ^ 2 := by positivity
      have h9 : (0 : ℝ) ≤ (3 * ε) ^ 2 := sq_nonneg _
      have h10 := mul_nonneg (add_nonneg hKS_nn h8) hW_nn
      nlinarith [mul_nonneg h9 hX_nn]
    have hwin : ∀ q : ℕ, q ≤ i →
        (1 : ℝ) + (∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      intro q hq
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega : q + 2 ≤ i + 2))
        (fun j _ _ => sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖))
      linarith
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 q (Φ₀ s)‖ ^ 2) ≤
        Real.sqrt (((∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q)) + 8 * ε ^ 2) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
          (3 * ε) ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt htotal_nn]
      have hper : ∀ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 q (Φ₀ s)‖ ^ 2 ≤
            (8 * Kcb q + 3 * Krl q) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              8 * ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 2) T₀‖ ^ 2 := by
        intro q hq
        have hq_le : q ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
        have hcomboE := hKcb T₀ (0 : SmoothCcTensor g₀ 0 2) hδ_le hδT hδ_le hδZ
          hTball hZball q s hs
        rw [hpair (q + 2)] at hcomboE
        have hz : ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 2)
            (0 : SmoothCcTensor g₀ 0 2)‖ = 0 := by
          rw [hicg0 (q + 2), norm_zero]
        rw [hz] at hcomboE
        have hcomboW := mul_le_mul_of_nonneg_left (hwin q hq_le) (hKcb_nn q)
        have hC0E := henvC0 q s hs
        have hC0E' := le_trans hC0E
          (mul_le_mul_of_nonneg_left (hwin q hq_le) (hKrl_nn q))
        have h1 : ‖iteratedCovGrad (I := I) g₀ 2 2 q (Φ₀ s)‖ ^ 2 ≤
            2 * ‖iteratedCovGrad (I := I) g₀ 2 2 q
              ((-2 : ℝ) • (linearizedRicciArm0CorrField (I := I) g₀ T₀
                  (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s
                + (3 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)
                - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                    (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)))‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 2 2 q (C0f s)‖ ^ 2 := by
          simp only [hΦ₀def]
          exact lc0b_normSq_icg_add_le (I := I) g₀ 2 2 q _ _
        have h2 : ‖iteratedCovGrad (I := I) g₀ 2 2 q
            ((-2 : ℝ) • (linearizedRicciArm0CorrField (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s
              + (3 / 2 : ℝ) •
                DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                  (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                  (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)))‖ ^ 2 =
            4 * ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (linearizedRicciArm0CorrField (I := I) g₀ T₀
                  (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s
                + (3 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)
                - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                    (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s))‖ ^ 2 := by
          rw [iteratedCovGrad_smul', norm_smul,
            show ‖(-2 : ℝ)‖ = 2 from by rw [Real.norm_eq_abs]; norm_num]
          ring
        have hslack : (0 : ℝ) ≤ Krl q * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
          mul_nonneg (hKrl_nn q) hW_nn
        have hexp : (8 * Kcb q + 3 * Krl q) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
            8 * ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 2) T₀‖ ^ 2 =
            8 * (Kcb q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) +
            2 * (Krl q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) +
            Krl q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
            8 * (ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 2) T₀‖ ^ 2) := by ring
        rw [hexp]
        linarith [h1, h2, hcomboE, hcomboW, hC0E', hslack]
      have hsum1 := Finset.sum_le_sum hper
      have hsum2 : ∑ q ∈ Finset.range (i + 1),
            ((8 * Kcb q + 3 * Krl q) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              8 * ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 2) T₀‖ ^ 2) =
          (∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q)) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
            8 * ε ^ 2 * ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 (q + 2) T₀‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      have hshift := sum_range_shift_two_sq_le (I := I) (M := M) g₀ i T₀
      have hmul8 := mul_le_mul_of_nonneg_left hshift
        (by positivity : (0 : ℝ) ≤ 8 * ε ^ 2)
      have hstep := le_trans hsum1 (le_of_eq hsum2)
      nlinarith [hstep, hmul8, mul_nonneg (sq_nonneg ε) hX_nn, sq_nonneg ε, hW_nn]
    have htower := pathIntegralCoeffField_jetL2_tower_le (I := I) (M := M) g₀ 2 i Φ₀
      hSI hSopen hjΦ₀ (Real.sqrt_nonneg _) hjet
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Φ₀
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjΦ₀)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 q
          (pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Φ₀
            (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjΦ₀)‖ ^ 2 :=
      Finset.single_le_sum (f := fun q => ‖iteratedCovGrad (I := I) g₀ 2 2 q
        (pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Φ₀
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjΦ₀)‖ ^ 2)
        (fun q _ => sq_nonneg _) (Finset.self_mem_range_succ i)
    have hfin := le_trans hsingle htower
    rw [Real.sq_sqrt htotal_nn] at hfin
    exact hfin
  · intro i
    have hW_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have hs_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith
    have hKS_nn : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q) :=
      Finset.sum_nonneg fun q _ => by
        have h1 := hKcb_nn q
        have h2 := hKrl_nn q
        linarith
    have hε8_nn : (0 : ℝ) ≤ 8 * ε ^ 2 := by positivity
    have hprod_nn : (0 : ℝ) ≤
        ((∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q)) + 8 * ε ^ 2) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
      mul_nonneg (add_nonneg hKS_nn hε8_nn) hW_nn
    have hwin : ∀ q : ℕ, q ≤ i →
        (1 : ℝ) + (∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      intro q hq
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega : q + 2 ≤ i + 2))
        (fun j _ _ => sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖))
      linarith
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 q (C2f s)‖ ^ 2) ≤
        Real.sqrt (((∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q)) + 8 * ε ^ 2) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hprod_nn]
      have hper : ∀ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 q (C2f s)‖ ^ 2 ≤
            (8 * Kcb q + 3 * Krl q) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
        intro q hq
        have hq_le : q ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
        have hC2E := henvC2 q s hs
        have hC2E' := le_trans hC2E
          (mul_le_mul_of_nonneg_left (hwin q hq_le) (hKrl_nn q))
        have hslack : (0 : ℝ) ≤ Kcb q * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
          mul_nonneg (hKcb_nn q) hW_nn
        have hslack2 : (0 : ℝ) ≤ Krl q * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
          mul_nonneg (hKrl_nn q) hW_nn
        have hexp : (8 * Kcb q + 3 * Krl q) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) =
            8 * (Kcb q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) +
            2 * (Krl q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) +
            Krl q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by ring
        rw [hexp]
        linarith [hC2E', hslack, hslack2]
      calc (∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 q (C2f s)‖ ^ 2)
          ≤ ∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
            Finset.sum_le_sum hper
        _ = (∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q)) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
            rw [Finset.sum_mul]
        _ ≤ ((∑ q ∈ Finset.range (i + 1), (8 * Kcb q + 3 * Krl q)) + 8 * ε ^ 2) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hW_nn
            linarith
    have htower := pathIntegralCoeffField_jetL2_tower_le (I := I) (M := M) g₀ 4 i C2f
      hSI hSopen hjC2 (Real.sqrt_nonneg _) hjet
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 C2f
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjC2)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 q
          (pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 C2f
            (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjC2)‖ ^ 2 :=
      Finset.single_le_sum (f := fun q => ‖iteratedCovGrad (I := I) g₀ 4 2 q
        (pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 C2f
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hjC2)‖ ^ 2)
        (fun q _ => sq_nonneg _) (Finset.self_mem_range_succ i)
    have hfin := le_trans hsingle htower
    rw [Real.sq_sqrt hprod_nn] at hfin
    exact hfin

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem deTurckPhiOnePathIntegral_zero_coeffSup_jetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Λ₁' : ℝ, 0 ≤ Λ₁' ∧
    ∃ K₁c : ℕ → ℝ, (∀ i, 0 ≤ K₁c i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckPhiOnePathIntegral (I := I) (M := M) g₀ g_bg T₀
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀
                    ((a : ℝ) + 2) hR₀))).toSection x) ≤ Λ₁' ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckPhiOnePathIntegral (I := I) (M := M) g₀ g_bg T₀
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀
                    ((a : ℝ) + 2) hR₀)))‖ ^ 2 ≤
              K₁c i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨Cbr, hCbr_nn, hCbr⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (a + 2)
  have hR_nn : (0 : ℝ) ≤ Cbr * R₀ := mul_nonneg hCbr_nn hR₀
  have h13 : (1 : ℝ) / 3 < 1 := by norm_num
  obtain ⟨ΛCr, hΛCr_nn, hC0r⟩ :=
    uniform_C0_bound_concrete_lichnerowicz_coeffFields (I := I) (M := M) g₀ g_bg a
      ha_super hR_nn h13
  obtain ⟨ΛL1, hΛL1_nn, hL1r⟩ :=
    deTurckLieArm1Coeff_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR_nn h13
  obtain ⟨KB, hKB_nn, hKB⟩ :=
    linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_tameEnvelope (I := I) (M := M)
      g₀ a ha_super hR_nn h13
  obtain ⟨KL, hKL_nn, hKL⟩ :=
    deTurckLieArm1Coeff_realizedFam_allOrder_tameEnvelope (I := I) (M := M) g₀ g_bg a
      ha_super hR_nn h13
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    linearizedRicciArm1CorrField_allOrder_tameEnvelope_interface (I := I) (M := M) g₀ a
      ha_super hR_nn h13
  refine ⟨Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1), Real.sqrt_nonneg _,
    fun i => ∑ q ∈ Finset.range (i + 1), (16 * KB q + 16 * KC q + 2 * KL q),
    fun i => Finset.sum_nonneg fun q _ => by
      have h1 := hKB_nn q
      have h2 := hKC_nn q
      have h3 := hKL_nn q
      linarith, ?_⟩
  intro T₀ hsymm hball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hδT : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ :=
    hδ_fibre T₀ hball
  have hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ :=
    hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
      (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀)
  have hicg0 : ∀ j : ℕ,
      iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    intro j
    have h := iteratedCovGrad_smul' (I := I) g₀ 0 2 j (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2)
    rwa [zero_smul, zero_smul] at h
  have hTball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ Cbr * R₀ := by
    intro j hj
    have hCjT := hCbr T₀
    rw [show ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 by norm_cast] at hCjT
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        ∑ j' ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j' T₀‖ :=
      Finset.single_le_sum (f := fun j' => ‖iteratedCovGrad (I := I) g₀ 0 2 j' T₀‖)
        (fun j' _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    exact le_trans hsingle (le_trans hCjT (mul_le_mul_of_nonneg_left hball hCbr_nn))
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ Cbr * R₀ := by
    intro j _
    rw [hicg0 j, norm_zero]
    exact hR_nn
  have hpair : ∀ n : ℕ,
      (∑ j ∈ Finset.range n,
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ^ 2)) =
      ∑ j ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
    intro n
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hicg0 j, norm_zero]
    ring
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ)) := realizedSmallSet_isOpen
  set Ψ₁ : ℝ → SmoothCcTensor g₀ 3 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s
      + deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) g_bg
    with hΨ₁def
  have hj1 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Ψ₁ (δ := δ) (δ' := δ) := by
    rw [hΨ₁def]
    exact deTurckPhiOne_jointSmooth_fw (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2) hδT hδZ
  have hc1 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₁ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Ψ₁
      (realizedSmallSet (δ := δ) (δ' := δ)) hj1 x
  have hPi1 : deTurckPhiOnePathIntegral (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀)) =
      pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
        (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj1 := rfl
  rw [hPi1]
  refine ⟨?_, ?_⟩
  · intro x
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Ψ₁ t).toSection x)) ≤
          Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1) := by
      intro t ht
      refine Real.sqrt_le_sqrt ?_
      simp only [hΨ₁def]
      have hadd := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 3 2
        ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          hδT hδZ t)
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t) g_bg) x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          (((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
            hδT hδZ t).toSection x) =
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              hδT hδZ t).toSection x) := by
        rw [show (((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T₀
            (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t).toSection x) =
            (-2 : ℝ) • ((linearizedRicciArm1Field (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t).toSection x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hRb := sq_bound_of_sqrt_le_fw
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 2 x _)
        ((hC0r T₀ (0 : SmoothCcTensor g₀ 0 2) hδ_le hδT hδ_le hδZ hTball hZball
          t ht x).2.1)
      have hL1 := hL1r T₀ (0 : SmoothCcTensor g₀ 0 2) hδ_le hδT hδ_le hδZ hTball hZball
        t ht x
      linarith
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M)
      g₀ 3 2 Ψ₁ (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj1 x
      (Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1)) (Real.sqrt_nonneg _)
      ((hc1 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ_lt)) hsup
  · intro i
    have hW_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have hs_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      linarith
    have hKS_nn : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1),
        (16 * KB q + 16 * KC q + 2 * KL q) :=
      Finset.sum_nonneg fun q _ => by
        have h1 := hKB_nn q
        have h2 := hKC_nn q
        have h3 := hKL_nn q
        linarith
    have hprod_nn : (0 : ℝ) ≤ (∑ q ∈ Finset.range (i + 1),
        (16 * KB q + 16 * KC q + 2 * KL q)) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := mul_nonneg hKS_nn hW_nn
    have hwin : ∀ q : ℕ, q ≤ i →
        (1 : ℝ) + (∑ j ∈ Finset.range (q + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      intro q hq
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega : q + 2 ≤ i + 2))
        (fun j _ _ => sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖))
      linarith
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 2 q (Ψ₁ s)‖ ^ 2) ≤
        Real.sqrt ((∑ q ∈ Finset.range (i + 1), (16 * KB q + 16 * KC q + 2 * KL q)) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hprod_nn]
      have hper : ∀ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 2 q (Ψ₁ s)‖ ^ 2 ≤
            (16 * KB q + 16 * KC q + 2 * KL q) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
        intro q hq
        have hq_le : q ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
        have hbase := hKB T₀ (0 : SmoothCcTensor g₀ 0 2) hδ_le hδT hδ_le hδZ
          hTball hZball q s hs
        rw [hpair (q + 2)] at hbase
        have hbase' := le_trans hbase
          (mul_le_mul_of_nonneg_left (hwin q hq_le) (hKB_nn q))
        have hlie := hKL T₀ (0 : SmoothCcTensor g₀ 0 2) hδ_le hδT hδ_le hδZ
          hTball hZball q s hs
        rw [hpair (q + 2)] at hlie
        have hlie' := le_trans hlie
          (mul_le_mul_of_nonneg_left (hwin q hq_le) (hKL_nn q))
        have hcorr := hKC T₀ (0 : SmoothCcTensor g₀ 0 2) hδ_le hδT hδ_le hδZ
          hTball hZball q s hs
        rw [hpair (q + 2)] at hcorr
        have hcorr' := le_trans hcorr
          (mul_le_mul_of_nonneg_left (hwin q hq_le) (hKC_nn q))
        have h1 : ‖iteratedCovGrad (I := I) g₀ 3 2 q (Ψ₁ s)‖ ^ 2 ≤
            2 * ‖iteratedCovGrad (I := I) g₀ 3 2 q
              ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 3 2 q
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)
                g_bg)‖ ^ 2 := by
          simp only [hΨ₁def]
          exact lc0b_normSq_icg_add_le (I := I) g₀ 3 2 q _ _
        have h2 : ‖iteratedCovGrad (I := I) g₀ 3 2 q
            ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)‖ ^ 2 =
            4 * ‖iteratedCovGrad (I := I) g₀ 3 2 q
              (linearizedRicciArm1Field (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)‖ ^ 2 := by
          rw [iteratedCovGrad_smul', norm_smul,
            show ‖(-2 : ℝ)‖ = 2 from by rw [Real.norm_eq_abs]; norm_num]
          ring
        have h3 : ‖iteratedCovGrad (I := I) g₀ 3 2 q
            (linearizedRicciArm1Field (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)‖ ^ 2 ≤
            2 * ‖iteratedCovGrad (I := I) g₀ 3 2 q
              (linearizedRicciArm1BaseCoeff (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 3 2 q
              (linearizedRicciArm1CorrField (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s)‖ ^ 2 := by
          rw [show linearizedRicciArm1Field (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s =
              linearizedRicciArm1BaseCoeff (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s +
              linearizedRicciArm1CorrField (I := I) g₀ T₀
                (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s from rfl]
          exact lc0b_normSq_icg_add_le (I := I) g₀ 3 2 q _ _
        have hexp : (16 * KB q + 16 * KC q + 2 * KL q) *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) =
            16 * (KB q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) +
            16 * (KC q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) +
            2 * (KL q * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by ring
        rw [hexp]
        linarith
      calc (∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 2 q (Ψ₁ s)‖ ^ 2)
          ≤ ∑ q ∈ Finset.range (i + 1), (16 * KB q + 16 * KC q + 2 * KL q) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
            Finset.sum_le_sum hper
        _ = (∑ q ∈ Finset.range (i + 1), (16 * KB q + 16 * KC q + 2 * KL q)) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
            rw [Finset.sum_mul]
    have htower := pathIntegralCoeffField_jetL2_tower_le (I := I) (M := M) g₀ 3 i Ψ₁
      hSI hSopen hj1 (Real.sqrt_nonneg _) hjet
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj1)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 q
          (pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
            (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj1)‖ ^ 2 :=
      Finset.single_le_sum (f := fun q => ‖iteratedCovGrad (I := I) g₀ 3 2 q
        (pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj1)‖ ^ 2)
        (fun q _ => sq_nonneg _) (Finset.self_mem_range_succ i)
    have hfin := le_trans hsingle htower
    rw [Real.sq_sqrt hprod_nn] at hfin
    exact hfin

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_deTurckRHSArmDiff_zero_canonicalTop_curvatureRefold_coeffSup_jetEnvelope_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCr : ℝ, 0 ≤ εCr ∧
      (0 ≤ δ → εCr ≤ 19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εar : ℝ, 0 ≤ εar ∧
      3 * Real.sqrt (Module.finrank ℝ E) * εar ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λ₁ : ℝ, 0 ≤ Λ₁ ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (C₁ : SmoothCcTensor g₀ (2 + 1) 2)
          (C₂r : SmoothCcTensor g₀ (2 + 2) 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
              deTurckRHSArmG0 (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀))) =
            operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀)))
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂r (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λ₁ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) 2 x (C₁.toSection x) ≤ Λ₁ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂r.toSection x) ≤
              εCr ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εar ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 1) 2 i C₁‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂r‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨Λ₀, hΛ₀_nn, ε₀, hε₀_nn, hε₀_cap, K₀c, hK₀c_nn, hN2⟩ :=
    deTurckPhiZeroPathIntegral_zero_curvatureRefold_coeffSup_jetEnvelope (I := I) (M := M)
      g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Λ₁', hΛ₁'_nn, K₁c, hK₁c_nn, hN3⟩ :=
    deTurckPhiOnePathIntegral_zero_coeffSup_jetEnvelope (I := I) (M := M)
      g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨max (19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0,
    le_max_right _ _, ?_, fun i => K₀c i + K₁c i,
    fun i => add_nonneg (hK₀c_nn i) (hK₁c_nn i), ε₀, hε₀_nn, hε₀_cap, max Λ₀ Λ₁',
    le_trans hΛ₀_nn (le_max_left _ _), ?_⟩
  · intro hδ_nn
    refine max_le (le_refl _) ?_
    have hfc : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) := Real.sqrt_nonneg _
    have hκ : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    positivity
  · intro T₀ hT₀symm hball
    have hzsymm : ∀ (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x v w =
          smoothCcTensorBilinForm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x w v :=
      ccTensorBilin_zero_symm_fw (I := I) (M := M) g₀
    obtain ⟨C₀dd, C₂r, hrefold, hC₀sup, hC₂rsup, hC₀env, hC₂renv⟩ := hN2 T₀ hT₀symm hball
    obtain ⟨hC₁sup, hC₁env⟩ := hN3 T₀ hT₀symm hball
    have hN1 := deTurckRHSArmDiff_eq_pathIntegralCoeff_triple_of_symm (I := I) (M := M)
      g₀ g_bg T₀ (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀))
      hT₀symm hzsymm
    rw [sub_zero] at hN1
    rw [hrefold] at hN1
    refine ⟨C₀dd,
      deTurckPhiOnePathIntegral (I := I) (M := M) g₀ g_bg T₀ (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (smoothCcToTensorHs_zero_norm_le_fw (I := I) (M := M) g₀ ((a : ℝ) + 2) hR₀)),
      C₂r, ?_, ?_, ?_, hC₂rsup, ?_, ?_, ?_⟩
    · rw [hN1]
      abel
    · intro x
      exact le_trans (hC₀sup x)
        (pow_le_pow_left₀ hΛ₀_nn (le_max_left _ _) 2)
    · intro x
      exact le_trans (hC₁sup x)
        (pow_le_pow_left₀ hΛ₁'_nn (le_max_right _ _) 2)
    · intro i
      refine le_trans (hC₀env i) ?_
      have hsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by positivity
      have hle : K₀c i ≤ K₀c i + K₁c i := le_add_of_nonneg_right (hK₁c_nn i)
      have hmono := mul_le_mul_of_nonneg_right hle hsum_nn
      linarith
    · intro i
      refine le_trans (hC₁env i) ?_
      have hsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by positivity
      have hle : K₁c i ≤ K₀c i + K₁c i := le_add_of_nonneg_left (hK₀c_nn i)
      exact mul_le_mul_of_nonneg_right hle hsum_nn
    · intro i
      refine le_trans (hC₂renv i) ?_
      have hsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by positivity
      have hle : K₀c i ≤ K₀c i + K₁c i := le_add_of_nonneg_right (hK₁c_nn i)
      exact mul_le_mul_of_nonneg_right hle hsum_nn

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
