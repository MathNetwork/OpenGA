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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem)

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b1_rfns_neg (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  have h := b1_rfns_smul_value (I := I) (M := M) g r s x (-1) v
  rw [neg_one_smul] at h
  rw [h]
  norm_num

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b1_sqrt_rfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (a - b)) ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x a)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x b) := by
  rw [sub_eq_add_neg]
  refine le_trans (b1_sqrt_rfns_add_le (I := I) (M := M) g r s x a (-b)) ?_
  rw [b1_rfns_neg (I := I) (M := M) g r s x b]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma k1_unitModel_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
        (A + B) x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
          A x +
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
          B x := by
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma k1_unitModel_smul (g : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (A : SmoothCcTensor g 0 s) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
        (c • A) x =
      c • DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
        g s A x := by
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma k1_domDomCongr_add {d : ℕ} (σ : Equiv.Perm (Fin d))
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (f + g) =
      ContinuousMultilinearMap.domDomCongr σ f + ContinuousMultilinearMap.domDomCongr σ g := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.add_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma k1_domDomCongr_smul {d : ℕ} (σ : Equiv.Perm (Fin d)) (c : ℝ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (c • f) =
      c • ContinuousMultilinearMap.domDomCongr σ f := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.smul_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k1_domDomCongrSection_add (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A + B) =
      domDomCongrSection (I := I) g σ A + domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    k1_unitModel_add (I := I) (M := M) g s A B x, k1_domDomCongr_add,
    k1_unitModel_add (I := I) (M := M) g s
      (domDomCongrSection (I := I) g σ A) (domDomCongrSection (I := I) g σ B) x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k1_domDomCongrSection_smul (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (c : ℝ) (A : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (c • A) =
      c • domDomCongrSection (I := I) g σ A := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    k1_unitModel_smul (I := I) (M := M) g s c A x, k1_domDomCongr_smul,
    k1_unitModel_smul (I := I) (M := M) g s c (domDomCongrSection (I := I) g σ A) x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k1_domDomCongrSection_comp (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ τ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (domDomCongrSection (I := I) g τ S) =
      domDomCongrSection (I := I) g (τ.trans σ) S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k1_domDomCongrSection_refl (g : SmoothRiemannianMetric I M) {s : ℕ}
    (S : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g (Equiv.refl (Fin s)) S = S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k1_symmS_eq_half (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ T =
      (1 / 2 : ℝ) • T +
        (1 / 2 : ℝ) • domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T := by
  have h := iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T 0
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k1_domDomCongrSection_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (ccTensor02Symm (I := I) (M := M) g₀ T) =
      ccTensor02Symm (I := I) (M := M) g₀ T := by
  conv_lhs => rw [k1_symmS_eq_half (I := I) (M := M) g₀ T]
  rw [k1_domDomCongrSection_add (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1),
    k1_domDomCongrSection_smul (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1) (1 / 2) T,
    k1_domDomCongrSection_smul (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1) (1 / 2)
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T),
    k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1)
      (Equiv.swap (0 : Fin 2) 1) T,
    show (Equiv.swap (0 : Fin 2) 1).trans (Equiv.swap (0 : Fin 2) 1) =
      Equiv.refl (Fin 2) from by decide,
    k1_domDomCongrSection_refl (I := I) (M := M) g₀ T,
    k1_symmS_eq_half (I := I) (M := M) g₀ T]
  abel

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k1_zeroTensor_eq_smul_unitTensor (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) •
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x := by
  classical
  have hunit : Tensor0SNabla.tensor0Iso I M x
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x) =
      (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k1_symmS_toModel_rel (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ∀ (y : M) (d : Tensor0SBundle.Tensor0SSpace 0 I y),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
            (ccTensor02Symm (I := I) (M := M) g₀ T).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
              (ccTensor02Symm (I := I) (M := M) g₀ T).toSection y) d)) := by
  intro y d
  have hunit : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I)
      (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) y =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
          g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) y) := by
    conv_lhs => rw [← k1_domDomCongrSection_symmS (I := I) (M := M) g₀ T]
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
  rw [k1_zeroTensor_eq_smul_unitTensor (I := I) (M := M) y d]
  rw [ContinuousLinearMap.map_smul, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    k1_domDomCongr_smul]
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel] at hunit
  rw [← hunit]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k1_symmSCovGrad3_swap12 (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3 (I := I) g₀ T) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3 (I := I) g₀ T := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hnat := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_rs_toModel_domDomCongr
    (I := I) (M := M) g₀ 0 2 (Equiv.swap (0 : Fin 2) 1)
    (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T)
    (k1_symmS_toModel_rel (I := I) (M := M) g₀ T) x
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x) v
  rw [show Equiv.Perm.decomposeFin.symm ((0 : Fin 3), Equiv.swap (0 : Fin 2) 1) =
    Equiv.swap (1 : Fin 3) 2 from by decide] at hnat
  rw [ContinuousMultilinearMap.domDomCongr_apply] at hnat
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3_def]
  exact hnat.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma k1_rfns_add_expand (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b) =
      riemannianFiberNormSq (I := I) (M := M) g r s x a
        + riemannianFiberNormSq (I := I) (M := M) g r s x b
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b) := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (a + b),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a,
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b]
  rw [TensorRSSpace.toModel_add]
  rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right]
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x
      (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) a) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b) from
    tensorInnerPointwise_symm (I := I) (M := M) g r s x _ _]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k1_rfns_addadd_expand (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b c : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b + c) =
      riemannianFiberNormSq (I := I) (M := M) g r s x a
        + riemannianFiberNormSq (I := I) (M := M) g r s x b
        + riemannianFiberNormSq (I := I) (M := M) g r s x c
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b)
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) c)
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) c) := by
  rw [k1_rfns_add_expand (I := I) (M := M) g r s x (a + b) c,
    k1_rfns_add_expand (I := I) (M := M) g r s x a b]
  rw [TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k1_rfns_addsub_expand (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b c : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b - c) =
      riemannianFiberNormSq (I := I) (M := M) g r s x a
        + riemannianFiberNormSq (I := I) (M := M) g r s x b
        + riemannianFiberNormSq (I := I) (M := M) g r s x c
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b)
        - 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) c)
        - 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) c) := by
  have hsub : a + b - c = a + b + (-1 : ℝ) • c := by
    rw [neg_one_smul]
    abel
  rw [hsub]
  rw [k1_rfns_addadd_expand (I := I) (M := M) g r s x a b ((-1 : ℝ) • c)]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_right,
    tensorInnerPointwise_smul_right]
  rw [show riemannianFiberNormSq (I := I) (M := M) g r s x ((-1 : ℝ) • c) =
      riemannianFiberNormSq (I := I) (M := M) g r s x c from by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x ((-1 : ℝ) • c),
      riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x c,
      TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]
    ring]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_koszulCovecCc_le_iteratedCovGrad_symmetrization_succ (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (u : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc
            (I := I) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (u + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (u + 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) := by
  classical
  set B : SmoothCcTensor g₀ 0 3 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3 (I := I) g₀ T
    with hB_def
  have hπ : domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) B = B :=
    k1_symmSCovGrad3_swap12 (I := I) (M := M) g₀ T
  have hkC : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc
      (I := I) g₀ T =
      (1 / 2 : ℝ) •
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B
          + domDomCongrSection (I := I) g₀ (finRotate 3) B
          - B) := by
    have h0 : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc
        (I := I) g₀ T =
        (1 / 2 : ℝ) •
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B
            + domDomCongrSection (I := I) g₀ (finRotate 3) B
            - domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) B) := rfl
    rw [h0, hπ]
  have hE : domDomCongrSection (I := I) g₀ (finRotate 3) B =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B := by
    rw [show (finRotate 3) =
      (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1) from by decide]
    rw [← k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 1)
      (Equiv.swap (1 : Fin 3) 2) B]
    rw [hπ]
  have hab_sec : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B
        + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B := by
    rw [k1_domDomCongrSection_add (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2) B
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)]
    rw [k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2)
      (Equiv.swap (0 : Fin 3) 1) B]
    rw [show (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (0 : Fin 3) 2) =
      finRotate 3 from by decide]
    rw [hE]
  have hbc_sec : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B + B := by
    rw [k1_domDomCongrSection_add (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 1) B
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)]
    rw [k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 1)
      (Equiv.swap (0 : Fin 3) 1) B]
    rw [show (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (0 : Fin 3) 1) =
      Equiv.refl (Fin 3) from by decide]
    rw [k1_domDomCongrSection_refl (I := I) (M := M) g₀ B]
  have hac_sec : domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) =
      B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B := by
    rw [k1_domDomCongrSection_add (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2) B
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)]
    rw [hπ]
    rw [k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2)
      (Equiv.swap (0 : Fin 3) 1) B]
    rw [show (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2) =
      (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 2) from by decide]
    rw [← k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2)
      (Equiv.swap (1 : Fin 3) 2) B]
    rw [hπ]
  rw [hkC]
  rw [b1_iteratedCovGrad_smul (I := I) (M := M) g₀ 0 3 u]
  rw [iteratedCovGrad_sub (I := I) g₀ 0 3 u, iteratedCovGrad_add (I := I) g₀ 0 3 u]
  rw [b1_toSection_smul (I := I) (M := M) g₀ 0 (3 + u)]
  rw [b1_rfns_smul_value (I := I) (M := M) g₀ 0 (3 + u) x (1 / 2)]
  rw [b1_toSection_sub (I := I) (M := M) g₀ 0 (3 + u), b1_toSection_add (I := I) (M := M) g₀ 0 (3 + u)]
  rw [hE]
  have hexp := k1_rfns_addsub_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have habc := k1_rfns_addadd_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have hpos := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
      + (iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x
      + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have e_ab := k1_rfns_add_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x)
  have e_bc := k1_rfns_add_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have e_ac := k1_rfns_add_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have f1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 2) B u x
  have f2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 1) B u x
  have g_ab : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u
          (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 3 u
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B
            + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x from by
      rw [iteratedCovGrad_add (I := I) g₀ 0 3 u,
        b1_toSection_add (I := I) (M := M) g₀ 0 (3 + u)]]
    rw [← hab_sec]
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 2)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) u x
  have g_bc : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u
          (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 3 u
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B + B)).toSection x from by
      rw [iteratedCovGrad_add (I := I) g₀ 0 3 u,
        b1_toSection_add (I := I) (M := M) g₀ 0 (3 + u)]]
    rw [← hbc_sec]
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 1)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) u x
  have g_ac : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u
          (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 3 u
          (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x from by
      rw [iteratedCovGrad_add (I := I) g₀ 0 3 u,
        b1_toSection_add (I := I) (M := M) g₀ 0 (3 + u)]
      exact add_comm _ _]
    rw [← hac_sec]
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 3) 2)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) u x
  have hNval : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (u + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (u + 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) := by
    have hS3cov : B = iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ T) := by
      rw [hB_def]
      rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3_def]
      rw [iteratedCovGrad_succ (I := I) g₀ 0 2 0, iteratedCovGrad_zero (I := I) g₀ 0 2]
    rw [hS3cov]
    have hcomp := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 1 u
      (ccTensor02Symm (I := I) (M := M) g₀ T) x
    rw [hcomp]
    rw [show 1 + u = u + 1 from Nat.add_comm 1 u]
  rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 from by norm_num]
  linarith [hexp, habc, hpos, e_ab, e_bc, e_ac, f1, f2, g_ab, g_bc, g_ac, hNval]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kOut0Perm3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kOut0Perm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kOut0Perm3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kOut0Perm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kOut0Perm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kOut0Perm2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kOut0Perm3012 : Equiv.Perm (Fin 4) :=
  ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kOut0Perm2013 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kMid0Perm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_kMid0Perm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem b3_b3_slotPermCc0Fib_contMDiff (_g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel d d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel d d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace d d I z) x
        (show Tensor0SBundle.TensorRSSpace d d I x from DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (φ := fun x : M => DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x)
  intro Y
  have h := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_field_contMDiff (I := I) ρ (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def b3_slotPermCc0 (g₀ : SmoothRiemannianMetric I M) {d : ℕ} (ρ : Equiv.Perm (Fin d)) :
    SmoothCcTensor g₀ d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x)
      contMDiff_toFun := b3_b3_slotPermCc0Fib_contMDiff (I := I) (M := M) g₀ ρ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private theorem b3_order0KernelField_eq_arm_combination (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁ =
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3201)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2301)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
                (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                  (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102)
                  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm
        + ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3102)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120)
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1302)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm
        + ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1203)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2103)
              (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
                (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
                  (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120)
                  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)
      - ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3012)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2013)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem b3_armOuter24_rfns_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g₀ 2 4) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 4 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
            (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 4 q W).toSection x) := by
  refine riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 4 σ
    W (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W)
    (fun y d => ?_) q x
  have hy : (show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 4 I y from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4
        (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W).toSection y) d =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) σ y
        ((show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 4 I y from W.toSection y) d) := rfl
  rw [hy, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem b3_armOuter23_rfns_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (W : SmoothCcTensor g₀ 2 3) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 3 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
            (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 3 q W).toSection x) := by
  refine riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 3 σ
    W (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W)
    (fun y d => ?_) q x
  have hy : (show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 3 I y from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
        (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W).toSection y) d =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) σ y
        ((show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 3 I y from W.toSection y) d) := rfl
  rw [hy, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma b4_sum_atg_eq_bfgWindow (b : ℕ → ℝ) {K W : ℕ} (hW : W ≤ K + 1) :
    ∑ k ∈ Finset.range W, Combinatorics.antidiagonalTupleGrid b k =
      Combinatorics.boundedFactorGridWindow b K W := by
  rw [Combinatorics.boundedFactorGridWindow]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  exact Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem b4_cDCIF_le (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 4 n
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField
            (I := I) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField_eq_reindex_slotExtend_two
    (I := I) (M := M) g₀ g₁]
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
    (slotExtend (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionReindexPerm n x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
    (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) n x) ?_
  rw [show ((Module.finrank ℝ E : ℝ)) ^ 2 = (Module.finrank ℝ E : ℝ) *
    (Module.finrank ℝ E : ℝ) from pow_two (Module.finrank ℝ E : ℝ)]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g₁ g₀) n x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem b4_inner_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField
            (I := I) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 1 2 m
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField_eq_reindex_slotExtend
    (I := I) (M := M) g₀ g₁]
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 3
    (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm m x]
  exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g₁ g₀) m x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem b4_gradCore_le (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 4 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField
            (I := I) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField_eq_reindex_slotExtend
    (I := I) (M := M) g₀ g₁]
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
    (slotExtend (I := I) (M := M) g₀ 1 3
      (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm i x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 3
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) i x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact le_of_eq (rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
    (connDiffSection (I := I) g₁ g₀) x)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem b4_quadArm_capped (g₀ : SmoothRiemannianMetric I M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (core : SmoothCcTensor g₀ 3 4) (W23 : SmoothCcTensor g₀ 2 3)
    (CA : ℕ → ℝ) (hCA_nn : ∀ j, 0 ≤ CA j) {fr : ℝ} (hfr : 0 ≤ fr)
    {i l : ℕ} (hl : l ≤ i) (x : M)
    (hcore : ∀ n, n ≤ l → riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) ≤
      fr ^ 2 * CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2))
    (hW : ∀ m, m ≤ l → riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
      ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x) ≤
      fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 4 l
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 core W23)).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) l *
          ∑ n ∈ Finset.range (l + 1), ∑ m ∈ Finset.range (l + 1 - n),
            fr ^ 3 * CA n * CA m *
              Combinatorics.windowPairCellCount (n + 2) (m + 2)) *
        Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ l 2 3 4 core W23 x) ?_
  have hwin_nn : ∀ K W : ℕ, 0 ≤ Combinatorics.boundedFactorGridWindow b K W :=
    fun K W => Combinatorics.boundedFactorGridWindow_nonneg b hb K W
  have hterm : ∀ n ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) *
        ∑ m ∈ Finset.range (l + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x) ≤
      (∑ m ∈ Finset.range (l + 1 - n),
        fr ^ 3 * CA n * CA m *
          Combinatorics.windowPairCellCount (n + 2) (m + 2)) *
        Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have h1 := hcore n (by omega)
    have h2 : (∑ m ∈ Finset.range (l + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
          ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x)) ≤
        ∑ m ∈ Finset.range (l + 1 - n),
          fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      rw [Finset.mem_range] at hm
      exact hW m (by omega)
    have hprod : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) *
        (∑ m ∈ Finset.range (l + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x)) ≤
        (fr ^ 2 * CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2)) *
          ∑ m ∈ Finset.range (l + 1 - n),
            fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) :=
      mul_le_mul h1 h2
        (Finset.sum_nonneg (fun m _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (3 + m) x _))
        (mul_nonneg (mul_nonneg (pow_nonneg hfr 2) (hCA_nn n)) (hwin_nn (i + 1) (n + 2)))
    refine le_trans hprod ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    have hww := Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1) (n + 2) (m + 2)
      (by omega) (by omega)
    have hmono : Combinatorics.boundedFactorGridWindow b (i + 1) ((n + 2) + (m + 2) - 1) ≤
        Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_mono b hb (le_refl (i + 1)) (by omega)
    have hc_nn : (0 : ℝ) ≤ fr ^ 3 * CA n * CA m :=
      mul_nonneg (mul_nonneg (pow_nonneg hfr 3) (hCA_nn n)) (hCA_nn m)
    calc (fr ^ 2 * CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2)) *
            (fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2))
        = (fr ^ 3 * CA n * CA m) *
            (Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2)) := by ring
      _ ≤ (fr ^ 3 * CA n * CA m) *
            (Combinatorics.windowPairCellCount (n + 2) (m + 2) *
              Combinatorics.boundedFactorGridWindow b (i + 1) ((n + 2) + (m + 2) - 1)) :=
          mul_le_mul_of_nonneg_left hww hc_nn
      _ ≤ (fr ^ 3 * CA n * CA m) *
            (Combinatorics.windowPairCellCount (n + 2) (m + 2) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmono
              (Combinatorics.windowPairCellCount_nonneg (n + 2) (m + 2)))
            hc_nn
      _ = fr ^ 3 * CA n * CA m *
            Combinatorics.windowPairCellCount (n + 2) (m + 2) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul]
  exact le_of_eq (by ring)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma b4_coeff_into_sqrt {c X w : ℝ} (hc : 0 ≤ c) :
    c * Real.sqrt (X * w) = Real.sqrt ((c ^ 2 * X) * w) := by
  rw [show (c ^ 2 * X) * w = c ^ 2 * (X * w) from by ring]
  rw [Real.sqrt_mul (sq_nonneg c) (X * w), Real.sqrt_sq hc]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma b4_sqrt_le_coeff_mul {A c B : ℝ} (hA : A ≤ c ^ 2 * B) (hc : 0 ≤ c) :
    Real.sqrt A ≤ c * Real.sqrt B := by
  refine le_trans (Real.sqrt_le_sqrt hA) ?_
  rw [Real.sqrt_mul (sq_nonneg c) B, Real.sqrt_sq hc]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma b4_young_head3 {T e btop c1 c2 c3 w : ℝ}
    (hbtop : 0 ≤ btop) (hw : 0 ≤ w) (he : 0 ≤ e)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hT0 : 0 ≤ T)
    (hT : Real.sqrt T ≤ e * Real.sqrt btop
      + (Real.sqrt (c1 * w) + Real.sqrt (c2 * w) + Real.sqrt (c3 * w))) :
    T ≤ (3 / 2) * e ^ 2 * btop + 9 * (c1 + c2 + c3) * w := by
  set u : ℝ := e * Real.sqrt btop with hu_def
  set v : ℝ := Real.sqrt (c1 * w) + Real.sqrt (c2 * w) + Real.sqrt (c3 * w) with hv_def
  have hu0 : 0 ≤ u := mul_nonneg he (Real.sqrt_nonneg _)
  have hv0 : 0 ≤ v := by
    have := Real.sqrt_nonneg (c1 * w)
    have := Real.sqrt_nonneg (c2 * w)
    have := Real.sqrt_nonneg (c3 * w)
    linarith
  have hTuv : T ≤ (u + v) ^ 2 := by
    have hsq : Real.sqrt T ^ 2 ≤ (u + v) ^ 2 := by
      nlinarith [hT, Real.sqrt_nonneg T]
    rw [Real.sq_sqrt hT0] at hsq
    exact hsq
  have hyoung := rfns_tl_young_sq u v (1 / 2) (by norm_num)
  have hu2 : u ^ 2 = e ^ 2 * btop := by
    rw [hu_def, mul_pow, Real.sq_sqrt hbtop]
  have hv2 : v ^ 2 ≤ 3 * (c1 * w + c2 * w + c3 * w) := by
    have h1 : Real.sqrt (c1 * w) ^ 2 = c1 * w := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (c2 * w) ^ 2 = c2 * w := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (c3 * w) ^ 2 = c3 * w := Real.sq_sqrt (by positivity)
    rw [hv_def]
    nlinarith [sq_nonneg (Real.sqrt (c1 * w) - Real.sqrt (c2 * w)),
      sq_nonneg (Real.sqrt (c1 * w) - Real.sqrt (c3 * w)),
      sq_nonneg (Real.sqrt (c2 * w) - Real.sqrt (c3 * w))]
  have hinv : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  rw [hinv] at hyoung
  calc T ≤ (u + v) ^ 2 := hTuv
    _ ≤ (1 + 1 / 2) * u ^ 2 + (1 + 2) * v ^ 2 := hyoung
    _ ≤ (3 / 2) * e ^ 2 * btop + 9 * (c1 + c2 + c3) * w := by
        rw [hu2]
        nlinarith [hv2]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma b4_sqrt_eightArm (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v1 v2 v3 v4 v5 v6 v7 v8 : TensorRSSpace r s I x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x
        (v1 + v2 + v3 + v4 + v5 + v6 - v7 - v8)) ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v1)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v2)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v3)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v4)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v5)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v6)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v7)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v8) := by
  have c1 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x v1 v2
  have c2 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x (v1 + v2) v3
  have c3 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x (v1 + v2 + v3) v4
  have c4 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x (v1 + v2 + v3 + v4) v5
  have c5 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x (v1 + v2 + v3 + v4 + v5) v6
  have c6 := b1_sqrt_rfns_sub_le (I := I) (M := M) g r s x (v1 + v2 + v3 + v4 + v5 + v6) v7
  have c7 := b1_sqrt_rfns_sub_le (I := I) (M := M) g r s x
    (v1 + v2 + v3 + v4 + v5 + v6 - v7) v8
  linarith [c1, c2, c3, c4, c5, c6, c7]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k2_coframeS_one_eq_g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM_apply, dualToCotangent_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma k2_fiberNormSqComponent_sharpFlatEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 1 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J =
      g₀.inner x
        (inverseMetricSharpFib (I := I) g₁ x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))) (e (J 0)) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
        (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) from rfl]
  rw [k2_coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        TensorRSSpace.ofCLM
          ((DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x)))
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0))) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
        (inverseMetricSharpFib (I := I) g₁ x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))) from rfl]
  rw [show (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
        (inverseMetricSharpFib (I := I) g₁ x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))))
        (fun k => e (J k)) =
      cotangentToDual (I := I) (x := x)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
          (inverseMetricSharpFib (I := I) g₁ x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))))
        (e (J 0)) from by
    rw [cotangentToDual_apply]
    rfl]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM (I := I) g₀ x
    (inverseMetricSharpFib (I := I) g₁ x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))) (e (J 0))]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k2_gram_sum_sq (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (d : Fin n → ℝ)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    g.inner x (∑ j, d j • e j) (∑ l, d l • e l) = ∑ j, d j ^ 2 := by
  classical
  have hbil : g.inner x (∑ j, d j • e j) (∑ l, d l • e l)
      = ∑ j, ∑ l, (d j * d l) * g.inner x (e j) (e l) := by
    rw [show g.inner x (∑ j, d j • e j) = ∑ j, d j • g.inner x (e j) from by
      rw [map_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [map_smul]]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, smul_eq_mul]; ring
  rw [hbil]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single j]
  · rw [horth j j, if_pos rfl, mul_one]; ring
  · intro l _ hl; rw [horth j l, if_neg (fun h => hl h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k2_fiberNormSqComponent_compRS_eq
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (x : M)
    (Φx : TensorRSSpace b c I x) (Wx : TensorRSSpace a b I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin a → Fin n) (J : Fin c → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x a c
        (show TensorRSSpace a c I x from
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
            (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)) n e K J =
      ∑ P : Fin b → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P *
          fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J := by
  classical
  change (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin a) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K k)))))
      (fun k => e (J k)) = _
  set wval : Tensor0SSpace b I x :=
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin a) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k)))) with hwval
  have hexp := tensorS_coframe_expansion (I := I) (M := M) g x b e bse hbse horth wval
  conv_lhs => rw [hexp]
  rw [map_sum]
  rw [show (∑ P : Fin b → Fin n,
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          ((wval (fun k : Fin b => e (P k))) • coframeS (I := I) (M := M) g x b e P)) =
      ∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P) from by
    refine Finset.sum_congr rfl (fun P _ => ?_); rw [map_smul]]
  rw [show ((∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel (∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) from rfl]
  rw [← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply]
  have hΦcomp : Tensor0SSpace.toModel
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
        (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) =
      fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J := rfl
  rw [hΦcomp]
  have hwcomp : wval (fun k : Fin b => e (P k)) =
      fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P := rfl
  rw [hwcomp, smul_eq_mul]

private lemma k2_sum_fin1 {α : Type*} [AddCommMonoid α] {n : ℕ} (f : (Fin 1 → Fin n) → α) :
    ∑ K : Fin 1 → Fin n, f K = ∑ k : Fin n, f (fun _ => k) := by
  classical
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) f (fun k => f (fun _ => k)) ?_
  intro K
  refine congrArg f ?_
  funext i
  rw [Subsingleton.elim i 0]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem rfns_appCcRS_sharpFlatEndoCc_contravariantSlot_op_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (c : ℕ) (D : SmoothCcTensor g₀ 1 c) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 c x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 c D
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc
            (I := I) g₀ g₁)).toSection x) ≤
      (1 / (1 - δ₀)) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 c x (D.toSection x) := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have h1δ₀ : (0 : ℝ) < 1 - δ₀ := by linarith
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hrepr02⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hWop : ∀ u : TangentSpace I x,
      g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u) ≤
      (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
    intro u
    have hs := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.sqrt_inner_gInvRaisedEndo_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ P y) htie
      (show δ < 1 from by linarith) hδ0 hbound x u
    have h0T : 0 ≤ g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u) :=
      DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    have h0u : 0 ≤ g₀.inner x u u := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hinv : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
      rw [div_le_div_iff₀ h1δ h1δ₀]
      linarith
    have hsq := Real.sq_sqrt h0T
    have hsqu := Real.sq_sqrt h0u
    have h1 : Real.sqrt (g₀.inner x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)) ≤
        (1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u) :=
      le_trans hs (mul_le_mul_of_nonneg_right hinv (Real.sqrt_nonneg _))
    calc g₀.inner x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
        = Real.sqrt (g₀.inner x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)) ^ 2 :=
          hsq.symm
      _ ≤ ((1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u)) ^ 2 :=
          by nlinarith [h1, Real.sqrt_nonneg (g₀.inner x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u))]
      _ = (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
          rw [mul_pow, hsqu]
  rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 c D
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁) x]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 c x _ e bse hnE hbse horth]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 c x
    (D.toSection x) e bse hnE hbse horth]
  have hcomp : ∀ (K : Fin 1 → Fin n) (J : Fin c → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 c
          (show TensorRSSpace 1 c I x from
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace c I x from D.toSection x).comp
              (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) n e K J =
        ∑ Pf : Fin 1 → Fin n,
          fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
              ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e Pf J :=
    fun K J => k2_fiberNormSqComponent_compRS_eq (I := I) (M := M) g₀ 1 1 c x
      (D.toSection x) ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
      e bse hbse horth K J
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun K _ =>
    Finset.sum_congr rfl (fun J _ => by rw [hcomp K J])))) ?_
  rw [Finset.sum_comm]
  rw [show (∑ K : Fin 1 → Fin n, ∑ J : Fin c → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e K J) ^ 2) =
    ∑ J : Fin c → Fin n, ∑ K : Fin 1 → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e K J) ^ 2 from
    Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun J _ => ?_)
  set y : Fin n → ℝ := fun p =>
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e (fun _ => p) J
    with hy_def
  set u : TangentSpace I x := ∑ p : Fin n, y p • e p with hu_def
  have hsfe_val : ∀ K Pf : Fin 1 → Fin n,
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf =
        g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x (e (K 0))) (e (Pf 0)) := by
    intro K Pf
    rw [k2_fiberNormSqComponent_sharpFlatEndoCc (I := I) (M := M) g₀ g₁ x e K Pf]
    rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo_apply (I := I) g₀ g₁ x (e (K 0))]
  have hinner_sum : ∀ K : Fin 1 → Fin n,
      (∑ Pf : Fin 1 → Fin n,
        fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
            ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf *
          fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e Pf J) =
      g₀.inner x u (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x (e (K 0))) := by
    intro K
    rw [k2_sum_fin1 (fun Pf : Fin 1 → Fin n =>
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf *
        fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e Pf J)]
    rw [hu_def]
    rw [show g₀.inner x (∑ p : Fin n, y p • e p)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x (e (K 0))) =
      ∑ p : Fin n, y p * g₀.inner x (e p)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x (e (K 0))) from by
      rw [show g₀.inner x (∑ p : Fin n, y p • e p) =
          ∑ p : Fin n, y p • g₀.inner x (e p) from by
        rw [map_sum]; exact Finset.sum_congr rfl (fun p _ => by rw [map_smul])]
      rw [ContinuousLinearMap.sum_apply]
      exact Finset.sum_congr rfl (fun p _ => by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul])]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hsfe_val K (fun _ => p)]
    rw [g₀.symm x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x (e (K 0))) (e p)]
    rw [hy_def]
    ring
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) => by rw [hinner_sum K] :
    ∀ K ∈ Finset.univ, ((∑ Pf : Fin 1 → Fin n,
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf *
        fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e Pf J) ^ 2) =
      (g₀.inner x u (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x (e (K 0)))) ^ 2)]
  rw [k2_sum_fin1 (fun K : Fin 1 → Fin n =>
    (g₀.inner x u (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x (e (K 0)))) ^ 2)]
  refine le_trans (gFrame_adjoint_parseval_le (I := I) (M := M) g₀ x
    (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x) ((1 / (1 - δ₀)) ^ 2) (by positivity)
    hWop e hpars u) ?_
  rw [hu_def, k2_gram_sum_sq (I := I) (M := M) g₀ x e y horth]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  rw [k2_sum_fin1 (fun K : Fin 1 → Fin n =>
    (fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e K J) ^ 2)]

private def k3_slotExtendIterFib (g : SmoothRiemannianMetric I M) (b c : ℕ) (x : M)
    (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) :
    ∀ w : ℕ, Tensor0SSpace (b + w) I x →L[ℝ] Tensor0SSpace (c + w) I x
  | 0 => A
  | (w + 1) => slotExtendPointwise (I := I) (M := M) g (b + w) (c + w) x
      (k3_slotExtendIterFib g b c x A w)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k3_appCcLeibnizPsi_succ_succ_eq (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i j : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        slotExtend (I := I) (M := M) g (b + j) (c + i)
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) := by
  rw [show appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        castCcTensorSourceRank g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
          (castCcTensorRank g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) from rfl]
  rw [castCcTensorRank, castCcTensorSourceRank]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma k3_appCcLeibnizPsi_diag_toSection (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) (x : M) :
    ((appCcLeibnizPsi (I := I) (M := M) g b c Φ i i).toSection x :
        Tensor0SSpace (b + i) I x →L[ℝ] Tensor0SSpace (c + i) I x) =
      k3_slotExtendIterFib (I := I) (M := M) g b c x
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hdiag : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (i + 1) =
          slotExtend (I := I) (M := M) g (b + i) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i) := by
        rw [k3_appCcLeibnizPsi_succ_succ_eq (I := I) (M := M) g b c Φ i i]
        rw [if_neg (by omega : ¬ (i + 1 < i + 1)), zero_add]
      rw [hdiag]
      rw [show (k3_slotExtendIterFib (I := I) (M := M) g b c x
            (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) (i + 1)) =
          slotExtendPointwise (I := I) (M := M) g (b + i) (c + i) x
            (k3_slotExtendIterFib (I := I) (M := M) g b c x
              (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i)
          from rfl]
      rw [← ih]
      rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_fiberNormSqComponent_slotExtendFib_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K' : Fin (r + 1) → Fin n) (J' : Fin (s + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) g r s x A)
        n e K' J' =
      (if J' 0 = K' 0 then (1 : ℝ) else 0) *
        fiberNormSqComponent (I := I) (M := M) g x r s
          (show TensorRSSpace r s I x from A) n e
          (fun k => K' (Fin.succ k)) (fun k => J' (Fin.succ k)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) g r s x A)
        n e K' J' =
      Tensor0SSpace.toModel
        (slotExtendPointwise (I := I) (M := M) g r s x A
          (coframeS (I := I) (M := M) g x (r + 1) e K'))
        (Fin.cons (show E from e (J' 0)) (fun k : Fin s => (show E from e (J' (Fin.succ k))))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
          (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendPointwise (I := I) (M := M) g r s x A)
          n e K' J' =
        Tensor0SSpace.toModel
          (slotExtendPointwise (I := I) (M := M) g r s x A
            (coframeS (I := I) (M := M) g x (r + 1) e K'))
          (fun k => (show E from e (J' k))) from rfl]
    congr 1
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
  rw [hcomp]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x A
    (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0))
    (fun k : Fin s => (show E from e (J' (Fin.succ k))))]
  have hcurry : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
        (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0)) =
      (if J' 0 = K' 0 then (1 : ℝ) else 0) •
        coframeS (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) := by
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := r)
      (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0)) u]
    have hcf : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x (r + 1) e K')
          (Fin.cons (show E from e (J' 0)) u) =
        coframeS (I := I) (M := M) g x (r + 1) e K' (Fin.cons (show E from e (J' 0)) u) := rfl
    rw [hcf, coframeS_apply (I := I) (M := M) g x (r + 1) e K' (Fin.cons (show E from e (J' 0)) u)]
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [horth (K' 0) (J' 0)]
    rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hcf2 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x r e
          (fun k => K' (Fin.succ k))) u =
        coframeS (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) u := rfl
    rw [hcf2, coframeS_apply (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) u]
    by_cases h : K' 0 = J' 0
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [hcurry, map_smul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  congr 1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_metricInner_injective (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x}
    (hab : ∀ w : TangentSpace I x, g₁.inner x a w = g₁.inner x b w) : a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsymm₁ : g₁.inner x (a - b) (a - b) =
        g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsymm₁, g₁.symm x (a - b) a, g₁.symm x (a - b) b]
    have e1 : g₁.inner x a (a - b) = g₁.inner x b (a - b) := hab (a - b)
    rw [e1]; ring
  exact absurd hzero (ne_of_gt hpos)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_cometric_sum_eq_invSharp (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (b : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x b ((Module.finBasis ℝ E) k) •
          DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₁ x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x b) := by
  classical
  apply k3_metricInner_injective (I := I) g₁ x
  intro w
  have hcoord : ∀ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).cDualBasis k (w : E) =
        (Module.finBasis ℝ E).repr (w : E) k := by
    intro k
    rw [show ((Module.finBasis ℝ E).cDualBasis k) =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
      rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
      congr 1
      exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
    rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  have hlhs : ∀ k : Fin (Module.finrank ℝ E),
      (g₁.inner x (g₀.inner x b ((Module.finBasis ℝ E) k) •
          DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))) w =
        g₀.inner x b ((Module.finBasis ℝ E) k) *
          (Module.finBasis ℝ E).repr (w : E) k := by
    intro k
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 1
    have hinner : g₁.inner x (DeTurck.cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) w =
        (Module.finBasis ℝ E).cDualBasis k (w : E) := by
      have h1 : DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) =
          inverseMetricSharpFib (I := I) g₁ x
            ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) := rfl
      rw [h1, inverseMetricSharpFib_inner (I := I) g₁ x _ w, cotangentToDualLinear_apply,
        cotangentToDual_apply]
      change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) (fun _ : Fin 1 => (w : E)) = _
      rw [Tensor0SBundle.model_covectorOfCLM_apply]
    rw [hinner, hcoord k]
  rw [Finset.sum_congr rfl (fun k _ => hlhs k)]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply,
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM]
  have hwexp : (w : TangentSpace I x) =
      ∑ k : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr (w : E) k • ((Module.finBasis ℝ E) k : TangentSpace I x) := by
    have h := (Module.finBasis ℝ E).sum_repr (w : E)
    exact h.symm
  conv_rhs => rw [hwexp, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_cometric_dualsum_inner_collapse (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a c : TangentSpace I x) :
    (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x c ((Module.finBasis ℝ E) k) *
          g₀.inner x a (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))) =
      g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x c)) := by
  classical
  have hsumeq := k3_cometric_sum_eq_invSharp (I := I) (M := M) g₀ g₁ x c
  calc (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x c ((Module.finBasis ℝ E) k) *
          g₀.inner x a (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
      = ∑ k : Fin (Module.finrank ℝ E), g₀.inner x a
          (g₀.inner x c ((Module.finBasis ℝ E) k) •
            DeTurck.cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    _ = g₀.inner x a
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x c ((Module.finBasis ℝ E) k) •
              DeTurck.cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) := (map_sum (g₀.inner x a) _ _).symm
    _ = g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x c)) := by
        rw [hsumeq]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_slotPerm_coframeS (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (d : ℕ) (ρ : Equiv.Perm (Fin d))
    (Q : Fin d → Fin n) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x
        (coframeS (I := I) (M := M) g x d e Q) =
      coframeS (I := I) (M := M) g x d e (fun k => Q (ρ.symm k)) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun z => ?_)
  beta_reduce
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply (I := I) ρ x
    (coframeS (I := I) (M := M) g x d e Q)]
  rw [Tensor0SSpace.toModel_ofModel]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have h1 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x d e Q)
        (fun i => z (ρ i)) =
      coframeS (I := I) (M := M) g x d e Q (fun i => z (ρ i)) := rfl
  have h2 : Tensor0SSpace.toModel
        (coframeS (I := I) (M := M) g x d e (fun k => Q (ρ.symm k))) z =
      coframeS (I := I) (M := M) g x d e (fun k => Q (ρ.symm k)) z := rfl
  rw [h1, h2, coframeS_apply (I := I) (M := M) g x d e Q (fun i => z (ρ i)),
    coframeS_apply (I := I) (M := M) g x d e (fun k => Q (ρ.symm k)) z]
  refine Fintype.prod_equiv ρ _ _ (fun a => ?_)
  rw [Equiv.symm_apply_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_fnsc_comp_slotPerm (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (d s : ℕ)
    (A : Tensor0SSpace d I x →L[ℝ] Tensor0SSpace s I x) (ρ : Equiv.Perm (Fin d))
    (Q : Fin d → Fin n) (L : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x d s
        (show TensorRSSpace d s I x from
          A.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x))
        n e Q L =
      fiberNormSqComponent (I := I) (M := M) g x d s
        (show TensorRSSpace d s I x from A) n e (fun k => Q (ρ.symm k)) L := by
  have hread : fiberNormSqComponent (I := I) (M := M) g x d s
        (show TensorRSSpace d s I x from
          A.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x))
        n e Q L =
      Tensor0SSpace.toModel
        (A (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x
          (coframeS (I := I) (M := M) g x d e Q)))
        (fun k => e (L k)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  have hread2 : fiberNormSqComponent (I := I) (M := M) g x d s
        (show TensorRSSpace d s I x from A) n e (fun k => Q (ρ.symm k)) L =
      Tensor0SSpace.toModel
        (A (coframeS (I := I) (M := M) g x d e (fun k => Q (ρ.symm k))))
        (fun k => e (L k)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  rw [hread, hread2, k3_slotPerm_coframeS (I := I) (M := M) g x e d ρ Q]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_doubleTrace_component_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (Q : Fin 4 → Fin n) (L : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
        n e Q L =
      (if Q 2 = L 0 then (1 : ℝ) else 0) * (if Q 3 = L 1 then (1 : ℝ) else 0) *
        g₀.inner x (e (Q 0))
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
            (I := I) g₀ g₁ x (e (Q 1))) := by
  classical
  have hread : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
        n e Q L =
      Tensor0SSpace.toModel
        ((DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
          (coframeS (I := I) (M := M) g₀ x 4 e Q))
        (fun k => e (L k)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  rw [hread, DeTurck.cometricDoubleTraceFib_toModel]
  rw [DeTurck.modelDoubleTrace_apply (E := E) 2 (DeTurck.cometricLmodel (I := I) g₁ x) _
    (fun k => e (L k))]
  have hterm : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e Q)
        (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (L l)))) =
        (g₀.inner x (e (Q 2)) (e (L 0)) * g₀.inner x (e (Q 3)) (e (L 1))) *
          (g₀.inner x (e (Q 1)) ((Module.finBasis ℝ E) k) *
            g₀.inner x (e (Q 0)) (DeTurck.cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))) := by
    intro k
    set base : Fin 4 → E :=
      Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (L l))) with hbase
    have hcfeval : Tensor0SBundle.Tensor0SSpace.toModel
          (coframeS (I := I) (M := M) g₀ x 4 e Q) base =
        ∏ i : Fin 4, g₀.inner x (e (Q i)) (base i) :=
      coframeS_apply (I := I) (M := M) g₀ x 4 e Q base
    rw [hcfeval, Fin.prod_univ_four]
    have hb0 : base 0 = DeTurck.cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) := by rw [hbase, Fin.cons_zero]
    have hb1 : base 1 = (Module.finBasis ℝ E) k := by
      rw [hbase, show (1 : Fin 4) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
    have hb2 : base 2 = e (L 0) := by
      rw [hbase, show (2 : Fin 4) = Fin.succ 1 from rfl, Fin.cons_succ,
        show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
    have hb3 : base 3 = e (L 1) := by
      rw [hbase, show (3 : Fin 4) = Fin.succ 2 from rfl, Fin.cons_succ,
        show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]
    rw [hb0, hb1, hb2, hb3]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [← Finset.mul_sum]
  rw [k3_cometric_dualsum_inner_collapse (I := I) (M := M) g₀ g₁ x (e (Q 0)) (e (Q 1))]
  rw [horth (Q 2) (L 0), horth (Q 3) (L 1)]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo_apply
    (I := I) g₀ g₁ x (e (Q 1))]

private lemma k3_pair_delta_sum_right {nn : ℕ} (a b : Fin nn) :
    (∑ L : Fin 2 → Fin nn,
      (if a = L 0 then (1 : ℝ) else 0) * (if b = L 1 then (1 : ℝ) else 0)) = 1 := by
  classical
  rw [← (finTwoArrowEquiv (Fin nn)).symm.sum_comp
    (fun L : Fin 2 → Fin nn =>
      (if a = L 0 then (1 : ℝ) else 0) * (if b = L 1 then (1 : ℝ) else 0))]
  rw [Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hin : ∀ j0 : Fin nn,
      (∑ j1 : Fin nn, (if a = j0 then (1 : ℝ) else 0) * (if b = j1 then (1 : ℝ) else 0))
        = (if a = j0 then (1 : ℝ) else 0) := by
    intro j0
    rw [← Finset.mul_sum, Finset.sum_ite_eq Finset.univ b (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun j0 _ => hin j0)]
  rw [Finset.sum_ite_eq Finset.univ a (fun _ => (1 : ℝ))]
  simp

private lemma k3_sum_fin4_split {nn : ℕ} (F : (Fin 4 → Fin nn) → ℝ) :
    ∑ Q : Fin 4 → Fin nn, F Q =
      ∑ q0 : Fin nn, ∑ q1 : Fin nn, ∑ Q2 : Fin 2 → Fin nn,
        F (Fin.cons q0 (Fin.cons q1 Q2)) := by
  classical
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin 4 => Fin nn))
    (fun pr : Fin nn × (Fin 3 → Fin nn) => F (Fin.cons pr.1 pr.2))
    (fun Q : Fin 4 → Fin nn => F Q)
    (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun q0 _ => ?_)
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin 3 => Fin nn))
    (fun pr : Fin nn × (Fin 2 → Fin nn) => F (Fin.cons q0 (Fin.cons pr.1 pr.2)))
    (fun Q' : Fin 3 → Fin nn => F (Fin.cons q0 Q'))
    (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]

private lemma k3_cons_indices {nn : ℕ} (q0 q1 : Fin nn) (Q2 : Fin 2 → Fin nn) :
    (Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin nn) 0 = q0 ∧
    (Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin nn) 1 = q1 ∧
    (Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin nn) 2 = Q2 0 ∧
    (Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin nn) 3 = Q2 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fin.cons_zero]
  · rw [show (1 : Fin 4) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
  · rw [show (2 : Fin 4) = Fin.succ 1 from rfl, Fin.cons_succ,
      show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
  · rw [show (3 : Fin 4) = Fin.succ 2 from rfl, Fin.cons_succ,
      show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_singleTrace_functional_sq_le (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (V : (Fin 4 → Fin n) → ℝ) :
    ∑ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
            n e Q L) ^ 2 ≤
      (∑ a : Fin n, ∑ b : Fin n,
          (g₀.inner x (e a)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
              (I := I) g₀ g₁ x (e b))) ^ 2) *
        ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
  classical
  set m : Fin n → Fin n → ℝ := fun a b =>
    g₀.inner x (e a)
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
        (I := I) g₀ g₁ x (e b)) with hm_def
  set χ : (Fin 4 → Fin n) → (Fin 2 → Fin n) → ℝ := fun Q L =>
    (if Q 2 = L 0 then (1 : ℝ) else 0) * (if Q 3 = L 1 then (1 : ℝ) else 0) with hχ_def
  have hχ01 : ∀ Q L, χ Q L = 0 ∨ χ Q L = 1 := by
    intro Q L
    rw [hχ_def]
    by_cases h2 : Q 2 = L 0 <;> by_cases h3 : Q 3 = L 1 <;> simp [h2, h3]
  have hcomp : ∀ (Q : Fin 4 → Fin n) (L : Fin 2 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
        n e Q L = χ Q L * m (Q 0) (Q 1) := fun Q L =>
    k3_doubleTrace_component_eq (I := I) (M := M) g₀ g₁ x e horth Q L
  have hCS : ∀ L : Fin 2 → Fin n,
      (∑ Q : Fin 4 → Fin n, V Q *
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
          n e Q L) ^ 2 ≤
      (∑ Q : Fin 4 → Fin n, (m (Q 0) (Q 1)) ^ 2 * χ Q L) *
        (∑ Q : Fin 4 → Fin n, (V Q) ^ 2 * χ Q L) := by
    intro L
    have hrw : (∑ Q : Fin 4 → Fin n, V Q *
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
          n e Q L) =
        ∑ Q : Fin 4 → Fin n, (m (Q 0) (Q 1) * χ Q L) * (V Q * χ Q L) := by
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [hcomp Q L]
      rcases hχ01 Q L with h | h <;> rw [h] <;> ring
    rw [hrw]
    refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun Q : Fin 4 → Fin n => m (Q 0) (Q 1) * χ Q L)
      (fun Q : Fin 4 → Fin n => V Q * χ Q L)) (le_of_eq ?_)
    congr 1
    · refine Finset.sum_congr rfl (fun Q _ => ?_)
      rcases hχ01 Q L with h | h <;> rw [h] <;> ring
    · refine Finset.sum_congr rfl (fun Q _ => ?_)
      rcases hχ01 Q L with h | h <;> rw [h] <;> ring
  have hmsum : ∀ L : Fin 2 → Fin n,
      (∑ Q : Fin 4 → Fin n, (m (Q 0) (Q 1)) ^ 2 * χ Q L) =
        ∑ a : Fin n, ∑ b : Fin n, (m a b) ^ 2 := by
    intro L
    rw [k3_sum_fin4_split (fun Q : Fin 4 → Fin n => (m (Q 0) (Q 1)) ^ 2 * χ Q L)]
    refine Finset.sum_congr rfl (fun q0 _ => Finset.sum_congr rfl (fun q1 _ => ?_))
    have hval : ∀ Q2 : Fin 2 → Fin n,
        (m ((Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin n) 0)
            ((Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin n) 1)) ^ 2 *
          χ (Fin.cons q0 (Fin.cons q1 Q2)) L =
        (m q0 q1) ^ 2 *
          ((if Q2 0 = L 0 then (1 : ℝ) else 0) * (if Q2 1 = L 1 then (1 : ℝ) else 0)) := by
      intro Q2
      obtain ⟨g0eq, g1eq, g2eq, g3eq⟩ := k3_cons_indices q0 q1 Q2
      rw [hχ_def]
      beta_reduce
      rw [g0eq, g1eq, g2eq, g3eq]
    rw [Finset.sum_congr rfl (fun Q2 _ => hval Q2)]
    rw [← Finset.mul_sum]
    have hδ : (∑ Q2 : Fin 2 → Fin n,
        (if Q2 0 = L 0 then (1 : ℝ) else 0) * (if Q2 1 = L 1 then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_congr rfl (fun Q2 _ => by
        rw [show (if Q2 0 = L 0 then (1 : ℝ) else 0) = (if L 0 = Q2 0 then (1 : ℝ) else 0) from by
          by_cases h : Q2 0 = L 0
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (fun hc => h hc.symm)],
        show (if Q2 1 = L 1 then (1 : ℝ) else 0) = (if L 1 = Q2 1 then (1 : ℝ) else 0) from by
          by_cases h : Q2 1 = L 1
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (fun hc => h hc.symm)]])]
      exact k3_pair_delta_sum_right (L 0) (L 1)
    rw [hδ, mul_one]
  have hVsum : (∑ L : Fin 2 → Fin n, ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 * χ Q L) =
      ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [← Finset.mul_sum]
    rw [show (∑ L : Fin 2 → Fin n, χ Q L) = 1 from k3_pair_delta_sum_right (Q 2) (Q 3)]
    rw [mul_one]
  calc ∑ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
            n e Q L) ^ 2
      ≤ ∑ L : Fin 2 → Fin n,
          (∑ Q : Fin 4 → Fin n, (m (Q 0) (Q 1)) ^ 2 * χ Q L) *
            (∑ Q : Fin 4 → Fin n, (V Q) ^ 2 * χ Q L) :=
        Finset.sum_le_sum (fun L _ => hCS L)
    _ = (∑ a : Fin n, ∑ b : Fin n, (m a b) ^ 2) *
          ∑ L : Fin 2 → Fin n, ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 * χ Q L := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun L _ => by rw [hmsum L])
    _ = (∑ a : Fin n, ∑ b : Fin n, (m a b) ^ 2) * ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
        rw [hVsum]

private def k3_permOfImages {n : ℕ} (f g : Fin n → Fin n)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Equiv.Perm (Fin n) :=
  ⟨f, g, h₁, h₂⟩

private def k3_perm4_0231 : Equiv.Perm (Fin 4) :=
  k3_permOfImages ![0, 2, 3, 1] ![0, 3, 1, 2] (by decide) (by decide)

private def k3_perm4_0321 : Equiv.Perm (Fin 4) :=
  k3_permOfImages ![0, 3, 2, 1] ![0, 3, 2, 1] (by decide) (by decide)

private def k3_perm4_2301 : Equiv.Perm (Fin 4) :=
  k3_permOfImages ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_fourTraceCLM_eq (g₁ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
        (I := I) g₁ x =
      ((1 : ℝ) / 2) •
        ((DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x).comp
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
              (I := I) k3_perm4_0231 x)
          + (DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x).comp
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
              (I := I) k3_perm4_0321 x)
          - DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x
          - (DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x).comp
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
              (I := I) k3_perm4_2301 x)) :=
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_fnsc_half_comb (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (A B C D : Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x)
    (Q : Fin 4 → Fin n) (L : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 4 2
        (show TensorRSSpace 4 2 I x from ((1 : ℝ) / 2) • (A + B - C - D)) n e Q L =
      (1 / 2 : ℝ) *
        (fiberNormSqComponent (I := I) (M := M) g x 4 2
            (show TensorRSSpace 4 2 I x from A) n e Q L
          + fiberNormSqComponent (I := I) (M := M) g x 4 2
            (show TensorRSSpace 4 2 I x from B) n e Q L
          - fiberNormSqComponent (I := I) (M := M) g x 4 2
            (show TensorRSSpace 4 2 I x from C) n e Q L
          - fiberNormSqComponent (I := I) (M := M) g x 4 2
            (show TensorRSSpace 4 2 I x from D) n e Q L) := by
  unfold fiberNormSqComponent
  rw [show (((1 : ℝ) / 2) • (A + B - C - D))
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k)))) =
      ((1 : ℝ) / 2) • (A ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k))))
        + B ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k))))
        - C ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k))))
        - D ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k))))) from by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_fourTrace_hA (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (V : (Fin 4 → Fin n) → ℝ) :
    ∑ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
                (I := I) g₁ x)
            n e Q L) ^ 2 ≤
      (4 * ∑ a : Fin n, ∑ b : Fin n,
          (g₀.inner x (e a)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
              (I := I) g₀ g₁ x (e b))) ^ 2) *
        ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
  classical
  set T : Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x :=
    DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x with hT_def
  set HS : ℝ := ∑ a : Fin n, ∑ b : Fin n,
    (g₀.inner x (e a)
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
        (I := I) g₀ g₁ x (e b))) ^ 2 with hHS_def
  set SV : ℝ := ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 with hSV_def
  have hSV_nn : 0 ≤ SV := Finset.sum_nonneg (fun Q _ => sq_nonneg _)
  have hsingle : ∀ (ρ : Equiv.Perm (Fin 4)),
      ∑ L : Fin 2 → Fin n,
          (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) ρ x))
              n e Q L) ^ 2 ≤ HS * SV := by
    intro ρ
    set ψ : (Fin 4 → Fin n) ≃ (Fin 4 → Fin n) :=
      Equiv.arrowCongr ρ (Equiv.refl (Fin n)) with hψ_def
    have hψ_apply : ∀ (Q : Fin 4 → Fin n) (k : Fin 4), ψ Q k = Q (ρ.symm k) := by
      intro Q k
      rfl
    have hreindex : ∀ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from
              T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                (I := I) ρ x))
            n e Q L) =
        ∑ Q' : Fin 4 → Fin n, V (ψ.symm Q') *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from T) n e Q' L := by
      intro L
      refine Fintype.sum_equiv ψ _ _ (fun Q => ?_)
      rw [k3_fnsc_comp_slotPerm (I := I) (M := M) g₀ x e 4 2 T ρ Q L]
      rw [Equiv.symm_apply_apply]
      have hfun : (fun k => Q (ρ.symm k)) = ψ Q := by
        funext k
        rw [hψ_apply Q k]
      rw [hfun]
    have happ := k3_singleTrace_functional_sq_le (I := I) (M := M) g₀ g₁ x e horth
      (fun Q' => V (ψ.symm Q'))
    have hVsq : (∑ Q' : Fin 4 → Fin n, (V (ψ.symm Q')) ^ 2) = SV := by
      rw [hSV_def]
      exact Equiv.sum_comp ψ.symm (fun Q => (V Q) ^ 2)
    rw [Finset.sum_congr rfl (fun L _ => by rw [hreindex L])]
    rw [← hT_def] at happ
    rw [hVsq] at happ
    exact happ
  have hcomb : ∀ L : Fin 2 → Fin n,
      (∑ Q : Fin 4 → Fin n, V Q *
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
              (I := I) g₁ x)
          n e Q L) =
      (1 / 2 : ℝ) *
        ((∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0231 x)) n e Q L)
          + (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0321 x)) n e Q L)
          - (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_2301 x)) n e Q L)
          - (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from T) n e Q L)) := by
    intro L
    have hpt : ∀ Q : Fin 4 → Fin n,
        V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
              (I := I) g₁ x)
          n e Q L =
        (1 / 2 : ℝ) *
          (V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0231 x)) n e Q L
            + V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0321 x)) n e Q L
            - V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_2301 x)) n e Q L
            - V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from T) n e Q L) := by
      intro Q
      rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
                (I := I) g₁ x)
            n e Q L =
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from ((1 : ℝ) / 2) •
              (T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0231 x)
                + T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0321 x)
                - T
                - T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_2301 x)))
            n e Q L from by
        rw [hT_def]
        exact congrArg (fun (S : TensorRSSpace 4 2 I x) =>
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2 S n e Q L)
          (k3_fourTraceCLM_eq (I := I) (M := M) g₁ x)]
      rw [k3_fnsc_half_comb (I := I) (M := M) g₀ x e _ _ _ _ Q L]
      ring
    rw [Finset.sum_congr rfl (fun Q _ => hpt Q)]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hquad : ∀ w1 w2 w3 w4 : ℝ,
      ((1 / 2 : ℝ) * (w1 + w2 - w3 - w4)) ^ 2 ≤ w1 ^ 2 + w2 ^ 2 + w3 ^ 2 + w4 ^ 2 := by
    intro w1 w2 w3 w4
    nlinarith [sq_nonneg (w1 - w2), sq_nonneg (w1 + w3), sq_nonneg (w1 + w4),
      sq_nonneg (w2 + w3), sq_nonneg (w2 + w4), sq_nonneg (w3 - w4)]
  calc ∑ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
                (I := I) g₁ x)
            n e Q L) ^ 2
      ≤ ∑ L : Fin 2 → Fin n,
          ((∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_0231 x)) n e Q L) ^ 2
            + (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_0321 x)) n e Q L) ^ 2
            + (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_2301 x)) n e Q L) ^ 2
            + (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from T) n e Q L) ^ 2) := by
        refine Finset.sum_le_sum (fun L _ => ?_)
        rw [hcomb L]
        exact hquad _ _ _ _
    _ = (∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_0231 x)) n e Q L) ^ 2)
          + (∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_0321 x)) n e Q L) ^ 2)
          + (∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_2301 x)) n e Q L) ^ 2)
          + (∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from T) n e Q L) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ HS * SV + HS * SV + HS * SV + HS * SV := by
        have h1 := hsingle k3_perm4_0231
        have h2 := hsingle k3_perm4_0321
        have h3 := hsingle k3_perm4_2301
        have h4 : ∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from T) n e Q L) ^ 2 ≤ HS * SV := by
          have happ := k3_singleTrace_functional_sq_le (I := I) (M := M) g₀ g₁ x e horth V
          rw [← hT_def] at happ
          exact happ
        exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = (4 * HS) * SV := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma k3_sum_sq_component_slotExtendIterFib_op_le (g : SmoothRiemannianMetric I M)
    (x : M) {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    ∀ (w b c : ℕ) (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) (κ : ℝ)
      (_hA : ∀ V : (Fin b → Fin n) → ℝ,
        ∑ L : Fin c → Fin n,
            (∑ Q : Fin b → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g x b c
                (show TensorRSSpace b c I x from A) n e Q L) ^ 2 ≤
          κ * ∑ Q : Fin b → Fin n, (V Q) ^ 2)
      (V : (Fin (b + w) → Fin n) → ℝ),
      ∑ J : Fin (c + w) → Fin n,
          (∑ P : Fin (b + w) → Fin n,
            V P * fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
              (show TensorRSSpace (b + w) (c + w) I x from
                k3_slotExtendIterFib (I := I) (M := M) g b c x A w) n e P J) ^ 2 ≤
        κ * ∑ P : Fin (b + w) → Fin n, (V P) ^ 2
  | 0 => fun b c A κ hA V => hA V
  | (w + 1) => by
      intro b c A κ hA V
      set cw : (Fin (b + w) → Fin n) → (Fin (c + w) → Fin n) → ℝ := fun P J =>
        fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
          (show TensorRSSpace (b + w) (c + w) I x from
            k3_slotExtendIterFib (I := I) (M := M) g b c x A w) n e P J with hcw_def
      have hpeel : ∀ (P : Fin (b + (w + 1)) → Fin n) (J : Fin (c + (w + 1)) → Fin n),
          fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
              (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                k3_slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J =
            (if J 0 = P 0 then (1 : ℝ) else 0) *
              cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k)) := fun P J =>
        k3_fiberNormSqComponent_slotExtendFib_eq (I := I) (M := M) g (b + w) (c + w) x
          (k3_slotExtendIterFib (I := I) (M := M) g b c x A w) e horth P J
      have hstep : ∀ J : Fin (c + (w + 1)) → Fin n,
          (∑ P : Fin (b + (w + 1)) → Fin n,
            V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
              (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                k3_slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J) =
          ∑ P' : Fin (b + w) → Fin n,
            V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k)) := by
        intro J
        calc (∑ P : Fin (b + (w + 1)) → Fin n,
              V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
                (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                  k3_slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J)
            = ∑ P : Fin (b + (w + 1)) → Fin n,
                V P * ((if J 0 = P 0 then (1 : ℝ) else 0) *
                  cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k))) :=
              Finset.sum_congr rfl (fun P _ => by rw [hpeel P J])
          _ = ∑ pr : Fin n × (Fin (b + w) → Fin n),
                V (Fin.cons pr.1 pr.2) * ((if J 0 = pr.1 then (1 : ℝ) else 0) *
                  cw pr.2 (fun k => J (Fin.succ k))) :=
              (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (b + w + 1) => Fin n))
                (fun pr : Fin n × (Fin (b + w) → Fin n) =>
                  V (Fin.cons pr.1 pr.2) * ((if J 0 = pr.1 then (1 : ℝ) else 0) *
                    cw pr.2 (fun k => J (Fin.succ k))))
                (fun P => V P * ((if J 0 = P 0 then (1 : ℝ) else 0) *
                  cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k))))
                (fun pr => by simp [Fin.consEquiv])).symm
          _ = ∑ p₀ : Fin n, ∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons p₀ P') * ((if J 0 = p₀ then (1 : ℝ) else 0) *
                  cw P' (fun k => J (Fin.succ k))) := Fintype.sum_prod_type _
          _ = ∑ P' : Fin (b + w) → Fin n, ∑ p₀ : Fin n,
                V (Fin.cons p₀ P') * ((if J 0 = p₀ then (1 : ℝ) else 0) *
                  cw P' (fun k => J (Fin.succ k))) := Finset.sum_comm
          _ = ∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k)) := by
              refine Finset.sum_congr rfl (fun P' _ => ?_)
              simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_zero]
              rw [Finset.sum_ite_eq Finset.univ (J 0) (fun p₀ =>
                V (Fin.cons p₀ P') * cw P' (fun k => J (Fin.succ k)))]
              rw [if_pos (Finset.mem_univ (J 0))]
      calc (∑ J : Fin (c + (w + 1)) → Fin n,
            (∑ P : Fin (b + (w + 1)) → Fin n,
              V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
                (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                  k3_slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J) ^ 2)
          = ∑ J : Fin (c + (w + 1)) → Fin n,
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k))) ^ 2 :=
            Finset.sum_congr rfl (fun J _ => by rw [hstep J])
        _ = ∑ pr : Fin n × (Fin (c + w) → Fin n),
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons pr.1 P') * cw P' pr.2) ^ 2 :=
            (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (c + w + 1) => Fin n))
              (fun pr : Fin n × (Fin (c + w) → Fin n) =>
                (∑ P' : Fin (b + w) → Fin n, V (Fin.cons pr.1 P') * cw P' pr.2) ^ 2)
              (fun J => (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k))) ^ 2)
              (fun pr => by simp [Fin.consEquiv])).symm
        _ = ∑ j₀ : Fin n, ∑ J' : Fin (c + w) → Fin n,
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons j₀ P') * cw P' J') ^ 2 := Fintype.sum_prod_type _
        _ ≤ ∑ j₀ : Fin n,
              (κ * ∑ P' : Fin (b + w) → Fin n, (V (Fin.cons j₀ P')) ^ 2) :=
            Finset.sum_le_sum (fun j₀ _ =>
              k3_sum_sq_component_slotExtendIterFib_op_le g x e horth w b c A κ hA
                (fun P' => V (Fin.cons j₀ P')))
        _ = κ * ∑ j₀ : Fin n, ∑ P' : Fin (b + w) → Fin n, (V (Fin.cons j₀ P')) ^ 2 := by
            rw [Finset.mul_sum]
        _ = κ * ∑ P : Fin (b + (w + 1)) → Fin n, (V P) ^ 2 := by
            refine congrArg (fun t : ℝ => κ * t) ?_
            exact Eq.trans (Fintype.sum_prod_type
                (fun pr : Fin n × (Fin (b + w) → Fin n) => (V (Fin.cons pr.1 pr.2)) ^ 2)).symm
              (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (b + w + 1) => Fin n))
                (fun pr : Fin n × (Fin (b + w) → Fin n) => (V (Fin.cons pr.1 pr.2)) ^ 2)
                (fun P => (V P) ^ 2)
                (fun pr => by simp [Fin.consEquiv]))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem k3_rfns_comp_slotExtendIterFib_op_le (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w p b c : ℕ) (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) (κ : ℝ) (_hκ : 0 ≤ κ)
    (hA : ∀ V : (Fin b → Fin n) → ℝ,
      ∑ L : Fin c → Fin n,
          (∑ Q : Fin b → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g x b c
              (show TensorRSSpace b c I x from A) n e Q L) ^ 2 ≤
        κ * ∑ Q : Fin b → Fin n, (V Q) ^ 2)
    (U : Tensor0SSpace p I x →L[ℝ] Tensor0SSpace (b + w) I x) :
    riemannianFiberNormSq (I := I) (M := M) g p (c + w) x
        (show TensorRSSpace p (c + w) I x from
          (k3_slotExtendIterFib (I := I) (M := M) g b c x A w).comp U) ≤
      κ * riemannianFiberNormSq (I := I) (M := M) g p (b + w) x
        (show TensorRSSpace p (b + w) I x from U) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g p (c + w) x _ e bse hn hbse horth]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g p (b + w) x _ e bse hn hbse horth]
  have hcomp : ∀ (K : Fin p → Fin n) (J : Fin (c + w) → Fin n),
      fiberNormSqComponent (I := I) (M := M) g x p (c + w)
          (show TensorRSSpace p (c + w) I x from
            (k3_slotExtendIterFib (I := I) (M := M) g b c x A w).comp U) n e K J =
        ∑ P : Fin (b + w) → Fin n,
          fiberNormSqComponent (I := I) (M := M) g x p (b + w)
            (show TensorRSSpace p (b + w) I x from U) n e K P *
            fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
              (show TensorRSSpace (b + w) (c + w) I x from
                k3_slotExtendIterFib (I := I) (M := M) g b c x A w) n e P J :=
    fun K J => k2_fiberNormSqComponent_compRS_eq (I := I) (M := M) g p (b + w) (c + w) x
      (show TensorRSSpace (b + w) (c + w) I x from
        k3_slotExtendIterFib (I := I) (M := M) g b c x A w)
      (show TensorRSSpace p (b + w) I x from U) e bse hbse horth K J
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun J (_ : J ∈ Finset.univ) => by rw [hcomp K J]))]
  refine le_trans (Finset.sum_le_sum (fun K (_ : K ∈ Finset.univ) =>
    k3_sum_sq_component_slotExtendIterFib_op_le (I := I) (M := M) g x e horth w b c A κ hA
      (fun P => fiberNormSqComponent (I := I) (M := M) g x p (b + w)
        (show TensorRSSpace p (b + w) I x from U) n e K P))) ?_
  rw [← Finset.mul_sum]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_appCcRS_ricciCometricFourTraceCastG0_corner_op_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (i : ℕ) (U : SmoothCcTensor g₀ 2 (4 + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
              (I := I) g₀ g₁) i i) U).toSection x) ≤
      4 * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x (U.toSection x) := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have h1δ₀ : (0 : ℝ) < 1 - δ₀ := by linarith
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hrepr02⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hWop : ∀ u : TangentSpace I x,
      g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u) ≤
      (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
    intro u
    have hs := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.sqrt_inner_gInvRaisedEndo_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ P y) htie
      (show δ < 1 from by linarith) hδ0 hbound x u
    have h0T : 0 ≤ g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u) :=
      DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    have h0u : 0 ≤ g₀.inner x u u := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hinv : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
      rw [div_le_div_iff₀ h1δ h1δ₀]
      linarith
    have hsq := Real.sq_sqrt h0T
    have hsqu := Real.sq_sqrt h0u
    have h1 : Real.sqrt (g₀.inner x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)) ≤
        (1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u) :=
      le_trans hs (mul_le_mul_of_nonneg_right hinv (Real.sqrt_nonneg _))
    calc g₀.inner x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
        = Real.sqrt (g₀.inner x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)) ^ 2 :=
          hsq.symm
      _ ≤ ((1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u)) ^ 2 :=
          by nlinarith [h1, Real.sqrt_nonneg (g₀.inner x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo (I := I) g₀ g₁ x u))]
      _ = (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
          rw [mul_pow, hsqu]
  have hHS : (∑ a : Fin n, ∑ b : Fin n,
      (g₀.inner x (e a)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
          (I := I) g₀ g₁ x (e b))) ^ 2) ≤
      (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2 := by
    rw [Finset.sum_comm]
    have hcol : ∀ b : Fin n,
        (∑ a : Fin n, (g₀.inner x (e a)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
            (I := I) g₀ g₁ x (e b))) ^ 2) ≤ (1 / (1 - δ₀)) ^ 2 := by
      intro b
      have hp := hpars (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
        (I := I) g₀ g₁ x (e b))
      rw [hp]
      refine le_trans (hWop (e b)) ?_
      rw [horth b b, if_pos rfl, mul_one]
    calc (∑ b : Fin n, ∑ a : Fin n, (g₀.inner x (e a)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
            (I := I) g₀ g₁ x (e b))) ^ 2)
        ≤ ∑ _b : Fin n, (1 / (1 - δ₀)) ^ 2 := Finset.sum_le_sum (fun b _ => hcol b)
      _ = (n : ℝ) * (1 / (1 - δ₀)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2 := by rw [hnE]
  have hA : ∀ V : (Fin 4 → Fin n) → ℝ,
      ∑ L : Fin 2 → Fin n,
          (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
                  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
                    (I := I) g₀ g₁).toSection x)) n e Q L) ^ 2 ≤
        (4 * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) *
          ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
    intro V
    have h := k3_fourTrace_hA (I := I) (M := M) g₀ g₁ x e horth V
    refine le_trans (le_of_eq ?_) (le_trans h ?_)
    · rfl
    · refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun Q _ => sq_nonneg _))
      calc 4 * ∑ a : Fin n, ∑ b : Fin n,
            (g₀.inner x (e a)
              (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.metricComparisonEndo
                (I := I) g₀ g₁ x (e b))) ^ 2
          ≤ 4 * ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) :=
            mul_le_mul_of_nonneg_left hHS (by norm_num)
        _ = 4 * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2 := by ring
  rw [appCcRS_toSection (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
    (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
        (I := I) g₀ g₁) i i) U x]
  rw [show (show Tensor0SSpace (4 + i) I x →L[ℝ] Tensor0SSpace (2 + i) I x from
        (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
            (I := I) g₀ g₁) i i).toSection x) =
      k3_slotExtendIterFib (I := I) (M := M) g₀ 4 2 x
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
            (I := I) g₀ g₁).toSection x) i from
    k3_appCcLeibnizPsi_diag_toSection (I := I) (M := M) g₀ 4 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
        (I := I) g₀ g₁) i x]
  exact k3_rfns_comp_slotExtendIterFib_op_le (I := I) (M := M) g₀ x e bse hnE hbse horth
    i 2 4 2
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
        (I := I) g₀ g₁).toSection x)
    (4 * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) (by positivity)
    hA
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (4 + i) I x from U.toSection x)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem b4_L0_topSeparated_proof (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (_hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g₀ g₁)).toSection x) ≤
          ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + K i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ₀ := by linarith
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  set d : ℝ := 1 / (1 - δ₀) with hd_def
  have hd : 0 ≤ d := by positivity
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ktop0, hKtop0_nn, Kc, hKc_nn, hTS⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CK, hCK_nn, hCK⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0KernelField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  set Qq : ℕ → ℝ := fun i => diagonalGridGrowthFactor (E := E) i *
    ∑ n ∈ Finset.range (i + 1), ∑ m ∈ Finset.range (i + 1 - n),
      fr ^ 3 * CA n * CA m * Combinatorics.windowPairCellCount (n + 2) (m + 2) with hQq_def
  have hQq_nn : ∀ i, 0 ≤ Qq i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) ?_
    refine Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun m _ => ?_))
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hfr 3) (hCA_nn n)) (hCA_nn m))
      (Combinatorics.windowPairCellCount_nonneg (n + 2) (m + 2))
  set Clow : ℕ → ℝ := fun i => (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
    ∑ k ∈ Finset.range i,
      C4 (i - k) * CK k * Combinatorics.windowPairCellCount (i - k + 1) (k + 3) with hClow_def
  have hClow_nn : ∀ i, 0 ≤ Clow i := by
    intro i
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i)) ?_
    refine Finset.sum_nonneg (fun k _ => ?_)
    exact mul_nonneg (mul_nonneg (hC4_nn (i - k)) (hCK_nn k))
      (Combinatorics.windowPairCellCount_nonneg (i - k + 1) (k + 3))
  set Kfun : ℕ → ℝ := fun i => 9 * (144 * fr * d ^ 2 * Qq i
    + 16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) + Clow i) with hKfun_def
  have hKfun_nn : ∀ i, 0 ≤ Kfun i := by
    intro i
    have h1 := hQq_nn i
    have h2 := hKc_nn (i + 1)
    have h3 := hClow_nn i
    have h4 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
    simp only [hKfun_def]
    positivity
  refine ⟨Kfun, hKfun_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set w : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hw_def
  have hw_nn : 0 ≤ w := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn (i + 1) (i + 3)
  have hbtop_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x _
  have hAgrid : ∀ n : ℕ, n ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2) :=
    fun n hn => le_trans (hCA g₁ P htie hδ_le hδ0 hbound n x)
      (mul_le_mul_of_nonneg_left
        (le_of_eq (b4_sum_atg_eq_bfgWindow b (show n + 2 ≤ (i + 1) + 1 from by omega)))
        (hCA_nn n))
  have hcore : ∀ n, n ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 4 n
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
      fr ^ 2 * CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2) := by
    intro n hn
    refine le_trans (b4_cDCIF_le (I := I) (M := M) g₀ g₁ n x) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hAgrid n (by omega)) (by positivity)
  have hWinner : ∀ m, m ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)).toSection x) ≤
      fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) := by
    intro m hm
    refine le_trans (b4_inner_le (I := I) (M := M) g₀ g₁ m x) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hAgrid m (by omega)) hfr
  have hquad : ∀ W23 : SmoothCcTensor g₀ 2 3,
      (∀ m, m ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x) ≤
        fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2)) →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 4 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) W23)).toSection x) ≤
      Qq i * w :=
    fun W23 hW => b4_quadArm_capped (I := I) (M := M) g₀ b hb_nn
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) W23 CA hCA_nn hfr
      (le_refl i) x hcore hW
  have hWa : ∀ m, m ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
            (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))).toSection x) ≤
      fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) := by
    intro m hm
    rw [b3_armOuter23_rfns_eq (I := I) (M := M) g₀ b3_kMid0Perm102
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁) m x]
    exact hWinner m hm
  have hWb : ∀ m, m ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3
            (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))).toSection x) ≤
      fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) := by
    intro m hm
    rw [b3_armOuter23_rfns_eq (I := I) (M := M) g₀ b3_kMid0Perm120
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁) m x]
    exact hWinner m hm
  have hrkval : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc
        (I := I) (M := M) g₀ g₁ P htie,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq
        (I := I) (M := M) g₀ P (i + 1) x]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_koszulCovecCc_le_iteratedCovGrad_symmetrization_succ (I := I) (M := M) g₀ P (i + 1) x) ?_
    exact b1_rfns_icg_symmS_le (I := I) (M := M) g₀ P (i + 2) x
  have hres : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁))
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (Kc (i + 1) * ((i : ℝ) + 1)) * w := by
    refine le_trans ((hTS g₁ P htie hδ_le hδ0 hbound (i + 1) x).2) ?_
    have hcell : ∀ k ∈ Finset.range (i + 1),
        b (i + 1 - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤ w := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
        (show k + 1 ≤ i + 1 from by omega)]
      refine le_trans (Combinatorics.single_factor_mul_boundedFactorGrid_le b hb_nn
        (K := i + 1) (k + 1) (i + 1 - k) (by omega) (by omega)) ?_
      rw [show (k + 1) + (i + 1 - k) = i + 2 from by omega, hw_def]
      exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb_nn (by omega)
    calc Kc (i + 1) * ∑ k ∈ Finset.range (i + 1),
            b (i + 1 - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
        ≤ Kc (i + 1) * ∑ k ∈ Finset.range (i + 1), w :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (hKc_nn (i + 1))
      _ = (Kc (i + 1) * ((i : ℝ) + 1)) * w := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hAsqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
        (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
      d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
      + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w) := by
    have hsplitA : (iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
        (connDiffSection (I := I) g₁ g₀)).toSection x =
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁))
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁))
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁)).toSection x := by
      rw [b1_toSection_sub (I := I) (M := M) g₀ 1 (2 + (i + 1))]
      abel
    rw [hsplitA]
    refine le_trans (b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 1 (2 + (i + 1)) x _ _)
      (add_le_add ?_ (b1_sqrt_le_of_le hres))
    refine le_trans (b4_sqrt_le_coeff_mul (c := d)
      (rfns_appCcRS_sharpFlatEndoCc_contravariantSlot_op_le (I := I) (M := M) g₀ g₁ P htie hδ₀
        hδ_le hδ0 hbound (2 + (i + 1))
        (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁)) x) hd) ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrkval) hd
  have hgrad_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)).toSection x)) ≤
      Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0
          (2 + (i + 2)) x ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)) := by
    have hval : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 4 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
        (Real.sqrt fr) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
      rw [Real.sq_sqrt hfr]
      exact b4_gradCore_le (I := I) (M := M) g₀ g₁ i x
    refine le_trans (b4_sqrt_le_coeff_mul hval (Real.sqrt_nonneg fr)) ?_
    exact mul_le_mul_of_nonneg_left hAsqrt (Real.sqrt_nonneg fr)
  have hjets : (iteratedCovGrad (I := I) g₀ 2 4 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 4 i (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3201) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2301) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3102) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1302) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1203) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2103) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 4 i (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3012) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁))).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2013) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)).toSection x := by
    rw [b3_order0KernelField_eq_arm_combination (I := I) (M := M) g₀ g₁]
    simp only [iteratedCovGrad_sub, iteratedCovGrad_add, b1_toSection_sub, b1_toSection_add]
  have hq1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3201) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x) ≤ Qq i * w := by
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm3201
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) i x]
    exact hquad _ hWa
  have hq2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2301) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)).toSection x) ≤ Qq i * w := by
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2301) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm i x]
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm2301
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) i x]
    exact hquad _ hWa
  have hq3 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3102) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x) ≤ Qq i * w := by
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm3102
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) i x]
    exact hquad _ hWb
  have hq4 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1302) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)).toSection x) ≤ Qq i * w := by
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1302) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm i x]
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm1302
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)) i x]
    exact hquad _ hWinner
  have hq5 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1203) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))).toSection x) ≤ Qq i * w := by
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm1203
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)) i x]
    exact hquad _ hWinner
  have hq6 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2103) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)).toSection x) ≤ Qq i * w := by
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2103) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm i x]
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm2103
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) i x]
    exact hquad _ hWb
  have hs7 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3012) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁))).toSection x)) ≤
      Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)) := by
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm3012
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁) i x]
    exact hgrad_sqrt
  have hs8 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2013) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm)).toSection x)) ≤
      Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2013) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerContractionSwapPerm i x]
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm2013
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁) i x]
    exact hgrad_sqrt
  have hWK_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x)) ≤
      6 * Real.sqrt (Qq i * w)
      + 2 * (Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w))) := by
    rw [hjets]
    refine le_trans (b4_sqrt_eightArm (I := I) (M := M) g₀ 2 (4 + i) x _ _ _ _ _ _ _ _) ?_
    have t1 := b1_sqrt_le_of_le hq1
    have t2 := b1_sqrt_le_of_le hq2
    have t3 := b1_sqrt_le_of_le hq3
    have t4 := b1_sqrt_le_of_le hq4
    have t5 := b1_sqrt_le_of_le hq5
    have t6 := b1_sqrt_le_of_le hq6
    linarith [t1, t2, t3, t4, t5, t6, hs7, hs8]
  have hcval : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i i)
        (iteratedCovGrad (I := I) g₀ 2 4 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x) ≤
      (2 * Real.sqrt fr * d) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) := by
    rw [show (2 * Real.sqrt fr * d) ^ 2 = 4 * fr * d ^ 2 from by
      rw [mul_pow, mul_pow, Real.sq_sqrt hfr]; norm_num]
    exact rfns_appCcRS_ricciCometricFourTraceCastG0_corner_op_le (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound i
      (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)) x
  have hlow : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 (4 + k) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i k)
          (iteratedCovGrad (I := I) g₀ 2 4 k
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x) ≤ Clow i * w := by
    refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 2 4 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁) i x) ?_
    have hcell : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ 4 2 (i - k)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 2 4 k
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) ≤
        C4 (i - k) * CK k * Combinatorics.windowPairCellCount (i - k + 1) (k + 3) * w := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h4 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (i - k)) x
          ((iteratedCovGrad (I := I) g₀ 4 2 (i - k)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
          C4 (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1) (i - k + 1) :=
        le_trans (hC4 g₁ P htie hδ_le hδ0 hbound (i - k) x)
          (mul_le_mul_of_nonneg_left
            (le_of_eq (b4_sum_atg_eq_bfgWindow b (show (i - k) + 1 ≤ (i + 1) + 1 from by omega)))
            (hC4_nn (i - k)))
      have hKk : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + k) x
          ((iteratedCovGrad (I := I) g₀ 2 4 k
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) ≤
          CK k * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) :=
        le_trans (hCK g₁ P htie hδ_le hδ0 hbound k x)
          (mul_le_mul_of_nonneg_left
            (le_of_eq (b4_sum_atg_eq_bfgWindow b (show k + 3 ≤ (i + 1) + 1 from by omega)))
            (hCK_nn k))
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (i - k)) x
              ((iteratedCovGrad (I := I) g₀ 4 2 (i - k)
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + k) x
              ((iteratedCovGrad (I := I) g₀ 2 4 k
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x)
          ≤ (C4 (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1) (i - k + 1)) *
              (CK k * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3)) :=
            mul_le_mul h4 hKk
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (4 + k) x _)
              (mul_nonneg (hC4_nn (i - k))
                (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn (i + 1) (i - k + 1)))
        _ = (C4 (i - k) * CK k) *
              (Combinatorics.boundedFactorGridWindow b (i + 1) (i - k + 1) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3)) := by ring
        _ ≤ (C4 (i - k) * CK k) *
              (Combinatorics.windowPairCellCount (i - k + 1) (k + 3) *
                Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k + 1) + (k + 3) - 1)) :=
            mul_le_mul_of_nonneg_left
              (Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (i - k + 1) (k + 3)
                (by omega) (by omega))
              (mul_nonneg (hC4_nn (i - k)) (hCK_nn k))
        _ = C4 (i - k) * CK k * Combinatorics.windowPairCellCount (i - k + 1) (k + 3) * w := by
            rw [show (i - k + 1) + (k + 3) - 1 = i + 3 from by omega, hw_def]
            ring
    calc (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ∑ k ∈ Finset.range i,
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (i - k)) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 (i - k)
                    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 2 4 k
                    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x)
        ≤ (i : ℝ) * diagonalGridGrowthFactor (E := E) i *
            ∑ k ∈ Finset.range i,
              C4 (i - k) * CK k * Combinatorics.windowPairCellCount (i - k + 1) (k + 3) * w :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
            (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
      _ = Clow i * w := by
          simp only [hClow_def]
          rw [← Finset.sum_mul]
          ring
  have hsplitL0 : (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g₀ g₁)).toSection x =
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 4 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x +
      (∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 (4 + k) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i k)
            (iteratedCovGrad (I := I) g₀ 2 4 k
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField_eq_ricciCometricFourTrace_comp_kernelField (I := I) (M := M) g₀ g₁,
      iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 2 4 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁) i,
      b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i)]
  have hself : Real.sqrt fr * Real.sqrt fr = fr := Real.mul_self_sqrt hfr
  have hfold1 : (12 * Real.sqrt fr * d) * Real.sqrt (Qq i * w) =
      Real.sqrt ((144 * fr * d ^ 2 * Qq i) * w) := by
    rw [b4_coeff_into_sqrt (show (0 : ℝ) ≤ 12 * Real.sqrt fr * d from by positivity),
      show (12 * Real.sqrt fr * d) ^ 2 * Qq i = 144 * fr * d ^ 2 * Qq i from by
        rw [mul_pow, mul_pow, Real.sq_sqrt hfr]; ring]
  have hfold2 : (4 * fr * d) * Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w) =
      Real.sqrt ((16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1))) * w) := by
    rw [b4_coeff_into_sqrt (show (0 : ℝ) ≤ 4 * fr * d from by positivity),
      show (4 * fr * d) ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) = 16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) from by ring]
  have htot : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (4 * fr * d ^ 2) * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
      + (Real.sqrt ((144 * fr * d ^ 2 * Qq i) * w) + Real.sqrt ((16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1))) * w) + Real.sqrt ((Clow i) * w)) := by
    rw [hsplitL0]
    refine le_trans (b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hcs : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 4 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x)) ≤
        (2 * Real.sqrt fr * d) *
          (6 * Real.sqrt (Qq i * w)
            + 2 * (Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
              + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)))) :=
      le_trans (b4_sqrt_le_coeff_mul hcval (by positivity))
        (mul_le_mul_of_nonneg_left hWK_sqrt (by positivity))
    have hls : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 2 (4 + k) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i k)
            (iteratedCovGrad (I := I) g₀ 2 4 k
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x)) ≤ Real.sqrt (Clow i * w) := b1_sqrt_le_of_le hlow
    refine le_trans (add_le_add hcs hls) (le_of_eq ?_)
    rw [← hfold1, ← hfold2]
    linear_combination (4 * d ^ 2 * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
      + 4 * d * Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)) * hself
  have hfin := b4_young_head3
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x _) hw_nn
    (show (0 : ℝ) ≤ 4 * fr * d ^ 2 from by positivity)
    (show (0 : ℝ) ≤ 144 * fr * d ^ 2 * Qq i from by have h1 := hQq_nn i; positivity)
    (show (0 : ℝ) ≤ 16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) from by
      have h1 := hKc_nn (i + 1)
      have h2 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
      positivity)
    (show (0 : ℝ) ≤ Clow i from hClow_nn i)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x _) htot
  refine le_trans hfin ?_
  have hcoef : (3 / 2 : ℝ) * (4 * fr * d ^ 2) ^ 2 ≤ ((21 / 4) * fr * d ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (fr * d ^ 2)]
  have hKeq : Kfun i = 9 * (144 * fr * d ^ 2 * Qq i + 16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) + Clow i) := by
    simp only [hKfun_def]
  rw [hKeq]
  exact add_le_add (mul_le_mul_of_nonneg_right hcoef hbtop_nn) (le_refl _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma b4_young_head1 {T e btop c K w : ℝ}
    (hbtop : 0 ≤ btop) (hw : 0 ≤ w) (he : 0 ≤ e) (hc : 0 ≤ c) (hK : 0 ≤ K) (hT0 : 0 ≤ T)
    (hT : Real.sqrt T ≤ e * Real.sqrt btop + c * Real.sqrt (K * w)) :
    T ≤ (5 / 4) * e ^ 2 * btop + 5 * c ^ 2 * K * w := by
  set u : ℝ := e * Real.sqrt btop with hu_def
  set v : ℝ := c * Real.sqrt (K * w) with hv_def
  have hu0 : 0 ≤ u := mul_nonneg he (Real.sqrt_nonneg _)
  have hv0 : 0 ≤ v := mul_nonneg hc (Real.sqrt_nonneg _)
  have hTuv : T ≤ (u + v) ^ 2 := by
    have hsq : Real.sqrt T ^ 2 ≤ (u + v) ^ 2 := by
      nlinarith [hT, Real.sqrt_nonneg T]
    rw [Real.sq_sqrt hT0] at hsq
    exact hsq
  have hyoung := rfns_tl_young_sq u v (1 / 4) (by norm_num)
  have hu2 : u ^ 2 = e ^ 2 * btop := by
    rw [hu_def, mul_pow, Real.sq_sqrt hbtop]
  have hv2 : v ^ 2 = c ^ 2 * (K * w) := by
    rw [hv_def, mul_pow, Real.sq_sqrt (by positivity)]
  have hinv : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
  rw [hinv] at hyoung
  calc T ≤ (u + v) ^ 2 := hTuv
    _ ≤ (1 + 1 / 4) * u ^ 2 + (1 + 4) * v ^ 2 := hyoung
    _ = (5 / 4) * e ^ 2 * btop + 5 * c ^ 2 * K * w := by
        rw [hu2, hv2]
        ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem riemannianFiberNormSq_iteratedCovGrad_refoldKernelContractionMonomialField_topSeparated_and_lowerWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (i : ℕ) (x : M),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFoldRemainderSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (ccTensor02Symm (I := I) (M := M) g₀ P))))))).toSection x) ≤
          ((1 / (1 - δ₀)) ^ 2) ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        ∧
        (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                σ)).toSection x
            - (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFoldRemainderSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (ccTensor02Symm (I := I) (M := M) g₀ P))))))).toSection x) ≤
          K i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
  obtain ⟨K, hK_nn, hres⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_rfns_icg_refoldKernelContractionMonomialField_leibnizResidual_window
      (I := I) (M := M) g₀ hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound σ i x
  exact ⟨DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_compRS_mvPairTraceOp_leibnizCorner_le
      (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound σ i x,
    hres g₁ P htie hδ_le hδ0 hbound σ i x⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem refoldKernelContractionMonomialField_eq_of_finrank_one (h1 : Module.finrank ℝ E = 1)
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ σ' : Equiv.Perm (Fin 4)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ' := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField_toSection (I := I) (M := M) g₀ g₁ G σ x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField_toSection (I := I) (M := M) g₀ g₁ G σ' x]
  refine congrArg (fun (T : Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
      Tensor0SBundle.Tensor0SSpace 2 I x) =>
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM T)) ?_
  rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M) g₁
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G) σ x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.curvatureRefoldMonomialFrameContraction (I := I) (M := M)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G) σ
        (smoothOrthoFrame (I := I) g₁ x) x from rfl,
    show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M) g₁
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G) σ' x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.curvatureRefoldMonomialFrameContraction (I := I) (M := M)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G) σ'
        (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ)
  apply ContinuousMultilinearMap.ext
  intro v
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialFibFixedFrame_toModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialFibFixedFrame_toModel]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  refine congrArg _ ?_
  have hperm : ∀ (ρ : Equiv.Perm (Fin 4)) (W : Fin 4 → E),
      Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G x)
          (fun i => W (ρ i)) =
        Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G x) W := by
    intro ρ W
    rw [← ContinuousMultilinearMap.domDomCongr_apply,
      dim1_domDomCongr_eq (E := E) (d := 4) h1
        (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ from
          Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorRank4EvalAtUnitZeroSec
              (I := I) (M := M) g₀ G x)) ρ]
  rw [hperm σ, hperm σ']

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem b4_refold_topSeparated_proof (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (_hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
                (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x) ≤
          ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + K i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  by_cases hn1 : Module.finrank ℝ E = 1
  · refine ⟨fun _ => 0, fun _ => le_refl 0, ?_⟩
    intro g₁ P htie δ hδ_le hδ0 hbound i x
    have hzero : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
        (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 = 0 := by
      rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
          (I := I) (M := M) g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
          (1 / 2 : ℝ) •
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
              + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) 1) from rfl]
      rw [refoldKernelContractionMonomialField_eq_of_finrank_one (I := I) (M := M) hn1 g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3) (Equiv.swap (0 : Fin 4) 2),
        refoldKernelContractionMonomialField_eq_of_finrank_one (I := I) (M := M) hn1 g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) (Equiv.swap (0 : Fin 4) 2),
        refoldKernelContractionMonomialField_eq_of_finrank_one (I := I) (M := M) hn1 g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) 1 (Equiv.swap (0 : Fin 4) 2)]
      rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2) = 0 from by abel]
      rw [smul_zero]
    rw [hzero, rfns_tl_icg_zero (I := I) g₀ 2 2 i,
      rfns_tl_toSection_zero (I := I) g₀ 2 (2 + i) x,
      riemannianFiberNormSq_zero (I := I) (M := M) g₀ 2 (2 + i) x]
    simp only [zero_mul, add_zero]
    exact mul_nonneg (sq_nonneg _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x _)
  · have hn2 : 2 ≤ Module.finrank ℝ E := by
      have h1 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
      omega
    obtain ⟨KM, hKM_nn, hKM⟩ := riemannianFiberNormSq_iteratedCovGrad_refoldKernelContractionMonomialField_topSeparated_and_lowerWindow_le (I := I) (M := M) g₀ hδ₀
    refine ⟨fun i => 5 * 2 ^ 2 * KM i,
      fun i => by have := hKM_nn i; positivity, ?_⟩
    intro g₁ P htie δ hδ_le hδ0 hbound i x
    have hb_nn : ∀ l, (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    have hw_nn : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_nonneg _ hb_nn (i + 1) (i + 3)
    have hsm : ∀ σ : Equiv.Perm (Fin 4),
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) σ)).toSection x)) ≤
        (1 / (1 - δ₀)) ^ 2 * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0
            (2 + (i + 2)) x ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          + Real.sqrt (KM i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
      intro σ
      have hconj := hKM g₁ P htie hδ_le hδ0 hbound σ i x
      have h1 := b1_sqrt_le_of_le hconj.1
      have h2 := b1_sqrt_le_of_le hconj.2
      have hd2 : Real.sqrt (((1 / (1 - δ₀)) ^ 2) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) =
          (1 / (1 - δ₀)) ^ 2 *
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) := by
        rw [Real.sqrt_mul (by positivity) _, Real.sqrt_sq (by positivity)]
      calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              σ)).toSection x)))
          = Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              σ)).toSection x)
                - (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFoldRemainderSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (ccTensor02Symm (I := I) (M := M) g₀ P))))))).toSection x)
                + (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFoldRemainderSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (ccTensor02Symm (I := I) (M := M) g₀ P))))))).toSection x)) := by
            rw [sub_add_cancel]
        _ ≤ Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              σ)).toSection x)
                - (ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFoldRemainderSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (ccTensor02Symm (I := I) (M := M) g₀ P))))))).toSection x))
            + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
                ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.secondMetricPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciFoldRemainderSlotPerm
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (ccTensor02Symm (I := I) (M := M) g₀ P))))))).toSection x)) :=
            b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _
        _ ≤ Real.sqrt (KM i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
            + Real.sqrt (((1 / (1 - δ₀)) ^ 2) ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add h2 h1
        _ = (1 / (1 - δ₀)) ^ 2 *
              Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
            + Real.sqrt (KM i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
            rw [hd2]
            ring
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
          (I := I) (M := M) g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x =
        (1 / 2 : ℝ) •
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2))).toSection x
          + (iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3))).toSection x
          - (iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))).toSection x
          - (iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) 1)).toSection x) := by
      rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
          (I := I) (M := M) g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
          (1 / 2 : ℝ) •
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
              + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) 1) from rfl]
      rw [b1_iteratedCovGrad_smul (I := I) (M := M) g₀ 2 2 i]
      rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i, iteratedCovGrad_sub (I := I) g₀ 2 2 i,
        iteratedCovGrad_add (I := I) g₀ 2 2 i]
      rw [b1_toSection_smul (I := I) (M := M) g₀ 2 (2 + i)]
      rw [b1_toSection_sub (I := I) (M := M) g₀ 2 (2 + i),
        b1_toSection_sub (I := I) (M := M) g₀ 2 (2 + i),
        b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i)]
    have htot : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
            (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x)) ≤
        (2 * (1 / (1 - δ₀)) ^ 2) * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0
            (2 + (i + 2)) x ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          + 2 * Real.sqrt (KM i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
      rw [hsplit]
      refine le_trans (b4_sqrt_le_coeff_mul (c := 1 / 2)
        (le_of_eq (b1_rfns_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2) _))
        (by norm_num)) ?_
      have hsub2 := b1_sqrt_rfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2))).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3))).toSection x
        - (iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) 1)).toSection x)
      have hsub1 := b1_sqrt_rfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2))).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))).toSection x)
      have hadd1 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3))).toSection x)
      have h1 := hsm (Equiv.swap (0 : Fin 4) 2)
      have h2 := hsm (Equiv.swap (1 : Fin 4) 3)
      have h3 := hsm (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
      have h4 := hsm 1
      linarith [hsub2, hsub1, hadd1, h1, h2, h3, h4]
    have hfin := b4_young_head1 (hb_nn (i + 2)) hw_nn
      (show (0 : ℝ) ≤ 2 * (1 / (1 - δ₀)) ^ 2 from by positivity)
      (show (0 : ℝ) ≤ (2 : ℝ) from by norm_num) (hKM_nn i)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x _) htot
    refine le_trans hfin (add_le_add ?_ (le_refl _))
    refine mul_le_mul_of_nonneg_right ?_ (hb_nn (i + 2))
    have hfr2 : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn2
    have hd4 : (0 : ℝ) ≤ ((1 / (1 - δ₀)) ^ 2) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul hfr2 hfr2 (by norm_num) (by linarith)) hd4]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem riemannianFiberNormSq_iteratedCovGrad_refoldKernelContractionField_symmetrizationSecondCovGrad_topAmplitude_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
                (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x) ≤
          ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + K i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
  b4_refold_topSeparated_proof (I := I) (M := M) g₀ hδ₀ hδ₀half

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_topAmplitude_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g₀ g₁)).toSection x) ≤
          ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + K i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
  b4_L0_topSeparated_proof (I := I) (M := M) g₀ hδ₀ hδ₀half

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

private theorem rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombination_topSeparated_budgetDualCap_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                  (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ g₁)).toSection x) ≤
          ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + C i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  by_cases hn1 : Module.finrank ℝ E = 1
  · refine ⟨0, le_refl 0, ?_, fun _ => 0, fun _ => le_refl 0, ?_⟩
    · rw [mul_zero]
      rw [rfns_tl_fibreConst_one hn1]
      norm_num
    · intro g₁ P htie δ hδ_le hδ0 hbound i x
      have hS : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁ = (0 : SmoothCcTensor g₀ 2 2) := by
        rw [dim1_linearizedRicciConnDiffOrder0CoeffField_eq_zero (I := I) (M := M) hn1 g₀ g₁,
          dim1_ricciArmOrder0RiemannCoeff_eq_zero (I := I) (M := M) hn1 g₀ g₁]
        rw [smul_zero, add_zero]
      rw [hS]
      rw [rfns_tl_icg_zero (I := I) g₀ 2 2 i]
      rw [rfns_tl_toSection_zero (I := I) g₀ 2 (2 + i) x]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 2 (2 + i) x]
      rw [show ((0 : ℝ)) ^ 2 = 0 from by norm_num, zero_mul, zero_mul, add_zero]
  · have hn2 : 2 ≤ Module.finrank ℝ E := by
      have h1 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
      omega
    obtain ⟨KC, hKC_nn, hKC⟩ := riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_topAmplitude_le (I := I) (M := M) g₀ hδ₀ hδ₀half
    obtain ⟨KR, hKR_nn, hKR⟩ := riemannianFiberNormSq_iteratedCovGrad_refoldKernelContractionField_symmetrizationSecondCovGrad_topAmplitude_le (I := I) (M := M) g₀ hδ₀ hδ₀half
    obtain ⟨KA, hKA_nn, hKA⟩ :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0AACommCoeffField_window
        (I := I) (M := M) g₀ hδ₀
    obtain ⟨KB, hKB_nn, hKB⟩ := riemannianFiberNormSq_iteratedCovGrad_bgRDiffRefoldRemainderField_boundedFactorGridWindow_le (I := I) (M := M) g₀ hδ₀
    obtain ⟨KM, hKM_nn, hKM⟩ := b1_fixedField_jet_bound (I := I) (M := M) g₀ 2 2
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
          (I := I) (M := M) g₀ g₀)
    refine ⟨(804 / 125 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2,
      by positivity,
      rfns_tl_budgetDualCap (Module.finrank ℝ E) hn2 hδ₀ hδ₀half
        (by norm_num) (by norm_num),
      fun i => 505 * (KC i + KR i + KA i + KB i + KM i),
      fun i => by
        have h1 := hKC_nn i
        have h2 := hKR_nn i
        have h3 := hKA_nn i
        have h4 := hKB_nn i
        have h5 := hKM_nn i
        positivity, ?_⟩
    intro g₁ P htie δ hδ_le hδ0 hbound i x
    have hQsymm : ∀ (y : M) (v w : TangentSpace I y),
        smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w =
        smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y w v := by
      intro y v w
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P y v w,
        ccTensorBilin_symmS (I := I) (M := M) g₀ P y w v,
        ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
      ring
    have htie' : ∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w := by
      intro y v w
      rw [show ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w =
          (1 / 2 : ℝ) * (smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w
            + smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y w v) from by
        rw [ccTensorBilinSymm_apply]]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P y v w,
        ccTensorBilin_symmS (I := I) (M := M) g₀ P y w v,
        ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, htie y v w,
        ccTensorBilinSymm_apply]
      ring
    have hhalf := b1_halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
      (I := I) (M := M) g₀ g₁ (ccTensor02Symm (I := I) (M := M) g₀ P) htie' hQsymm
    have hdec : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
          (I := I) (M := M) g₀ g₁
        + (1 / 2 : ℝ) •
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₁ =
        (((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀ := by
      have hgoal : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
          (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁
          - (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀ := by
        rw [← hhalf]
        rw [smul_sub]
      have hstep : (((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + ((1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀ g₁
            - (1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀ g₀) := by
        rw [show (((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁
            + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁
            + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) from by abel]
        rw [hgoal]
      rw [hstep]
      abel
    rw [hdec]
    rw [iteratedCovGrad_add (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i,
      iteratedCovGrad_add (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i]
    rw [b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i), b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i),
      b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i), b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i)]
    have hb_nn : ∀ l, (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    have hw_nn : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_nonneg _ hb_nn (i + 1) (i + 3)
    have hw_one : (1 : ℝ) ≤ Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
      Combinatorics.one_le_boundedFactorGridWindow _ hb_nn (by omega)
    have hL0b := hKC g₁ P htie hδ_le hδ0 hbound i x
    have hRb := hKR g₁ P htie hδ_le hδ0 hbound i x
    have hAb := hKA g₁ P htie hδ_le hδ0 hbound i x
    have hBb := hKB g₁ P htie hδ_le hδ0 hbound i x
    have hMb : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          ((1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀)).toSection x) ≤
        KM i * Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
      refine le_trans (hKM i x) ?_
      nlinarith [hw_one, hKM_nn i]
    set T1 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
        (I := I) (M := M) g₀ g₁)).toSection x with hT1_def
    set T2 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
        (I := I) (M := M) g₀ g₁)).toSection x with hT2_def
    set T3 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffRefoldRemainderField
        (I := I) (M := M) g₀ g₁)).toSection x with hT3_def
    set T4 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
        (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x with hT4_def
    set T5 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
          (I := I) (M := M) g₀ g₀)).toSection x with hT5_def
    set btop : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) with hbtop_def
    set w : ℝ := Combinatorics.boundedFactorGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) with hw_def
    have hsq_chain : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) ≤
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T1)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T2)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T3)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T4)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T5) := by
      have h4 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x
        (((T1 + T2) + T3) + T4) T5
      have h3 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((T1 + T2) + T3) T4
      have h2 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x (T1 + T2) T3
      have h1 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x T1 T2
      linarith [h1, h2, h3, h4]
    have hsp1 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T1) ≤
        ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
        + Real.sqrt (KC i * w) :=
      b1_sqrt_head_split (by positivity) (hb_nn (i + 2)) (hKC_nn i) hw_nn hL0b
    have hsp4 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T4) ≤
        ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
        + Real.sqrt (KR i * w) :=
      b1_sqrt_head_split (by positivity) (hb_nn (i + 2)) (hKR_nn i) hw_nn hRb
    have hsp2 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T2) ≤
        Real.sqrt (KA i * w) := b1_sqrt_le_of_le hAb
    have hsp3 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T3) ≤
        Real.sqrt (KB i * w) := b1_sqrt_le_of_le hBb
    have hsp5 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T5) ≤
        Real.sqrt (KM i * w) := b1_sqrt_le_of_le hMb
    have hTsum : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) ≤
        (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)) * Real.sqrt btop
        + (Real.sqrt (KC i * w) + Real.sqrt (KR i * w) + Real.sqrt (KA i * w)
          + Real.sqrt (KB i * w) + Real.sqrt (KM i * w)) := by
      have hexp : (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)) * Real.sqrt btop =
          ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop := by
        ring
      rw [hexp]
      linarith [hsq_chain, hsp1, hsp2, hsp3, hsp4, hsp5]
    have hfin := b1_young_assembly (hb_nn (i + 2)) hw_nn
      (by positivity : (0 : ℝ) ≤ (23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
      (by positivity : (0 : ℝ) ≤ (21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
      (hKC_nn i) (hKR_nn i) (hKA_nn i) (hKB_nn i) (hKM_nn i)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) hTsum
    have hEamp : (((201 : ℝ) / 200) *
        (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2))) ^ 2 =
        ((804 / 125 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 := by
      ring
    rw [hEamp] at hfin
    exact hfin

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

private theorem linearizedRicciConnDiffOrder0RiemannHalfCombination_perOrder_l2_topArm_tameEnvelope_generic_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), a < i →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                  (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
              ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
  classical
  obtain ⟨ε, hε_nn, hε_cap, C, hC_nn, hC⟩ :=
    rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombination_topSeparated_budgetDualCap_le
      (I := I) (M := M) g₀ hδ₀ hδ₀half
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders
      (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * Kflat i, fun i => mul_nonneg (hC_nn i) (hKflat_nn i),
    ε, hε_nn, hε_cap, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨hWint, hWbound⟩ := hKflat P hPball i
    have hbint : MeasureTheory.Integrable
        (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      DifferentialGeometry.Integral.Connection.integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)
    have hF_int : MeasureTheory.Integrable
        (fun x => ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
          + C i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      MeasureTheory.Integrable.add (hbint.const_mul (ε ^ 2)) (hWint.const_mul (C i))
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁))
      (fun x => ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
        + C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
      hF_int
      (fun x => hC g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_add (hbint.const_mul (ε ^ 2)) (hWint.const_mul (C i)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hPtop : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
          (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]
    rw [hPtop]
    have h2 : C i * (∫ x, Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      calc C i * (∫ x, Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
          ≤ C i * (Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hWbound (hC_nn i)
        _ = (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
    linarith
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hK_nn : (0 : ℝ) ≤ C i * Kflat i := mul_nonneg (hC_nn i) (hKflat_nn i)
    have h1 : (0 : ℝ) ≤ (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
      mul_nonneg hK_nn (by linarith)
    have h2 : (0 : ℝ) ≤ ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 :=
      mul_nonneg (sq_nonneg ε) (sq_nonneg _)
    nlinarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem exists_linearizedRicciArm0CorrField_realizedFam_jetL2_topArm_tameEnvelope_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), a < i → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0Coeff
                  (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
                + (3 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
              ε ^ 2 * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by
  classical
  obtain ⟨K, hK_nn, ε, hε_nn, hε_cap, hK⟩ :=
    linearizedRicciConnDiffOrder0RiemannHalfCombination_perOrder_l2_topArm_tameEnvelope_generic_highOrder
      (I := I) (M := M) g₀ a ha_super hR hδ₀ hδ₀half
  refine ⟨K, hK_nn, ε, hε_nn, hε_cap, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hnorm_le : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤
        (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul', iteratedCovGrad_smul']
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖
        ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := hnorm_le j
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hwin_ineq : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have hnorm := hnorm_le j
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    nlinarith [mul_le_mul hnorm hnorm (norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrArm0Combination_eq_order0_add_halfRiemann
    (I := I) (M := M) g₀ T T' hδ hδ' s]
  have hmain := hK (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
  have hwinsum : ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_le_sum (fun j _ => hwin_ineq j)
  have h1 : K i * (1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
      K i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (hK_nn i)
  have h2 : ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
        (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      ε ^ 2 * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (hwin_ineq (i + 2)) (sq_nonneg ε)
  linarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem linearizedRicciArm0CorrField_allOrder_tameEnvelope_interface
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s
                + (3 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
                    (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
              ε ^ 2 * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by
  classical
  obtain ⟨Kle, hKle_nn, hKle⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Kgt, hKgt_nn, ε, hε_nn, hε_cap, hKgt⟩ :=
    exists_linearizedRicciArm0CorrField_realizedFam_jetL2_topArm_tameEnvelope_highOrder
      (I := I) (M := M) g₀ a ha_super hR hδ₀ hδ₀half
  refine ⟨fun i => Kle i + Kgt i, fun i => add_nonneg (hKle_nn i) (hKgt_nn i),
    ε, hε_nn, hε_cap, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
  have hid :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
      (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec.2.2.2.2.1
  rw [show linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0Coeff
          (I := I) g₀ T T' hδ hδ' s
        - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s from hid s]
  have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have htop_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdist : (Kle i + Kgt i) * (1 + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) =
      Kle i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
      Kgt i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := add_mul _ _ _
  rcases le_or_gt i a with hia | hia
  · have hb := hKle T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hia s hs
    have h1 : (0 : ℝ) ≤ Kgt i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) :=
      mul_nonneg (hKgt_nn i) (by linarith)
    have h2 : (0 : ℝ) ≤ ε ^ 2 * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
      mul_nonneg (sq_nonneg ε) htop_nn
    linarith
  · have hb := hKgt T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hia s hs
    have h1 : (0 : ℝ) ≤ Kle i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) :=
      mul_nonneg (hKle_nn i) (by linarith)
    linarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem linearizedRicciThreeArmHjoint_add (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s + B s) (δ := δ) (δ' := δ') := by
  have hadd := jointTotalSpaceRS_add_fw (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem linearizedRicciThreeArmHjoint_add_smul (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s + c • B s) (δ := δ) (δ' := δ') := by
  have hsmul := lieArm_jointRS_const_smul_local (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) c
    (fun p : M × ℝ => (B p.2).toSection p.1) hB
  have hadd := jointTotalSpaceRS_add_fw (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => c • (B p.2).toSection p.1)
    hA hsmul
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem threeArmHjoint_const_smul_fw (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => c • B s) (δ := δ) (δ' := δ') := by
  have hsmul := lieArm_jointRS_const_smul_local (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) c
    (fun p : M × ℝ => (B p.2).toSection p.1) hB
  refine hsmul.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem exists_riemannPalatini_curvatureRefold_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_half : δ₀ ≤ 1 / 2) :
    ∃ Λra : ℝ, 0 ≤ Λra ∧ ∃ Kra : ℕ → ℝ, (∀ i, 0 ≤ Kra i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0ra : ℝ → SmoothCcTensor g₀ 2 2) (C2ra : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0ra (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2ra (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                  (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0ra s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 (C2ra s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0ra s).toSection x) ≤
              Λra ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ Λra ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2ra s).toSection x) ≤
              (max (8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0ra s)‖ ^ 2 ≤
              Kra i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2ra s)‖ ^ 2 ≤
              Kra i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) :=
  by
    classical
    obtain ⟨Λid, hΛid_nn, Kid, hKid_nn, qA, qB, hqAB, hID⟩ :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_riemannPalatini_refold_identity_data
        (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Λrm, hΛrm_nn, hRm⟩ :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_ricciArmOrder0RiemannCoeff_realizedFam_riemannianFiberNormSq_ballUniform_sq
        (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Kwin, hKwin_nn, hWin⟩ :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_riemannPalatiniRefoldC2Family_l2JetWindow
        (I := I) (M := M) g₀ a ha_super hR hδ₀ qA qB hqAB
    have hsum_nn : (0 : ℝ) ≤ Λid ^ 2 + Λrm ^ 2 := by positivity
    refine ⟨Real.sqrt (Λid ^ 2 + Λrm ^ 2), Real.sqrt_nonneg _,
      fun i => Kid i + Kwin i,
      fun i => by
        have h1 := hKid_nn i
        have h2 := hKwin_nn i
        linarith, ?_⟩
    intro T hTsymm δ hδ_le hδ hδZ hTjets
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ_half : δ ≤ 1 / 2 := hδ_le.trans hδ₀_half
    obtain ⟨C0ra, hjC0, hidRA, hsupC0, henvC0⟩ := hID T hTsymm hδ_le hδ hδZ hTjets
    obtain ⟨-, henvC2⟩ := hWin T hδ_le hδ_half hδ hδZ hTjets
    refine ⟨C0ra,
      fun s => (2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannPalatiniRefoldC2Family
          (I := I) (M := M) g₀ T hδ hδZ qA qB s,
      hjC0,
      threeArmHjoint_const_smul_fw (I := I) (M := M) g₀ 4 (2 : ℝ) _
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannPalatiniRefoldC2Family_threeArmHjoint
          (I := I) (M := M) g₀ T hδ hδZ qA qB),
      hidRA, ?_, ?_,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannPalatiniRefoldC2Family_riemannianFiberNormSq_le
        (I := I) (M := M) g₀ T hδ_lt hδ_half hδ hδZ qA qB hqAB,
      ?_, ?_⟩
    · intro s hs x
      have h := hsupC0 s hs x
      have h2 := sq_nonneg Λrm
      rw [Real.sq_sqrt hsum_nn]
      linarith
    · intro s hs x
      have h := hRm T hδ_le hδ hδZ hTjets s hs x
      have h1 := sq_nonneg Λid
      rw [Real.sq_sqrt hsum_nn]
      linarith
    · intro i s hs
      try dsimp only
      have h := henvC0 i s hs
      have hX : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
      nlinarith [mul_nonneg (hKwin_nn i) hX]
    · intro i s hs
      try dsimp only
      have h := henvC2 i s hs
      have hX : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
      nlinarith [mul_nonneg (hKid_nn i) hX]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
