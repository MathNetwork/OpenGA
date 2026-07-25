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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_sub_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - S') x =
      unitModel (I := I) (M := M) g s S x - unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - S').toSection x = S.toSection x - S'.toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S - S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_sub]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_add_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + S').toSection x = S.toSection x + S'.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S + S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_add]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma threeArmCoeffSum_rfns_le (g₀ : SmoothRiemannianMetric I M) {r s : ℕ}
    (R L : SmoothCcTensor g₀ r s) (ΛR ΛL : ℝ) (x : M)
    (hR : riemannianFiberNormSq (I := I) (M := M) g₀ r s x (R.toSection x) ≤ ΛR ^ 2)
    (hL : riemannianFiberNormSq (I := I) (M := M) g₀ r s x (L.toSection x) ≤ ΛL ^ 2) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((R + L).toSection x) ≤
      Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2) ^ 2 := by
  have hsqrt : Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2) ^ 2 = 2 * ΛR ^ 2 + 2 * ΛL ^ 2 := by
    refine Real.sq_sqrt ?_
    have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r s x (R.toSection x)
    have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r s x (L.toSection x)
    nlinarith [hR, hL]
  rw [hsqrt]
  have hsec : (R + L).toSection x = R.toSection x + L.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [hsec]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ r s x
    (R.toSection x) (L.toSection x)
  nlinarith [hadd, hR, hL]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_smul_value_tame
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (c : ℝ)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_smul_tame (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (c • T) x =
      c • unitModel (I := I) (M := M) g₀ s T x := by
  rw [unitModel, unitModel]
  have hsec : (c • T).toSection x = c • T.toSection x := by
    rw [SmoothCcTensor.toSection_smul]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (c • T).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma appCc_smul_left_tame (g : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r 2) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r 2 (c • Φ) W =
      c • operatorFieldApply (I := I) (M := M) g r 2 Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g r 2 Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g r 2 Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r 2 I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma unitModel_appCc_smul_left_apply_tame (g : SmoothRiemannianMetric I M) (r : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r 2) (W : SmoothCcTensor g 0 r)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (operatorFieldApply (I := I) (M := M) g r 2 (c • Φ) W) x v =
      c * unitModel (I := I) (M := M) g 2 (operatorFieldApply (I := I) (M := M) g r 2 Φ W) x v := by
  rw [appCc_smul_left_tame, unitModel_smul_tame, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_add2_apply_tame (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v + unitModel (I := I) (M := M) g₀ 2 S' x v := by
  rw [unitModel_add_local, ContinuousMultilinearMap.add_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma threeArm_unitModel_appCc_intervalIntegrable_tame
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r)
    {δ δ' : ℝ} (hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ'))
    (hcont : ∀ x : M, ContinuousOn
      (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ r 2 (Φ s) W) x v)
      MeasureTheory.volume 0 1 := by
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  have hkey : ∀ s : ℝ,
      unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ r 2 (Φ s) W) x v =
        ((Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x))
          (Tensor0SSpace.toModel u)) v := by
    intro s
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r 2 x ((Φ s).toSection x) u]
  have hcontApp : ContinuousOn (fun s : ℝ =>
      ((Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x))
        (Tensor0SSpace.toModel u)) v) (realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hstep : ContinuousOn (fun s : ℝ =>
        (Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x)) (Tensor0SSpace.toModel u))
        (realizedSmallSet (δ := δ) (δ' := δ')) :=
      (ContinuousLinearMap.apply ℝ (Tensor0SModel 2 ℝ E)
        (Tensor0SSpace.toModel u)).continuous.comp_continuousOn (hcont x)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ v).continuous.comp_continuousOn
      hstep
  have hcontFinal : ContinuousOn (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ r 2 (Φ s) W) x v)
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hcontApp.congr (fun s _ => ?_)
    exact (hkey s).symm
  exact (hcontFinal.mono hSI).intervalIntegrable

theorem uniform_C0_bound_concrete_lichnerowicz_coeffFields
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC : ℝ, 0 ≤ ΛC ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmFields_concrete_lichnerowicz_uniform_rfns_ballUniform
    (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀

private theorem linearizedRicciArm0BaseCoeff_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i :=
  DifferentialGeometry.Integral.Connection.linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

private theorem linearizedRicciArm0CorrField_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i := by
  classical
  obtain ⟨KR, hKR_nn, hKR⟩ :=
    ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i =>
    3 * (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound
        (I := I) (M := M) g₀ a R δ₀ i * (1 + 2 * ((a : ℝ) + 2) * R ^ 2)) +
      27 / 2 * (KR i +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₀)‖ ^ 2) +
      6 * (KC i +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
            (I := I) (M := M) g₀ g₀)‖ ^ 2),
    fun i => ?_, ?_⟩
  · have h1 :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound_nonneg
        (I := I) (M := M) g₀ a R δ₀ i
    have h2 : (0 : ℝ) ≤ 1 + 2 * ((a : ℝ) + 2) * R ^ 2 := by positivity
    have h3 := hKR_nn i
    have h4 := hKC_nn i
    have h5 : (0 : ℝ) ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    have h6 : (0 : ℝ) ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
            (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    have h7 := mul_nonneg h1 h2
    linarith
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    have hicg_smul : ∀ (r s' j : ℕ) (c : ℝ) (w : SmoothCcTensor g₀ r s'),
        iteratedCovGrad (I := I) g₀ r s' j (c • w) =
          c • iteratedCovGrad (I := I) g₀ r s' j w := by
      intro r s' j c w
      induction j with
      | zero => simp only [iteratedCovGrad_zero]
      | succ j ih =>
        rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]
    have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
            (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) :=
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation_gFibreOpBound
        (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
    have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
      have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
      have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
      nlinarith [e1, e2]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
                (I := I) g₀ T T' s) y v w :=
      fun y v w =>
        DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam_inner_of_mem
          (I := I) g₀ T T' hδ hδ' (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
            (I := I) g₀ T T' s)‖ ≤ R := by
      intro j hj
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
            (I := I) g₀ T T' s) =
          (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T' +
            s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
            (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, hicg_smul, hicg_smul]
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T' +
              s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
              ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
              s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
        _ ≤ (1 - s) * R + s * R :=
            add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
              (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
        _ = R := by ring
    have hRmDiff := hKR (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
        (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
    have hCvDiff := hKC (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation
        (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
    obtain ⟨_, _, hbound, _⟩ :=
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
        (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
    have hjet := ((hbound ha_super hR hδ₀ hδ_le hδ'_le hTball hT'ball).2 i hi s hs).1
    have hwin : ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) ≤ 2 * ((a : ℝ) + 2) * R ^ 2 := by
      have hterm : ∀ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 ≤ 2 * R ^ 2 := by
        intro j hj
        have hj_le : j ≤ a + 2 := by
          have hj' := Finset.mem_range.mp hj
          omega
        have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 ≤ R ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hTball j hj_le) 2
        have h2 : ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 ≤ R ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hT'ball j hj_le) 2
        linarith
      have hsum := Finset.sum_le_card_nsmul (Finset.range (i + 2)) _ (2 * R ^ 2) hterm
      rw [Finset.card_range, nsmul_eq_mul] at hsum
      have hcast : ((i + 2 : ℕ) : ℝ) ≤ (a : ℝ) + 2 := by
        have hia : (i : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr hi
        push_cast
        linarith
      have h2R : (0 : ℝ) ≤ 2 * R ^ 2 := by positivity
      calc ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
          ≤ ((i + 2 : ℕ) : ℝ) * (2 * R ^ 2) := hsum
        _ ≤ ((a : ℝ) + 2) * (2 * R ^ 2) := mul_le_mul_of_nonneg_right hcast h2R
        _ = 2 * ((a : ℝ) + 2) * R ^ 2 := by ring
    have hone : (1 : ℝ) + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) ≤
        1 + 2 * ((a : ℝ) + 2) * R ^ 2 := by linarith
    have hK_nn :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound_nonneg
        (I := I) (M := M) g₀ a R δ₀ i
    have hZraw := le_trans hjet (mul_le_mul_of_nonneg_left hone hK_nn)
    rw [show linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' =
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
          (I := I) g₀ T T' hδ hδ').choose from rfl]
    set Cf := (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
        (I := I) g₀ T T' hδ hδ').choose s with hCf_def
    set Rmf := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
        (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hRmf_def
    set Cvf := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
        (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hCvf_def
    set Rm0 := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
        (I := I) (M := M) g₀ g₀ with hRm0_def
    set Cv0 := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0CurvCoeff
        (I := I) (M := M) g₀ g₀ with hCv0_def
    have hRm_split : iteratedCovGrad (I := I) g₀ 2 2 i Rmf =
        iteratedCovGrad (I := I) g₀ 2 2 i (Rmf - Rm0) +
          iteratedCovGrad (I := I) g₀ 2 2 i Rm0 := by
      rw [iteratedCovGrad_sub]
      abel
    have hRm_norm : ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (Rmf - Rm0)‖ +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Rm0‖ := by
      rw [hRm_split]
      exact norm_add_le _ _
    have hRm_sq : ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ ^ 2 ≤
        2 * KR i + 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rm0‖ ^ 2 := by
      have hx := pow_le_pow_left₀ (norm_nonneg _) hRm_norm 2
      nlinarith [hRmDiff, hx,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (Rmf - Rm0)‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Rm0‖)]
    have hCv_split : iteratedCovGrad (I := I) g₀ 2 2 i Cvf =
        iteratedCovGrad (I := I) g₀ 2 2 i (Cvf - Cv0) +
          iteratedCovGrad (I := I) g₀ 2 2 i Cv0 := by
      rw [iteratedCovGrad_sub]
      abel
    have hCv_norm : ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (Cvf - Cv0)‖ +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cv0‖ := by
      rw [hCv_split]
      exact norm_add_le _ _
    have hCv_sq : ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖ ^ 2 ≤
        2 * KC i + 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i Cv0‖ ^ 2 := by
      have hx := pow_le_pow_left₀ (norm_nonneg _) hCv_norm 2
      nlinarith [hCvDiff, hx,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (Cvf - Cv0)‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cv0‖)]
    have hsm : iteratedCovGrad (I := I) g₀ 2 2 i ((3 / 2 : ℝ) • Rmf) =
        (3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf :=
      hicg_smul 2 2 i (3 / 2 : ℝ) Rmf
    have hCf_split : Cf = Cf + (3 / 2 : ℝ) • Rmf - Cvf - (3 / 2 : ℝ) • Rmf + Cvf := by
      abel
    have hicg_split : iteratedCovGrad (I := I) g₀ 2 2 i Cf =
        iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf) -
          (3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf +
          iteratedCovGrad (I := I) g₀ 2 2 i Cvf := by
      conv_lhs => rw [hCf_split]
      rw [iteratedCovGrad_add, iteratedCovGrad_sub, hsm]
    have ht3 : ‖(3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ =
        (3 / 2 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    have htri : ‖iteratedCovGrad (I := I) g₀ 2 2 i Cf‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf)‖ +
          (3 / 2 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ +
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖ := by
      rw [hicg_split]
      have ht1 := norm_add_le
        (iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf) -
          (3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf)
        (iteratedCovGrad (I := I) g₀ 2 2 i Cvf)
      have ht2 := norm_sub_le
        (iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf))
        ((3 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i Rmf)
      linarith [ht1, ht2, ht3.le, ht3.ge]
    have hx2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hxsq : ‖iteratedCovGrad (I := I) g₀ 2 2 i Cf‖ ^ 2 ≤
        3 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf)‖ ^ 2 +
          27 / 4 * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ ^ 2 +
          3 * ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖ ^ 2 := by
      nlinarith [hx2,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf)‖ -
          (3 / 2 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 2 2 i (Cf + (3 / 2 : ℝ) • Rmf - Cvf)‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖),
        sq_nonneg ((3 / 2 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 2 2 i Rmf‖ -
          ‖iteratedCovGrad (I := I) g₀ 2 2 i Cvf‖)]
    linarith [hxsq, hZraw, hRm_sq, hCv_sq]

private theorem linearizedRicciArm1BaseCoeff_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i :=
  DifferentialGeometry.Integral.Connection.linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

private theorem linearizedRicciArm1CorrField_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i := by
  classical
  refine ⟨fun i =>
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound
        (I := I) (M := M) g₀ a R δ₀ i * (1 + 2 * ((a : ℝ) + 2) * R ^ 2),
    fun i =>
      mul_nonneg
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound_nonneg
          (I := I) (M := M) g₀ a R δ₀ i)
        (by positivity), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  obtain ⟨_, _, hbound, _⟩ :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
      (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
  have hjet := ((hbound ha_super hR hδ₀ hδ_le hδ'_le hTball hT'ball).2 i hi s hs).2
  have hwin : ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) ≤ 2 * ((a : ℝ) + 2) * R ^ 2 := by
    have hterm : ∀ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 ≤ 2 * R ^ 2 := by
      intro j hj
      have hj_le : j ≤ a + 2 := by
        have hj' := Finset.mem_range.mp hj
        omega
      have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hTball j hj_le) 2
      have h2 : ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hT'ball j hj_le) 2
      linarith
    have hsum := Finset.sum_le_card_nsmul (Finset.range (i + 2)) _ (2 * R ^ 2) hterm
    rw [Finset.card_range, nsmul_eq_mul] at hsum
    have hcast : ((i + 2 : ℕ) : ℝ) ≤ (a : ℝ) + 2 := by
      have hia : (i : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr hi
      push_cast
      linarith
    have h2R : (0 : ℝ) ≤ 2 * R ^ 2 := by positivity
    calc ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
        ≤ ((i + 2 : ℕ) : ℝ) * (2 * R ^ 2) := hsum
      _ ≤ ((a : ℝ) + 2) * (2 * R ^ 2) := mul_le_mul_of_nonneg_right hcast h2R
      _ = 2 * ((a : ℝ) + 2) * R ^ 2 := by ring
  have hone : (1 : ℝ) + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) ≤
      1 + 2 * ((a : ℝ) + 2) * R ^ 2 := by linarith
  have hK_nn :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.corrFieldTameJetBound_nonneg
      (I := I) (M := M) g₀ a R δ₀ i
  rw [show linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' =
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
        (I := I) g₀ T T' hδ hδ').choose_spec.choose from rfl]
  exact le_trans hjet (mul_le_mul_of_nonneg_left hone hK_nn)

private theorem ricciArmPrincipalCoeff_realizedFam_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i :=
  DifferentialGeometry.Integral.Connection.ricciArmPrincipalCoeff_realizedFam_jetL2_perOrder_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

private theorem traceHessianCoeff_realizedFam_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i :=
  DifferentialGeometry.Integral.Connection.traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform
    (I := I) (M := M) g₀ a ha_super hR hδ₀

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma normSq_iteratedCovGrad_add_le_tame
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (A B : SmoothCcTensor g₀ r s) (PA PB : ℝ)
    (hA : ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2 ≤ PA)
    (hB : ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 ≤ PB) :
    ‖iteratedCovGrad (I := I) g₀ r s i (A + B)‖ ^ 2 ≤ 2 * PA + 2 * PB := by
  rw [iteratedCovGrad_add]
  have htri : ‖iteratedCovGrad (I := I) g₀ r s i A + iteratedCovGrad (I := I) g₀ r s i B‖ ≤
      ‖iteratedCovGrad (I := I) g₀ r s i A‖ + ‖iteratedCovGrad (I := I) g₀ r s i B‖ :=
    norm_add_le _ _
  nlinarith [htri, hA, hB, norm_nonneg (iteratedCovGrad (I := I) g₀ r s i A),
    norm_nonneg (iteratedCovGrad (I := I) g₀ r s i B),
    norm_nonneg (iteratedCovGrad (I := I) g₀ r s i A + iteratedCovGrad (I := I) g₀ r s i B),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i A‖ - ‖iteratedCovGrad (I := I) g₀ r s i B‖)]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul_tame (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma normSq_iteratedCovGrad_sub_smul_le_tame
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (A B : SmoothCcTensor g₀ r s) (c : ℝ) (PA PB : ℝ)
    (hA : ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2 ≤ PA)
    (hB : ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 ≤ PB) :
    ‖iteratedCovGrad (I := I) g₀ r s i (A - c • B)‖ ^ 2 ≤ 2 * PA + 2 * c ^ 2 * PB := by
  rw [iteratedCovGrad_sub, iteratedCovGrad_smul_tame]
  have htri : ‖iteratedCovGrad (I := I) g₀ r s i A - c • iteratedCovGrad (I := I) g₀ r s i B‖ ≤
      ‖iteratedCovGrad (I := I) g₀ r s i A‖ + ‖c • iteratedCovGrad (I := I) g₀ r s i B‖ := by
    rw [sub_eq_add_neg]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_neg]
  rw [norm_smul, Real.norm_eq_abs] at htri
  have habs : |c| * ‖iteratedCovGrad (I := I) g₀ r s i B‖ ≤
      |c| * Real.sqrt PB := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    rw [show ‖iteratedCovGrad (I := I) g₀ r s i B‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hB
  have hAsqrt : ‖iteratedCovGrad (I := I) g₀ r s i A‖ ≤ Real.sqrt PA := by
    rw [show ‖iteratedCovGrad (I := I) g₀ r s i A‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hA
  have hPA_nn : 0 ≤ PA := le_trans (sq_nonneg _) hA
  have hPB_nn : 0 ≤ PB := le_trans (sq_nonneg _) hB
  have hsumbnd : ‖iteratedCovGrad (I := I) g₀ r s i A - c • iteratedCovGrad (I := I) g₀ r s i B‖ ≤
      Real.sqrt PA + |c| * Real.sqrt PB := by
    refine htri.trans ?_
    have := add_le_add hAsqrt habs
    linarith [this]
  have hsum_nn : 0 ≤ Real.sqrt PA + |c| * Real.sqrt PB :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg c) (Real.sqrt_nonneg _))
  have hnorm_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r s i A - c • iteratedCovGrad (I := I) g₀ r s i B‖ :=
    norm_nonneg _
  have hsq : ‖iteratedCovGrad (I := I) g₀ r s i A - c • iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 ≤
      (Real.sqrt PA + |c| * Real.sqrt PB) ^ 2 := by
    have := mul_self_le_mul_self hnorm_nn hsumbnd
    nlinarith [this]
  have hsqrtPA : Real.sqrt PA ^ 2 = PA := Real.sq_sqrt hPA_nn
  have hsqrtPB : Real.sqrt PB ^ 2 = PB := Real.sq_sqrt hPB_nn
  have habsc : |c| ^ 2 = c ^ 2 := sq_abs c
  refine hsq.trans ?_
  nlinarith [hsqrtPA, hsqrtPB, habsc, Real.sqrt_nonneg PA, Real.sqrt_nonneg PB,
    abs_nonneg c, sq_nonneg (Real.sqrt PA - |c| * Real.sqrt PB),
    mul_nonneg (abs_nonneg c) (mul_nonneg (Real.sqrt_nonneg PA) (Real.sqrt_nonneg PB))]

private theorem linearizedRicciArm_concreteField_perOrder_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i ∧
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i ∧
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i := by
  classical
  obtain ⟨P0b, hP0b_nn, hP0b⟩ :=
    linearizedRicciArm0BaseCoeff_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨P0c, hP0c_nn, hP0c⟩ :=
    linearizedRicciArm0CorrField_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨P1b, hP1b_nn, hP1b⟩ :=
    linearizedRicciArm1BaseCoeff_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨P1c, hP1c_nn, hP1c⟩ :=
    linearizedRicciArm1CorrField_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨Pp, hPp_nn, hPp⟩ :=
    ricciArmPrincipalCoeff_realizedFam_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨Ph, hPh_nn, hPh⟩ :=
    traceHessianCoeff_realizedFam_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  refine ⟨fun i => max (2 * P0b i + 2 * P0c i)
      (max (2 * P1b i + 2 * P1c i) (2 * Pp i + 2 * (1 / 2 : ℝ) ^ 2 * Ph i)), ?_, ?_⟩
  · intro i
    refine le_max_of_le_left ?_
    nlinarith [hP0b_nn i, hP0c_nn i]
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
    have hb0 := hP0b T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hc0 := hP0c T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hb1 := hP1b T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hc1 := hP1c T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hp := hPp T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    have hh := hPh T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
    refine ⟨?_, ?_, ?_⟩
    · rw [linearizedRicciArm0Field]
      exact (normSq_iteratedCovGrad_add_le_tame (I := I) g₀ 2 2 i
        (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)
        (linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s) (P0b i) (P0c i) hb0 hc0).trans
        (le_max_left _ _)
    · rw [linearizedRicciArm1Field]
      refine (normSq_iteratedCovGrad_add_le_tame (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)
        (linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s) (P1b i) (P1c i) hb1 hc1).trans ?_
      exact le_max_of_le_right (le_max_left _ _)
    · rw [linearizedRicciArm2FieldLichnerowicz]
      refine (normSq_iteratedCovGrad_sub_smul_le_tame (I := I) g₀ 4 2 i
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (1 / 2 : ℝ) (Pp i) (Ph i) hp hh).trans ?_
      exact le_max_of_le_right (le_max_right _ _)

theorem linearizedRicciArm_concreteField_jetL2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) ≤ B ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) ≤ B ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) ≤ B ^ 2) := by
  classical
  obtain ⟨P, hP_nn, hP⟩ :=
    linearizedRicciArm_concreteField_perOrder_rfns_ballUniform (I := I) g₀ a ha_super hR hδ₀
  set Psum : ℝ := ∑ i ∈ Finset.range (a + 1), P i with hPsum_def
  have hPsum_nn : 0 ≤ Psum := Finset.sum_nonneg (fun i _ => hP_nn i)
  refine ⟨Real.sqrt Psum, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hB_sq : Real.sqrt Psum ^ 2 = Psum := Real.sq_sqrt hPsum_nn
  have hkey : ∀ (r : ℕ) (Φ : ℝ → SmoothCcTensor g₀ r 2)
      (s : ℝ),
      (∀ (i : ℕ), i ∈ Finset.range (a + 1) →
        ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2 ≤ P i) →
      (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2) ≤ Real.sqrt Psum ^ 2 := by
    intro r Φ s hbound
    rw [hB_sq]
    calc ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2
        ≤ ∑ i ∈ Finset.range (a + 1), P i := Finset.sum_le_sum hbound
      _ = Psum := hPsum_def.symm
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact hkey 2 (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ') s
      (fun i hi => (hP T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).1)
  · intro s hs
    exact hkey 3 (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ') s
      (fun i hi => (hP T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).2.1)
  · intro s hs
    exact hkey 4 (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ') s
      (fun i hi => (hP T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).2.2)

private theorem uniform_rfns_bound_lichnerowicz_coeffFields
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC B : ℝ, 0 ≤ ΛC ∧ 0 ≤ B ∧
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
        ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
          (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedRicciAt (I := I) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛC) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛC) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛC) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) := by
  classical
  obtain ⟨ΛC, hΛC_nn, hC0⟩ :=
    uniform_C0_bound_concrete_lichnerowicz_coeffFields (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨B, hB_nn, hJet⟩ :=
    linearizedRicciArm_concreteField_jetL2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  refine ⟨ΛC, B, hΛC_nn, hB_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  set Φ₀ : ℝ → SmoothCcTensor g₀ 2 2 := linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ'
  set Φ₁ : ℝ → SmoothCcTensor g₀ 3 2 := linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ'
  set Φ₂ : ℝ → SmoothCcTensor g₀ 4 2 :=
    linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ'
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨hJet0, hJet1, hJet2⟩ := hJet T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  refine ⟨Φ₀, Φ₁, Φ₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ'
  · exact linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ'
  · exact linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ'
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ')
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ')
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ')
  · intro s hs x v
    obtain ⟨_, _, _, hident, _, _⟩ :=
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
        (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
    exact hident hTsymm hT'symm s hs x v hδ_lt hδ'_lt
  · intro s hs x
    have h := hC0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
    exact h.1
  · intro s hs x
    have h := hC0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
    exact h.2.1
  · intro s hs x
    have h := hC0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
    exact h.2.2
  · exact hJet0
  · exact hJet1
  · exact hJet2

private theorem ricciArm_threeArm_coeffFields_uniformC0
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR B : ℝ, 0 ≤ ΛR ∧ 0 ≤ B ∧
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
        ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
          (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedRicciAt (I := I) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) := by
  exact uniform_rfns_bound_lichnerowicz_coeffFields (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀

private theorem ricciArm_threeArm_coeffFields_C0_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR B : ℝ, 0 ≤ ΛR ∧ 0 ≤ B ∧
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
        ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
          (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedRicciAt (I := I) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) := by
  exact ricciArm_threeArm_coeffFields_uniformC0 (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀

theorem exists_ricciArm_threeArm_coeffFields_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR B : ℝ, 0 ≤ ΛR ∧ 0 ≤ B ∧
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
        ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
          (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁
            (δ := δ) (δ' := δ') ∧
          linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂
            (δ := δ) (δ' := δ') ∧
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedRicciAt (I := I) g₀ T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛR) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) :=
  ricciArm_threeArm_coeffFields_C0_bound (I := I) g₀ g_bg a ha_super hR hδ₀

private theorem exists_ricciArmCoeff_ballUniform_C0_sup
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
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
        ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            ((-2 : ℝ) * ricciTensor (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)) x (v 0) (v 1)
                - (-2 : ℝ) * ricciTensor (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')) x (v 0) (v 1)) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (R₀.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (R₁.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ ΛR ^ 2) := by
  classical
  obtain ⟨ΛR, B, hΛR_nn, hB_nn, hbrick⟩ :=
    exists_ricciArm_threeArm_coeffFields_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨2 * ΛR, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hc0, hc1, hc2, hid, hb0, hb1, hb2, _, _, _⟩ :=
    hbrick T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le (zero_le_one)]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set P₀ : SmoothCcTensor g₀ 2 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 with hP₀
  set P₁ : SmoothCcTensor g₀ 3 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 with hP₁
  set P₂ : SmoothCcTensor g₀ 4 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 with hP₂
  refine ⟨(-2 : ℝ) • P₀, (-2 : ℝ) • P₁, (-2 : ℝ) • P₂, ?_, ?_, ?_, ?_⟩
  · intro x v
    set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
    set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
    set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
    have hRic :=
      ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)
    have htoinfty : ∀ (g : SmoothRiemannianMetric I M),
        ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x (v 0) (v 1) =
          ricciTensor (I := I) g x (v 0) (v 1) := fun g => rfl
    have hPidentity :
        ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1) -
            ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1) =
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 P₀ W₀
              + operatorFieldApply (I := I) (M := M) g₀ 3 2 P₁ W₁
              + operatorFieldApply (I := I) (M := M) g₀ 4 2 P₂ W₂) x v := by
      rw [hRic]
      have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
            unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s) W₀) x v
              + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s) W₁) x v
              + unitModel (I := I) (M := M) g₀ 2 (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s) W₂) x v := by
        rw [MeasureTheory.ae_iff]
        have hnull : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
        refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
        rw [Set.mem_setOf_eq, Classical.not_imp] at hs
        obtain ⟨hsmem, hsneq⟩ := hs
        rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
        rw [Set.mem_singleton_iff]
        by_contra hne
        have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
        exact hsneq (by rw [hid s hsIoo x v, unitModel_add2_apply_tame,
          unitModel_add2_apply_tame])
      rw [intervalIntegral.integral_congr_ae hintegrand]
      have hI0 : IntervalIntegrable
          (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s) W₀) x v)
          MeasureTheory.volume 0 1 :=
        threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 2 Φ₀ W₀ hSI hc0 x v
      have hI1 : IntervalIntegrable
          (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s) W₁) x v)
          MeasureTheory.volume 0 1 :=
        threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 3 Φ₁ W₁ hSI hc1 x v
      have hI2 : IntervalIntegrable
          (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s) W₂) x v)
          MeasureTheory.volume 0 1 :=
        threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 4 Φ₂ W₂ hSI hc2 x v
      rw [intervalIntegral.integral_add (hI0.add hI1) hI2,
        intervalIntegral.integral_add hI0 hI1]
      have he0 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Φ₀ W₀
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0 x v
      have he1 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 3 2 Φ₁ W₁
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1 x v
      have he2 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 Φ₂ W₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2 x v
      rw [← hP₀] at he0
      rw [← hP₁] at he1
      rw [← hP₂] at he2
      rw [← he0, ← he1, ← he2, unitModel_add2_apply_tame, unitModel_add2_apply_tame]
    rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame,
      unitModel_appCc_smul_left_apply_tame, unitModel_appCc_smul_left_apply_tame,
      unitModel_appCc_smul_left_apply_tame, htoinfty, htoinfty]
    rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame] at hPidentity
    linarith [hPidentity]
  · intro x
    have hsmul : ((-2 : ℝ) • P₀).toSection x = (-2 : ℝ) • P₀.toSection x := by
      rw [SmoothCcTensor.toSection_smul]; rfl
    rw [hsmul, riemannianFiberNormSq_smul_value_tame]
    have hPbound : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (P₀.toSection x) ≤ ΛR ^ 2 := by
      rw [hP₀]
      exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 2 2 Φ₀
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 x ΛR hΛR_nn
        ((hc0 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
        (fun t ht => hb0 t ht x)
    nlinarith [hPbound, sq_nonneg ΛR, riemannianFiberNormSq_nonneg
      (I := I) (M := M) g₀ 2 2 x (P₀.toSection x)]
  · intro x
    have hsmul : ((-2 : ℝ) • P₁).toSection x = (-2 : ℝ) • P₁.toSection x := by
      rw [SmoothCcTensor.toSection_smul]; rfl
    rw [hsmul, riemannianFiberNormSq_smul_value_tame]
    have hPbound : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (P₁.toSection x) ≤ ΛR ^ 2 := by
      rw [hP₁]
      exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 3 2 Φ₁
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 x ΛR hΛR_nn
        ((hc1 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
        (fun t ht => hb1 t ht x)
    nlinarith [hPbound, sq_nonneg ΛR, riemannianFiberNormSq_nonneg
      (I := I) (M := M) g₀ 3 2 x (P₁.toSection x)]
  · intro x
    have hsmul : ((-2 : ℝ) • P₂).toSection x = (-2 : ℝ) • P₂.toSection x := by
      rw [SmoothCcTensor.toSection_smul]; rfl
    rw [hsmul, riemannianFiberNormSq_smul_value_tame]
    have hPbound : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (P₂.toSection x) ≤ ΛR ^ 2 := by
      rw [hP₂]
      exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 4 2 Φ₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 x ΛR hΛR_nn
        ((hc2 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
        (fun t ht => hb2 t ht x)
    nlinarith [hPbound, sq_nonneg ΛR, riemannianFiberNormSq_nonneg
      (I := I) (M := M) g₀ 4 2 x (P₂.toSection x)]

theorem deTurckRicciArm_appCc_graded_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
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
        ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            (-2 : ℝ) •
                (ricciTensor (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ) x (v 0) (v 1)
                  - ricciTensor (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x (v 0) (v 1)) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (R₀.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (R₁.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ ΛR ^ 2) := by
  classical
  obtain ⟨ΛR, hΛR_nn, hsup⟩ :=
    exists_ricciArmCoeff_ballUniform_C0_sup (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛR, hΛR_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨R₀, R₁, R₂, hval, hR₀, hR₁, hR₂⟩ :=
    hsup T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  refine ⟨R₀, R₁, R₂, fun x v => ?_, hR₀, hR₁, hR₂⟩

  rw [smul_sub, smul_eq_mul, smul_eq_mul]
  exact hval x v

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
