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
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieArmChartValueMatrixNormalFormCombinatorics
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Field
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0JointSmooth


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

section

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope lieDeTurckChartSlope_eq_orderSplit contMDiffOn_clm_section_of_pointwise_joint_manifold_time)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricLmodel)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth deTurckLieArm2PrincipalCoeff_apply_eq cometricFinBasisTrace_eq_chartInvGram_bilin quadrilinearMapSlotBilinearAt unitModel4SlotBilin_apply)

set_option backward.isDefEq.respectTransparency false

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lieArm2_appCc_value_invGram
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (D : SmoothCcTensor g₀ 0 4)
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg) D) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          (unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) i, (chartModelBasis E) l,
                (chartModelBasis E) j, (chartModelBasis E) k₁]
            + unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) j, (chartModelBasis E) l,
                (chartModelBasis E) i, (chartModelBasis E) k₁]
            - unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) i, (chartModelBasis E) j,
                (chartModelBasis E) l, (chartModelBasis E) k₁]) := by
  classical
  refine (deTurckLieArm2PrincipalCoeff_apply_eq (I := I) g₀ g₁ g_bg D x
    ![(chartModelBasis E) i, (chartModelBasis E) j]).trans ?_
  have hv0 : (![(chartModelBasis E) i, (chartModelBasis E) j] :
      Fin 2 → TangentSpace I x) 0 = (chartModelBasis E) i := rfl
  have hv1 : (![(chartModelBasis E) i, (chartModelBasis E) j] :
      Fin 2 → TangentSpace I x) 1 = (chartModelBasis E) j := rfl
  simp only [hv0, hv1]
  have hpack13 : ∀ (u w : TangentSpace I x) (c v : E),
      quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
        1 3 (by decide) ![(show E from u), 0, (show E from w), 0] c v =
      unitModel (I := I) (M := M) g₀ 4 D x ![u, c, w, v] := by
    intro u w c v
    rw [unitModel4SlotBilin_apply]
    refine congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t) ?_
    funext m
    fin_cases m <;> simp [Function.update]
  have hpack23 : ∀ (u w : TangentSpace I x) (c v : E),
      quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
        2 3 (by decide) ![(show E from u), (show E from w), 0, 0] c v =
      unitModel (I := I) (M := M) g₀ 4 D x ![u, w, c, v] := by
    intro u w c v
    rw [unitModel4SlotBilin_apply]
    refine congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t) ?_
    funext m
    fin_cases m <;> simp [Function.update]
  have hpat : ∀ (u w : TangentSpace I x),
      (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![u, cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            w, (Module.finBasis ℝ E) k]) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 D x
            ![u, (chartModelBasis E) l, w, (chartModelBasis E) k₁] := by
    intro u w
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![u, cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            w, (Module.finBasis ℝ E) k]) =
      ∑ k : Fin (Module.finrank ℝ E),
        quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
          1 3 (by decide) ![(show E from u), 0, (show E from w), 0]
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ => (hpack13 u w _ _).symm)]
    rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [smul_eq_mul, hpack13 u w]
  have hpatH : (∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 D x
        ![(chartModelBasis E) i, (chartModelBasis E) j,
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (Module.finBasis ℝ E) k]) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 D x
            ![(chartModelBasis E) i, (chartModelBasis E) j,
              (chartModelBasis E) l, (chartModelBasis E) k₁] := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![(chartModelBasis E) i, (chartModelBasis E) j,
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k]) =
      ∑ k : Fin (Module.finrank ℝ E),
        quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
          2 3 (by decide)
          ![(chartModelBasis E) i, (chartModelBasis E) j, 0, 0]
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ =>
        (hpack23 ((chartModelBasis E) i) ((chartModelBasis E) j) _ _).symm)]
    rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [smul_eq_mul, hpack23 ((chartModelBasis E) i) ((chartModelBasis E) j)]
  rw [hpat ((chartModelBasis E) i) ((chartModelBasis E) j),
    hpat ((chartModelBasis E) j) ((chartModelBasis E) i), hpatH]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (domDomCongrSection_unitModel unitModel_basisChart_eq_tensorChartComponentRaw tensorChartComponentRaw tensorChartComponentRaw_add tensorChartComponentRaw_smul arm2ReadoutCovDerivPair arm1ReadoutCovDeriv iteratedCovGrad2_chartComponent_readout iteratedCovGrad1_chartComponent_readout partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw covDerivLowerOrderTerm02_center_eq covDerivLowerOrderTerm03_center_eq euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE partialDeriv_scalarOnE_eq_euclidPartial_local toEuclidean_extChartAt_mem_chartTargetEuclid symm_toEuclidean_symm_toEuclidean_extChartAt)
open DifferentialGeometry.Analysis.Sobolev.Chart (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity (tensorChartComponentRaw_eq_chartFrame chartFrameBasisModel covDerivLowerOrderTerm euclidPartial euclidPartial_def covDerivComponent_lowerOrder_contDiffOn euclidPartial_chartPushedRaw_contDiffOn chartPushedRaw_tensorChartComponentRaw_contDiffOn)
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)
open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_frame0_eq_unitTensor (x b : M) :
    chartFrameBasisModel (I := I) (M := M) x b 0 ![] = unitTensor (I := I) (M := M) b := by
  apply ContinuousMultilinearMap.ext
  intro v
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_rawComponent_eq_unitModel_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 s W x ![] Jdx b =
      unitModel (I := I) (M := M) g s W b
        (fun j => (show E from chartBasisVecFiber (I := I) x (Jdx j) b)) := by
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 s W x hb ![] Jdx]
  rw [lieArm_frame0_eq_unitTensor (I := I) (M := M) x b]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_euclidPartial_add_local
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z + h z) y =
      euclidPartial (E := E) l f y + euclidPartial (E := E) l h y := by
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def, fderiv_fun_add hf hh,
    ContinuousLinearMap.add_apply]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_covDerivLowerOrderTerm_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) x) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g₀ r s S x m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g₀ r s S x Idx' Jdx')
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_euclidPartial_chartPushedRaw_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) x) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g₀ r s S x k Idx Jdx
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_unitModel4_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      euclidPartial (E := E) a
          (fun y' => euclidPartial (E := E) b
            (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
              h x ![] ![c, d])) y')
          (toEuclidean (E := E) (extChartAt I x x))
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀ h x ![a, b, c, d] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c,
        chartModelBasis E d] : Fin 4 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c, d] : Fin 4 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 2)
    (iteratedCovGrad (I := I) g₀ 0 2 2 h) x (![a, b, c, d])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad2_chartComponent_readout (I := I) g₀ h x (![a, b, c, d])]
  have hJ0 : (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJ1 : (Matrix.vecTail (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) 0 = b := rfl
  have hJtail2 : Matrix.vecTail (Matrix.vecTail
      (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) = ![c, d] := by
    funext j; fin_cases j <;> rfl
  simp only [arm2ReadoutCovDerivPair, hJ0, hJ1, hJtail2]
  have hPdiff : DifferentiableAt ℝ
      (euclidPartial (E := E) b
        (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d])))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    lieArm_euclidPartial_chartPushedRaw_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  have hQdiff : DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d])
      (toEuclidean (E := E) (extChartAt I x x)) :=
    lieArm_covDerivLowerOrderTerm_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  rw [lieArm_euclidPartial_add_local a hPdiff hQdiff]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_unitModel3_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            h x ![] ![b, c]))
          (toEuclidean (E := E) (extChartAt I x x))
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀ h x ![a, b, c] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] :
        Fin 3 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c] : Fin 3 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 1)
    (iteratedCovGrad (I := I) g₀ 0 2 1 h) x (![a, b, c])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad1_chartComponent_readout (I := I) g₀ h x (![a, b, c])]
  have hJ0 : (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJtail : Matrix.vecTail (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) = ![b, c] := by
    funext j; fin_cases j <;> rfl
  simp only [arm1ReadoutCovDeriv, hJ0, hJtail]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_symmS_rawComponent
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (x : M)
    (c d : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (ccTensor02Symm (I := I) (M := M) g S) x ![] ![c, d] b =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![c, d] b +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b) := by
  classical
  have hswap : tensorChartComponentRaw (I := I) (M := M) g 0 2
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) x ![] ![c, d] b =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b := by
    rw [lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 _ x ![c, d] hb,
      lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 S x ![d, c] hb]
    rw [domDomCongrSection_unitModel (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) S b]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg (fun t : Fin 2 → E => unitModel (I := I) (M := M) g 2 S b t) ?_
    funext j
    fin_cases j <;> rfl
  rw [show ccTensor02Symm (I := I) (M := M) g S =
      (1 / 2 : ℝ) • (S + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) from rfl]
  rw [tensorChartComponentRaw_smul, tensorChartComponentRaw_add, hswap]
  rw [smul_eq_mul]

omit [BoundarylessManifold I M] in
private lemma lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d]) =ᶠ[𝓝 (extChartAt I x x)]
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d := by
  classical
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hx_src
  have htarget_open : IsOpen ((extChartAt I x).target : Set E) :=
    isOpen_extChartAt_target (I := I) x
  filter_upwards [htarget_open.mem_nhds htarget, hev] with y hy_tgt hev_y
  rw [hev_y]
  have hb : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hy_tgt
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]
  rw [lieArm_symmS_rawComponent (I := I) (M := M) g₀ (T - T') x c d hb]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def,
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]

omit [BoundarylessManifold I M] in
private lemma lieArm_partialDeriv_symmS_scalar_eventuallyEq
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d])) =ᶠ[𝓝 (extChartAt I x x)]
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d) := by
  have hev := (lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d).eventuallyEq_nhds
  filter_upwards [hev] with y hy
  unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
  rw [hy.fderiv_eq]

omit [BoundarylessManifold I M] in
private lemma lieArm_U4_readout
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d))
          (extChartAt I x x)
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c, d] := by
  classical
  rw [lieArm_unitModel4_basisChart_readout_split (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c d]
  refine congrArg (fun t : ℝ =>
    t + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c, d]) ?_
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x b a c d]
  have hev1 := lieArm_partialDeriv_symmS_scalar_eventuallyEq (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c d
  change fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d])))
      (extChartAt I x x) ((chartModelBasis E) a) = fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d))
      (extChartAt I x x) ((chartModelBasis E) a)
  rw [hev1.fderiv_eq]

omit [BoundarylessManifold I M] in
private lemma lieArm_U3_readout
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c)
          (extChartAt I x x)
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c] := by
  classical
  rw [lieArm_unitModel3_basisChart_readout_split (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c]
  refine congrArg (fun t : ℝ =>
    t + arm1ReadoutCovDeriv (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c]) ?_
  have hYmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) x (mem_chart_source H x)
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  have h := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialDeriv_scalarOnE_eq_euclidPartial_local (I := I) (M := M)
    (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![b, c]) x a hYmem
  rw [hround] at h
  rw [← h]
  have hev1 := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c
  unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
  rw [hev1.fderiv_eq]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_chartInvGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) g x a b
        (extChartAt I x x) =
      chartInvGramMatrix (I := I) g x x a b := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE_def]
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_chartGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g x a b
        (extChartAt I x x) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def]
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_chartInvGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g x x a b = chartInvGramMatrix (I := I) g x x b a := by
  have hherm : (DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x)⁻¹.IsHermitian :=
    (DifferentialGeometry.Integral.Measure.chartGramMatrix_isHermitian (I := I) g x x).inv
  have h := congrFun (congrFun hherm a) b
  rw [Matrix.conjTranspose_apply, star_trivial] at h
  exact h.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_gram_invGram_collapse (g : SmoothRiemannianMetric I M) (x : M)
    (l j : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
          chartInvGramMatrix (I := I) g x x k l) =
      if l = j then (1 : ℝ) else 0 := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x
  have hmul := DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx_base
  have h := congrFun (congrFun hmul l) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
        chartInvGramMatrix (I := I) g x x k l) =
    ∑ k : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x l k *
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j from
    Finset.sum_congr rfl (fun k _ => by
      rw [lieArm_chartInvGramMatrix_symm (I := I) g x k l]; ring)]
  rw [h]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma lieArm_partialDeriv2_realizedGramDeriv_swap
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m₁ m₂ a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₂
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₁
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₂
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) := by
  rw [partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₁ m₂ a b,
    partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₂ m₁ a b]
  rw [euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw (I := I) g₀ (T - T') x m₂ m₁ a b, euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw (I := I) g₀ (T - T') x m₂ m₁ b a]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)
open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma lieArm_P2_halfCollapse
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (d e : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
                (extChartAt I x x)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l *
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d
              (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x e k₁))
              (extChartAt I x x)
            - (1 / 2 : ℝ) *
              DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d
                (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) e
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁))
                (extChartAt I x x)) := by
  classical
  set pd2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun d' a' l' b' =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d'
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a'
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l' b'))
      (extChartAt I x x) with hpd2
  set CIM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    chartInvGramMatrix (I := I) g₁ x x a b with hCIM
  set CGM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g₁ x x a b with hCGM
  have hHB : ∀ k a b : Fin (Module.finrank ℝ E),
      chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
          (extChartAt I x x) =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          CIM k l * (pd2 d a l b + pd2 d b l a - pd2 d l a b) := by
    intro k a b
    rw [chartDeTurckCorrHessBlockRaw]
    refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k l]
  have hstep1 : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
            chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
              (extChartAt I x x)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))) := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
                (extChartAt I x x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        CGM k e * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          CIM a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            CIM k l * (pd2 d a l b + pd2 d b l a - pd2 d l a b)) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [lieArm_chartGramOnE_center (I := I) g₁ x k e]
      refine congrArg (fun t : ℝ => CGM k e * t) ?_
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a b, hHB k a b]]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  rw [hstep1]
  have hstep2 : ∀ a b : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b)))) =
      CIM a b * ((1 / 2 : ℝ) * (pd2 d a e b + pd2 d b e a - pd2 d e a b)) := by
    intro a b
    rw [Finset.sum_congr rfl (fun l _ => by
        rw [lieArm_gram_invGram_collapse (I := I) g₁ x l e] :
      ∀ l ∈ Finset.univ,
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))) =
        CIM a b * ((1 / 2 : ℝ) *
          ((if l = e then (1 : ℝ) else 0) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))))]
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl, one_mul]
    · intro l _ hl
      rw [if_neg hl, zero_mul, mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ e) h
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep2 a b))]
  have hterm1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * pd2 d a e b)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * ((1 / 2 : ℝ) * pd2 d l e k₁) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show CIM l k₁ = CIM k₁ l from lieArm_chartInvGramMatrix_symm (I := I) g₁ x l k₁]
  have hterm3 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * pd2 d e a b)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * ((1 / 2 : ℝ) * pd2 d e l k₁) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show CIM l k₁ = CIM k₁ l from lieArm_chartInvGramMatrix_symm (I := I) g₁ x l k₁]
  have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * (pd2 d a e b + pd2 d b e a - pd2 d e a b))) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d a e b))
      + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d b e a))
      - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d e a b)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsplit, hterm1, hterm3]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm2PrincipalCoeff_apply_eq cometricFinBasisTrace_eq_chartInvGram_bilin quadrilinearMapSlotBilinearAt unitModel4SlotBilin_apply)

omit [BoundarylessManifold I M] in
private lemma lieArm_arm2_value_eq_principal_add_tail
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g₁ g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
        + ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k₁ l *
              (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
                + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
                - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁]) := by
  classical
  set pd2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun d' a' l' b' =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d'
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a'
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l' b'))
      (extChartAt I x x) with hpd2
  set R4 : (Fin 4 → Fin (Module.finrank ℝ E)) → ℝ := fun Jdx =>
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x Jdx with hR4
  set CIM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    chartInvGramMatrix (I := I) g₁ x x a b with hCIM
  rw [lieArm2_appCc_value_invGram (I := I) g₀ g₁ g_bg
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x i j]
  have hU4 : ∀ a b c d : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
          ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
        pd2 a b c d + R4 ![a, b, c, d] := fun a b c d =>
    lieArm_U4_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b c d
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => by
      rw [hU4 i l j k₁, hU4 j l i k₁, hU4 i j l k₁] :
    ∀ l ∈ Finset.univ,
      chartInvGramMatrix (I := I) g₁ x x k₁ l *
        (unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E l, chartModelBasis E j, chartModelBasis E k₁]
          + unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E j, chartModelBasis E l, chartModelBasis E i, chartModelBasis E k₁]
          - unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E l, chartModelBasis E k₁]) =
      CIM k₁ l *
        ((pd2 i l j k₁ + R4 ![i, l, j, k₁])
          + (pd2 j l i k₁ + R4 ![j, l, i, k₁])
          - (pd2 i j l k₁ + R4 ![i, j, l, k₁]))))]
  have hsplit : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      CIM k₁ l *
        ((pd2 i l j k₁ + R4 ![i, l, j, k₁])
          + (pd2 j l i k₁ + R4 ![j, l, i, k₁])
          - (pd2 i j l k₁ + R4 ![i, j, l, k₁]))) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * (pd2 i l j k₁ + pd2 j l i k₁ - pd2 i j l k₁))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * (R4 ![i, l, j, k₁] + R4 ![j, l, i, k₁] - R4 ![i, j, l, k₁])) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hsplit]
  refine congrArg (fun t : ℝ => t + _) ?_
  rw [show chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g₁ g_bg x
      (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x) =
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k j (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i a b k
                (extChartAt I x x)) +
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x i k (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x)) from rfl]
  rw [Finset.sum_congr rfl (fun k _ => by
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) g₁ x i k
        (extChartAt I x x)] :
    ∀ k ∈ Finset.univ,
      chartGramOnE (I := I) g₁ x i k (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x) =
      chartGramOnE (I := I) g₁ x k i (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x))]
  rw [lieArm_P2_halfCollapse (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x i j,
    lieArm_P2_halfCollapse (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x j i]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [hpd2]
  rw [lieArm_partialDeriv2_realizedGramDeriv_swap (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i j l k₁]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def lieArm_slot34Eval (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (u w : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => F c v u w
          map_add' := fun v₁ v₂ => by simp
          map_smul' := fun r v => by simp }
      map_add' := fun c₁ c₂ => by
        ext v
        simp
      map_smul' := fun r c => by
        ext v
        simp }

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_cometric_doubleTrace_eq_invGram
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l)
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k₁ p *
            (chartInvGramMatrix (I := I) g₁ x x l₁ m *
              F (chartModelBasis E m) (chartModelBasis E l₁)
                (chartModelBasis E p) (chartModelBasis E k₁)) := by
  classical
  have hinner : ∀ c v : E,
      (∑ l : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) c v) =
      (∑ l : Fin (Module.finrank ℝ E),
        (F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) : E →L[ℝ] E →L[ℝ] ℝ)) c v := by
    intro c v
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k)) =
    ∑ k : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        (F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) : E →L[ℝ] E →L[ℝ] ℝ))
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => (hinner _ _))]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
  rw [smul_eq_mul]
  rw [show (∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x k₁ p *
        (chartInvGramMatrix (I := I) g₁ x x l₁ m *
          F (chartModelBasis E m) (chartModelBasis E l₁)
            (chartModelBasis E p) (chartModelBasis E k₁))) =
    chartInvGramMatrix (I := I) g₁ x x k₁ p *
      ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x l₁ m *
          F (chartModelBasis E m) (chartModelBasis E l₁)
            (chartModelBasis E p) (chartModelBasis E k₁) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l₁ _ => ?_)
    rw [Finset.mul_sum]]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k₁ p * t) ?_
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
      F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l) (chartModelBasis E p) (chartModelBasis E k₁)) =
    ∑ l : Fin (Module.finrank ℝ E),
      lieArm_slot34Eval (E := E) F (chartModelBasis E p) (chartModelBasis E k₁)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l) from
    Finset.sum_congr rfl (fun l _ => rfl)]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))
  rw [smul_eq_mul]
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (unitModel3SlotBilin metricConnDiffLoweredTrilin metricConnDiffLoweredTrilin_apply deTurckLieArm1Coeff deTurckLieArm1Coeff_apply_eq)

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_unitModel3SlotBilin_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i j : Fin 3) (hij : i ≠ j) (base : Fin 3 → E) (c v : E) :
    unitModel3SlotBilin (E := E) f i j hij base c v =
      f (Function.update (Function.update base i c) j v) := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def lieArm_F4mul (A B : E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => LinearMap.toContinuousLinearMap
            { toFun := fun c' => LinearMap.toContinuousLinearMap
                { toFun := fun v' => A c c' * B v v'
                  map_add' := fun v₁ v₂ => by
                    simp [map_add,
                      mul_add]
                  map_smul' := fun r v' => by
                    simp [map_smul,
                      smul_eq_mul]
                    ring }
              map_add' := fun c₁ c₂ => by
                ext v'
                simp [LinearMap.toContinuousLinearMap, map_add,
                  ContinuousLinearMap.add_apply, add_mul]
              map_smul' := fun r c' => by
                ext v'
                simp [LinearMap.toContinuousLinearMap, map_smul,
                  ContinuousLinearMap.smul_apply, smul_eq_mul]
                ring }
          map_add' := fun v₁ v₂ => by
            ext c' v'
            simp [LinearMap.toContinuousLinearMap, map_add,
              ContinuousLinearMap.add_apply, mul_add]
          map_smul' := fun r v => by
            ext c' v'
            simp [LinearMap.toContinuousLinearMap, map_smul,
              ContinuousLinearMap.smul_apply, smul_eq_mul]
            ring }
      map_add' := fun c₁ c₂ => by
        ext v c' v'
        simp [LinearMap.toContinuousLinearMap, map_add,
          ContinuousLinearMap.add_apply, add_mul]
      map_smul' := fun r c => by
        ext v c' v'
        simp [LinearMap.toContinuousLinearMap, map_smul,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_F4mul_apply (A B : E →L[ℝ] E →L[ℝ] ℝ) (c v c' v' : E) :
    lieArm_F4mul (E := E) A B c v c' v' = A c c' * B v v' := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def lieArm_fix3 (f : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (e : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f c v e
          map_add' := fun v₁ v₂ => by
            simp [map_add, ContinuousLinearMap.add_apply]
          map_smul' := fun r v => by
            simp [map_smul, ContinuousLinearMap.smul_apply] }
      map_add' := fun c₁ c₂ => by
        ext v
        simp [LinearMap.toContinuousLinearMap, map_add, ContinuousLinearMap.add_apply]
      map_smul' := fun r c => by
        ext v
        simp [LinearMap.toContinuousLinearMap, map_smul, ContinuousLinearMap.smul_apply] }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_doubleTrace_slotBilin
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i₁ i₂ : Fin 3) (h12 : i₁ ≠ i₂) (base : Fin 3 → E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)))
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) *
          B ((Module.finBasis ℝ E) l) ((Module.finBasis ℝ E) k)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k₁ p *
            (chartInvGramMatrix (I := I) g₁ x x l₁ m *
              (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
                  (chartModelBasis E m) (chartModelBasis E p) *
                B (chartModelBasis E l₁) (chartModelBasis E k₁))) := by
  classical
  have hbrick := lieArm_cometric_doubleTrace_eq_invGram (I := I) g₁ x
    (lieArm_F4mul (E := E) (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base) B)
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))) *
        B ((Module.finBasis ℝ E) l) ((Module.finBasis ℝ E) k)) =
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      lieArm_F4mul (E := E) (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base) B
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))]
  · rw [hbrick]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
    rw [lieArm_F4mul_apply]
  · rw [lieArm_F4mul_apply]

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_slot12_pack
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (w c v : E) :
    unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![w, 0, 0] c v = W3 ![w, c, v] := by
  rw [lieArm_unitModel3SlotBilin_apply]
  refine congrArg (fun t : Fin 3 → E => W3 t) ?_
  funext j
  fin_cases j <;> simp [Function.update]

omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_slot02_pack
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (w c v : E) :
    unitModel3SlotBilin (E := E) W3 0 2 (by decide) ![0, w, 0] c v = W3 ![c, w, v] := by
  rw [lieArm_unitModel3SlotBilin_apply]
  refine congrArg (fun t : Fin 3 → E => W3 t) ?_
  funext j
  fin_cases j <;> simp [Function.update]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_arm1_group_traced
    (g₀X g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (v0 v1 : E) :
    ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k))
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) v1)
      - W3 ![v0, v1,
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀X : Π y : M, TangentSpace I y) x)]
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l))
      - (∑ k : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              ((Module.finBasis ℝ E) k)])
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k))) =
    ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) v1)))
      - W3 ![v0, v1,
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀X : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E l₁))
                (chartModelBasis E k₁))))) := by
  classical
  have hT2 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 (chartModelBasis E l₁))
                (chartModelBasis E k₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 1 2 (by decide)
      ![v0, 0, 0] ((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v1)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot12_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot12_pack]
      rfl
  have hT3 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) v1) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) v1))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 1 2 (by decide)
      ![v0, 0, 0] (lieArm_fix3 (E := E) (metricConnDiffLoweredTrilin (I := I) g₁ g₁ g_bg x) v1)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot12_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot12_pack]
      rfl
  have hT5 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E k₁))
                (chartModelBasis E l₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 0 2 (by decide)
      ![0, v1, 0] (((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v0).flip)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot02_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot02_pack]
      rfl
  have hT7 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E l₁))
                (chartModelBasis E k₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 0 2 (by decide)
      ![0, v1, 0] ((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v0)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot02_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot02_pack]
      rfl
  have hT6 : (∑ k : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              ((Module.finBasis ℝ E) k)]) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E k₁]) := by
    have h := cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x
      (unitModel3SlotBilin (E := E) W3 0 2 (by decide)
        ![0, (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1), 0])
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [lieArm_slot02_pack]
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      rw [smul_eq_mul, lieArm_slot02_pack]
  rw [hT2, hT3, hT5, hT7, hT6]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_arm1_T14_traced
    (g₀X g₁ : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (v0 v1 : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        W3 ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              ((Module.finBasis ℝ E) k)]) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E p,
                chartModelBasis E k₁]) := by
  classical
  have h := cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide)
      ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1), 0, 0])
  refine Eq.trans ?_ (Eq.trans h ?_)
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [lieArm_slot12_pack]
  · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
    rw [smul_eq_mul, lieArm_slot12_pack]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_arm1_value_traced
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (D : SmoothCcTensor g₀ 0 3)
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg) D) x
        ![chartModelBasis E i, chartModelBasis E j] =
      unitModel (I := I) (M := M) g₀ 3 D x
        ![(show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x),
          chartModelBasis E i, chartModelBasis E j]
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) (chartModelBasis E j))))
      - unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), (chartModelBasis E j),
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E j)),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E l₁))
                (chartModelBasis E k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) (chartModelBasis E i))))
      - unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), (chartModelBasis E i),
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E i)),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E l₁))
                (chartModelBasis E k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E j)),
                chartModelBasis E p,
                chartModelBasis E k₁]) := by
  classical
  refine (deTurckLieArm1Coeff_apply_eq (I := I) g₀ g₁ g_bg D x
    ![chartModelBasis E i, chartModelBasis E j]).trans ?_
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_) ?_
  · exact lieArm_arm1_group_traced (I := I) g₀ g₁ g_bg x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E i) (chartModelBasis E j)
  · exact lieArm_arm1_group_traced (I := I) g₀ g₁ g_bg x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E j) (chartModelBasis E i)
  · exact lieArm_arm1_T14_traced (I := I) g₀ g₁ x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E i) (chartModelBasis E j)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_inner_chartBasis_center (g : SmoothRiemannianMetric I M) (x : M)
    (p q : Fin (Module.finrank ℝ E)) :
    g.inner x ((chartModelBasis E) p : TangentSpace I x)
        ((chartModelBasis E) q : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x p q := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply,
    DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p,
    DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x q]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_connDiff_chartBasis_center
    (gA gB : SmoothRiemannianMetric I M) (x : M) (j k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.connDiff (I := I) gA gB x
        ((chartModelBasis E) j : TangentSpace I x)
        ((chartModelBasis E) k : TangentSpace I x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x k j p
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x k j p
            (extChartAt I x x)) •
          ((chartModelBasis E) p : TangentSpace I x) := by
  rw [show ((chartModelBasis E) j : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x j x from
    (DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x j).symm]
  rw [show ((chartModelBasis E) k : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x k x from
    (DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x k).symm]
  rw [PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) gA gB x
    (DifferentialGeometry.Integral.Connection.self_mem_chartLeviCivitaGoodSet (I := I) (α := x))
    j k]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_bilin_expand_fst (F : E →L[ℝ] E →L[ℝ] ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → E) (v : E) :
    F (∑ q : Fin (Module.finrank ℝ E), c q • w q) v =
      ∑ q : Fin (Module.finrank ℝ E), c q * F (w q) v := by
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_bilin_expand_snd (F : E →L[ℝ] E →L[ℝ] ℝ) (u : E)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → E) :
    F u (∑ q : Fin (Module.finrank ℝ E), c q • w q) =
      ∑ q : Fin (Module.finrank ℝ E), c q * F u (w q) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, smul_eq_mul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_U3_sum_slot0
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (u v : E) :
    W3 ![∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q, u, v] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![chartModelBasis E q, u, v] := by
  refine ((lieArm_slot02_pack (E := E) W3 u
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q) v).symm).trans ?_
  refine (lieArm_bilin_expand_fst (E := E)
    (unitModel3SlotBilin (E := E) W3 0 2 (by decide) ![0, u, 0]) c
    (fun q => chartModelBasis E q) v).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot02_pack (E := E) W3 u (chartModelBasis E q) v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_U3_sum_slot1
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (u : E) (c : Fin (Module.finrank ℝ E) → ℝ) (v : E) :
    W3 ![u, ∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q, v] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![u, chartModelBasis E q, v] := by
  refine ((lieArm_slot12_pack (E := E) W3 u
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q) v).symm).trans ?_
  refine (lieArm_bilin_expand_fst (E := E)
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![u, 0, 0]) c
    (fun q => chartModelBasis E q) v).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot12_pack (E := E) W3 u (chartModelBasis E q) v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_U3_sum_slot2
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (u v : E) (c : Fin (Module.finrank ℝ E) → ℝ) :
    W3 ![u, v, ∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![u, v, chartModelBasis E q] := by
  refine ((lieArm_slot12_pack (E := E) W3 u v
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q)).symm).trans ?_
  refine (lieArm_bilin_expand_snd (E := E)
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![u, 0, 0]) v c
    (fun q => chartModelBasis E q)).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot12_pack (E := E) W3 u v (chartModelBasis E q))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_inner_connDiff_chartBasis_value
    (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c d : Fin (Module.finrank ℝ E)) :
    gm.inner x
        (PDE.DeTurck.connDiff (I := I) gA gB x (chartModelBasis E a) (chartModelBasis E c))
        (chartModelBasis E d) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) gm x x q d := by
  refine (congrArg (fun t : TangentSpace I x => gm.inner x t (chartModelBasis E d))
    (lieArm_connDiff_chartBasis_center (I := I) gA gB x a c)).trans ?_
  refine (lieArm_bilin_expand_fst (E := E) (gm.inner x)
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x))
    (fun q => chartModelBasis E q) (chartModelBasis E d)).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul _) (lieArm_inner_chartBasis_center (I := I) gm x q d)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_U3_deTurckVF_slot0_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M) (u v : E) :
    W3 ![(show E from
        (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x), u, v] =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) *
          W3 ![chartModelBasis E w, u, v] := by
  have hW : (show E from
      (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x) =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) •
          chartModelBasis E w :=
    PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) gA gB x
  refine (congrArg (fun t : E => W3 ![t, u, v]) hW).trans ?_
  exact lieArm_U3_sum_slot0 (E := E) W3
    (fun w => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
      (extChartAt I x x)) u v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_U3_deTurckVF_slot2_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M) (u v : E) :
    W3 ![u, v, (show E from
        (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x)] =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) *
          W3 ![u, v, chartModelBasis E w] := by
  have hW : (show E from
      (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x) =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) •
          chartModelBasis E w :=
    PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) gA gB x
  refine (congrArg (fun t : E => W3 ![u, v, t]) hW).trans ?_
  exact lieArm_U3_sum_slot2 (E := E) W3 u v
    (fun w => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
      (extChartAt I x x))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_U3_connDiff_slot0_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c : Fin (Module.finrank ℝ E)) (u v : E) :
    W3 ![(show E from PDE.DeTurck.connDiff (I := I) gA gB x
        (chartModelBasis E a) (chartModelBasis E c)), u, v] =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          W3 ![chartModelBasis E q, u, v] := by
  have hconn : (show E from PDE.DeTurck.connDiff (I := I) gA gB x
      (chartModelBasis E a) (chartModelBasis E c)) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) •
          chartModelBasis E q :=
    lieArm_connDiff_chartBasis_center (I := I) gA gB x a c
  refine (congrArg (fun t : E => W3 ![t, u, v]) hconn).trans ?_
  exact lieArm_U3_sum_slot0 (E := E) W3
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x)) u v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lieArm_U3_connDiff_slot1_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c : Fin (Module.finrank ℝ E)) (u v : E) :
    W3 ![u, (show E from PDE.DeTurck.connDiff (I := I) gA gB x
        (chartModelBasis E a) (chartModelBasis E c)), v] =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          W3 ![u, chartModelBasis E q, v] := by
  have hconn : (show E from PDE.DeTurck.connDiff (I := I) gA gB x
      (chartModelBasis E a) (chartModelBasis E c)) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) •
          chartModelBasis E q :=
    lieArm_connDiff_chartBasis_center (I := I) gA gB x a c
  refine (congrArg (fun t : E => W3 ![u, t, v]) hconn).trans ?_
  exact lieArm_U3_sum_slot1 (E := E) W3 u
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x)) v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_arm1_value_realized
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (_hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (_hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![chartModelBasis E i, chartModelBasis E j] =
      (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g_bg x k₁ l₁ q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
      - (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x k₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x j i q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g_bg x k₁ l₁ q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
      - (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x k₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x i j q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x j i q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])) := by
  classical
  refine (lieArm_arm1_value_traced (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
    (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x i j).trans ?_
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · exact lieArm_U3_deTurckVF_slot0_value (I := I)
      (unitModel (I := I) (M := M) g₀ 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
      (chartModelBasis E i) (chartModelBasis E j)
  · refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) ?_ ?_) ?_) ?_) ?_) ?_
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j l₁ k₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x l₁ k₁ j)))
    · exact lieArm_U3_deTurckVF_slot2_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (chartModelBasis E i) (chartModelBasis E j)
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i k₁ l₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      exact congrArg (HMul.hMul _)
        (lieArm_U3_connDiff_slot1_value (I := I)
          (unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i j
          (chartModelBasis E p) (chartModelBasis E k₁))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i l₁ k₁)))
  · refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) ?_ ?_) ?_) ?_) ?_) ?_
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i l₁ k₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x l₁ k₁ i)))
    · exact lieArm_U3_deTurckVF_slot2_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (chartModelBasis E j) (chartModelBasis E i)
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j k₁ l₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      exact congrArg (HMul.hMul _)
        (lieArm_U3_connDiff_slot1_value (I := I)
          (unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j i
          (chartModelBasis E p) (chartModelBasis E k₁))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j l₁ k₁)))
  · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
    exact congrArg (HMul.hMul _)
      (lieArm_U3_connDiff_slot0_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i j
        (chartModelBasis E p) (chartModelBasis E k₁))

namespace O1Abstract

variable {n : ℕ}

private lemma o1_sum_ite (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, g q * (if p = q then (1 : ℝ) else 0)) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, mul_one]
  · intro q _ hq
    rw [if_neg (fun h => hq h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

private lemma o1_sink4 (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, F k₁ p l₁ m q)
    = ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, ∑ k₁ : Fin n, F k₁ p l₁ m q := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]

private lemma o1_sink4mid (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, F k₁ p l₁ m q)
    = ∑ k₁ : Fin n, ∑ p : Fin n, ∑ m : Fin n, ∑ q : Fin n, ∑ l₁ : Fin n, F k₁ p l₁ m q := by
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]

section Collapses

variable (ig cg : Fin n → Fin n → ℝ)

private lemma o1_col2
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (p q : Fin n) :
    (∑ k : Fin n, ig k p * cg q k) = if p = q then (1 : ℝ) else 0 := by
  rw [show (∑ k : Fin n, ig k p * cg q k) = ∑ k : Fin n, cg k q * ig k p from
    Finset.sum_congr rfl (fun k _ => by rw [hcgs q k]; ring)]
  exact hcol p q

private lemma o1_col3
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a) (q c : Fin n) :
    (∑ l : Fin n, ig q l * cg l c) = if q = c then (1 : ℝ) else 0 := by
  rw [show (∑ l : Fin n, ig q l * cg l c) = ∑ l : Fin n, cg l c * ig l q from
    Finset.sum_congr rfl (fun l _ => by rw [higs q l]; ring)]
  exact hcol q c

private lemma o1_col4
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (l m : Fin n) :
    (∑ c : Fin n, cg l c * ig c m) = if m = l then (1 : ℝ) else 0 := by
  rw [show (∑ c : Fin n, cg l c * ig c m) = ∑ c : Fin n, cg c l * ig c m from
    Finset.sum_congr rfl (fun c _ => by rw [hcgs l c])]
  exact hcol m l

end Collapses

section QuadCollapse

variable (ig cg : Fin n → Fin n → ℝ) (g1 g0 : Fin n → Fin n → Fin n → ℝ)
    (X : Fin n → Fin n → ℝ)

private lemma o1_quadAC
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (v : Fin n) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 l₁ v q - g0 l₁ v q) * cg q k₁))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a v c * X b c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a v c * X b c)) := by
  have hpt : ∀ k₁ p l₁ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 l₁ v q - g0 l₁ v q) * cg q k₁)))
      = ∑ q : Fin n,
          (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁) := by
    intro k₁ p l₁ m
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => hpt k₁ p l₁ m))))]
  rw [o1_sink4 (fun k₁ p l₁ m q =>
    (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁))]
  have hcolpt : ∀ p l₁ m q : Fin n,
      (∑ k₁ : Fin n,
        (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁))
      = (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (if p = q then (1 : ℝ) else 0) := by
    intro p l₁ m q
    rw [← Finset.mul_sum, o1_col2 ig cg hcol hcgs p q]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l₁ _ =>
    Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun q _ => hcolpt p l₁ m q))))]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l₁ _ =>
    Finset.sum_congr rfl (fun m _ =>
      o1_sum_ite (fun q => ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) p)))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun l₁ _ => Finset.sum_comm)]
  rw [show (∑ l₁ : Fin n, ∑ m : Fin n, ∑ p : Fin n,
      ig l₁ m * ((g1 l₁ v p - g0 l₁ v p) * X m p))
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (ig a b * (g1 a v c * X b c) - ig a b * (g0 a v c * X b c)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_quadB
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (v : Fin n) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 k₁ v q - g0 k₁ v q) * cg q l₁))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a v c * X c b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a v c * X c b)) := by
  have hpt : ∀ k₁ p l₁ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 k₁ v q - g0 k₁ v q) * cg q l₁)))
      = ∑ q : Fin n,
          (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁) := by
    intro k₁ p l₁ m
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => hpt k₁ p l₁ m))))]
  rw [o1_sink4mid (fun k₁ p l₁ m q =>
    (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁))]
  have hcolpt : ∀ k₁ p m q : Fin n,
      (∑ l₁ : Fin n,
        (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁))
      = (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (if m = q then (1 : ℝ) else 0) := by
    intro k₁ p m q
    rw [← Finset.mul_sum, o1_col2 ig cg hcol hcgs m q]
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun q _ => hcolpt k₁ p m q))))]
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun m _ =>
      o1_sum_ite (fun q => ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) m)))]
  rw [show (∑ k₁ : Fin n, ∑ p : Fin n, ∑ m : Fin n,
      ig k₁ p * ((g1 k₁ v m - g0 k₁ v m) * X m p))
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (ig a b * (g1 a v c * X c b) - ig a b * (g0 a v c * X c b)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

end QuadCollapse

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_sum_ite2 (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, (if q = p then (1 : ℝ) else 0) * g q) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, one_mul]
  · intro q _ hq
    rw [if_neg hq, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

section EFshapes

variable (ig : Fin n → Fin n → ℝ) (g1 g0 : Fin n → Fin n → Fin n → ℝ)
    (f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_pullE (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 p q k))
    = (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
      - (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 u v q * f3 p q k)) := by
  rw [show (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 p q k))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
          (ig k p * (g1 u v q * f3 p q k) - ig k p * (g0 u v q * f3 p q k)) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_pullF (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 q p k))
    = (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 q p k))
      - (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 u v q * f3 q p k)) := by
  rw [show (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 q p k))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
          (ig k p * (g1 u v q * f3 q p k) - ig k p * (g0 u v q * f3 q p k)) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_swapE (ga : Fin n → Fin n → Fin n → ℝ)
    (hgas : ∀ a b k : Fin n, ga a b k = ga b a k) (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga u v q * f3 p q k))
    = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga v u q * f3 p q k) :=
  Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun q _ => by rw [hgas u v q])))

private lemma o1_swapF (ga : Fin n → Fin n → Fin n → ℝ)
    (hgas : ∀ a b k : Fin n, ga a b k = ga b a k) (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga u v q * f3 q p k))
    = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga v u q * f3 q p k) :=
  Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun q _ => by rw [hgas u v q])))

private lemma o1_vf0exp (u v : Fin n) :
    (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 u v w)
    = (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g1 a b w * f3 u v w))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 u v w)) := by
  rw [show (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 u v w)
      = ∑ w : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          (ig a b * (g1 a b w * f3 u v w) - ig a b * (g0 a b w * f3 u v w)) from
    Finset.sum_congr rfl (fun w _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun b _ => by ring)))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  simp only [Finset.sum_sub_distrib]

end EFshapes

section DerivedHyps

private lemma o1_hgb2 (ig cg : Fin n → Fin n → ℝ) (gb g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (a b l : Fin n) :
    gb a b l = 2 * ∑ c : Fin n, cg l c * g1 a b c := by
  have h1 : (∑ c : Fin n, cg l c * g1 a b c)
      = ∑ c : Fin n, ∑ m : Fin n, (cg l c * ig c m) * ((1 / 2 : ℝ) * gb a b m) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hga1 a b c, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have h2 : (∑ c : Fin n, ∑ m : Fin n, (cg l c * ig c m) * ((1 / 2 : ℝ) * gb a b m))
      = ∑ m : Fin n, (if m = l then (1 : ℝ) else 0) * ((1 / 2 : ℝ) * gb a b m) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_mul, o1_col4 ig cg hcol hcgs l m]
  rw [h1, h2, o1_sum_ite2 (fun m => (1 / 2 : ℝ) * gb a b m) l]
  ring

private lemma o1_hdg2 (ig cg : Fin n → Fin n → ℝ) (dg gb g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (m u v : Fin n) :
    dg m u v = (∑ c : Fin n, cg v c * g1 m u c) + (∑ c : Fin n, cg u c * g1 m v c) := by
  have h1 : dg m u v = (1 / 2 : ℝ) * (gb m u v + gb m v u) := by
    rw [hgbdef m u v, hgbdef m v u, hdgs m v u, hdgs u v m, hdgs v u m]
    ring
  rw [h1, o1_hgb2 ig cg gb g1 hcol hcgs hga1 m u v,
    o1_hgb2 ig cg gb g1 hcol hcgs hga1 m v u]
  ring

private lemma o1_hdig2 (ig cg : Fin n → Fin n → ℝ) (dg gb dig g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (hdig : ∀ m a b : Fin n, dig m a b
      = -(∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y))
    (m a b : Fin n) :
    dig m a b = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)) := by
  have hsub : ∀ x y : Fin n, ig a x * ig y b * dg m x y
      = (∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        + ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c) := by
    intro x y
    rw [o1_hdg2 ig cg dg gb g1 hcol hcgs hgbdef hdgs hga1 m x y]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun c _ => by ring)
    · exact Finset.sum_congr rfl (fun c _ => by ring)
  have h0 : (∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y)
      = (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        + ∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c) := by
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hsub x y))]
    simp only [Finset.sum_add_distrib]
  have hP1 : (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
      = ∑ p : Fin n, ig a p * g1 m p b := by
    have e1 : ∀ x : Fin n,
        (∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        = ∑ c : Fin n, (ig a x * g1 m x c) * (if b = c then (1 : ℝ) else 0) := by
      intro x
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [← Finset.mul_sum, hcol b c]
    rw [Finset.sum_congr rfl (fun x _ => e1 x)]
    exact Finset.sum_congr rfl (fun x _ => o1_sum_ite (fun c => ig a x * g1 m x c) b)
  have hP2 : (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c))
      = ∑ p : Fin n, ig p b * g1 m p a := by
    have e2 : ∀ y c : Fin n, (∑ x : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c))
        = (ig y b * g1 m y c) * (if a = c then (1 : ℝ) else 0) := by
      intro y c
      rw [← Finset.mul_sum, o1_col3 ig cg hcol higs a c]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun c _ => e2 y c))]
    exact Finset.sum_congr rfl (fun y _ => o1_sum_ite (fun c => ig y b * g1 m y c) a)
  rw [hdig m a b, h0, hP1, hP2, ← Finset.sum_add_distrib]

end DerivedHyps

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_neg_push (c d : ℝ) (P : Fin n → Fin n → ℝ) :
    c * ((-(∑ q : Fin n, ∑ p : Fin n, P q p)) * d)
    = ∑ q : Fin n, ∑ p : Fin n, -(P q p * (d * c)) := by
  rw [show c * ((-(∑ q : Fin n, ∑ p : Fin n, P q p)) * d)
      = -((∑ q : Fin n, ∑ p : Fin n, P q p) * (d * c)) from by ring]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_neg_push1 (t : ℝ) (P : Fin n → Fin n → ℝ) :
    (-(∑ q : Fin n, ∑ p : Fin n, P q p)) * t
    = ∑ q : Fin n, ∑ p : Fin n, -(P q p * t) := by
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_sum_ite' (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, g q * (if q = p then (1 : ℝ) else 0)) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, mul_one]
  · intro q _ hq
    rw [if_neg hq, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

private lemma o1_neg_push3 (c d : ℝ) (X : Fin n → ℝ) :
    c * (d * (-(∑ q : Fin n, X q))) = ∑ q : Fin n, -(X q * (d * c)) := by
  rw [show c * (d * (-(∑ q : Fin n, X q))) = -((∑ q : Fin n, X q) * (d * c)) from by ring]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

section RQ3

variable (ig cg : Fin n → Fin n → ℝ) (g1 g0 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rq3
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a) (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u p q * ig q b)) * (g1 a b k - g0 a b k)))
    = -(∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
        ig k₁ p * (ig l₁ m * (f3 u m p * (∑ q : Fin n, (g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v)))) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u p q * ig q b)) * (g1 a b k - g0 a b k)))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          -((ig a p * f3 u p q * ig q b) * ((g1 a b k - g0 a b k) * cg k v)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact o1_neg_push (cg k v) (g1 a b k - g0 a b k) (fun q p => ig a p * f3 u p q * ig q b)
  rw [hflat]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  have hrhs : (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (f3 u m p * (∑ q : Fin n, (g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v))))
      = ∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n,
          ig k₁ p * (ig l₁ m * (f3 u m p * ((g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v))) := by
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [hrhs]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
    Finset.sum_congr rfl (fun x3 _ => Finset.sum_congr rfl (fun x4 _ =>
      Finset.sum_congr rfl (fun x5 _ => ?_)))))
  rw [higs x4 x3, hf3s u x2 x4]
  ring

end RQ3

section RG7

variable (ig cg : Fin n → Fin n → ℝ) (gb g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rg7
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hgb2 : ∀ a b l : Fin n, gb a b l = 2 * ∑ c : Fin n, cg l c * g1 a b c)
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l)))
    = -(∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g1 a b w * f3 u v w)) := by
  have hinner : ∀ k a b : Fin n,
      ((1 / 2 : ℝ) * ∑ l : Fin n,
        (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l)
      = -(∑ q : Fin n, (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q) := by
    intro k a b
    have hpt1 : ∀ l : Fin n,
        (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l
        = ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
            ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c) := by
      intro l
      rw [hgb2 a b l]
      rw [show (2 : ℝ) * ∑ c : Fin n, cg l c * g1 a b c
          = ∑ c : Fin n, 2 * (cg l c * g1 a b c) from Finset.mul_sum _ _ _]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [o1_neg_push1 (2 * (cg l c * g1 a b c)) (fun q p => ig k p * f3 u p q * ig q l)]
      refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_))
      ring
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun l _ => congrArg (HMul.hMul (1 / 2 : ℝ)) (hpt1 l))]
    have hro : (∑ l : Fin n, (1 / 2 : ℝ) * ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
        ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c))
        = ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n, ∑ l : Fin n,
            (1 / 2 : ℝ) * (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)) := by
      rw [show (∑ l : Fin n, (1 / 2 : ℝ) * ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c))
          = ∑ l : Fin n, ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
              (1 / 2 : ℝ) * (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)) from
        Finset.sum_congr rfl (fun l _ => by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [Finset.mul_sum])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_comm]
    rw [hro]
    have hcolstep : ∀ c q p : Fin n,
        (∑ l : Fin n, (1 / 2 : ℝ) *
          (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)))
        = (-((ig k p * f3 u p q) * g1 a b c)) * (if q = c then (1 : ℝ) else 0) := by
      intro c q p
      rw [show (∑ l : Fin n, (1 / 2 : ℝ) *
          (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)))
          = ∑ l : Fin n, (-((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c) from
        Finset.sum_congr rfl (fun l _ => by ring)]
      rw [← Finset.mul_sum, o1_col3 ig cg hcol higs q c]
    rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun p _ => hcolstep c q p)))]
    have hite : (∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
        (-((ig k p * f3 u p q) * g1 a b c)) * (if q = c then (1 : ℝ) else 0))
        = ∑ q : Fin n, ∑ p : Fin n, -((ig k p * f3 u p q) * g1 a b q) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      exact o1_sum_ite (fun c => -((ig k p * f3 u p q) * g1 a b c)) q
    rw [hite]
    rw [show (∑ q : Fin n, ∑ p : Fin n, -((ig k p * f3 u p q) * g1 a b q))
        = ∑ q : Fin n, -((∑ p : Fin n, ig k p * f3 u p q) * g1 a b q) from
      Finset.sum_congr rfl (fun q _ => by
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul])]
    rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl (fun k _ => congrArg (HMul.hMul (cg k v))
    (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      congrArg (HMul.hMul (ig a b)) (hinner k a b)))))]
  have hflat2 : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      ig a b * (-(∑ q : Fin n, (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          (-((f3 u p q * (ig a b * g1 a b q))) * (cg k v * ig k p)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [o1_neg_push3 (cg k v) (ig a b)
      (fun q => (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [show -((∑ p : Fin n, ig k p * f3 u p q) * g1 a b q * (ig a b * cg k v))
        = ∑ p : Fin n, -((f3 u p q * (ig a b * g1 a b q)) * (cg k v * ig k p)) from by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hflat2]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_comm)))]
  have hcolk : ∀ a b q p : Fin n,
      (∑ k : Fin n, (-((f3 u p q * (ig a b * g1 a b q))) * (cg k v * ig k p)))
      = (-((f3 u p q * (ig a b * g1 a b q)))) * (if p = v then (1 : ℝ) else 0) := by
    intro a b q p
    rw [← Finset.mul_sum, hcol p v]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => hcolk a b q p))))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ =>
      o1_sum_ite' (fun p => -((f3 u p q * (ig a b * g1 a b q)))) v)))]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, -((f3 u v q * (ig a b * g1 a b q))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, -(ig a b * (g1 a b q * f3 u v q)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_neg_distrib]

end RG7

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_neg_push1d (t : ℝ) (P : Fin n → ℝ) :
    (-(∑ p : Fin n, P p)) * t = ∑ p : Fin n, -(P p * t) := by
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_sum3_add (F G : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, F a b c)
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, G a b c)
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, (F a b c + G a b c) := by
  simp only [Finset.sum_add_distrib]

private lemma o1_abswap3 (H : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, H a b p)
    = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, H b a p :=
  Finset.sum_comm

section RF1

variable (ig cg : Fin n → Fin n → ℝ) (dig g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rf1a
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hdig2 : ∀ m a b : Fin n, dig m a b
      = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)))
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, dig u a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
    = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 b v c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 c v b))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 v b c)) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, dig u a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
          (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * (cg k v * ig k l) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hflat]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  have hcolk : ∀ a b l : Fin n,
      (∑ k : Fin n,
        (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * (cg k v * ig k l))
      = (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b)))
          * (if l = v then (1 : ℝ) else 0) := by
    intro a b l
    rw [← Finset.mul_sum, hcol l v]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun l _ => hcolk a b l)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    o1_sum_ite' (fun l => dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) v))]
  have h2 : ∀ a b : Fin n,
      dig u a b * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))
      = ∑ p : Fin n,
          (-((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))
           + -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))) := by
    intro a b
    rw [hdig2 u a b, o1_neg_push1d ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))
      (fun p => ig a p * g1 u p b + ig p b * g1 u p a)]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h2 a b))]
  simp only [Finset.sum_add_distrib]
  have hmerge : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
      -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
          -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))) := by
    rw [o1_abswap3 (fun a b p =>
      -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun p _ => ?_)))
    rw [higs p a, hf3s v b a]
    ring
  rw [hmerge]
  rw [o1_sum3_add
    (fun a b p => -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))
    (fun a b p => -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
      (-((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))
       + -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
          ((-((ig a p * g1 u p b) * f3 a v b) + -((ig a p * g1 u p b) * f3 b v a))
           + (ig a p * g1 u p b) * f3 v a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun p _ => by ring)))]
  simp only [Finset.sum_add_distrib]
  have hT1 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, -((ig a p * g1 u p b) * f3 a v b))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 b v c)) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [show (∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -((ig a p * g1 u p b) * f3 a v b))
        = ∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -(ig p a * (g1 p u b * f3 a v b)) from
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))]
    simp only [Finset.sum_neg_distrib]
  have hT2 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, -((ig a p * g1 u p b) * f3 b v a))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 c v b)) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [show (∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -((ig a p * g1 u p b) * f3 b v a))
        = ∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -(ig p a * (g1 p u b * f3 b v a)) from
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))]
    simp only [Finset.sum_neg_distrib]
  have hT3 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, (ig a p * g1 u p b) * f3 v a b)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 v b c) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))
  rw [hT1, hT2, hT3]
  ring

end RF1

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_const_pull3 (c : ℝ) (X : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, c * X a b l)
    = c * ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, X a b l := by
  simp only [← Finset.mul_sum]

private lemma o1_const_pull5 (c : ℝ) (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n, c * X a b l p k)
    = c * ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n, X a b l p k := by
  simp only [← Finset.mul_sum]

private lemma o1_ftriple3 (f3 : Fin n → Fin n → Fin n → ℝ) (W : Fin n → Fin n → Fin n → ℝ)
    (hW : ∀ a b l : Fin n, W a b l = W b a l) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * (f3 a l b + f3 b l a - f3 l a b))
    = 2 * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 a l b)
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 l a b) := by
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * (f3 a l b + f3 b l a - f3 l a b))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
          ((W a b l * f3 a l b + W a b l * f3 b l a) - W a b l * f3 l a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => by ring)))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 b l a)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 a l b := by
    rw [o1_abswap3 (fun a b l => W a b l * f3 b l a)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => ?_)))
    rw [hW b a l]
  rw [hAB]
  ring

private lemma o1_ftriple5 (f3 : Fin n → Fin n → Fin n → ℝ)
    (W : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (hW : ∀ a b l p k : Fin n, W a b l p k = W b a l p k) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * (f3 a l b + f3 b l a - f3 l a b))
    = 2 * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 a l b)
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 l a b) := by
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * (f3 a l b + f3 b l a - f3 l a b))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ((W a b l p k * f3 a l b + W a b l p k * f3 b l a) - W a b l p k * f3 l a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun k _ => by ring)))))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * f3 b l a)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          W a b l p k * f3 a l b := by
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 b l a)
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            W b a l p k * f3 a l b from Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun k _ => ?_)))))
    rw [hW b a l p k]
  rw [hAB]
  ring

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

section RF1B

variable (ig cg : Fin n → Fin n → ℝ) (dig g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rf1b
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hdig2 : ∀ m a b : Fin n, dig m a b
      = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)))
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, dig u k l * (f3 a l b + f3 b l a - f3 l a b))))
    = -(∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
      + (1 / 2 : ℝ) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 q p k))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
      + (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, dig u k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
          ((-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
              * (cg k v * ig k p)
           + -(ig a b * (ig p l * ((1 / 2 : ℝ) *
              ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v)))))) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hdig2 u k l, o1_neg_push1d (f3 a l b + f3 b l a - f3 l a b)
      (fun p => ig k p * g1 u p l + ig p l * g1 u p k)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hflat]
  simp only [Finset.sum_add_distrib]
  have hS1 : (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
      (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
        * (cg k v * ig k p))
      = -(∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
        + (1 / 2 : ℝ) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 q p k)) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]
    have hck : ∀ a b l p : Fin n,
        (∑ k : Fin n,
          (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
            * (cg k v * ig k p))
        = (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
            * (if p = v then (1 : ℝ) else 0) := by
      intro a b l p
      rw [← Finset.mul_sum, hcol p v]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ => hck a b l p))))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => o1_sum_ite' (fun p =>
        -((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l)) v)))]
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        -((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u v l))
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
            (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * (f3 a l b + f3 b l a - f3 l a b) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun l _ => by ring)))]
    rw [o1_ftriple3 f3 (fun a b l => -((1 / 2 : ℝ) * (ig a b * g1 u v l)))
      (fun a b l => by
        change -((1 / 2 : ℝ) * (ig a b * g1 u v l)) = -((1 / 2 : ℝ) * (ig b a * g1 u v l))
        rw [higs a b])]
    have hE : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 a l b)
        = (-(1 / 2 : ℝ)) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 p q k)) := by
      rw [Finset.sum_comm]
      rw [show (∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 a l b)
          = ∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
              (-(1 / 2 : ℝ)) * (ig b a * (g1 u v l * f3 a l b)) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun l _ => by rw [higs a b]; ring)))]
      rw [o1_const_pull3]
    have hF : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 l a b)
        = (-(1 / 2 : ℝ)) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 q p k)) := by
      rw [Finset.sum_comm]
      rw [show (∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 l a b)
          = ∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
              (-(1 / 2 : ℝ)) * (ig b a * (g1 u v l * f3 l a b)) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun l _ => by rw [higs a b]; ring)))]
      rw [o1_const_pull3]
    rw [hE, hF]
    ring
  have hS2 : (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
      -(ig a b * (ig p l * ((1 / 2 : ℝ) *
        ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v))))))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
        + (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        -(ig a b * (ig p l * ((1 / 2 : ℝ) *
          ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v))))))
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v)))))
              * (f3 a l b + f3 b l a - f3 l a b) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
          Finset.sum_congr rfl (fun k _ => by ring)))))]
    rw [o1_ftriple5 f3
      (fun a b l p k => -((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v)))))
      (fun a b l p k => by
        change -((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))
          = -((1 / 2 : ℝ) * (ig b a * (ig p l * (g1 u p k * cg k v))))
        rw [higs a b])]
    have hR1 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 a l b)
        = (-(1 / 2 : ℝ)) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v)))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 a l b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
              (-(1 / 2 : ℝ)) * (ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v)))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
            Finset.sum_congr rfl (fun k _ => by ring)))))]
      rw [o1_const_pull5]
    have hR2 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 l a b)
        = (-(1 / 2 : ℝ)) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 l a b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
              (-(1 / 2 : ℝ)) * (ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
            Finset.sum_congr rfl (fun k _ => by ring)))))]
      rw [o1_const_pull5]
    rw [hR1, hR2]
    ring
  rw [hS1, hS2]
  ring

end RF1B

private lemma o1_mul_sum_sum (x y : ℝ) (A B : Fin n → ℝ) :
    (x * (y * ∑ l : Fin n, A l)) * (∑ c : Fin n, B c)
    = ∑ l : Fin n, ∑ c : Fin n, (y * (x * B c)) * A l := by
  rw [show (x * (y * ∑ l : Fin n, A l)) * (∑ c : Fin n, B c)
      = (∑ l : Fin n, A l) * (∑ c : Fin n, B c) * (x * y) from by ring]
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun c _ => by ring)

section RLVF

variable (ig cg : Fin n → Fin n → ℝ) (dg g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rlvf
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hdg2 : ∀ m a b : Fin n, dg m a b
      = (∑ c : Fin n, cg b c * g1 m a c) + (∑ c : Fin n, cg a c * g1 m b c))
    (u v : Fin n) :
    (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
    = (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 a l b * (g1 v p k * cg k u))))
      - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v))))
      - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 l a b * (g1 v p k * cg k u)))) := by
  have hsplit : (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
      = (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
            * (∑ c : Fin n, cg v c * g1 k u c))
        + ∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg u c * g1 k v c) := by
    rw [show (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
        = ∑ k : Fin n, ((∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg v c * g1 k u c)
           + (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg u c * g1 k v c)) from
      Finset.sum_congr rfl (fun k _ => by rw [hdg2 k u v, mul_add])]
    rw [Finset.sum_add_distrib]
  rw [hsplit]
  have hhalf : ∀ u' v' : Fin n,
      (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
          * (∑ c : Fin n, cg v' c * g1 k u' c))
      = (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u' p k * cg k v'))))
        - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u' p k * cg k v')))) := by
    intro u' v'
    have hflat : (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
          * (∑ c : Fin n, cg v' c * g1 k u' c))
        = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ c : Fin n,
            ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c))))
              * (f3 a l b + f3 b l a - f3 l a b) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [o1_mul_sum_sum (ig a b) (1 / 2 : ℝ)
        (fun l => ig k l * (f3 a l b + f3 b l a - f3 l a b))
        (fun c => cg v' c * g1 k u' c)]
      refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun c _ => ?_))
      ring
    rw [hflat]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [o1_ftriple5 f3
      (fun a b l k c => (1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c))))
      (fun a b l k c => by
        change (1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))
          = (1 / 2 : ℝ) * (ig b a * (ig k l * (cg v' c * g1 k u' c)))
        rw [higs a b])]
    have hB1 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 a l b)
        = (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 a l b * (g1 u' p k * cg k v')))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
          ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 a l b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
              (1 / 2 : ℝ) * (ig a b * (ig k l * (f3 a l b * (g1 u' k c * cg c v')))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
            Finset.sum_congr rfl (fun c _ => by
              rw [hcgs v' c, hg1s k u' c]; ring)))))]
      rw [o1_const_pull5]
    have hB2 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 l a b)
        = (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 l a b * (g1 u' p k * cg k v')))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
          ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 l a b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
              (1 / 2 : ℝ) * (ig a b * (ig k l * (f3 l a b * (g1 u' k c * cg c v')))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
            Finset.sum_congr rfl (fun c _ => by
              rw [hcgs v' c, hg1s k u' c]; ring)))))]
      rw [o1_const_pull5]
    rw [hB1, hB2]
    ring
  rw [hhalf u v, hhalf v u]
  ring

end RLVF

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

section Tail

variable (ig : Fin n → Fin n → ℝ) (g0 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_tail
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hg0s : ∀ a b k : Fin n, g0 a b k = g0 b a k)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (i j : Fin n) :
    (∑ k₁ : Fin n, ∑ l : Fin n, ig k₁ l *
      ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
          + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
       + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
          + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
       - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
          + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r)))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 c j b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 c i b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 b j c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 b i c))
      - 2 * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k))
      + (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 q p k))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 i j w))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 j i w)) := by
  have hcomb : ∀ k₁ l : Fin n, ig k₁ l *
      ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
          + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
       + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
          + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
       - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
          + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r))))
      = ∑ r : Fin n,
          (((ig k₁ l * (g0 j l r * f3 i r k₁) + ig k₁ l * (g0 j k₁ r * f3 i l r)
              + ig k₁ l * (g0 i j r * f3 r l k₁) + ig k₁ l * (g0 i l r * f3 j r k₁)
              + ig k₁ l * (g0 i k₁ r * f3 j l r))
            - (ig k₁ l * (g0 l j r * f3 i r k₁) + ig k₁ l * (g0 l k₁ r * f3 i j r)
              + ig k₁ l * (g0 i l r * f3 r j k₁) + ig k₁ l * (g0 i j r * f3 l r k₁)
              + ig k₁ l * (g0 i k₁ r * f3 l j r)))
           - (ig k₁ l * (g0 l i r * f3 j r k₁) + ig k₁ l * (g0 l k₁ r * f3 j i r)
              + ig k₁ l * (g0 j l r * f3 r i k₁) + ig k₁ l * (g0 j i r * f3 l r k₁)
              + ig k₁ l * (g0 j k₁ r * f3 l i r))) := by
    intro k₁ l
    rw [show ∀ P Q R : Fin n → ℝ, (-(∑ r : Fin n, P r)) + (-(∑ r : Fin n, Q r))
        - (-(∑ r : Fin n, R r)) = (∑ r : Fin n, R r) - (∑ r : Fin n, P r) - (∑ r : Fin n, Q r)
      from fun P Q R => by ring]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => hcomb k₁ l))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hp1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l j r * f3 i r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hf3s i r k₁])))
  have hp2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l k₁ r * f3 i j r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 i j w) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l])))
  have hp3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i l r * f3 r j k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 c j b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s i l r])))
  have hp4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i j r * f3 l r k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by ring)))
  have hp5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i k₁ r * f3 l j r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 b j c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s i k₁ r])))
  have hq1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l i r * f3 j r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hf3s j r k₁])))
  have hq2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l k₁ r * f3 j i r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 j i w) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l])))
  have hq3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j l r * f3 r i k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 c i b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s j l r])))
  have hq4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j i r * f3 l r k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j i r])))
  have hq5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j k₁ r * f3 l i r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 b i c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j k₁ r])))
  have hr1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j l r * f3 i r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s j l r, hf3s i r k₁])))
  have hr2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j k₁ r * f3 i l r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j k₁ r])))
  have hr3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i j r * f3 r l k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 q p k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by ring)))
  have hr4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i l r * f3 j r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s i l r, hf3s j r k₁])))
  have hr5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i k₁ r * f3 j l r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s i k₁ r])))
  rw [hp1, hp2, hp3, hp4, hp5, hq1, hq2, hq3, hq4, hq5, hr1, hr2, hr3, hr4, hr5]
  ring

end Tail

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

set_option maxHeartbeats 3200000 in
private lemma o1_master (ig cg : Fin n → Fin n → ℝ)
    (dg gb dig g1 g0 gbg f3 : Fin n → Fin n → Fin n → ℝ) (w1 : Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hg0s : ∀ a b k : Fin n, g0 a b k = g0 b a k)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (hdig : ∀ m a b : Fin n, dig m a b
      = -(∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y))
    (i j : Fin n) :
    ((∑ w : Fin n, w1 w * f3 w i j)
      + ((∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 i m p * (∑ q : Fin n, (g1 l₁ j q - g0 l₁ j q) * cg q k₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 i m p * (∑ q : Fin n, (g1 k₁ l₁ q - gbg k₁ l₁ q) * cg q j))))
        - (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 i j w)
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m j p * (∑ q : Fin n, (g1 k₁ i q - g0 k₁ i q) * cg q l₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n,
            ig k₁ p * (∑ q : Fin n, (g1 j i q - g0 j i q) * f3 p q k₁))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m j p * (∑ q : Fin n, (g1 l₁ i q - g0 l₁ i q) * cg q k₁)))))
      + ((∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 j m p * (∑ q : Fin n, (g1 l₁ i q - g0 l₁ i q) * cg q k₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 j m p * (∑ q : Fin n, (g1 k₁ l₁ q - gbg k₁ l₁ q) * cg q i))))
        - (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 j i w)
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m i p * (∑ q : Fin n, (g1 k₁ j q - g0 k₁ j q) * cg q l₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n,
            ig k₁ p * (∑ q : Fin n, (g1 i j q - g0 i j q) * f3 p q k₁))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m i p * (∑ q : Fin n, (g1 l₁ j q - g0 l₁ j q) * cg q k₁)))))
      + (∑ k₁ : Fin n, ∑ p : Fin n,
          ig k₁ p * (∑ q : Fin n, (g1 j i q - g0 j i q) * f3 q p k₁)))
    + (∑ k₁ : Fin n, ∑ l : Fin n, ig k₁ l *
        ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
            + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
         + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
            + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
         - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
            + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r)))))
    = ((∑ k : Fin n, cg k j *
          ((∑ a : Fin n, ∑ b : Fin n, dig i a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig i k l * (f3 a l b + f3 b l a - f3 l a b))))
      + ∑ k : Fin n, cg i k *
          ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))))
    + ((∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k i j)
      + (∑ k : Fin n, w1 k * f3 k i j)
      + (∑ k : Fin n, cg k j * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 i p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 i p q * ig q l)) * gb a b l))))
      + (∑ k : Fin n, cg i k * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))))) := by
  have hgb2 := o1_hgb2 ig cg gb g1 hcol hcgs hga1
  have hdg2 := o1_hdg2 ig cg dg gb g1 hcol hcgs hgbdef hdgs hga1
  have hdig2 := o1_hdig2 ig cg dg gb dig g1 hcol higs hcgs hgbdef hdgs hga1 hdig
  have hT2 := o1_quadAC ig cg g1 g0 (fun m p => f3 i m p) hcol hcgs j
  have hT5 := o1_quadB ig cg g1 g0 (fun m p => f3 m j p) hcol hcgs i
  have hT7 := o1_quadAC ig cg g1 g0 (fun m p => f3 m j p) hcol hcgs i
  have hT8 := o1_quadAC ig cg g1 g0 (fun m p => f3 j m p) hcol hcgs i
  have hT11 := o1_quadB ig cg g1 g0 (fun m p => f3 m i p) hcol hcgs j
  have hT13 := o1_quadAC ig cg g1 g0 (fun m p => f3 m i p) hcol hcgs j
  have hT4 := o1_vf0exp ig g1 g0 f3 i j
  have hT10 := o1_vf0exp ig g1 g0 f3 j i
  have hT6 := (o1_pullE ig g1 g0 f3 j i).trans
    (congrArg₂ (· - ·) (o1_swapE ig f3 g1 hg1s j i) (o1_swapE ig f3 g0 hg0s j i))
  have hT12 := o1_pullE ig g1 g0 f3 i j
  have hT14 := (o1_pullF ig g1 g0 f3 j i).trans
    (congrArg₂ (· - ·) (o1_swapF ig f3 g1 hg1s j i) (o1_swapF ig f3 g0 hg0s j i))
  have hTail := o1_tail ig g0 f3 higs hg0s hf3s i j
  have hFRsplit : ∀ u' v' : Fin n,
      (∑ k : Fin n, cg k v' *
        ((∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
         + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))))
      = (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
        + ∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))) := by
    intro u' v'
    rw [show (∑ k : Fin n, cg k v' *
        ((∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
         + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))))
        = ∑ k : Fin n,
            (cg k v' * (∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
             + cg k v' * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b)))) from
      Finset.sum_congr rfl (fun k _ => mul_add _ _ _)]
    rw [Finset.sum_add_distrib]
  have hCDsplit : ∀ u' v' : Fin n,
      (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
        ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
         + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
            (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))))
      = (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
          (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)))
        + ∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
            ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l)) := by
    intro u' v'
    rw [show (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
        ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
         + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
            (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))))
        = ∑ k : Fin n,
            (cg k v' * (∑ a : Fin n, ∑ b : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k))
             + cg k v' * (∑ a : Fin n, ∑ b : Fin n,
                ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                  (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))) from
      Finset.sum_congr rfl (fun k _ => by
        rw [show (∑ a : Fin n, ∑ b : Fin n,
            ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
             + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l)))
            = (∑ a : Fin n, ∑ b : Fin n,
                (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k))
              + ∑ a : Fin n, ∑ b : Fin n,
                  ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                    (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l) from by
          simp only [Finset.sum_add_distrib]]
        rw [mul_add])]
    rw [Finset.sum_add_distrib]
  have hflipFR : (∑ k : Fin n, cg i k *
      ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
       + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, cg k i *
          ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))) :=
    Finset.sum_congr rfl (fun k _ => by rw [hcgs i k])
  have hflipCD : (∑ k : Fin n, cg i k * (∑ a : Fin n, ∑ b : Fin n,
      ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
       + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
          (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))))
      = ∑ k : Fin n, cg k i * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))) :=
    Finset.sum_congr rfl (fun k _ => by rw [hcgs i k])
  rw [hflipFR, hflipCD]
  rw [hFRsplit i j, hFRsplit j i, hCDsplit i j, hCDsplit j i]
  rw [o1_rf1a ig cg dig g1 f3 hcol higs hf3s hg1s hdig2 i j]
  rw [o1_rf1a ig cg dig g1 f3 hcol higs hf3s hg1s hdig2 j i]
  rw [o1_rf1b ig cg dig g1 f3 hcol higs hdig2 i j]
  rw [o1_rf1b ig cg dig g1 f3 hcol higs hdig2 j i]
  rw [o1_rlvf ig cg dg g1 f3 higs hcgs hg1s hdg2 i j]
  rw [o1_rq3 ig cg g1 gbg f3 higs hf3s i j]
  rw [o1_rq3 ig cg g1 gbg f3 higs hf3s j i]
  rw [o1_rg7 ig cg gb g1 f3 hcol higs hgb2 i j]
  rw [o1_rg7 ig cg gb g1 f3 hcol higs hgb2 j i]
  rw [o1_swapE ig f3 g1 hg1s j i, o1_swapF ig f3 g1 hg1s j i]
  rw [hT2, hT5, hT7, hT8, hT11, hT13, hT4, hT10, hT6, hT12, hT14, hTail]
  ring

end O1Abstract

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lieArm_chartGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b
    = DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x b a := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply,
    DifferentialGeometry.Integral.Measure.chartGramMatrix_apply]
  exact g.symm _ _ _

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma lieArm_realizedGramDeriv_symm (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b : Fin (Module.finrank ℝ E)) :
    realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b
    = realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b a := by
  funext y
  change DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b y
    - DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b y
    = DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x b a y
    - DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x b a y
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) _ x a b,
    DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) _ x a b]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_chartChristoffel_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g x a b k (extChartAt I x x)
    = (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          DeTurckCoefficients.gramBracket (I := I) g x a b l (extChartAt I x x) := by
  rw [DeTurckCoefficients.chartChristoffel_eq_sum_invGramOnE_bracket (I := I) g x a b k (extChartAt I x x)]
  refine congrArg (HMul.hMul (1 / 2 : ℝ)) (Finset.sum_congr rfl (fun l _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g x k l]

omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_partial_chartInvGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (m a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
      (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) g x a b) (extChartAt I x x)
    = -(∑ x' : Fin (Module.finrank ℝ E), ∑ y' : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a x' * chartInvGramMatrix (I := I) g x x y' b *
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
            (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g x x' y') (extChartAt I x x)) := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv_chartInvGramOnE_eq (I := I) g x
    (extChartAt I x x) m a b
    (DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x))]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun y' _ => ?_)))
  rw [lieArm_chartInvGramOnE_center (I := I) g x a x', lieArm_chartInvGramOnE_center (I := I) g x y' b]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lieArm_chartDeTurckVFComp_center (gA gB : SmoothRiemannianMetric I M) (x : M)
    (k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x k (extChartAt I x x)
    = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) gA x x a b *
          (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x a b k (extChartAt I x x)
           - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x a b k (extChartAt I x x)) := by
  rw [PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_def]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) gA x a b]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma lieArm_o1raw_center_eq (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.lieDeTurckOrder1Raw (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
    = ((∑ k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k j *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x) * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x))))
         + ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l) (extChartAt I x x) * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x)))))
      + ∑ k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i k *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x) * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x))))
         + ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l) (extChartAt I x x) * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x)))))
    + ((∑ k : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x)))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) k (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j) (extChartAt I x x))
      + (∑ k : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) k (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) (extChartAt I x x))
      + (∑ k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k j * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a p * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) (extChartAt I x x) * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q b)) * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x a b k (extChartAt I x x))
         + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k p * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) (extChartAt I x x) * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l)) * DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x)))))
      + (∑ k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i k * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a p * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) (extChartAt I x x) * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q b)) * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x a b k (extChartAt I x x))
         + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k p * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) (extChartAt I x x) * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l)) * DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x)))))) := by
  unfold PDE.DeTurck.DeTurckLinearization.lieDeTurckOrder1Raw
    PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrFirstOrderRemainderRaw
    PDE.DeTurck.DeTurckLinearization.order1PartRaw
    PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipalRaw
    PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrDeriv1Raw
    PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrGramDerivBlockRaw
    PDE.DeTurck.DeTurckLinearization.chartLinearizedChristoffelPrincipalRaw
  simp only [lieArm_chartInvGramOnE_center, lieArm_chartGramOnE_center]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_arm1_value_eq_order1Raw_add_tail (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![chartModelBasis E i, chartModelBasis E j]
    = PDE.DeTurck.DeTurckLinearization.lieDeTurckOrder1Raw (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
      + (((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
        ((-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r) (extChartAt I x x))))
         + (-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l i r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r) (extChartAt I x x))))
         - (-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r) (extChartAt I x x))))))) := by
  classical
  refine (lieArm_arm1_value_realized (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' s x i j).trans ?_
  have hs1 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j]) = (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) w (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j]) = ∑ w : Fin (Module.finrank ℝ E), (PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) w (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) (extChartAt I x x) + PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x w i j]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs2 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs3 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs4 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w]) = (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j w) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w]) = ∑ w : Fin (Module.finrank ℝ E), ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j w) (extChartAt I x x) + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j w,
          lieArm_chartDeTurckVFComp_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs5 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs6 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]) from
          Finset.sum_congr rfl (fun q _ => by
            rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k₁]
            ring)]
        rw [Finset.sum_add_distrib, mul_add]))]
    simp only [Finset.sum_add_distrib]
  have hs7 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs8 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs9 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs10 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w]) = (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i w) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w]) = ∑ w : Fin (Module.finrank ℝ E), ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i w) (extChartAt I x x) + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j i w,
          lieArm_chartDeTurckVFComp_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs11 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs12 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]) from
          Finset.sum_congr rfl (fun q _ => by
            rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k₁]
            ring)]
        rw [Finset.sum_add_distrib, mul_add]))]
    simp only [Finset.sum_add_distrib]
  have hs13 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs14 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁]) from
          Finset.sum_congr rfl (fun q _ => by
            rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q p k₁]
            ring)]
        rw [Finset.sum_add_distrib, mul_add]))]
    simp only [Finset.sum_add_distrib]
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14]
  rw [lieArm_o1raw_center_eq (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' s x i j]
  have hcol' : ∀ l j' : Fin (Module.finrank ℝ E), (∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k j' *
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l) = if l = j' then (1 : ℝ) else 0 :=
    fun l j' => lieArm_gram_invGram_collapse (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l j'
  have higs' : ∀ a b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b = chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x b a :=
    fun a b => lieArm_chartInvGramMatrix_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b
  have hcgs' : ∀ a b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b = DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x b a :=
    fun a b => lieArm_chartGramMatrix_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b
  have hf3s' : ∀ d a b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x) = DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b a) (extChartAt I x x) :=
    fun d a b => congrArg
      (fun F => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d F (extChartAt I x x))
      (lieArm_realizedGramDeriv_symm (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
  have hg1s' : ∀ a b k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x) = DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x b a k (extChartAt I x x) :=
    fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_symm (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x)
  have hg0s' : ∀ a b k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b k (extChartAt I x x) = DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x b a k (extChartAt I x x) :=
    fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_symm (I := I)
      g₀ x a b k (extChartAt I x x)
  have hgbdef' : ∀ a b l : Fin (Module.finrank ℝ E), DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x)
      = DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x) :=
    fun a b l => rfl
  have hdgs' : ∀ m a b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x) = DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x b a) (extChartAt I x x) :=
    fun m a b => congrArg
      (fun F => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m F (extChartAt I x x))
      (funext (fun y => DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b y))
  have hga1' : ∀ a b k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x)
      = (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l * DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x) :=
    fun a b k => lieArm_chartChristoffel_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k
  have hdig' : ∀ m a b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x)
      = -(∑ x' : Fin (Module.finrank ℝ E), ∑ y' : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a x' * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x y' b * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x' y') (extChartAt I x x)) :=
    fun m a b => lieArm_partial_chartInvGramOnE_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x m a b
  have hM := O1Abstract.o1_master
    (fun a b => chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b)
    (fun a b => DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b)
    (fun m a b => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x))
    (fun a b l => DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x))
    (fun m a b => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x))
    (fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x))
    (fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b k (extChartAt I x x))
    (fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x a b k (extChartAt I x x))
    (fun d a b => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x))
    (fun k => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k (extChartAt I x x))
    hcol' higs' hcgs' hf3s' hg1s' hg0s' hgbdef' hdgs' hga1' hdig' i j
  linear_combination hM

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lieArm_jointRS_add_local {r s : ℕ} {S : Set ℝ}
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lieArm_jointRS_const_smul_local {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
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
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem lieArm_hjoint_reindex (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) (σ' : Equiv.Perm (Fin r)) {δ δ' : ℝ}
    (hΦ : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r Φ (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => reindexCoeffGen (I := I) (M := M) g₀ r 2 (Φ s) σ') (δ := δ) (δ' := δ') := by
  classical
  rw [linearizedRicciThreeArmHjoint] at hΦ ⊢
  have htest : ∀ (Y : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel r ℝ E,
      fun x : M => Tensor0SBundle.Tensor0SSpace r I x⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
          ((reindexCoeffFibGen (I := I) r 2 σ' p.1
            (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I p.1 from
              (Φ p.2).toSection p.1)) (Y p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro Y
    have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr σ'
              (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
      refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
        (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
        (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr σ'
              (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
              Tensor0SBundle.Tensor0SSpace r I x))).mpr ?_
      have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
        (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
        (fun x => Y x)).mp Y.contMDiff
      intro τ x₀
      refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
      filter_upwards [Filter.univ_mem] with x _
      rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
      change (ContinuousMultilinearMap.domDomCongr σ'
          (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
          (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
            ((Module.finBasis ℝ E) (τ j))) = _
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      rfl
    have hYσJ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr σ'
              (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      (hYσ.comp contMDiff_fst).contMDiffOn
    have hRY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hΦ hYσJ
    refine hRY.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
    exact (reindexCoeffFibGen_apply (I := I) r 2 σ' p.1
      (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from (Φ p.2).toSection p.1) (Y p.1)).symm
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel r ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace r I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => reindexCoeffFibGen (I := I) r 2 σ' p.1
      (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from (Φ p.2).toSection p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ')) htest
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [reindexCoeffGen_toSection]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem lieArm_hjAbsorb (g₀ : SmoothRiemannianMetric I M) {δ δ' : ℝ}
    (r : ℕ) (Φ : ℝ → SmoothCcTensor g₀ (2 + r) 2) (σ' : Equiv.Perm (Fin (2 + r)))
    (hΦ : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ (2 + r) Φ (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ (2 + r)
      (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ r (Φ s) σ') (δ := δ) (δ' := δ') := by
  classical
  have hRein := lieArm_hjoint_reindex (I := I) g₀ (2 + r)
    Φ σ' (δ := δ) (δ' := δ') hΦ
  rw [linearizedRicciThreeArmHjoint] at hΦ hRein ⊢
  have hA := lieArm_jointRS_const_smul_local (I := I) (r := 2 + r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
    (fun p : M × ℝ => (Φ p.2).toSection p.1) hΦ
  have hB := lieArm_jointRS_const_smul_local (I := I) (r := 2 + r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
    (fun p : M × ℝ => (reindexCoeffGen (I := I) (M := M) g₀ (2 + r) 2 (Φ p.2) σ').toSection p.1)
    hRein
  have hAB := lieArm_jointRS_add_local (I := I) (r := 2 + r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hA hB
  refine hAB.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (2 + r) 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace (2 + r) 2 I z) p.1 t) ?_
  rw [symmAbsorbedCoeff, smoothCcTensor_toSection_add_apply,
    smoothCcTensor_toSection_smul_apply, smoothCcTensor_toSection_smul_apply]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckVFCovDeriv connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

theorem deTurckLieCoeffField_add_deTurckLieRemainderField_realizedFam_jointSmooth
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ δ' : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
        lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') := by
  have h1 := deTurckLieCoeffField_realizedFam_jointSmooth
    (I := I) g₀ T T' hδ hδ' g_bg
  have h2 := lieCorr0_path_joint (I := I) g₀ T T' hδ hδ' g_bg
  rw [linearizedRicciThreeArmHjoint] at h1 h2 ⊢
  have hadd := lieArm_jointRS_add_local (I := I) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ => (lieCorr0Field (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    h1 h2
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) p.1 t) ?_
  rw [smoothCcTensor_toSection_add_apply]


set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
lemma lieArm_chartSlope_center_value_eq_threeArm
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s
        (extChartAt I x x) =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  classical
  have hy : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hsplit := lieDeTurckChartSlope_eq_orderSplit (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg x i j s hy
  have h0 := lie0_order0_eq (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg s x i j
  have h1 := lieArm_arm1_value_eq_order1Raw_add_tail (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' s x i j
  have h2 := lieArm_arm2_value_eq_principal_add_tail (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j
  refine hsplit.trans ?_
  rw [unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  linear_combination -h0 - h1 - h2

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem realizedDeTurckLie_threeArm_symmAbsorbed_perm_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (σ'₀ : Equiv.Perm (Fin 2)) (σ'₁ : Equiv.Perm (Fin 3)) (σ'₂ : Equiv.Perm (Fin 4)),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 0
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
            + lieCorr0Field (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₀)
        (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 1
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁)
        (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂)
        (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
              deriv (fun s : ℝ =>
                DeTurckCoefficients.chartLieDeTurckComp (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2
                  (symmAbsorbedCoeff (I := I) (M := M) g₀ 0
                    (deTurckLieCoeffField (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                      + lieCorr0Field (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₀)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2
                  (symmAbsorbedCoeff (I := I) (M := M) g₀ 1
                    (deTurckLieArm1Coeff (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2
                  (symmAbsorbedCoeff (I := I) (M := M) g₀ 2
                    (deTurckLieArm2PrincipalCoeff (I := I) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨σ'₀, hσ'₀⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0
  obtain ⟨σ'₁, hσ'₁⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 1
  obtain ⟨σ'₂, hσ'₂⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 2
  refine ⟨σ'₀, σ'₁, σ'₂,
    lieArm_hjAbsorb (I := I) g₀ 0 _ σ'₀
      (deTurckLieCoeffField_add_deTurckLieRemainderField_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    lieArm_hjAbsorb (I := I) g₀ 1 _ σ'₁
      (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    lieArm_hjAbsorb (I := I) g₀ 2 _ σ'₂
      (deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    ?_⟩
  intro s hs x v
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
            (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro i j
    rw [deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i j hs]
    exact lieArm_chartSlope_center_value_eq_threeArm (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' s x i j
  set Wbase : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
      + operatorFieldApply (I := I) (M := M) g₀ 3 2
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
      + operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckLieArm2PrincipalCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) with hWbase
  have hexpand : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
        deriv (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
      unitModel (I := I) (M := M) g₀ 2 Wbase x v := by
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
  rw [hexpand]
  have habs0 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 (T - T')
    (deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
      + lieCorr0Field (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₀ hσ'₀ x v
  have habs1 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 1 (T - T')
    (deTurckLieArm1Coeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁ hσ'₁ x v
  have habs2 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 (T - T')
    (deTurckLieArm2PrincipalCoeff (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂ hσ'₂ x v
  rw [hWbase]
  rw [unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  rw [habs0, habs1, habs2]

theorem realizedDeTurckLie_threeArm_covariant_identity
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀L : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁L : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂L : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀L (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁L (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂L (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
              deriv (fun s : ℝ =>
                DeTurckCoefficients.chartLieDeTurckComp (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨_, _, _, hj0, hj1, hj2, hident⟩ :=
    realizedDeTurckLie_threeArm_symmAbsorbed_perm_data (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ'
  exact ⟨_, _, _, hj0, hj1, hj2, hident⟩

end

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
