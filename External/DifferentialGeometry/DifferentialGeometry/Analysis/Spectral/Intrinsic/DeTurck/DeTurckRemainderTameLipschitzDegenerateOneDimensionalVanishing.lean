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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma dim1_smul_rep (h1 : Module.finrank ℝ E = 1) (e : E) (he : e ≠ 0) (v : E) :
    ∃ c : ℝ, c • e = v :=
  exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := E) h1 he v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma dim1_domDomCongr_eq (h1 : Module.finrank ℝ E = 1) {d : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) (ρ : Equiv.Perm (Fin d)) :
    ContinuousMultilinearMap.domDomCongr ρ f = f := by
  classical
  have hpos : 0 < Module.finrank ℝ E := h1 ▸ Nat.one_pos
  set b := Module.finBasis ℝ E with hb
  set e : E := b ⟨0, hpos⟩ with he_def
  have he : e ≠ 0 := b.ne_zero _
  apply ContinuousMultilinearMap.ext
  intro v
  have hrep : ∀ i : Fin d, ∃ c : ℝ, c • e = v i := fun i => dim1_smul_rep h1 e he (v i)
  choose c hc using hrep
  have hv : v = fun i => c i • e := by
    funext i
    exact (hc i).symm
  rw [ContinuousMultilinearMap.domDomCongr_apply, hv]
  have hL : (f fun i => c (ρ i) • e) = (∏ i, c (ρ i)) • f (fun _ => e) :=
    f.map_smul_univ (fun i => c (ρ i)) (fun _ => e)
  have hR : (f fun i => c i • e) = (∏ i, c i) • f (fun _ => e) :=
    f.map_smul_univ c (fun _ => e)
  rw [hL, hR, Equiv.prod_comp ρ c]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dim1_slotPermCLM_eq (h1 : Module.finrank ℝ E = 1) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (x : M) (D : Tensor0SBundle.Tensor0SSpace d I x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x D = D := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply]
  rw [dim1_domDomCongr_eq h1 (Tensor0SBundle.Tensor0SSpace.toModel D) ρ]
  exact Tensor0SBundle.Tensor0SSpace.ofModel_toModel (𝕜 := ℝ) D

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricciCometricFourTraceCLM_eq_zero_of_finrank_eq_one (h1 : Module.finrank ℝ E = 1)
    (g₁ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
      (I := I) g₁ x = 0 := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM]
  have hF : ∀ ρ₁ ρ₂ ρ₃ : Equiv.Perm (Fin 4),
      (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₁ x)
        + (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₂ x)
        - DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x
        - (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₃ x)
        = 0 := by
    intro ρ₁ ρ₂ ρ₃
    apply ContinuousLinearMap.ext
    intro Z
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [dim1_slotPermCLM_eq (I := I) h1 ρ₁ x Z, dim1_slotPermCLM_eq (I := I) h1 ρ₂ x Z,
      dim1_slotPermCLM_eq (I := I) h1 ρ₃ x Z]
    rw [ContinuousLinearMap.zero_apply]
    abel
  rw [hF]
  rw [smul_zero]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma dim1_linearizedRicciConnDiffOrder0CoeffField_eq_zero
    (h1 : Module.finrank ℝ E = 1) (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
      (I := I) (M := M) g₀ g₁ = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField_toSection]
  change (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CometricTracedCLM
      (I := I) g₀ g₁ x) = _
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CometricTracedCLM]
  rw [ricciCometricFourTraceCLM_eq_zero_of_finrank_eq_one (I := I) h1 g₁ x]
  rw [ContinuousLinearMap.zero_comp]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma dim1_riemannOp_first_two_eq_zero (h1 : Module.finrank ℝ E = 1)
    (g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x)
    (hw : w ≠ 0) :
    DifferentialGeometry.Integral.Connection.riemannOp
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x v w u = 0 := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := TangentSpace I x)
    (show Module.finrank ℝ (TangentSpace I x) = 1 from h1) hw v
  have hself : DifferentialGeometry.Integral.Connection.riemannOp
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x w w u = 0 := by
    have hsw := DifferentialGeometry.Integral.Connection.riemannOp_swap
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x w w u
    have h2 : (2 : ℝ) • (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x w w u) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hsw]
      abel
    have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
    exact (smul_eq_zero.mp h2).resolve_left h2ne
  rw [← hc]
  rw [(DifferentialGeometry.Integral.Connection.riemannOp
    (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x).map_smul c w]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [hself, smul_zero]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma dim1_smoothOrthoFrame_ne_zero (g₁ : SmoothRiemannianMetric I M) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x a x ≠ 0 := by
  intro h0
  have horth := DifferentialGeometry.Integral.Connection.smoothOrthoFrame_orthonormal_at_center
    (I := I) g₁ x a a
  rw [if_pos rfl] at horth
  rw [h0] at horth
  rw [map_zero] at horth
  exact one_ne_zero horth.symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
lemma dim1_ricciArmOrder0RiemannCoeff_eq_zero (h1 : Module.finrank ℝ E = 1)
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
      (I := I) (M := M) g₀ g₁ = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff_toSection]
  change (Tensor0SBundle.TensorRSSpace.ofCLM
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib (I := I) g₁ x)) = _
  have hfib : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib
      (I := I) g₁ x = 0 := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib]
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ)
    apply ContinuousMultilinearMap.ext
    intro v
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_toModel]
    have hz : ∀ a b : Fin (Module.finrank ℝ E),
        (g₁.inner x) (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x (v 0)
            (DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x a x)
            (DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x b x))
          (v 1) *
          D.toModel ![DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x a x,
            DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x b x] = 0 := by
      intro a b
      rw [dim1_riemannOp_first_two_eq_zero (I := I) h1 g₁ x (v 0) _ _
        (dim1_smoothOrthoFrame_ne_zero (I := I) g₁ x a)]
      rw [map_zero, ContinuousLinearMap.zero_apply, zero_mul]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hz a b))]
    rw [Finset.sum_const, Finset.sum_const]
    simp only [smul_zero, mul_zero]
    have : (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        ((0 : Tensor0SBundle.TensorRSSpace 2 2 I x) D)) v = 0 := by
      change (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        ((0 : Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) D)) v = 0
      rw [ContinuousLinearMap.zero_apply]
      rw [show (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        (0 : Tensor0SBundle.Tensor0SSpace 2 I x)) = 0 from map_zero _]
      rfl
    rw [this]
  rw [hfib]
  rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
