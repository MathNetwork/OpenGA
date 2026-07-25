import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmDiffL2TameBallUniformYoungHolderPathIntegral
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

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem lieArm_threeArm_coeffFields_perOrder_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
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
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedDeTurckLieAt (I := I) g₀ g_bg T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
                  x (v 0) (v 1) s =
                unitModel (I := I) (M := M) g₀ 2
                  (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                    + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x) ≤ P 0 ∧
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x) ≤ P 0 ∧
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x) ≤ P 0) ∧
          (∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2 ≤ P i ∧
            ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2 ≤ P i ∧
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2 ≤ P i) :=
  by
    classical
    obtain ⟨P0jet, hP0jet_nn, hP0jet⟩ :=
      deTurckLieCoeffField_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
        ha_super hR hδ₀
    obtain ⟨PLjet, hPLjet_nn, hPLjet⟩ :=
      lieCorr0Field_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
        ha_super hR hδ₀
    obtain ⟨P1jet, hP1jet_nn, hP1jet⟩ :=
      deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
        ha_super hR hδ₀
    obtain ⟨P2jet, hP2jet_nn, hP2jet⟩ :=
      deTurckLieArm2PrincipalCoeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀
        g_bg a ha_super hR hδ₀
    obtain ⟨Λ0, hΛ0_nn, hΛ0⟩ :=
      deTurckLieCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
        ha_super hR hδ₀
    obtain ⟨ΛL, hΛL_nn, hΛL⟩ :=
      lieCorr0Field_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
        ha_super hR hδ₀
    obtain ⟨Λ1, hΛ1_nn, hΛ1⟩ :=
      deTurckLieArm1Coeff_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
        ha_super hR hδ₀
    obtain ⟨Λ2, hΛ2_nn, hΛ2⟩ :=
      deTurckLieArm2PrincipalCoeff_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀
        g_bg a ha_super hR hδ₀
    set C : ℝ := (2 * Λ0 + 2 * ΛL + Λ1 + Λ2) +
      ∑ k ∈ Finset.range (a + 1), (2 * (P0jet k + PLjet k) + P1jet k + P2jet k) with hC_def
    have hsum_nn : 0 ≤ ∑ k ∈ Finset.range (a + 1),
        (2 * (P0jet k + PLjet k) + P1jet k + P2jet k) := by
      refine Finset.sum_nonneg fun k _ => ?_
      have h1 := hP0jet_nn k
      have h2 := hPLjet_nn k
      have h3 := hP1jet_nn k
      have h4 := hP2jet_nn k
      linarith
    have hΛpart_nn : 0 ≤ 2 * Λ0 + 2 * ΛL + Λ1 + Λ2 := by linarith
    have hC_nn : 0 ≤ C := by
      rw [hC_def]
      linarith
    refine ⟨fun _ => C, fun i => hC_nn, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
    obtain ⟨σ'₀, σ'₁, σ'₂, hj0, hj1, hj2, hident⟩ :=
      realizedDeTurckLie_threeArm_symmAbsorbed_perm_data (I := I) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
    refine ⟨_, _, _, hj0, hj1, hj2, ?_, ?_, ?_⟩
    · intro s hs x v
      rw [linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ' x (v 0) (v 1) hs]
      rw [(hasDerivAt_realizedDeTurckLieChartSum_general (I := I) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ' x (v 0) (v 1) hs).deriv]
      exact hident s hs x v
    · intro s hs x
      refine ⟨?_, ?_, ?_⟩
      · refine le_trans (symmAbsorbedCoeff_riemannianFiberNormSq_le (I := I) (M := M) g₀ 0 _ σ'₀ x) ?_
        have hadd := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) x
        refine le_trans hadd ?_
        have h1 := hΛ0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
        have h2 := hΛL T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
        rw [hC_def]
        linarith
      · refine le_trans (symmAbsorbedCoeff_riemannianFiberNormSq_le (I := I) (M := M) g₀ 1 _ σ'₁ x) ?_
        have h1 := hΛ1 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
        rw [hC_def]
        linarith
      · refine le_trans (symmAbsorbedCoeff_riemannianFiberNormSq_le (I := I) (M := M) g₀ 2 _ σ'₂ x) ?_
        have h1 := hΛ2 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
        rw [hC_def]
        linarith
    · intro i hi s hs
      have hmem : i ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
      refine ⟨?_, ?_, ?_⟩
      · set R0 : SmoothCcTensor g₀ 2 2 :=
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
            + lieCorr0Field (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg with hR0_def
        have hsingle : ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (symmAbsorbedCoeff (I := I) (M := M) g₀ 0 R0 σ'₀)‖ ^ 2 ≤
            ∑ k ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 k
              (symmAbsorbedCoeff (I := I) (M := M) g₀ 0 R0 σ'₀)‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ‖iteratedCovGrad (I := I) g₀ 2 2 k
            (symmAbsorbedCoeff (I := I) (M := M) g₀ 0 R0 σ'₀)‖ ^ 2)
            (fun k _ => sq_nonneg _) hmem
        have hjet := symmAbsorbedCoeff_jet_le (I := I) (M := M) g₀ 0 (a + 1) R0 σ'₀
        have hterm : ∀ k ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 k R0‖ ^ 2 ≤
            2 * (P0jet k + PLjet k) + P1jet k + P2jet k := by
          intro k hk
          have hk_le : k ≤ a := by
            have := Finset.mem_range.mp hk
            omega
          have hsplit := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 k
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (lieCorr0Field (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          have hA := hP0jet T T' hδ_le hδ hδ'_le hδ' hTball hT'ball k hk_le s hs
          have hB := hPLjet T T' hδ_le hδ hδ'_le hδ' hTball hT'ball k hk_le s hs
          have h3 := hP1jet_nn k
          have h4 := hP2jet_nn k
          rw [hR0_def]
          linarith
        calc ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (symmAbsorbedCoeff (I := I) (M := M) g₀ 0 R0 σ'₀)‖ ^ 2
            ≤ ∑ k ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 k
                (symmAbsorbedCoeff (I := I) (M := M) g₀ 0 R0 σ'₀)‖ ^ 2 := hsingle
          _ ≤ ∑ k ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ 2 2 k R0‖ ^ 2 := hjet
          _ ≤ ∑ k ∈ Finset.range (a + 1),
                (2 * (P0jet k + PLjet k) + P1jet k + P2jet k) :=
              Finset.sum_le_sum hterm
          _ ≤ C := by
              rw [hC_def]
              linarith
      · set R1 : SmoothCcTensor g₀ 3 2 :=
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg with hR1_def
        have hsingle : ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (symmAbsorbedCoeff (I := I) (M := M) g₀ 1 R1 σ'₁)‖ ^ 2 ≤
            ∑ k ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 k
              (symmAbsorbedCoeff (I := I) (M := M) g₀ 1 R1 σ'₁)‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ‖iteratedCovGrad (I := I) g₀ 3 2 k
            (symmAbsorbedCoeff (I := I) (M := M) g₀ 1 R1 σ'₁)‖ ^ 2)
            (fun k _ => sq_nonneg _) hmem
        have hjet := symmAbsorbedCoeff_jet_le (I := I) (M := M) g₀ 1 (a + 1) R1 σ'₁
        have hterm : ∀ k ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 2 k R1‖ ^ 2 ≤
            2 * (P0jet k + PLjet k) + P1jet k + P2jet k := by
          intro k hk
          have hk_le : k ≤ a := by
            have := Finset.mem_range.mp hk
            omega
          have hA := hP1jet T T' hδ_le hδ hδ'_le hδ' hTball hT'ball k hk_le s hs
          have h1 := hP0jet_nn k
          have h2 := hPLjet_nn k
          have h4 := hP2jet_nn k
          rw [hR1_def]
          linarith
        calc ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (symmAbsorbedCoeff (I := I) (M := M) g₀ 1 R1 σ'₁)‖ ^ 2
            ≤ ∑ k ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 k
                (symmAbsorbedCoeff (I := I) (M := M) g₀ 1 R1 σ'₁)‖ ^ 2 := hsingle
          _ ≤ ∑ k ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ 3 2 k R1‖ ^ 2 := hjet
          _ ≤ ∑ k ∈ Finset.range (a + 1),
                (2 * (P0jet k + PLjet k) + P1jet k + P2jet k) :=
              Finset.sum_le_sum hterm
          _ ≤ C := by
              rw [hC_def]
              linarith
      · set R2 : SmoothCcTensor g₀ 4 2 :=
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg with hR2_def
        have hsingle : ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (symmAbsorbedCoeff (I := I) (M := M) g₀ 2 R2 σ'₂)‖ ^ 2 ≤
            ∑ k ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 k
              (symmAbsorbedCoeff (I := I) (M := M) g₀ 2 R2 σ'₂)‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ‖iteratedCovGrad (I := I) g₀ 4 2 k
            (symmAbsorbedCoeff (I := I) (M := M) g₀ 2 R2 σ'₂)‖ ^ 2)
            (fun k _ => sq_nonneg _) hmem
        have hjet := symmAbsorbedCoeff_jet_le (I := I) (M := M) g₀ 2 (a + 1) R2 σ'₂
        have hterm : ∀ k ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 k R2‖ ^ 2 ≤
            2 * (P0jet k + PLjet k) + P1jet k + P2jet k := by
          intro k hk
          have hk_le : k ≤ a := by
            have := Finset.mem_range.mp hk
            omega
          have hA := hP2jet T T' hδ_le hδ hδ'_le hδ' hTball hT'ball k hk_le s hs
          have h1 := hP0jet_nn k
          have h2 := hPLjet_nn k
          have h3 := hP1jet_nn k
          rw [hR2_def]
          linarith
        calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (symmAbsorbedCoeff (I := I) (M := M) g₀ 2 R2 σ'₂)‖ ^ 2
            ≤ ∑ k ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 k
                (symmAbsorbedCoeff (I := I) (M := M) g₀ 2 R2 σ'₂)‖ ^ 2 := hsingle
          _ ≤ ∑ k ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 k R2‖ ^ 2 := hjet
          _ ≤ ∑ k ∈ Finset.range (a + 1),
                (2 * (P0jet k + PLjet k) + P1jet k + P2jet k) :=
              Finset.sum_le_sum hterm
          _ ≤ C := by
              rw [hC_def]
              linarith

private theorem lieArm_threeArm_coeffFields_C0_engine_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL B : ℝ, 0 ≤ ΛL ∧ 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
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
          (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
            ∀ (x : M) (v : Fin 2 → TangentSpace I x),
              linearizedDeTurckLieAt (I := I) g₀ g_bg T T'
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
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) := by
  classical
  obtain ⟨P, hP_nn, hData⟩ :=
    lieArm_threeArm_coeffFields_perOrder_data (I := I) g₀ g_bg a ha_super hR hδ₀
  set Psum : ℝ := ∑ i ∈ Finset.range (a + 1), P i with hPsum_def
  have hPsum_nn : 0 ≤ Psum := Finset.sum_nonneg (fun i _ => hP_nn i)
  refine ⟨Real.sqrt (P 0), Real.sqrt Psum, Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hid, hPt0, hL2⟩ :=
    hData T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  have hB_sq : Real.sqrt Psum ^ 2 = Psum := Real.sq_sqrt hPsum_nn
  have hkey : ∀ (r : ℕ) (Φ : ℝ → SmoothCcTensor g₀ r 2) (s : ℝ),
      (∀ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2 ≤ P i) →
      (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2) ≤ Real.sqrt Psum ^ 2 := by
    intro r Φ s hbound
    rw [hB_sq, hPsum_def]
    exact Finset.sum_le_sum hbound
  refine ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun s hs x => Real.sqrt_le_sqrt (hPt0 s hs x).1
  · exact fun s hs x => Real.sqrt_le_sqrt (hPt0 s hs x).2.1
  · exact fun s hs x => Real.sqrt_le_sqrt (hPt0 s hs x).2.2
  · intro s hs
    exact hkey 2 Φ₀ s (fun i hi =>
      (hL2 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).1)
  · intro s hs
    exact hkey 3 Φ₁ s (fun i hi =>
      (hL2 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).2.1)
  · intro s hs
    exact hkey 4 Φ₂ s (fun i hi =>
      (hL2 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs).2.2)

private theorem lieArm_threeArm_coeffFields_C0_engine
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL B : ℝ, 0 ≤ ΛL ∧ 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
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
              linearizedDeTurckLieAt (I := I) g₀ g_bg T T'
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
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) := by
  obtain ⟨ΛL, B, hΛL_nn, hB_nn, hdata⟩ :=
    lieArm_threeArm_coeffFields_C0_engine_data (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛL, B, hΛL_nn, hB_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hid, hc0, hc1, hc2, hb0, hb1, hb2⟩ :=
    hdata T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  refine ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, ?_, ?_, ?_, hid, hc0, hc1, hc2, hb0, hb1, hb2⟩
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hj0
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hj1
  · exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hj2

private theorem exists_lieArm_threeArm_coeffFields_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL B : ℝ, 0 ≤ ΛL ∧ 0 ≤ B ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
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
              linearizedDeTurckLieAt (I := I) g₀ g_bg T T'
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
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Φ₀ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Φ₁ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Φ₂ s).toSection x)) ≤ ΛL) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Φ₀ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Φ₁ s)‖ ^ 2) ≤ B ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ₂ s)‖ ^ 2) ≤ B ^ 2) :=
  lieArm_threeArm_coeffFields_C0_engine (I := I) g₀ g_bg a ha_super hR hδ₀

private theorem exists_lieArmCoeff_ballUniform_C0_sup
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL : ℝ, 0 ≤ ΛL ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
                lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ ΛL ^ 2) := by
  classical
  obtain ⟨ΛL, B, hΛL_nn, hB_nn, hbrick⟩ :=
    exists_lieArm_threeArm_coeffFields_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛL, hΛL_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hc0, hc1, hc2, hid, hb0, hb1, hb2, _, _, _⟩ :=
    hbrick T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
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
  refine ⟨P₀, P₁, P₂, ?_, ?_, ?_, ?_⟩
  · intro x v
    set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
    set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
    set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
    have hLie :=
      lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)
    rw [hLie]
    have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
        linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
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
      have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
      exact hsneq (by rw [hid s hsIoo x v, unitModel_add2_apply_tame, unitModel_add2_apply_tame])
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
  · intro x
    rw [hP₀]
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 x ΛL hΛL_nn
      ((hc0 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
      (fun t ht => hb0 t ht x)
  · intro x
    rw [hP₁]
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 x ΛL hΛL_nn
      ((hc1 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
      (fun t ht => hb1 t ht x)
  · intro x
    rw [hP₂]
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 x ΛL hΛL_nn
      ((hc2 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
      (fun t ht => hb2 t ht x)

private theorem deTurckLieArm_appCc_graded_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL : ℝ, 0 ≤ ΛL ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
                lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ ΛL ^ 2) := by
  classical
  obtain ⟨ΛL, hΛL_nn, hsup⟩ :=
    exists_lieArmCoeff_ballUniform_C0_sup (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛL, hΛL_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨L₀, L₁, L₂, hval, hL₀, hL₁, hL₂⟩ :=
    hsup T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  exact ⟨L₀, L₁, L₂, hval, hL₀, hL₁, hL₂⟩

private theorem deTurckRHSArmDiff_threeArm_unitModel_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC : ℝ, 0 ≤ ΛC ∧
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
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            unitModel (I := I) (M := M) g₀ 2
                (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                  deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x v =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) := by
  classical

  obtain ⟨ΛR, hΛR_nn, hRicci⟩ :=
    deTurckRicciArm_appCc_graded_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛL, hΛL_nn, hLie⟩ :=
    deTurckLieArm_appCc_graded_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀

  refine ⟨Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨R₀, R₁, R₂, hRval, hR₀, hR₁, hR₂⟩ :=
    hRicci T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨L₀, L₁, L₂, hLval, hL₀, hL₁, hL₂⟩ :=
    hLie T T' hδ_le hδ hδ'_le hδ' hTball hT'ball

  refine ⟨R₀ + L₀, R₁ + L₁, R₂ + L₂, ?_, ?_, ?_, ?_⟩
  · intro x v
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
    set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'

    rw [unitModel_sub_local (I := I) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply]
    rw [show (unitModel (I := I) (M := M) g₀ 2 (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) x) v =
          deTurckRicciRHS (I := I) g_bg g₁ x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T hδ_lt hδ
        (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x v]
    rw [show (unitModel (I := I) (M := M) g₀ 2 (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') x) v =
          deTurckRicciRHS (I := I) g_bg g₁' x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' hδ'_lt hδ'
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') rfl x v]

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

    rw [hRval x v, hLval x v]

    set Rblk : SmoothCcTensor g₀ 0 2 :=
      operatorFieldApply (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hRblk
    set Lblk : SmoothCcTensor g₀ 0 2 :=
      operatorFieldApply (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hLblk
    have hcoeffSum :
        operatorFieldApply (I := I) (M := M) g₀ 2 2 (R₀ + L₀) (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 3 2 (R₁ + L₁) (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 4 2 (R₂ + L₂) (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) =
        Rblk + Lblk := by
      rw [appCc_add_left (I := I) (M := M) g₀ 2 2 R₀ L₀,
        appCc_add_left (I := I) (M := M) g₀ 3 2 R₁ L₁,
        appCc_add_left (I := I) (M := M) g₀ 4 2 R₂ L₂, hRblk, hLblk]
      abel
    rw [hcoeffSum, unitModel_add_local (I := I) g₀ 2 Rblk Lblk x,
      ContinuousMultilinearMap.add_apply]
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₀ L₀ ΛR ΛL x (hR₀ x) (hL₀ x)
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₁ L₁ ΛR ΛL x (hR₁ x) (hL₁ x)
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₂ L₂ ΛR ΛL x (hR₂ x) (hL₂ x)

private theorem deTurckRHSArmDiff_threeArm_coeffC0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC : ℝ, 0 ≤ ΛC ∧
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
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) := by
  classical

  obtain ⟨ΛC, hΛC_nn, hgrade⟩ :=
    deTurckRHSArmDiff_threeArm_unitModel_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛC, hΛC_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨C₀, C₁, C₂, hval, hC₀, hC₁, hC₂⟩ :=
    hgrade T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  refine ⟨C₀, C₁, C₂, ?_, hC₀, hC₁, hC₂⟩

  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  exact hval x v

set_option maxHeartbeats 800000 in

private theorem deTurckRHSArmDiff_order0_riemannianFiberNormSq_intrinsic_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λa : ℝ, 0 ≤ Λa ∧
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
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                  deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x) ≤
            Λa ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
  classical

  obtain ⟨ΛC, hΛC_nn, hcore⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀

  obtain ⟨Cemb, hCemb_nn, hemb⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le (I := I) g₀ a ha_super
  refine ⟨Real.sqrt (4 * 3) * (ΛC * Cemb), by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨C₀, C₁, C₂, hid, hC₀, hC₁, hC₂⟩ :=
    hcore T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _

  set A₀ := operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂

  set f : ℕ → ℝ := fun m =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) with hf_def
  have hf_nn : ∀ m, 0 ≤ f m := fun m =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _

  have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x) ≤ ΛC ^ 2 * f 0 := by
    rw [hA₀, appCc_toSection (I := I) (M := M) g₀ 2 2 C₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 2 2 x
      (C₀.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₀ x) (hf_nn 0)
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x) ≤ ΛC ^ 2 * f 1 := by
    rw [hA₁, appCc_toSection (I := I) (M := M) g₀ 3 2 C₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 3 2 x
      (C₁.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₁ x) (hf_nn 1)
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x) ≤ ΛC ^ 2 * f 2 := by
    rw [hA₂, appCc_toSection (I := I) (M := M) g₀ 4 2 C₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 4 2 x
      (C₂.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₂ x) (hf_nn 2)

  have hsub : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((A₀ + A₁ + A₂).toSection x) ≤
      4 * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)) := by
    simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    have hadd1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 2 x
      (A₀.toSection x + A₁.toSection x) (A₂.toSection x)
    have hadd2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 2 x
      (A₀.toSection x) (A₁.toSection x)
    have h2nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)
    nlinarith [hadd1, hadd2, h2nn]

  have hcol : f 0 + f 1 + f 2 ≤ Cemb ^ 2 * S := by
    have hemb' := hemb (T - T') x
    have hsum3 : (∑ q ∈ Finset.range 3,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x)) = f 0 + f 1 + f 2 := by
      simp only [hf_def, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hS_def]
    rw [hsum3] at hemb'
    exact hemb'

  have hΛsq : (Real.sqrt (4 * 3) * (ΛC * Cemb)) ^ 2 = (4 * 3) * (ΛC ^ 2 * Cemb ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 * 3)]; ring
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ').toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((A₀ + A₁ + A₂).toSection x) := by
        rw [hid]
    _ ≤ 4 * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x)
          + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x)
          + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)) := hsub
    _ ≤ 4 * (ΛC ^ 2 * f 0 + ΛC ^ 2 * f 1 + ΛC ^ 2 * f 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add h0 h1) h2) (by norm_num)
    _ = (4 * ΛC ^ 2) * (f 0 + f 1 + f 2) := by ring
    _ ≤ (4 * ΛC ^ 2) * (Cemb ^ 2 * S) := by
        refine mul_le_mul_of_nonneg_left hcol (by positivity)
    _ ≤ (Real.sqrt (4 * 3) * (ΛC * Cemb)) ^ 2 * S := by
        rw [hΛsq]
        have : (4 * ΛC ^ 2) * (Cemb ^ 2 * S) ≤ ((4 * 3) * (ΛC ^ 2 * Cemb ^ 2)) * S := by
          nlinarith [hS_nn, sq_nonneg ΛC, sq_nonneg Cemb,
            mul_nonneg (sq_nonneg ΛC) (sq_nonneg Cemb)]
        linarith [this]

set_option maxHeartbeats 1000000 in
private theorem deTurckRicciArm_appCc_graded_jetL2_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR ΓR : ℝ, 0 ≤ ΛR ∧ 0 ≤ ΓR ∧
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
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ ΛR ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i R₀‖ ^ 2) ≤ ΓR ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i R₁‖ ^ 2) ≤ ΓR ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i R₂‖ ^ 2) ≤ ΓR ^ 2 := by
  classical
  obtain ⟨ΛR, B, hΛR_nn, hB_nn, hbrick⟩ :=
    exists_ricciArm_threeArm_coeffFields_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨2 * ΛR, 2 * B, by positivity, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hc0, hc1, hc2, hid, hb0, hb1, hb2, hjet0, hjet1, hjet2⟩ :=
    hbrick T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
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
  refine ⟨(-2 : ℝ) • P₀, (-2 : ℝ) • P₁, (-2 : ℝ) • P₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x v
    set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
    set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
    set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
    have hRic :=
      ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)
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
      unitModel_appCc_smul_left_apply_tame]
    rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame] at hPidentity
    rw [smul_sub, smul_eq_mul, smul_eq_mul]
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
  · have htower : (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i P₀‖ ^ 2) ≤ B ^ 2 := by
      rw [hP₀]
      exact pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 2 a Φ₀ hSI hSopen hj0 hB_nn hjet0
    have hscale : (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i ((-2 : ℝ) • P₀)‖ ^ 2) =
        4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i P₀‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [iteratedCovGrad_smul', norm_smul]
      rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
      ring
    rw [hscale]
    nlinarith [htower, sq_nonneg B, hB_nn]
  · have htower : (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 2 i P₁‖ ^ 2) ≤ B ^ 2 := by
      rw [hP₁]
      exact pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 3 a Φ₁ hSI hSopen hj1 hB_nn hjet1
    have hscale : (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 2 i ((-2 : ℝ) • P₁)‖ ^ 2) =
        4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i P₁‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [iteratedCovGrad_smul', norm_smul]
      rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
      ring
    rw [hscale]
    nlinarith [htower, sq_nonneg B, hB_nn]
  · have htower : (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 i P₂‖ ^ 2) ≤ B ^ 2 := by
      rw [hP₂]
      exact pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 4 a Φ₂ hSI hSopen hj2 hB_nn hjet2
    have hscale : (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 i ((-2 : ℝ) • P₂)‖ ^ 2) =
        4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i P₂‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [iteratedCovGrad_smul', norm_smul]
      rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
      ring
    rw [hscale]
    nlinarith [htower, sq_nonneg B, hB_nn]

set_option maxHeartbeats 1000000 in
private theorem deTurckLieArm_appCc_graded_jetL2_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL ΓL : ℝ, 0 ≤ ΛL ∧ 0 ≤ ΓL ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
                lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ ΛL ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i L₀‖ ^ 2) ≤ ΓL ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i L₁‖ ^ 2) ≤ ΓL ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i L₂‖ ^ 2) ≤ ΓL ^ 2 := by
  classical
  obtain ⟨ΛL, B, hΛL_nn, hB_nn, hbrick⟩ :=
    exists_lieArm_threeArm_coeffFields_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛL, B, hΛL_nn, hB_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hc0, hc1, hc2, hid, hb0, hb1, hb2, hjet0, hjet1, hjet2⟩ :=
    hbrick T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
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
  refine ⟨P₀, P₁, P₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x v
    set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
    set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
    set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
    have hLie :=
      lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)
    rw [hLie]
    have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
        linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
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
      have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
      exact hsneq (by rw [hid s hsIoo x v, unitModel_add2_apply_tame, unitModel_add2_apply_tame])
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
  · intro x
    rw [hP₀]
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 x ΛL hΛL_nn
      ((hc0 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
      (fun t ht => hb0 t ht x)
  · intro x
    rw [hP₁]
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 x ΛL hΛL_nn
      ((hc1 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
      (fun t ht => hb1 t ht x)
  · intro x
    rw [hP₂]
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 x ΛL hΛL_nn
      ((hc2 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt))
      (fun t ht => hb2 t ht x)
  · rw [hP₀]
    exact pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 2 a Φ₀ hSI hSopen hj0 hB_nn hjet0
  · rw [hP₁]
    exact pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 3 a Φ₁ hSI hSopen hj1 hB_nn hjet1
  · rw [hP₂]
    exact pathIntegralCoeffField_jetL2_tower_le (I := I) g₀ 4 a Φ₂ hSI hSopen hj2 hB_nn hjet2

set_option maxHeartbeats 1000000 in
private theorem deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform
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
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨ΛR, ΓR, hΛR_nn, hΓR_nn, hRicci⟩ :=
    deTurckRicciArm_appCc_graded_jetL2_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛL, ΓL, hΛL_nn, hΓL_nn, hLie⟩ :=
    deTurckLieArm_appCc_graded_jetL2_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2), Real.sqrt (2 * ΓR ^ 2 + 2 * ΓL ^ 2),
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨R₀, R₁, R₂, hRval, hR₀, hR₁, hR₂, hR₀jet, hR₁jet, hR₂jet⟩ :=
    hRicci T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨L₀, L₁, L₂, hLval, hL₀, hL₁, hL₂, hL₀jet, hL₁jet, hL₂jet⟩ :=
    hLie T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  have hΓtower : ∀ {r s : ℕ} (A B : SmoothCcTensor g₀ r s) (ΓA ΓB : ℝ),
      (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2) ≤ ΓA ^ 2 →
      (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2) ≤ ΓB ^ 2 →
      (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ r s i (A + B)‖ ^ 2) ≤
        Real.sqrt (2 * ΓA ^ 2 + 2 * ΓB ^ 2) ^ 2 := by
    intro r s A B ΓA ΓB hA hB
    have hsq : Real.sqrt (2 * ΓA ^ 2 + 2 * ΓB ^ 2) ^ 2 = 2 * ΓA ^ 2 + 2 * ΓB ^ 2 :=
      Real.sq_sqrt (by positivity)
    rw [hsq]
    refine (jetTowerSum_add_le (I := I) g₀ r s (a + 1) A B).trans ?_
    have hAnn : 0 ≤ ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hBnn : 0 ≤ ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [hA, hB, hAnn, hBnn]
  refine ⟨R₀ + L₀, R₁ + L₁, R₂ + L₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
    set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'
    rw [unitModel_sub_local (I := I) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply]
    rw [show (unitModel (I := I) (M := M) g₀ 2 (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) x) v =
          deTurckRicciRHS (I := I) g_bg g₁ x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T hδ_lt hδ
        (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x v]
    rw [show (unitModel (I := I) (M := M) g₀ 2 (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') x) v =
          deTurckRicciRHS (I := I) g_bg g₁' x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' hδ'_lt hδ'
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') rfl x v]
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
    rw [hRval x v, hLval x v]
    set Rblk : SmoothCcTensor g₀ 0 2 :=
      operatorFieldApply (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hRblk
    set Lblk : SmoothCcTensor g₀ 0 2 :=
      operatorFieldApply (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        operatorFieldApply (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hLblk
    have hcoeffSum :
        operatorFieldApply (I := I) (M := M) g₀ 2 2 (R₀ + L₀) (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 3 2 (R₁ + L₁) (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          operatorFieldApply (I := I) (M := M) g₀ 4 2 (R₂ + L₂) (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) =
        Rblk + Lblk := by
      rw [appCc_add_left (I := I) (M := M) g₀ 2 2 R₀ L₀,
        appCc_add_left (I := I) (M := M) g₀ 3 2 R₁ L₁,
        appCc_add_left (I := I) (M := M) g₀ 4 2 R₂ L₂, hRblk, hLblk]
      abel
    rw [hcoeffSum, unitModel_add_local (I := I) g₀ 2 Rblk Lblk x,
      ContinuousMultilinearMap.add_apply]
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₀ L₀ ΛR ΛL x (hR₀ x) (hL₀ x)
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₁ L₁ ΛR ΛL x (hR₁ x) (hL₁ x)
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₂ L₂ ΛR ΛL x (hR₂ x) (hL₂ x)
  · exact hΓtower R₀ L₀ ΓR ΓL hR₀jet hL₀jet
  · exact hΓtower R₁ L₁ ΓR ΓL hR₁jet hL₁jet
  · exact hΓtower R₂ L₂ ΓR ΓL hR₂jet hL₂jet

private theorem deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λc : ℝ, 0 ≤ Λc ∧
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
        ‖iteratedCovGrad (I := I) g₀ 0 2 a
            (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
          Λc * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical

  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀

  obtain ⟨K₀, hK₀_nn, hK₀⟩ := ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 2 2 a
  obtain ⟨K₁, hK₁_nn, hK₁⟩ := ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 3 2 a
  obtain ⟨K₂, hK₂_nn, hK₂⟩ := ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 4 2 a

  obtain ⟨Cemb, hCemb_nn, hemb⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le (I := I) g₀ a ha_super

  set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
  have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
  have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.sqrt (9 * (Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2))), Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _

  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hcoeff T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball

  have hWsup : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
        (Real.sqrt (Cemb ^ 2 * S)) ^ 2 := by
    intro m hm x
    rw [Real.sq_sqrt (by positivity)]
    have hembx := hemb (T - T') x
    rw [hS_def]
    have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    refine le_trans (Finset.single_le_sum
      (f := fun q => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x))
      (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _) hmem) ?_
    exact hembx

  have hWjet : ∀ (m : ℕ), m ≤ 2 →
      (∑ l ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S := by
    intro m hm

    have hcomp : ∀ l : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 := by
      intro l
      have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
          (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))
      have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T'))
      rw [hbridgeL, hbridgeR]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      have hrw := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l (T - T') x

      simpa only [Nat.add_assoc] using hrw

    rw [show (∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) =
        ∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 from
      Finset.sum_congr rfl (fun l _ => hcomp l)]
    rw [hS_def]

    set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hf_def
    have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
    have himg : (Finset.range (a + 1)).image (fun l => m + l) ⊆ Finset.range (a + 2 + 1) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨l, hl, rfl⟩ := hi
      rw [Finset.mem_range] at hl ⊢
      omega
    have hinj : ∀ l₁ ∈ Finset.range (a + 1), ∀ l₂ ∈ Finset.range (a + 1),
        m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
    calc (∑ l ∈ Finset.range (a + 1), f (m + l))
        = ∑ i ∈ (Finset.range (a + 1)).image (fun l => m + l), f i :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ i ∈ Finset.range (a + 2 + 1), f i :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)

  have harm : ∀ (m : ℕ) (hm : m ≤ 2) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
      (hKm_le : Km ≤ Kmax)
      (hKm : ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 a (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          Km * (ΛW ^ 2 * ∑ i ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2))
      (hCmsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
      (hCmjet : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 a
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤
        Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) * S := by
    intro m hm Cm Km hKm_le hKm hCmsup hCmjet
    have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
      ΛC (Real.sqrt (Cemb ^ 2 * S)) hΛC_nn (Real.sqrt_nonneg _) hCmsup (hWsup m hm)
    refine htame.trans ?_

    have hcoeffjet := hCmjet
    have hwjet := hWjet m hm
    have hΛWsq : (Real.sqrt (Cemb ^ 2 * S)) ^ 2 = Cemb ^ 2 * S := Real.sq_sqrt (by positivity)
    rw [hΛWsq]

    have hcjsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hwjsum_nn : 0 ≤ ∑ l ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 :=
      Finset.sum_nonneg fun l _ => sq_nonneg _
    have ha1 : (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb ^ 2 * S) * Γ ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeffjet (by positivity)
    have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S :=
      mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
    have hinner :
        (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
          + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
        ≤ Cemb ^ 2 * Γ ^ 2 * S + ΛC ^ 2 * S := by nlinarith [ha1, ha2]
    have hinner_nn : 0 ≤ (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
          + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by
      have : 0 ≤ (Cemb ^ 2 * S) := by positivity
      have : 0 ≤ ΛC ^ 2 := sq_nonneg _
      positivity
    calc Km * ((Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
        ≤ Kmax * (Cemb ^ 2 * Γ ^ 2 * S + ΛC ^ 2 * S) :=
          mul_le_mul hKm_le hinner hinner_nn hKmax_nn
      _ = Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) * S := by ring

  have ha0 := harm 0 (by norm_num) C₀ K₀ hK₀_le hK₀ hC₀sup hC₀jet
  have ha1 := harm 1 (by norm_num) C₁ K₁ hK₁_le hK₁ hC₁sup hC₁jet
  have ha2 := harm 2 (by norm_num) C₂ K₂ hK₂_le hK₂ hC₂sup hC₂jet

  set A₀ := operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  have hN_split : deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' = A₀ + A₁ + A₂ := by
    rw [hA₀, hA₁, hA₂]; exact hid
  set base : ℝ := Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) with hbase_def
  have hbase_nn : 0 ≤ base := by rw [hbase_def]; positivity

  have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha0)
  have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha1)
  have hnorm2 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha2)

  rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 a (A₀ + A₁) A₂,
    iteratedCovGrad_add (I := I) g₀ 0 2 a A₀ A₁]
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀ +
        iteratedCovGrad (I := I) g₀ 0 2 a A₁ +
        iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ≤
      Real.sqrt (base * S) + Real.sqrt (base * S) + Real.sqrt (base * S) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) hnorm2
  refine htri.trans ?_

  rw [show Real.sqrt (base * S) = Real.sqrt base * Real.sqrt S from Real.sqrt_mul hbase_nn S]
  rw [show Real.sqrt (9 * base) = Real.sqrt 9 * Real.sqrt base from Real.sqrt_mul (by norm_num) base]
  rw [show Real.sqrt (9 : ℝ) = 3 from by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact le_of_eq (by ring)

private theorem deTurckRHSArmDiff_endpoints_l2_tame_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧
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
        (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                    deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x) ≤
              Λ₀ ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
          ‖deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
            Λ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 a
              (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            Λ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical

  obtain ⟨Λa, hΛa_nn, hΛa⟩ :=
    deTurckRHSArmDiff_order0_riemannianFiberNormSq_intrinsic_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λc, hΛc_nn, hΛc⟩ :=
    deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀

  haveI : MeasureTheory.IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g₀
  set vol : ℝ := (riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ with hvol_def
  have hvol_nn : 0 ≤ vol := by rw [hvol_def]; exact MeasureTheory.measureReal_nonneg

  refine ⟨Λa * Real.sqrt (vol + 1) + Λc,
    by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set N : SmoothCcTensor g₀ 0 2 :=
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  set Λ₀ : ℝ := Λa * Real.sqrt (vol + 1) + Λc with hΛ₀_def
  have hΛ₀_nn : 0 ≤ Λ₀ := by rw [hΛ₀_def]; positivity

  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (vol + 1) :=
    Real.one_le_sqrt.mpr (by linarith)
  have hΛa_le : Λa ≤ Λ₀ := by
    rw [hΛ₀_def]
    have h1 : Λa ≤ Λa * Real.sqrt (vol + 1) := by
      nlinarith [hΛa_nn, hsqrt_ge_one]
    linarith [hΛc_nn]
  have hΛc_le : Λc ≤ Λ₀ := by rw [hΛ₀_def]; nlinarith [hΛa_nn, hsqrt_ge_one]

  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λa ^ 2 * S := by
    intro x
    rw [hN_def, hS_def]
    exact hΛa T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball x
  have hC0 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λ₀ ^ 2 * S := by
    intro x
    refine (hpt x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hS_nn
    exact pow_le_pow_left₀ hΛa_nn hΛa_le 2

  have hL0 : ‖N‖ ≤ Λ₀ * Real.sqrt S := by

    have hnormsq : ‖N‖ ^ 2 ≤ vol * (Λa ^ 2 * S) := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 2 N]
      have hint_le :
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            ∫ _x, Λa ^ 2 * S ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const _) ?_
        · exact MeasureTheory.ae_of_all _ fun x =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
        · exact MeasureTheory.ae_of_all _ fun x => hpt x
      rw [MeasureTheory.integral_const, smul_eq_mul, ← hvol_def] at hint_le
      exact hint_le

    have hnorm_nn : 0 ≤ ‖N‖ := norm_nonneg _
    have hrhs_nn : 0 ≤ vol * (Λa ^ 2 * S) := by positivity
    have hsqrt_le : ‖N‖ ≤ Real.sqrt (vol * (Λa ^ 2 * S)) := by
      rw [show ‖N‖ = Real.sqrt (‖N‖ ^ 2) from (Real.sqrt_sq hnorm_nn).symm]
      exact Real.sqrt_le_sqrt hnormsq
    refine hsqrt_le.trans ?_

    have hfac : Real.sqrt (vol * (Λa ^ 2 * S)) = Λa * (Real.sqrt vol * Real.sqrt S) := by
      rw [show vol * (Λa ^ 2 * S) = Λa ^ 2 * (vol * S) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛa_nn,
        Real.sqrt_mul hvol_nn]
    rw [hfac, hΛ₀_def, add_mul]
    have hvol_le : Real.sqrt vol ≤ Real.sqrt (vol + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    calc Λa * (Real.sqrt vol * Real.sqrt S)
        = (Λa * Real.sqrt vol) * Real.sqrt S := by ring
      _ ≤ (Λa * Real.sqrt (vol + 1)) * Real.sqrt S := by
          refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
          exact mul_le_mul_of_nonneg_left hvol_le hΛa_nn
      _ ≤ Λa * Real.sqrt (vol + 1) * Real.sqrt S + Λc * Real.sqrt S := by
          have : 0 ≤ Λc * Real.sqrt S := mul_nonneg hΛc_nn hsqrtS_nn
          linarith

  have hLa : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λ₀ * Real.sqrt S := by
    have hbase : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λc * Real.sqrt S := by
      rw [hN_def, hS_def]
      exact hΛc T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
    refine hbase.trans ?_
    exact mul_le_mul_of_nonneg_right hΛc_le hsqrtS_nn
  exact ⟨hC0, hL0, hLa⟩

private theorem deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical

  obtain ⟨Λ₀, hΛ₀_nn, hEndS⟩ :=
    deTurckRHSArmDiff_endpoints_l2_tame_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀

  have hEnd : ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
      (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
      (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                  deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x) ≤
            Λ₀ ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
        ‖deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
            deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
          Λ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
        ‖iteratedCovGrad (I := I) g₀ 0 2 a
            (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
          Λ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
    have hδS : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T)) δ :=
      gFibreOpBound_ccTensorBilinSymm_symmS (I := I) g₀ T hδ
    have hδ'S : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T')) δ' :=
      gFibreOpBound_ccTensorBilinSymm_symmS (I := I) g₀ T' hδ'
    have hTballS : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) g₀ T)‖ ≤ R := fun j hj =>
      (tensorL2Norm_iteratedCovGrad_symmS_le (I := I) g₀ T j).trans (hTball j hj)
    have hT'ballS : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) g₀ T')‖ ≤ R := fun j hj =>
      (tensorL2Norm_iteratedCovGrad_symmS_le (I := I) g₀ T' j).trans (hT'ball j hj)
    have hSle : ∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i
            (ccTensor02Symm (I := I) g₀ T - ccTensor02Symm (I := I) g₀ T')‖ ^ 2 ≤
        ∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hsymeq : ccTensor02Symm (I := I) g₀ T - ccTensor02Symm (I := I) g₀ T' =
          ccTensor02Symm (I := I) g₀ (T - T') := (symmS_sub (I := I) g₀ T T').symm
      rw [hsymeq]
      have hle := tensorL2Norm_iteratedCovGrad_symmS_le (I := I) g₀ (T - T') i
      have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i (ccTensor02Symm (I := I) g₀ (T - T'))‖ :=
        norm_nonneg _
      exact pow_le_pow_left₀ hnn hle 2
    have hsqrtSle : Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i
            (ccTensor02Symm (I := I) g₀ T - ccTensor02Symm (I := I) g₀ T')‖ ^ 2) ≤
        Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) :=
      Real.sqrt_le_sqrt hSle
    have hS_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    obtain ⟨hC0S, hL0S, hLaS⟩ :=
      hEndS (ccTensor02Symm (I := I) g₀ T) (ccTensor02Symm (I := I) g₀ T') hδ_le hδS hδ'_le hδ'S
        (ccTensorBilin_symmS_symm (I := I) g₀ T)
        (ccTensorBilin_symmS_symm (I := I) g₀ T') hTballS hT'ballS
    have hN_eq :
        deTurckRHSArmG0 (I := I) g₀ g_bg (ccTensor02Symm (I := I) g₀ T)
            (lt_of_le_of_lt hδ_le hδ₀) hδS -
          deTurckRHSArmG0 (I := I) g₀ g_bg (ccTensor02Symm (I := I) g₀ T')
            (lt_of_le_of_lt hδ'_le hδ₀) hδ'S =
        deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
          deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ' := by
      rw [deTurckRHSArmG0_symmS_eq (I := I) g₀ g_bg T
          (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ_le hδ₀) hδS,
        deTurckRHSArmG0_symmS_eq (I := I) g₀ g_bg T'
          (lt_of_le_of_lt hδ'_le hδ₀) hδ' (lt_of_le_of_lt hδ'_le hδ₀) hδ'S]
    rw [hN_eq] at hC0S hL0S hLaS
    refine ⟨fun x => ?_, ?_, ?_⟩
    · refine (hC0S x).trans ?_
      exact mul_le_mul_of_nonneg_left hSle (sq_nonneg _)
    · refine hL0S.trans ?_
      exact mul_le_mul_of_nonneg_left hsqrtSle hΛ₀_nn
    · refine hLaS.trans ?_
      exact mul_le_mul_of_nonneg_left hsqrtSle hΛ₀_nn

  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    refine ⟨Λ₀, hΛ₀_nn, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
    obtain rfl : q = 0 := Nat.le_zero.mp hq
    have hEnd' := hEnd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    simpa using hEnd'.2.1
  · obtain ⟨Cgn, hCgn_nn, hGN⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le
        (I := I) (M := M) g₀ 2 a hapos
    refine ⟨(Cgn + 1) * (Λ₀ + 1), by positivity, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    set N : SmoothCcTensor g₀ 0 2 :=
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
    set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
    obtain ⟨hC0, hL0, hLa⟩ := hEnd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball

    have hC0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤
        (Λ₀ * Real.sqrt S) ^ 2 := by
      intro x
      have hx := hC0 x
      rw [mul_pow, Real.sq_sqrt hS_nn]
      exact hx
    have hL0' : ‖N‖ ≤ Λ₀ * Real.sqrt S := by rw [hN_def, hS_def]; exact hL0
    have hLa' : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λ₀ * Real.sqrt S := by
      rw [hN_def, hS_def]; exact hLa

    have hN_norm_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ := norm_nonneg _
    have hΛ₀S_nn : 0 ≤ Λ₀ * Real.sqrt S := mul_nonneg hΛ₀_nn hsqrtS_nn

    suffices hgoal : ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ ≤
        ((Cgn + 1) * (Λ₀ + 1)) * Real.sqrt S by
      rw [hN_def, hS_def] at hgoal; exact hgoal
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst hq0
      have h0 : ‖iteratedCovGrad (I := I) g₀ 0 2 0 N‖ = ‖N‖ := by simp
      rw [h0]
      refine hL0'.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
      nlinarith [hCgn_nn, hΛ₀_nn]
    · rcases lt_or_eq_of_le hq with hqlt | hqeq
      · have hGNq := hGN N (Λ₀ * Real.sqrt S) hΛ₀S_nn hC0' q hqpos hqlt

        set e : ℝ := (q : ℝ) / a with he_def
        have he_nn : 0 ≤ e := by
          rw [he_def]; positivity
        have he_lt_one : e < 1 := by
          rw [he_def]
          rw [div_lt_one (by exact_mod_cast hapos)]
          exact_mod_cast hqlt
        have h1me_nn : 0 ≤ 1 - e := by linarith

        have hak_mono : (‖iteratedCovGrad (I := I) g₀ 0 2 a N‖) ^ e ≤
            (Λ₀ * Real.sqrt S) ^ e :=
          Real.rpow_le_rpow hN_norm_nn hLa' he_nn

        have hrhs_eq : Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) * (Λ₀ * Real.sqrt S) ^ e =
            Cgn * (Λ₀ * Real.sqrt S) := by
          rcases eq_or_lt_of_le hΛ₀S_nn with hzero | hpos
          · rw [← hzero, Real.zero_rpow (ne_of_gt (by linarith [he_lt_one] : (0 : ℝ) < 1 - e))]
            simp
          · rw [mul_assoc, ← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
        calc ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖
            ≤ Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) *
                (‖iteratedCovGrad (I := I) g₀ 0 2 a N‖) ^ e := by
              simpa only [he_def] using hGNq
          _ ≤ Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) * (Λ₀ * Real.sqrt S) ^ e := by
              refine mul_le_mul_of_nonneg_left hak_mono ?_
              exact mul_nonneg hCgn_nn (Real.rpow_nonneg hΛ₀S_nn _)
          _ = Cgn * (Λ₀ * Real.sqrt S) := hrhs_eq
          _ = (Cgn * Λ₀) * Real.sqrt S := by ring
          _ ≤ ((Cgn + 1) * (Λ₀ + 1)) * Real.sqrt S := by
              refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
              nlinarith [hCgn_nn, hΛ₀_nn]
      · subst hqeq
        refine hLa'.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
        nlinarith [hCgn_nn, hΛ₀_nn]

private theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical

  obtain ⟨Cn, hCn_nn, hCn⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀

  obtain ⟨Cl, hCl_nn, hCl⟩ :=
    rawTensorConnLapSmooth_iteratedCovGrad_l2_tame (I := I) g₀ a
  refine ⟨Cn + Cl, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀

  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _

  set N : SmoothCcTensor g₀ 0 2 :=
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def

  have hjet_split :
      iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
        iteratedCovGrad (I := I) g₀ 0 2 q N -
          iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')) := by
    rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
      (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ', ← hN_def, iteratedCovGrad_sub]

  have htri :
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ := by
    rw [hjet_split]; exact norm_sub_le _ _

  have hNarm : ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ ≤ Cn * Real.sqrt S := by
    rw [hN_def, hS_def]
    exact hCn T T' hδ_le hδ hδ'_le hδ' hTball hT'ball q hq
  have hLarm : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ ≤ Cl * Real.sqrt S := by
    rw [hS_def]; exact hCl (T - T') q hq
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖
      ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ := htri
    _ ≤ Cn * Real.sqrt S + Cl * Real.sqrt S := add_le_add hNarm hLarm
    _ = (Cn + Cl) * Real.sqrt S := by ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
theorem deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (∑ q ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
          Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  classical
  set K : ℕ := Module.finrank ℝ E / 2 + 1 with hK_def
  have hK_super : 2 * K > Module.finrank ℝ E + 2 * 0 := by rw [hK_def]; omega
  set L : ℕ := 4 * K + 4 with hL_def
  have hL_le : L ≤ a + 1 := by rw [hL_def, hK_def]; omega
  have hperdeg : ∀ q : ℕ, q ≤ 2 → ∃ Dq : ℝ, 0 ≤ Dq ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖) ≤
          Dq * ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    intro q hq
    obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
      tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g₀ 0 (2 + q) K 0 hK_super
    obtain ⟨Cit, hCit_nn, hCit⟩ :=
      iteratedCovGrad_toHs_norm_le (I := I) (M := M) g₀ 0 2 q (2 * K)
    obtain ⟨Crev, hCrev_nn, hCrev⟩ :=
      exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * K + q)
    refine ⟨Cemb * Cit * Crev, by positivity, fun W x => ?_⟩
    have hwin : 2 * (2 * K + q) + 1 ≤ L + 1 := by rw [hL_def]; omega
    have hrev : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * K + q) W‖ ≤
        Crev * ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
      refine le_trans (hCrev W) ?_
      refine mul_le_mul_of_nonneg_left ?_ hCrev_nn
      have hcongr : (∑ j ∈ Finset.range (2 * (2 * K + q) + 1),
          tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
            (iteratedCovGrad (I := I) g₀ 0 2 j W).toFun) =
          ∑ j ∈ Finset.range (2 * (2 * K + q) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ :=
        Finset.sum_congr rfl
          (fun j _ => (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm)
      rw [hcongr]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
        (fun j _ _ => norm_nonneg _)
    have hit : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
        (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q W)‖ ≤
        Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (2 * K + q) W‖ := hCit W
    have hemb := hCemb (iteratedCovGrad (I := I) g₀ 0 2 q W) x
    calc (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
          ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖)
        ≤ Cemb * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
            (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q W)‖ := hemb
      _ ≤ Cemb * (Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
            (2 * K + q) W‖) := mul_le_mul_of_nonneg_left hit hCemb_pos.le
      _ ≤ Cemb * (Cit * (Crev * ∑ j ∈ Finset.range (L + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrev hCit_nn) hCemb_pos.le
      _ = Cemb * Cit * Crev * ∑ j ∈ Finset.range (L + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by ring
  choose Dfun hDfun_nn hDfun using hperdeg
  set D : ℝ := max (Dfun 0 (by norm_num))
    (max (Dfun 1 (by norm_num)) (Dfun 2 (by norm_num))) with hD_def
  have hD_nn : 0 ≤ D := le_trans (hDfun_nn 0 (by norm_num)) (le_max_left _ _)
  have hD0 : Dfun 0 (by norm_num) ≤ D := le_max_left _ _
  have hD1 : Dfun 1 (by norm_num) ≤ D := le_trans (le_max_left _ _) (le_max_right _ _)
  have hD2 : Dfun 2 (by norm_num) ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.sqrt (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)), Real.sqrt_nonneg _, fun W x => ?_⟩
  set Ssum : ℝ := ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖
    with hSsum_def
  have hSsum_nn : 0 ≤ Ssum := Finset.sum_nonneg fun j _ => norm_nonneg _
  letI inst0 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI inst1 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI inst2 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 2) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  have hptdeg : ∀ q : ℕ, q ≤ 2 →
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖) ≤ D * Ssum := by
    intro q hq
    interval_cases q
    · exact le_trans (hDfun 0 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD0 hSsum_nn)
    · exact le_trans (hDfun 1 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD1 hSsum_nn)
    · exact le_trans (hDfun 2 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD2 hSsum_nn)
  have hcs : Ssum ^ 2 ≤ ((L + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2 := by
    rw [hSsum_def]
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (L + 1))
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hwin2 : (∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2) ≤
      ∑ i ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun i _ _ => sq_nonneg _)
  have hsqrt_sq : Real.sqrt (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)) ^ 2 =
      3 * D ^ 2 * ((L + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  rw [hsqrt_sq]
  set RHS : ℝ := ∑ i ∈ Finset.range (a + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hRHS_def
  have hRHS_nn : 0 ≤ RHS := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hpt0 := hptdeg 0 (by norm_num)
  have hpt1 := hptdeg 1 (by norm_num)
  have hpt2 := hptdeg 2 (by norm_num)
  have hcolsq_le : (∑ q ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
      3 * (D * Ssum) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add,
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x)]
    have hDS_nn : 0 ≤ D * Ssum := mul_nonneg hD_nn hSsum_nn
    nlinarith [hpt0, hpt1, hpt2,
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x), hDS_nn]
  calc (∑ q ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      ≤ 3 * (D * Ssum) ^ 2 := hcolsq_le
    _ = 3 * D ^ 2 * Ssum ^ 2 := by ring
    _ ≤ 3 * D ^ 2 * (((L + 1 : ℕ) : ℝ) * RHS) := by
        rw [hRHS_def]
        exact mul_le_mul_of_nonneg_left
          (le_trans hcs (mul_le_mul_of_nonneg_left hwin2 (by positivity))) (by positivity)
    _ = (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)) * RHS := by ring

private theorem appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ), q ≤ a →
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
            (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by
  classical
  set Kf : ℕ → ℝ := fun k => (ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose
    with hKf_def
  have hKf_nn : ∀ k, 0 ≤ Kf k := fun k =>
    (ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose_spec.1
  have hKf_spec : ∀ k, ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ k
            (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          Kf k * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := fun k =>
    (ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose_spec.2
  refine ⟨(Finset.range (a + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero a)) Kf,
    le_trans (hKf_nn 0) (Finset.le_sup' Kf (Finset.mem_range.mpr (Nat.succ_pos a))), ?_⟩
  intro q hq Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  have hqmem : q ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
  have hKq_le : Kf q ≤
      (Finset.range (a + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero a)) Kf :=
    Finset.le_sup' Kf hqmem
  refine le_trans (hKf_spec q Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup) ?_
  refine mul_le_mul_of_nonneg_right hKq_le ?_
  have h1 : 0 ≤ ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 := by positivity
  have h2 : 0 ≤ ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by positivity
  linarith

set_option maxHeartbeats 1000000 in
private theorem deTurckRHSArmDiff_threeArm_coeffC0_jetL2_crude_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hsymm⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛC, Γ, hΛC_nn, hΓ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_s : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T)) δ :=
    gFibreOpBound_ccTensorBilinSymm_symmS g₀ T hδ
  have hδ'_s : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T')) δ' :=
    gFibreOpBound_ccTensorBilinSymm_symmS g₀ T' hδ'
  obtain ⟨C₀, C₁, C₂, hid, h0s, h1s, h2s, h0j, h1j, h2j⟩ :=
    hsymm (ccTensor02Symm (I := I) g₀ T) (ccTensor02Symm (I := I) g₀ T') hδ_le hδ_s hδ'_le hδ'_s
      (ccTensorBilin_symmS_symm g₀ T) (ccTensorBilin_symmS_symm g₀ T')
      (fun j hj => le_trans (tensorL2Norm_iteratedCovGrad_symmS_le g₀ T j) (hTball j hj))
      (fun j hj => le_trans (tensorL2Norm_iteratedCovGrad_symmS_le g₀ T' j) (hT'ball j hj))
  obtain ⟨σ'₀, hσ'₀⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0
  obtain ⟨σ'₁, hσ'₁⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 1
  obtain ⟨σ'₂, hσ'₂⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 2
  refine ⟨symmAbsorbedCoeff (I := I) (M := M) g₀ 0 C₀ σ'₀,
    symmAbsorbedCoeff (I := I) (M := M) g₀ 1 C₁ σ'₁,
    symmAbsorbedCoeff (I := I) (M := M) g₀ 2 C₂ σ'₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he0 : operatorFieldApply (I := I) (M := M) g₀ 2 2
          (symmAbsorbedCoeff (I := I) (M := M) g₀ 0 C₀ σ'₀)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) =
        operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) g₀ (T - T'))) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 (T - T') C₀ σ'₀ hσ'₀ x v
    have he1 : operatorFieldApply (I := I) (M := M) g₀ 3 2
          (symmAbsorbedCoeff (I := I) (M := M) g₀ 1 C₁ σ'₁)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) =
        operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) g₀ (T - T'))) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 1 (T - T') C₁ σ'₁ hσ'₁ x v
    have he2 : operatorFieldApply (I := I) (M := M) g₀ 4 2
          (symmAbsorbedCoeff (I := I) (M := M) g₀ 2 C₂ σ'₂)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) =
        operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) g₀ (T - T'))) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 (T - T') C₂ σ'₂ hσ'₂ x v
    rw [he0, he1, he2, symmS_sub g₀ T T',
      ← deTurckRHSArmG0_symmS_eq g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ
        (lt_of_le_of_lt hδ_le hδ₀) hδ_s,
      ← deTurckRHSArmG0_symmS_eq g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        (lt_of_le_of_lt hδ'_le hδ₀) hδ'_s]
    exact hid
  · intro x
    exact (symmAbsorbedCoeff_riemannianFiberNormSq_le g₀ 0 C₀ σ'₀ x).trans (h0s x)
  · intro x
    exact (symmAbsorbedCoeff_riemannianFiberNormSq_le g₀ 1 C₁ σ'₁ x).trans (h1s x)
  · intro x
    exact (symmAbsorbedCoeff_riemannianFiberNormSq_le g₀ 2 C₂ σ'₂ x).trans (h2s x)
  · exact (symmAbsorbedCoeff_jet_le g₀ 0 (a + 1) C₀ σ'₀).trans h0j
  · exact (symmAbsorbedCoeff_jet_le g₀ 1 (a + 1) C₁ σ'₁).trans h1j
  · exact (symmAbsorbedCoeff_jet_le g₀ 2 (a + 1) C₂ σ'₂).trans h2j

set_option maxHeartbeats 1000000 in
private theorem deTurckSmoothRemainderDiff_connLapResidual_topCoeff_crude_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (_hR : 0 ≤ R)
    {ΛC Γ : ℝ} (_hΛC_nn : 0 ≤ ΛC) (_hΓ_nn : 0 ≤ Γ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λw Γw : ℝ, 0 ≤ Λw ∧ 0 ≤ Γw ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂arm : SmoothCcTensor g₀ 4 2),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂arm.toSection x) ≤ ΛC ^ 2) →
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2) ≤ Γ ^ 2 →
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂arm (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) →
          ∃ C₂' : SmoothCcTensor g₀ 4 2,
            (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂' (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
            (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂'.toSection x) ≤ Λw ^ 2) ∧
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂'‖ ^ 2) ≤ Γw ^ 2 := by
  classical
  obtain ⟨Λpure, Γpure, hΛpure_nn, hΓpure_nn, hpuresup, hpurejet⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_ricciArmPrincipalCoeffPure_self_fibre_jetL2_bound
      (I := I) (M := M) g₀ a
  refine ⟨Real.sqrt (2 * ΛC ^ 2 + 2 * Λpure ^ 2), Real.sqrt (2 * Γ ^ 2 + 2 * Γpure ^ 2),
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball C₀ C₁ C₂arm hC₂armsup hC₂armjet hidArm
  refine ⟨C₂arm - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
      (I := I) (M := M) g₀ g₀, ?_, ?_, ?_⟩
  · have hlift : rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') =
        operatorFieldApply (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
          (I := I) (M := M) g₀ (T - T') x v
    rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff (I := I) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ', hidArm, hlift,
      appCc_sub_left]
    abel
  · intro x
    rw [Real.sq_sqrt (by positivity)]
    have hsec : (C₂arm -
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀).toSection x =
        C₂arm.toSection x -
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀).toSection x := by
      have h1 := smoothCcTensor_toSection_add_apply g₀ C₂arm
        (-(DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀)) x
      rw [smoothCcTensor_toSection_neg_apply, ← sub_eq_add_neg, ← sub_eq_add_neg] at h1
      exact h1
    rw [hsec]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            (C₂arm.toSection x -
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀).toSection x)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂arm.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀).toSection x) :=
          riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 2 x _ _
      _ ≤ 2 * ΛC ^ 2 + 2 * Λpure ^ 2 := by
          have h1 := hC₂armsup x
          have h2 := hpuresup x
          linarith [h1, h2]
  · rw [Real.sq_sqrt (by positivity)]
    have hpi : ∀ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (C₂arm -
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
          2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀)‖ ^ 2 := by
      intro i _
      have h := normSq_iteratedCovGrad_sub_smul_le_tame (I := I) g₀ 4 2 i C₂arm
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀) 1
        (‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2)
        (‖iteratedCovGrad (I := I) g₀ 4 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)‖ ^ 2) (le_refl _) (le_refl _)
      rw [one_smul] at h
      simp only [one_pow, mul_one] at h
      linarith [h]
    calc (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (C₂arm -
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀)‖ ^ 2)
        ≤ ∑ i ∈ Finset.range (a + 1),
            (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2 +
              2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                  (I := I) (M := M) g₀ g₀)‖ ^ 2) := Finset.sum_le_sum hpi
      _ = 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2) +
            2 * (∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                  (I := I) (M := M) g₀ g₀)‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * Γ ^ 2 + 2 * Γpure ^ 2 := by linarith [hC₂armjet, hpurejet]

set_option maxHeartbeats 1000000 in
private theorem deTurckSmoothRemainderDiff_intrinsicPalatini_coeffC0_jetL2_crude_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, harm⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_jetL2_crude_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λw, Γw, hΛw_nn, hΓw_nn, hresid⟩ :=
    deTurckSmoothRemainderDiff_connLapResidual_topCoeff_crude_ballUniform
      (I := I) g₀ g_bg a ha_super hR hΛC_nn hΓ_nn hδ₀
  refine ⟨max ΛC Λw, max Γ Γw, le_trans hΛC_nn (le_max_left _ _),
    le_trans hΓ_nn (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨C₀, C₁, C₂arm, hidArm, hC₀sup, hC₁sup, hC₂armsup, hC₀jet, hC₁jet, hC₂armjet⟩ :=
    harm T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  obtain ⟨C₂', hidRem, hC₂'sup, hC₂'jet⟩ :=
    hresid T T' hδ_le hδ hδ'_le hδ' hTball hT'ball C₀ C₁ C₂arm hC₂armsup hC₂armjet hidArm
  have hΛCsq : ΛC ^ 2 ≤ max ΛC Λw ^ 2 := by
    have h1 : ΛC ≤ max ΛC Λw := le_max_left _ _
    nlinarith [h1, hΛC_nn]
  have hΛwsq : Λw ^ 2 ≤ max ΛC Λw ^ 2 := by
    have h2 : Λw ≤ max ΛC Λw := le_max_right _ _
    nlinarith [h2, hΛw_nn]
  have hΓsq : Γ ^ 2 ≤ max Γ Γw ^ 2 := by
    have h1 : Γ ≤ max Γ Γw := le_max_left _ _
    nlinarith [h1, hΓ_nn]
  have hΓwsq : Γw ^ 2 ≤ max Γ Γw ^ 2 := by
    have h2 : Γw ≤ max Γ Γw := le_max_right _ _
    nlinarith [h2, hΓw_nn]
  exact ⟨C₀, C₁, C₂', hidRem, fun x => le_trans (hC₀sup x) hΛCsq,
    fun x => le_trans (hC₁sup x) hΛCsq, fun x => le_trans (hC₂'sup x) hΛwsq,
    le_trans hC₀jet hΓsq, le_trans hC₁jet hΓsq, le_trans hC₂'jet hΓwsq⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_intrinsic_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
    deTurckSmoothRemainderDiff_intrinsicPalatini_coeffC0_jetL2_crude_ballUniform
      (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨K₀, hK₀_nn, hK₀⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 2 2 a
  obtain ⟨K₁, hK₁_nn, hK₁⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 3 2 a
  obtain ⟨K₂, hK₂_nn, hK₂⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 4 2 a
  obtain ⟨Cemb1, hCemb1_nn, hemb1⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow (I := I) g₀ a ha_super
  set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
  have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
  have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
  set base : ℝ := Kmax * (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) with hbase_def
  have hbase_nn : 0 ≤ base := by
    rw [hbase_def]; exact mul_nonneg hKmax_nn (by positivity)
  refine ⟨3 * Real.sqrt base, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set S₂ : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₂_def
  have hS₂_nn : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hcoeff T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  set A₀ := operatorFieldApply (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := operatorFieldApply (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := operatorFieldApply (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  have hN_split : deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' = A₀ + A₁ + A₂ := by
    rw [hA₀, hA₁, hA₂]; exact hid
  have hWsup : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
        (Real.sqrt (Cemb1 ^ 2 * S₂)) ^ 2 := by
    intro m hm x
    rw [Real.sq_sqrt (by positivity)]
    have hembx := hemb1 (T - T') x
    have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    refine le_trans (Finset.single_le_sum
      (f := fun qq => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + qq) x
        ((iteratedCovGrad (I := I) g₀ 0 2 qq (T - T')).toSection x))
      (fun qq _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + qq) x _) hmem) ?_
    refine le_trans hembx ?_
    rw [hS₂_def]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Cemb1)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun i _ _ => sq_nonneg _)
  have hWjet : ∀ (m : ℕ), m ≤ 2 →
      (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤
        ∑ i ∈ Finset.range (a + m + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
    intro m hm
    have hcomp : ∀ l : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 := by
      intro l
      have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
          (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))
      have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T'))
      rw [hbridgeL, hbridgeR]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      have hrw := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l (T - T') x
      simpa only [Nat.add_assoc] using hrw
    rw [show (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) =
        ∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 from
      Finset.sum_congr rfl (fun l _ => hcomp l)]
    set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hf_def
    have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
    have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆ Finset.range (a + m + 1) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨l, hl, rfl⟩ := hi
      rw [Finset.mem_range] at hl ⊢
      omega
    have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
        m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
    calc (∑ l ∈ Finset.range (q + 1), f (m + l))
        = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), f i :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ i ∈ Finset.range (a + m + 1), f i :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)
  have hcoeffjet_le : ∀ (m : ℕ) (Cm : SmoothCcTensor g₀ (2 + m) 2) (bnd : ℝ),
      0 ≤ bnd →
      (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ bnd →
      (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ bnd := by
    intro m Cm bnd hbnd_nn hjet
    refine le_trans ?_ hjet
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => sq_nonneg _)
    exact Finset.range_mono (by omega)
  have harm : ∀ (m : ℕ) (hm : m ≤ 2) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
      (hKm_le : Km ≤ Kmax)
      (hKm : ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          Km * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2))
      (hCmsup : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
      (hCmjet : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ≤ Real.sqrt (base * S₂) := by
    intro m hm Cm Km hKm_le hKm hCmsup hCmjet
    have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
      ΛC (Real.sqrt (Cemb1 ^ 2 * S₂)) hΛC_nn (Real.sqrt_nonneg _) hCmsup
      (hWsup m hm)
    have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * S₂)) ^ 2 = Cemb1 ^ 2 * S₂ := Real.sq_sqrt (by positivity)
    have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤
        Γ ^ 2 := hcoeffjet_le m Cm (Γ ^ 2) (sq_nonneg _) hCmjet
    have hwjet : (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S₂ := by
      refine le_trans (hWjet m hm) ?_
      rw [hS₂_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => sq_nonneg _)
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤ base * S₂ := by
      refine le_trans htame ?_
      rw [hΛWsq]
      have ha1 : (Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb1 ^ 2 * S₂) * Γ ^ 2 :=
        mul_le_mul_of_nonneg_left hcjet (by positivity)
      have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S₂ :=
        mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
      have hinner :
          (Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
          ≤ (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₂ := by
        calc (Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
            ≤ (Cemb1 ^ 2 * S₂) * Γ ^ 2 + ΛC ^ 2 * S₂ := add_le_add ha1 ha2
          _ = (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₂ := by ring
      have hinner_nn : 0 ≤ (Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by positivity
      calc Km * ((Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
          ≤ Kmax * ((Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₂) :=
            mul_le_mul hKm_le hinner hinner_nn hKmax_nn
        _ = base * S₂ := by rw [hbase_def]; ring
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hsq
  have ha0 := harm 0 (by norm_num) C₀ K₀ hK₀_le (hK₀ q hq) hC₀sup hC₀jet
  have ha1 := harm 1 (by norm_num) C₁ K₁ hK₁_le (hK₁ q hq) hC₁sup hC₁jet
  have ha2 := harm 2 (by norm_num) C₂ K₂ hK₂_le (hK₂ q hq) hC₂sup hC₂jet
  have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀‖ ≤ Real.sqrt (base * S₂) := by
    rw [hA₀]; exact ha0
  have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₁‖ ≤ Real.sqrt (base * S₂) := by
    rw [hA₁]; exact ha1
  have hnorm2 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤ Real.sqrt (base * S₂) := by
    rw [hA₂]; exact ha2
  have hsqrt_fac : Real.sqrt (base * S₂) = Real.sqrt base * Real.sqrt S₂ :=
    Real.sqrt_mul hbase_nn S₂
  have hgoal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ≤
      3 * Real.sqrt base * Real.sqrt S₂ := by
    rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 q (A₀ + A₁) A₂,
      iteratedCovGrad_add (I := I) g₀ 0 2 q A₀ A₁]
    have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀ +
          iteratedCovGrad (I := I) g₀ 0 2 q A₁ +
          iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
        Real.sqrt (base * S₂) + Real.sqrt (base * S₂) + Real.sqrt (base * S₂) := by
      refine le_trans (norm_add_le _ _) ?_
      exact add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) hnorm2
    refine htri.trans (le_of_eq ?_)
    rw [hsqrt_fac]; ring
  exact hgoal

theorem deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∑ q ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ^ 2) ≤
          C * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
  classical

  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_intrinsic_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨(a + 1 : ℕ) * C ^ 2, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def

  set Scol : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun i _ => sq_nonneg _

  have hsqrt_sq : Real.sqrt Scol ^ 2 = Scol := Real.sq_sqrt hScol_nn

  have hper : ∀ q ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 ≤ C ^ 2 * Scol := by
    intro q hq
    have hqa : q ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hbound : ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ≤ C * Real.sqrt Scol := by
      rw [hD_def, hScol_def]
      exact hC T T' hδ_le hδ hδ'_le hδ' hTball hT'ball q hqa
    have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ := norm_nonneg _
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2
        ≤ (C * Real.sqrt Scol) ^ 2 := pow_le_pow_left₀ hnn hbound 2
      _ = C ^ 2 * Scol := by rw [mul_pow, hsqrt_sq]

  calc (∑ q ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2)
      ≤ ∑ _q ∈ Finset.range (a + 1), C ^ 2 * Scol := Finset.sum_le_sum hper
    _ = (a + 1 : ℕ) * C ^ 2 * Scol := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
