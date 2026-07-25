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

set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open LieCorr0Core
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

private theorem realizedDeTurckLie_threeArm_lowerOrder_residual
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
          deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  obtain ⟨Φ₀L, Φ₁L, Φ₂L, hj0, hj1, hj2, hident⟩ :=
    realizedDeTurckLie_threeArm_covariant_identity (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₀L, Φ₁L, Φ₂L, hj0, hj1, hj2, fun s hs x v => ?_⟩
  rw [(hasDerivAt_realizedDeTurckLieChartSum_general (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
    x (v 0) (v 1) hs).deriv]
  exact hident s hs x v

section LieCorr0BoundsAll

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckVFCovDeriv connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

section LieCorr0BoundsA

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable (g₀ g_bg : SmoothRiemannianMetric I M)

private theorem lc0b_fn_of_bounded (N : ℕ) (Q : ℕ → ℝ → Prop)
    (h : ∀ k, k ≤ N → ∃ c : ℝ, 0 ≤ c ∧ Q k c) :
    ∃ f : ℕ → ℝ, (∀ k, 0 ≤ f k) ∧ ∀ k, k ≤ N → Q k (f k) := by
  induction N with
  | zero =>
    obtain ⟨c, hc0, hc⟩ := h 0 le_rfl
    refine ⟨fun _ => c, fun _ => hc0, ?_⟩
    intro k hk
    rw [Nat.le_zero.mp hk]
    exact hc
  | succ N ih =>
    obtain ⟨f, hf0, hf⟩ := ih (fun k hk => h k (le_trans hk (Nat.le_succ N)))
    obtain ⟨c, hc0, hc⟩ := h (N + 1) le_rfl
    refine ⟨Function.update f (N + 1) c, ?_, ?_⟩
    · intro k
      by_cases hk : k = N + 1
      · rw [hk, Function.update_self]; exact hc0
      · rw [Function.update_of_ne hk]; exact hf0 k
    · intro k hk
      by_cases hkN : k = N + 1
      · rw [hkN, Function.update_self]; exact hc
      · rw [Function.update_of_ne hkN]
        exact hf k (by omega)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_icg_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lc0b_covGrad_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    covGrad (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) = 0 := by
  have h := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul
    (I := I) (M := M) (g := g) (r := r) (s := s) (0 : ℝ) (0 : SmoothCcTensor g r s)
  rw [zero_smul, zero_smul] at h
  exact h

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_normSq_icg_add_le (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q (A + B)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g r s q A‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g r s q B‖ ^ 2 := by
  have htri : ‖iteratedCovGrad (I := I) g r s q (A + B)‖ ≤
      ‖iteratedCovGrad (I := I) g r s q A‖ + ‖iteratedCovGrad (I := I) g r s q B‖ := by
    rw [iteratedCovGrad_add]
    exact norm_add_le _ _
  nlinarith [htri, norm_nonneg (iteratedCovGrad (I := I) g r s q (A + B)),
    norm_nonneg (iteratedCovGrad (I := I) g r s q A),
    norm_nonneg (iteratedCovGrad (I := I) g r s q B),
    sq_nonneg (‖iteratedCovGrad (I := I) g r s q A‖ - ‖iteratedCovGrad (I := I) g r s q B‖)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_rfns_toSection_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((A + B).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x (B.toSection x) := by
  rw [show (A + B).toSection x = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r s x _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem lc0b_normSq_eq_integral (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g r s) :
    ‖W‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def]
  exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s W

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lc0b_rfns_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v,
    TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private theorem lc0b_rfns_icg_symmS_le (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j (ccTensor02Symm (I := I) (M := M) g T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j T).toSection x) := by
  have hsymm : iteratedCovGrad (I := I) g 0 2 j (ccTensor02Symm (I := I) (M := M) g T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) := by
    rw [show ccTensor02Symm (I := I) (M := M) g T = (1 / 2 : ℝ) •
        (T + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) from rfl]
    rw [lc0b_icg_smul, iteratedCovGrad_add, smul_add]
  rw [hsymm]
  have hadd : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
      (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
          (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x) :=
    lc0b_rfns_toSection_add_le (I := I) (M := M) g 0 (2 + j) _ _ x
  refine le_trans hadd ?_
  have h1 : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
      (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T).toSection x) =
      (1 / 2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j T).toSection x) := by
    rw [show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T).toSection x =
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 j T).toSection x from rfl]
    exact lc0b_rfns_smul (I := I) (M := M) g 0 (2 + j) x _ _
  have h2 : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
      (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      (1 / 2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j T).toSection x) := by
    rw [show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x =
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 j
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x from rfl]
    rw [lc0b_rfns_smul (I := I) (M := M) g 0 (2 + j) x _ _]
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g
      (Equiv.swap (0 : Fin 2) 1) T j x]
  rw [h1, h2]
  have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (2 + j) x
    ((iteratedCovGrad (I := I) g 0 2 j T).toSection x)
  nlinarith [hnn]

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_normSq_icg_symmS_le (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 j (ccTensor02Symm (I := I) (M := M) g T)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_mono ?_ ?_
    (fun x => lc0b_rfns_icg_symmS_le (I := I) (M := M) g T j x)
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (2 + j)
      (iteratedCovGrad (I := I) g 0 2 j (ccTensor02Symm (I := I) (M := M) g T))
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (2 + j)
      (iteratedCovGrad (I := I) g 0 2 j T)

omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_normSq_icg_raise_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 1 (s + 1) i
        (cometricRaiseSlot0Field (I := I) (M := M) g s W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 (s + 2) i W‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g s W i x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_rfns_symmS_zero_le (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        ((ccTensor02Symm (I := I) (M := M) g T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g 0 2 x
    ((ccTensor02Symm (I := I) (M := M) g T).toSection x) e bse hnE hbse horth]
  have hcof : coframeS (I := I) (M := M) g x 0 e = fun _ : Fin 0 → Fin n =>
      unitTensor (I := I) (M := M) x := by
    funext K
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e K) v =
        coframeS (I := I) (M := M) g x 0 e K v from rfl]
    rw [coframeS_apply (I := I) (M := M) g x 0 e K v]
    rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v =
        unitTensor (I := I) (M := M) x v from rfl]
    rw [Fin.prod_univ_zero]
    rw [unitTensor, Tensor0SSpace.ofModel]
    rfl
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g x 0 2
        ((ccTensor02Symm (I := I) (M := M) g T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g x 0 2
        ((ccTensor02Symm (I := I) (M := M) g T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g T x (e (J 0)) (e (J 1)) := by
      rw [show fiberNormSqComponent (I := I) (M := M) g x 0 2
          ((ccTensor02Symm (I := I) (M := M) g T).toSection x) n e K J =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (ccTensor02Symm (I := I) (M := M) g T).toSection x)
              (coframeS (I := I) (M := M) g x 0 e K))
            (fun i : Fin 2 => (e (J i) : E)) from rfl]
      rw [hcof]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun i : Fin 2 => (e (J i) : E)) =
          unitModel (I := I) (M := M) g 2 (ccTensor02Symm (I := I) (M := M) g T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [show unitModel (I := I) (M := M) g 2 (ccTensor02Symm (I := I) (M := M) g T) x
            ![e (J 0), e (J 1)] =
          smoothCcTensorBilinForm (I := I) g (ccTensor02Symm (I := I) (M := M) g T) x (e (J 0)) (e (J 1)) from
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g
          (ccTensor02Symm (I := I) (M := M) g T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2
          ((ccTensor02Symm (I := I) (M := M) g T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_WB_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    {δ₀ : ℝ} (P : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2) ∧
    (∀ l : ℕ, l ≤ a →
      ‖iteratedCovGrad (I := I) g₀ 1 1 l
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P))‖ ^ 2 ≤ R ^ 2) := by
  constructor
  · intro x
    have h0 := riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
      (ccTensor02Symm (I := I) (M := M) g₀ P) 0 x
    simp only [iteratedCovGrad_zero] at h0
    rw [h0]
    refine le_trans (lc0b_rfns_symmS_zero_le (I := I) (M := M) g₀ P hδ0 hδ x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hδmax : δ ≤ max δ₀ 0 := le_trans hδ_le (le_max_left _ _)
    exact pow_le_pow_left₀ hδ0 hδmax 2
  · intro l hl
    rw [lc0b_normSq_icg_raise_eq (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P) l]
    refine le_trans (lc0b_normSq_icg_symmS_le (I := I) (M := M) g₀ P l) ?_
    have h1 := hPball l (by omega)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem lc0b_twoArm_fn (g₀ : SmoothRiemannianMetric I M) (r₁ r₂ s₁ s₂ : ℕ) :
    ∃ C2 : ℕ → ℝ, (∀ k, 0 ≤ C2 k) ∧ ∀ k : ℕ,
      ∀ (S : SmoothCcTensor g₀ r₁ s₁) (T : SmoothCcTensor g₀ r₂ s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₁ s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₂ s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ r₁ (s₁ + n) x
                  ((iteratedCovGrad (I := I) g₀ r₁ s₁ n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g₀ r₂ s₂ l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ r₁ (s₁ + n) x
                  ((iteratedCovGrad (I := I) g₀ r₁ s₁ n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g₀ r₂ s₂ l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2 k * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ r₁ s₁ n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ r₂ s₂ l T‖ ^ 2) := by
  have h : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ r₁ s₁) (T : SmoothCcTensor g₀ r₂ s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₁ s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₂ s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ r₁ (s₁ + n) x
                  ((iteratedCovGrad (I := I) g₀ r₁ s₁ n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g₀ r₂ s₂ l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ r₁ (s₁ + n) x
                  ((iteratedCovGrad (I := I) g₀ r₁ s₁ n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g₀ r₂ s₂ l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ r₁ s₁ n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ r₂ s₂ l T‖ ^ 2) := by
    intro k
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ r₁ r₂ s₁ s₂ k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  choose C2 hC2_nn hC2 using h
  exact ⟨C2, hC2_nn, hC2⟩

theorem lc0b_appCcRS_normSq_le (g₀ : SmoothRiemannianMetric I M)
    (p a b : ℕ) (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a) (q : ℕ)
    (C2q ΛΦ ΛW FΦq FWq : ℝ) (hC2q : 0 ≤ C2q) (hΛΦ : 0 ≤ ΛΦ) (hΛW : 0 ≤ ΛW)
    (hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) ≤ ΛΦ)
    (hW0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (W.toSection x) ≤ ΛW)
    (hFΦ : ∑ n ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ a b n Φ‖ ^ 2 ≤ FΦq)
    (hFW : ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ p a l W‖ ^ 2 ≤ FWq)
    (htwo : ∀ (S : SmoothCcTensor g₀ a b) (T : SmoothCcTensor g₀ p a)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
                  ((iteratedCovGrad (I := I) g₀ a b n S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                      ((iteratedCovGrad (I := I) g₀ p a l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
                  ((iteratedCovGrad (I := I) g₀ a b n S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                      ((iteratedCovGrad (I := I) g₀ p a l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2q * (ΛT ^ 2 * ∑ n ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ a b n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ p a l T‖ ^ 2)) :
    ‖iteratedCovGrad (I := I) g₀ p b q (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W)‖ ^ 2 ≤
      diagonalGridGrowthFactor (E := E) q * (C2q * (ΛW * FΦq + ΛΦ * FWq)) := by
  have hΦ0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) ≤
      (Real.sqrt ΛΦ) ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛΦ]
    exact hΦ0 x
  have hW0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (W.toSection x) ≤
      (Real.sqrt ΛW) ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛW]
    exact hW0 x
  obtain ⟨hgi, hgb⟩ := htwo Φ W (Real.sqrt ΛΦ) (Real.sqrt ΛW)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hΦ0' hW0'
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ p (b + q)
    (iteratedCovGrad (I := I) g₀ p b q (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W))
    (fun x => diagonalGridGrowthFactor (E := E) q *
      ∑ n ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
            ((iteratedCovGrad (I := I) g₀ a b n Φ).toSection x)
          * ∑ l ∈ Finset.range (q + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                ((iteratedCovGrad (I := I) g₀ p a l W).toSection x))
    (hgi.const_mul (diagonalGridGrowthFactor (E := E) q))
    (fun x => riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ q p a b Φ W x)
  refine le_trans hkey ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
  refine le_trans hgb ?_
  refine mul_le_mul_of_nonneg_left ?_ hC2q
  rw [Real.sq_sqrt hΛΦ, Real.sq_sqrt hΛW]
  have e1 := mul_le_mul_of_nonneg_left hFΦ hΛW
  have e2 := mul_le_mul_of_nonneg_left hFW hΛΦ
  linarith [e1, e2]

end LieCorr0BoundsA

section LieCorr0BoundsB

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricRaiseSlot0Fib)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

private def lc0KappaField (g₁ gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ gB x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ gB⟩

def lc0Kappa (g₀ g₁ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0KappaField (I := I) (M := M) g₁ gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma lc0Kappa_unitModel_apply (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0Kappa (I := I) (M := M) g₀ g₁ gB) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0KappaField (I := I) (M := M) g₁ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ gB x m

private def lc0LowFixField (g₀ gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₀ g₀ gB x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₀ g₀ gB⟩

def lc0LowFix (g₀ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0LowFixField (I := I) (M := M) g₀ gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lc0LowFix_unitModel_apply (g₀ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0LowFix (I := I) (M := M) g₀ gB) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0LowFix (I := I) (M := M) g₀ gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0LowFixField (I := I) (M := M) g₀ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₀ g₀ gB x m

private def lc0PbLowField (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => ccBilinConnDiffLoweredFib (I := I) g₀ P gA gB x,
    ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ P gA gB⟩

def lc0PbLow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0PbLowField (I := I) (M := M) g₀ P gA gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0PbLow_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0PbLow (I := I) (M := M) g₀ P gA gB) x m =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0PbLow (I := I) (M := M) g₀ P gA gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0PbLowField (I := I) (M := M) g₀ P gA gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact ccBilinConnDiffLoweredFib_toModel (I := I) g₀ P gA gB x m

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lc0b_connDiffLowered_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_unitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m + unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A + B).toSection x) = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x + B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_kappa_decomp (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
        + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
        + lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
    lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
    lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m]
  rw [lc0Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ gB x m,
    lc0b_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
    lc0LowFix_unitModel_apply (I := I) (M := M) g₀ gB x m,
    lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P g₁ g₀ x m,
    lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P g₀ gB x m]
  rw [htie x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2)]
  rw [PDE.DeTurck.connDiff_cocycle (I := I) g₀ g₁ gB x (m 0) (m 1)]
  rw [map_add (g₀.inner x), map_add (ccTensorBilinSymm (I := I) g₀ P x)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  ring

def lc0FixCd (g₀ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection := (connDiffSection (I := I) g₀ gB).toSection
  hasCompactSupport := (connDiffSection (I := I) g₀ gB).hasCompactSupport

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lc0b_connDiffSection_eq_raise_lowered (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [lc0b_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x ![YZ 0, YZ 1, u]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_rfns_icg_lowered_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [lc0b_connDiffSection_eq_raise_lowered (I := I) (M := M) g₀ g₁]

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_normSq_icg_lowered_eq (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lc0b_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ n x

omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_pbLow_raise_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricRaiseSlot0Field_toSection, appCcRS_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  have hLHSval : Tensor0SSpace.toModel D
      (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) u := by
    have hum : unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)) x =
        Tensor0SSpace.toModel D := rfl
    rw [show Tensor0SSpace.toModel D
          (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P gA gB)) x ![u, YZ 0, YZ 1] from by
      rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
    rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
          ![YZ 0, YZ 1, u] from by
      funext i; fin_cases i <;> simp [finRotate_succ_apply]]
    rw [lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P gA gB x ![YZ 0, YZ 1, u]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        Ψc.toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) u := by
    rw [ContinuousLinearMap.comp_apply]
    set om' : Tensor0SSpace 1 I x :=
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) om with hom'
    rw [hΨc x]
    rw [connDiffFib_apply_eval (I := I) gA gB x om' YZ]
    rw [show om' (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) =
        Tensor0SSpace.toModel om' (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))) from rfl]
    rw [hom']
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) om) =
        cometricRaiseSlot0Fib (I := I) g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)) om from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [show Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from u)
            (fun _ : Fin 1 => (show E from
              PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)))) from by
      rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om) _ _, ← hu]]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
          (unitTensor (I := I) (M := M) x))
        (Fin.cons (show E from u)
          (fun _ : Fin 1 => (show E from
            PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)))) =
        unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x
          ![u, PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)] from by
      rw [unitModel]
      congr 1
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ P) x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    exact ccTensorBilinSymm_symm (I := I) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))
  rw [hLHS, hLHSval]
  exact hRHS.symm

omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_rfns_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (ccTensor02Symm (I := I) (M := M) g₀ P)))).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (lc0PbLow (I := I) (M := M) g₀ P gA gB))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (lc0PbLow (I := I) (M := M) g₀ P gA gB) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lc0PbLow (I := I) (M := M) g₀ P gA gB)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P gA gB)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (ccTensor02Symm (I := I) (M := M) g₀ P)))).toSection x) := by
        rw [lc0b_pbLow_raise_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc]

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_normSq_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (lc0PbLow (I := I) (M := M) g₀ P gA gB)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)))‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc n x

end LieCorr0BoundsB

section LieCorr0BoundsC

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  gInvRaisedEndo_eq_diff_add_id inverseMetricSharpFib_g0FlatCLM cotangentToDual_g0FlatCLM
  g0FlatCLM metricComparisonDiffEndo)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_toModel_om_single (x : M) (om : Tensor0SSpace 1 I x) (m : Fin 1 → E) :
    Tensor0SSpace.toModel om m = cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [cotangentToDual_apply]
  rw [show (om (fun _ : Fin 1 => (m 0 : TangentSpace I x)) : ℝ) =
      Tensor0SSpace.toModel om (fun _ : Fin 1 => m 0) from rfl]
  congr 1
  funext k
  rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_g0_inner_sharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) := by
  have h1 : ∀ w : TangentSpace I x,
      g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
    intro w
    rw [gInvRaisedEndo_apply]
    rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
    rw [cotangentToDualLinear_apply]
    exact cotangentToDual_g0FlatCLM (I := I) g₀ x v w
  have h2 : cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (metricComparisonEndo (I := I) g₀ g₁ x v) := by
    rw [inverseMetricSharpFib_inner (I := I) g₁ x om (metricComparisonEndo (I := I) g₀ g₁ x v)]
    rfl
  rw [h2]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [h1 (inverseMetricSharpFib (I := I) g₁ x om)]
  exact g₀.symm x (inverseMetricSharpFib (I := I) g₁ x om) v

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma lc0b_sharpFlat_eq_slotInsert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [lc0b_toModel_om_single (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [lc0b_toModel_om_single (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [lc0b_g0_inner_sharp_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma lc0b_fullRaised_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = metricComparisonDiffEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma lc0b_slotInsert_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A + B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x +
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

theorem lc0b_sharpFlat_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Km, hKm_nn, hKm⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀) with hIdIns_def
  obtain ⟨S0, hS0_nn, hS0⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 1 IdIns
  refine ⟨2 * Cb 0 + 2 * S0,
    fun i => ∑ q ∈ Finset.range (i + 1),
      (2 * (Cb q * Km q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2),
    by have := hCb_nn 0; linarith,
    fun i => Finset.sum_nonneg fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hCb_nn q) (hKm_nn q)))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      lc0b_fullRaised_diff_split (I := I) (M := M) g₀ g₁,
      lc0b_slotInsert_add (I := I) (M := M) g₀ 0]
  refine ⟨?_, ?_⟩
  · intro x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (IdIns.toSection x) := by
      rw [hdecomp]
      exact lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 1 1 _ _ x
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        (DiffIns.toSection x) ≤ Cb 0 := by
      have h2 := hCb g₁ P htie hδ_le hδ0 hδ 0 x
      simp only [iteratedCovGrad_zero] at h2
      have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
        simp
      rw [hgrid0, mul_one] at h2
      exact h2
    linarith [hsplit, hD0, hS0 x]
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    obtain ⟨hgi, hgb⟩ := hKm P hPball q hq_le
    have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ Cb q * Km q := by
      have hint : MeasureTheory.Integrable
          (fun x => Cb q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint
        (fun x => hCb g₁ P htie hδ_le hδ0 hδ q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hgb (hCb_nn q)
    have htri : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ +
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ := by
      rw [hdecomp, iteratedCovGrad_add]
      exact norm_add_le _ _
    nlinarith [htri, hDq,
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q IdIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
        ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖)]

theorem lc0b_cds_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((connDiffSection (I := I) g₁ g₀).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛK, FK, hΛK_nn, hFK_nn, hK⟩ :=
    raisedKoszul_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lc0b_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  refine ⟨ΛK ^ 2 * Λsf,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λsf * FK q + ΛK ^ 2 * Fsf q)),
    mul_nonneg (sq_nonneg _) hΛsf_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛsf_nn (hFK_nn q))
        (mul_nonneg (sq_nonneg _) (hFsf_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hKsup, hKsum⟩ := hK g₁ P hδ_le hδ htie hPball
  obtain ⟨hsfsup, hsfsum⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hid : connDiffSection (I := I) g₁ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro x
    rw [hid, appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
      (show TensorRSSpace 1 2 I x from (raisedKoszul (I := I) g₀ g₁).toSection x)
      (show TensorRSSpace 1 1 I x from (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    exact mul_le_mul (hKsup x) (hsfsup x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) (sq_nonneg ΛK)
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    rw [hid]
    exact lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
      (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) q
      (C2 q) (ΛK ^ 2) Λsf (FK q) (Fsf q)
      (hC2_nn q) (sq_nonneg ΛK) hΛsf_nn hKsup hsfsup (hKsum q hq_le) (hsfsum q hq_le)
      (hC2 q)

theorem lc0b_kappa_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
    lc0b_cds_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λlow, hΛlow_nn, hΛlow⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 3
      (lc0LowFix (I := I) (M := M) g₀ gB)
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lc0FixCd (I := I) (M := M) g₀ gB)
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  set nQ : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2 with hnQ_def
  have hnQ_nn : 0 ≤ nQ := by rw [hnQ_def]; positivity
  set FB : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2
    with hFB_def
  have hFB_nn : ∀ i, 0 ≤ FB i := fun i => Finset.sum_nonneg fun q _ => sq_nonneg _
  set Ffx : ℕ → ℝ := fun q => ∑ l ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ 1 2 l (lc0FixCd (I := I) (M := M) g₀ gB)‖ ^ 2
    with hFfx_def
  have hFfx_nn : ∀ q, 0 ≤ Ffx q := fun q => Finset.sum_nonneg fun l _ => sq_nonneg _
  set FC : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Fcd q + Λcd * (((q : ℝ) + 1) * R ^ 2)))
    with hFC_def
  have hFC_nn : ∀ i, 0 ≤ FC i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFcd_nn q))
        (mul_nonneg hΛcd_nn (by positivity))))
  set FD : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (nQ * Ffx q + Λfx * (((q : ℝ) + 1) * R ^ 2)))
    with hFD_def
  have hFD_nn : ∀ i, 0 ≤ FD i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFfx_nn q))
        (mul_nonneg hΛfx_nn (by positivity))))
  refine ⟨8 * Λcd + 8 * Λlow + 4 * (Λcd * nQ) + 2 * (Λfx * nQ),
    fun i => 8 * Fcd i + 8 * FB i + 4 * FC i + 2 * FD i,
    by
      have e1 := mul_nonneg hΛcd_nn hnQ_nn
      have e2 := mul_nonneg hΛfx_nn hnQ_nn
      linarith [hΛcd_nn, hΛlow_nn, e1, e2],
    fun i => by
      have := hFcd_nn i
      have := hFB_nn i
      have := hFC_nn i
      have := hFD_nn i
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hWB0, hWBL2⟩ :=
    lc0b_WB_feed (I := I) (M := M) g₀ a P hδ_le hδ0 hδ hPball
  obtain ⟨hcd0, hcdL2⟩ := hcd g₁ P htie hδ_le hδ0 hδ hPball
  have hκeq := lc0b_kappa_decomp (I := I) (M := M) g₀ g₁ gB P htie
  have hΨcC : ∀ x : M, (connDiffSection (I := I) g₁ g₀).toSection x =
      connDiffFib (I := I) g₁ g₀ x := fun x => rfl
  have hΨcD : ∀ x : M, (lc0FixCd (I := I) (M := M) g₀ gB).toSection x =
      connDiffFib (I := I) g₀ gB x := fun x => rfl
  have hWBsum : ∀ q : ℕ, q ≤ a →
      ∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 l
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P))‖ ^ 2 ≤ ((q : ℝ) + 1) * R ^ 2 := by
    intro q hq
    refine le_trans (Finset.sum_le_sum fun l hl =>
      hWBL2 l (le_trans (by have := Finset.mem_range.mp hl; omega : l ≤ q) hq)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_refl _
  refine ⟨?_, ?_⟩
  · intro x
    have hsec : (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x =
        ((connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
          + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
          + lc0PbLow (I := I) (M := M) g₀ P g₀ gB).toSection x) := by
      rw [hκeq]
    rw [hsec]
    have h1 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
        + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
      (lc0PbLow (I := I) (M := M) g₀ P g₀ gB) x
    have h2 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB)
      (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀) x
    have h3 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁) (lc0LowFix (I := I) (M := M) g₀ gB) x
    have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((connDiffLoweredCc (I := I) g₀ g₁).toSection x) ≤ Λcd := by
      have h := lc0b_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ 0 x
      simp only [iteratedCovGrad_zero] at h
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((connDiffLoweredCc (I := I) g₀ g₁).toSection x)
          = riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
              ((connDiffSection (I := I) g₁ g₀).toSection x) := h
        _ ≤ Λcd := hcd0 x
    have hB0 := hΛlow x
    have hC0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lc0PbLow (I := I) (M := M) g₀ P g₁ g₀).toSection x) ≤ Λcd * nQ := by
      have h := lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC 0 x
      simp only [iteratedCovGrad_zero] at h
      rw [h, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from (connDiffSection (I := I) g₁ g₀).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hcd0 x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛcd_nn
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lc0PbLow (I := I) (M := M) g₀ P g₀ gB).toSection x) ≤ Λfx * nQ := by
      have h := lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ gB
        (lc0FixCd (I := I) (M := M) g₀ gB) hΨcD 0 x
      simp only [iteratedCovGrad_zero] at h
      rw [h, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from
          (lc0FixCd (I := I) (M := M) g₀ gB).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hΛfx x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛfx_nn
    linarith [h1, h2, h3, hA0, hB0, hC0, hD0]
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
      intro q _
      have hnorm : ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
              + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
              + lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
        rw [hκeq]
      rw [hnorm]
      have k1 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
          + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
        (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)
      have k2 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB)
        (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
      have k3 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁) (lc0LowFix (I := I) (M := M) g₀ gB)
      linarith [k1, k2, k3]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hsplit : ∑ q ∈ Finset.range (i + 1),
        (8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2) =
        8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit]
    have hBsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 ≤ FB i := le_rfl
    have hAsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤ Fcd i := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
        lc0b_normSq_icg_lowered_eq (I := I) (M := M) g₀ g₁ q)) ?_
      exact hcdL2 i hi
    have hCsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 ≤ FC i := by
      rw [hFC_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lc0b_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC q]
      exact lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
        (connDiffSection (I := I) g₁ g₀)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) q
        (C2b q) Λcd nQ (Fcd q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛcd_nn hnQ_nn hcd0 hWB0 (hcdL2 q hq_le) (hWBsum q hq_le)
        (hC2b q)
    have hDsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 ≤ FD i := by
      rw [hFD_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lc0b_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ gB
        (lc0FixCd (I := I) (M := M) g₀ gB) hΨcD q]
      refine lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
        (lc0FixCd (I := I) (M := M) g₀ gB)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (ccTensor02Symm (I := I) (M := M) g₀ P)) q
        (C2b q) Λfx nQ (Ffx q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛfx_nn hnQ_nn hΛfx hWB0 le_rfl (hWBsum q hq_le)
        (hC2b q)
    linarith [hAsum, hCsum, hDsum, hBsum]

end LieCorr0BoundsC

section LieCorr0BoundsD

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  g0FlatCLM cotangentToDual_g0FlatCLM)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceField
  cometricDoubleTraceField_covGrad_eq_zero modelDoubleTrace_apply cometricLmodel
  cometric_dualTrace_eq_orthoFrame_diag)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_fixedField_rfns_jet (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have h : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc0 hc using h
  exact ⟨c, hc0, fun j x => hc j x⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem lc0b_normSq_le_scaled_of_pointwise (g₀ : SmoothRiemannianMetric I M)
    (r₁ s₁ r₂ s₂ : ℕ) (X : SmoothCcTensor g₀ r₁ s₁) (Y : SmoothCcTensor g₀ r₂ s₂)
    (c : ℝ) (_hc : 0 ≤ c)
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₁ s₁ x (X.toSection x) ≤
      c * riemannianFiberNormSq (I := I) (M := M) g₀ r₂ s₂ x (Y.toSection x)) :
    ‖X‖ ^ 2 ≤ c * ‖Y‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono ?_ ?_ hpt
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r₁ s₁ X
  · exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r₂ s₂ Y).const_mul c

private lemma lc0b_icg_succ_cometricDT_zero (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, lc0b_covGrad_zero]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_toModel_cons_sum_smul (_x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_toModel_cons_cons_sum_smul (_x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_orthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_g1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [cotangentToDualLinear_apply]
  exact cotangentToDual_g0FlatCLM (I := I) g₀ x v w

def lc0PureDT (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma lc0PureDT_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    lc0PureDT (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := lc0b_orthoFrame_center_repr (I := I) (M := M) g₁ x
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from metricComparisonEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [lc0b_g1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x
      (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact lc0b_toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := lc0b_toModel_cons_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := lc0b_orthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

theorem lc0b_pureDT_feed (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) s x
            ((lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ (s + 2) s q
              (lc0PureDT (I := I) (M := M) g₀ g₁ s)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lc0b_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨c0, hc0_nn, hc0⟩ := lc0b_fixedField_rfns_jet (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  have hfrpow_nn : 0 ≤ fr ^ (s + 1) := by positivity
  refine ⟨c0 0 * (fr ^ (s + 1) * Λsf),
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (c0 0 * (((q : ℝ) + 1) * (fr ^ (s + 1) * Fsf i))),
    mul_nonneg (hc0_nn 0) (mul_nonneg hfrpow_nn hΛsf_nn),
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hc0_nn 0) (mul_nonneg (by positivity)
        (mul_nonneg hfrpow_nn (hFsf_nn i)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hsfsup, hsfsum⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hid := lc0PureDT_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s
  set W : SmoothCcTensor g₀ (s + 2) (s + 2) :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) with hW_def
  have hWpt : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) ≤
      fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) := by
    intro l x
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) l x
    rw [← hfr_def] at h
    refine le_trans h ?_
    rw [← lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁]
  have hWsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x) ≤
      fr ^ (s + 1) * Λsf := by
    intro x
    have h := hWpt 0 x
    simp only [iteratedCovGrad_zero] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hsfsup x) hfrpow_nn
  have hWsum : ∀ i : ℕ, i ≤ a → ∀ l : ℕ, l ≤ i →
      ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 ≤ fr ^ (s + 1) * Fsf i := by
    intro i hi l hl
    have h1 : ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 ≤
        fr ^ (s + 1) * ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 :=
      lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) 1 (1 + l)
        (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)
        (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁))
        (fr ^ (s + 1)) hfrpow_nn (fun x => hWpt l x)
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hfrpow_nn)
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 :=
      Finset.single_le_sum (f := fun q =>
        ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2)
        (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
    exact le_trans hsingle (hsfsum i hi)
  have hpt : ∀ (q : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + q) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s q
          (lc0PureDT (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
      diagonalGridGrowthFactor (E := E) q * (c0 0 *
        ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) := by
    intro q x
    rw [hid]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ q (s + 2) (s + 2) s
      (cometricDoubleTraceField (I := I) g₀ s) W x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
    have hzero : ∀ i' ∈ Finset.range (q + 1), i' ≠ 0 →
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) = 0 := by
      intro i' _ hi'0
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
      rw [lc0b_icg_succ_cometricDT_zero (I := I) (M := M) g₀ s m]
      rw [show ((0 : SmoothCcTensor g₀ (s + 2) (s + (m + 1))).toSection x) =
          (0 : TensorRSSpace (s + 2) (s + (m + 1)) I x) from by
        rw [SmoothCcTensor.toSection_zero]; rfl]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ (s + 2) (s + (m + 1)) x]
      rw [zero_mul]
    have hsum_eq : (∑ i' ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - 0),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) := by
      refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
      intro i' hi' hi'0
      exact hzero i' hi' hi'0
    rw [hsum_eq]
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x _
    exact mul_le_mul_of_nonneg_right (hc0 0 x) hsum_nn
  refine ⟨?_, ?_⟩
  · intro x
    have h := hpt 0 x
    simp only [iteratedCovGrad_zero] at h
    have h2 : (∑ l ∈ Finset.range (0 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + 0) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) 0 W).toSection x) := by
      rw [Finset.sum_range_one]
    rw [h2] at h
    simp only [iteratedCovGrad_zero] at h
    have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x) ≤
        fr ^ (s + 1) * Λsf := hWsup x
    have happ : diagonalGridGrowthFactor (E := E) 0 = 1 := by
      rw [diagonalGridGrowthFactor, pow_zero]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) s x
          ((lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) 0 * (c0 0 *
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x)) := h
      _ = c0 0 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x
            (W.toSection x) := by rw [happ, one_mul]
      _ ≤ c0 0 * (fr ^ (s + 1) * Λsf) := mul_le_mul_of_nonneg_left h3 (hc0_nn 0)
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ i := by have := Finset.mem_range.mp hq; omega
    have hint : MeasureTheory.Integrable
        (fun x => diagonalGridGrowthFactor (E := E) q * (c0 0 *
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      refine MeasureTheory.Integrable.const_mul ?_ _
      refine MeasureTheory.Integrable.const_mul ?_ _
      exact MeasureTheory.integrable_finset_sum (Finset.range (q + 1)) fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
          (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      (s + 2) (s + q)
      (iteratedCovGrad (I := I) g₀ (s + 2) s q (lc0PureDT (I := I) (M := M) g₀ g₁ s))
      (fun x => diagonalGridGrowthFactor (E := E) q * (c0 0 *
        ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)))
      hint (fun x => hpt q x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hc0_nn 0)
    rw [MeasureTheory.integral_finset_sum (Finset.range (q + 1)) (fun l _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
        (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W))]
    have hterm : ∀ l ∈ Finset.range (q + 1),
        (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ fr ^ (s + 1) * Fsf i := by
      intro l hl
      have hleq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 :=
        (lc0b_normSq_eq_integral (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
          (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)).symm
      rw [hleq]
      exact hWsum i hi l (le_trans (by have := Finset.mem_range.mp hl; omega) hq_le)
    calc (∑ l ∈ Finset.range (q + 1),
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ ∑ l ∈ Finset.range (q + 1), fr ^ (s + 1) * Fsf i := Finset.sum_le_sum hterm
      _ = ((q : ℝ) + 1) * (fr ^ (s + 1) * Fsf i) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

end LieCorr0BoundsD

section LieCorr0BoundsE1

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (modelDoubleTrace_apply
  cometricLmodel)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_unitTensor_toModel (x : M) (m : Fin 0 → E) :
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) m = 1 := by
  rw [unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_curry_zero (x : M) (D : Tensor0SSpace 1 I x) (v0 : E) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v0 =
      (Tensor0SSpace.toModel D (fun _ : Fin 1 => v0)) • unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have h1 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v0) m =
      Tensor0SSpace.toModel D (Fin.cons v0 m) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := D) (v0 := v0) (vs := m)
  rw [h1]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    lc0b_unitTensor_toModel (I := I) (M := M) x m, smul_eq_mul, mul_one]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => j.elim0) k
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_clm_unit_smul (x : M) (s : ℕ)
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (c : ℝ) :
    A (c • unitTensor (I := I) (M := M) x) = c • A (unitTensor (I := I) (M := M) x) :=
  A.map_smul c _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lc0b_KLift_fiber_13 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D) m =
      Tensor0SSpace.toModel D (fun _ : Fin 1 => m 0) *
        Tensor0SSpace.toModel κ (Fin.tail m) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D) =
        slotExtendPointwise (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x) D from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x _ D (m 0) (Fin.tail m)]
    rw [lc0b_curry_zero (I := I) (M := M) x D (m 0)]
    rw [lc0b_clm_unit_smul (I := I) (M := M) x 3 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rfl
  rw [hLHS]
  rw [tensor0SProdKappaFib_apply (I := I) x κ D, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1
         funext k
         fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lc0b_KLift_fiber_21 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 1) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hstep1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D) =
      slotExtendPointwise (I := I) (M := M) g₀ 1 2 x
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 1 1 K).toSection x) D := rfl
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] * Tensor0SSpace.toModel κ (fun _ : Fin 1 => m 2) := by
    rw [hstep1]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x _ D (m 0) (Fin.tail m)]
    set D1 : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD1
    have hinner : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 1 1 K).toSection x) D1) =
        slotExtendPointwise (I := I) (M := M) g₀ 0 1 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x) D1 := rfl
    rw [hinner]
    rw [show (Fin.tail m : Fin 2 → E) = Fin.cons (m 1) (fun _ : Fin 1 => m 2) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 1 x _ D1 (m 1) (fun _ : Fin 1 => m 2)]
    rw [lc0b_curry_zero (I := I) (M := M) x D1 (m 1)]
    rw [lc0b_clm_unit_smul (I := I) (M := M) x 1 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD1val : Tensor0SSpace.toModel D1 (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD1]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
        (T := D) (v0 := m 0) (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD1val]
    first
      | rfl
      | (congr 1 <;>
          first
            | rfl
            | (congr 1
               funext k
               fin_cases k <;> rfl))
  rw [hLHS]
  rw [tensor0SProdKappaFib_apply (I := I) x κ D, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1
         funext k
         fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lc0b_KLift_fiber_23 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) =
        slotExtendPointwise (I := I) (M := M) g₀ 1 4 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 4 x _ D (m 0) (Fin.tail m)]
    set D1 : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD1
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D1) =
        slotExtendPointwise (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x) D1 from rfl]
    rw [show (Fin.tail m : Fin 4 → E) =
        Fin.cons (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x _ D1 (m 1)
      (fun j : Fin 3 => m (Fin.natAdd 2 j))]
    rw [lc0b_curry_zero (I := I) (M := M) x D1 (m 1)]
    rw [lc0b_clm_unit_smul (I := I) (M := M) x 3 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD1val : Tensor0SSpace.toModel D1 (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD1]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
        (T := D) (v0 := m 0) (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD1val]
    first
      | rfl
      | (congr 1 <;>
          first
            | rfl
            | (congr 1
               funext k
               fin_cases k <;> rfl))
  rw [hLHS]
  rw [tensor0SProdKappaFib_apply (I := I) x κ D, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1
         funext k
         fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lc0b_KLift_fiber_33 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 3 j)) := by
    rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) =
        slotExtendPointwise (I := I) (M := M) g₀ 2 5 x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 2 5 x _ D (m 0) (Fin.tail m)]
    set D2 : Tensor0SSpace 2 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (m 0) with hD2
    rw [lc0b_KLift_fiber_23 (I := I) (M := M) g₀ K x D2]
    rw [← hκ]
    rw [tensor0SProdKappaFib_apply (I := I) x κ D2, Tensor0SSpace.toModel_ofModel]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD2val : Tensor0SSpace.toModel D2
        ((Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD2]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
        (T := D) (v0 := m 0) (vs := (Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD2val]
    first
      | rfl
      | (congr 2
         funext j
         fin_cases j <;> rfl)
  rw [hLHS]
  rw [tensor0SProdKappaFib_apply (I := I) x κ D, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1
         funext k
         fin_cases k <;> rfl)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lc0b_kappa_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) =
      metricConnDiffLoweredFib (I := I) g₁ g₁ gB x := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0KappaField (I := I) (M := M) g₁ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma lc0b_traceStep_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (reindexCoeffGen (I := I) (M := M) g₀ (p + 2) p
        (lc0PureDT (I := I) (M := M) g₀ g₁ p) σ).toSection x) =
    lieCorr0TraceStep (I := I) g₁ p σ x := by
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (reindexCoeffGen (I := I) (M := M) g₀ (p + 2) p
        (lc0PureDT (I := I) (M := M) g₀ g₁ p) σ).toSection x) D) =
      reindexCoeffFibGen (I := I) (p + 2) p σ x
        (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
          (lc0PureDT (I := I) (M := M) g₀ g₁ p).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) (p + 2) p σ x _ D]
  rw [show ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (lc0PureDT (I := I) (M := M) g₀ g₁ p).toSection x)
      (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel D)))) =
      cometricDoubleTraceFib (I := I) g₁ p x
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel D))) from rfl]
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply]
  congr 1

end LieCorr0BoundsE1

section LieCorr0BoundsE2

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (modelDoubleTrace_apply
  cometricLmodel cometric_dualTrace_eq_orthoFrame_diag)

def lc0IVPerm : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2

noncomputable def lc0VFlat (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (lc0PureDT (I := I) (M := M) g₀ g₁ 1)
    (lc0Kappa (I := I) (M := M) g₀ g₁ gB)

omit [SigmaCompactSpace M] in
private lemma lc0b_vflat_value (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (u : E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
          (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => u) =
      g₁.inner x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x) u := by
  have hfib : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x) := by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x) =
        (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0PureDT (I := I) (M := M) g₀ g₁ 1).toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x) from rfl]
    rw [ContinuousLinearMap.comp_apply]
    rw [lc0b_kappa_fiber (I := I) (M := M) g₀ g₁ gB x]
    rfl
  rw [hfib]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 1 x]
  rw [modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x))
    (fun _ : Fin 1 => u)]
  have hterm : ∀ c : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
        (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (fun _ : Fin 1 => u))) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x
        (smoothOrthoFrame (I := I) g₁ x c x) (smoothOrthoFrame (I := I) g₁ x c x)) u := by
    intro c
    rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ gB x]
    rfl
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  rw [PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ gB x]
  rw [map_sum, ContinuousLinearMap.sum_apply]

omit [SigmaCompactSpace M] in
private lemma lc0b_iV_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (B : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
        (reindexCoeffGen (I := I) (M := M) g₀ 3 1
          (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm)
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2
          (lc0VFlat (I := I) (M := M) g₀ g₁ gB))).toSection x) B =
    Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x) B := by
  classical
  set V : TangentSpace I x :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x with hV
  set Vf : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) with hVf
  have hchain : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
        (reindexCoeffGen (I := I) (M := M) g₀ 3 1
          (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm)
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2
          (lc0VFlat (I := I) (M := M) g₀ g₁ gB))).toSection x) B) =
      lieCorr0TraceStep (I := I) g₁ 1 lc0IVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
          (reindexCoeffGen (I := I) (M := M) g₀ 3 1
            (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm)
          (slotExtendIter (I := I) (M := M) g₀ 0 1 2
            (lc0VFlat (I := I) (M := M) g₀ g₁ gB))).toSection x) B) =
        (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 3 1
            (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm).toSection x)
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 1 2
              (lc0VFlat (I := I) (M := M) g₀ g₁ gB)).toSection x) B) from rfl]
    rw [lc0b_KLift_fiber_21 (I := I) (M := M) g₀ (lc0VFlat (I := I) (M := M) g₀ g₁ gB) x B]
    rw [← hVf]
    have h := lc0b_traceStep_fiber (I := I) (M := M) g₀ g₁ 1 lc0IVPerm x
    exact congrFun (congrArg DFunLike.coe h)
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B)
  rw [hchain]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  have hLHS : Tensor0SSpace.toModel
      (lieCorr0TraceStep (I := I) g₁ 1 lc0IVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B)) w =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel B
            ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] *
          Tensor0SSpace.toModel Vf
            (fun _ : Fin 1 => (smoothOrthoFrame (I := I) g₁ x c x : E)) := by
    rw [show lieCorr0TraceStep (I := I) g₁ 1 lc0IVPerm x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B) =
        cometricDoubleTraceFib (I := I) g₁ 1 x
          (domDomCongrFibRank (I := I) 3 lc0IVPerm x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B)) from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ 1 x]
    rw [modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (domDomCongrFibRank (I := I) 3 lc0IVPerm x
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x Vf B))) w]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [domDomCongrFibRank_apply (I := I) 3 lc0IVPerm x, Tensor0SSpace.toModel_ofModel]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [tensor0SProdKappaFib_apply (I := I) x Vf B, Tensor0SSpace.toModel_ofModel]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · congr 1
      funext k
      fin_cases k <;> rfl
    · congr 1
      funext k
      fin_cases k <;> rfl
  rw [hLHS]
  have hterm : ∀ c : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel B
          ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] *
        Tensor0SSpace.toModel Vf
          (fun _ : Fin 1 => (smoothOrthoFrame (I := I) g₁ x c x : E)) =
      (g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V) *
        Tensor0SSpace.toModel B
          ![(smoothOrthoFrame (I := I) g₁ x c x : E), w 0] := by
    intro c
    rw [hVf, lc0b_vflat_value (I := I) (M := M) g₀ g₁ gB x
      ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)]
    rw [← hV]
    rw [g₁.symm x V (smoothOrthoFrame (I := I) g₁ x c x)]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  have hRHS : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V B) w =
      Tensor0SSpace.toModel B (Fin.cons (show E from V) (fun k => (show E from w k))) :=
    lc0b_interior_product_toModel_eval (I := I) (M := M) 1 x V B w
  rw [hRHS]
  have hrepr := lc0b_orthoFrame_center_repr (I := I) (M := M) g₁ x V
  have hexp : Tensor0SSpace.toModel B (Fin.cons (show E from V) (fun k => (show E from w k))) =
      ∑ c : Fin (Module.finrank ℝ E),
        (g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V) *
          Tensor0SSpace.toModel B
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (fun k => (show E from w k))) := by
    have hsum := lc0b_toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel B)
      (Module.finrank ℝ E)
      (fun c => g₁.inner x (smoothOrthoFrame (I := I) g₁ x c x) V)
      (fun c => ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E))
      (fun k => (show E from w k))
    rw [← hsum]
    exact congrArg (fun t : TangentSpace I x =>
      Tensor0SSpace.toModel B (Fin.cons (show E from t) (fun k => (show E from w k)))) hrepr
  rw [hexp]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  congr 1
  funext k
  fin_cases k <;> rfl

noncomputable def lc0NEndoSec (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ⟨fun x : M => lieCorr0NEndo (I := I) g₀ g₁ g_bg x,
    lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg⟩

noncomputable def lc0IVField (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
    (reindexCoeffGen (I := I) (M := M) g₀ 3 1
      (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm)
    (slotExtendIter (I := I) (M := M) g₀ 0 1 2 (lc0VFlat (I := I) (M := M) g₀ g₁ gB))

noncomputable def lc0CdVField (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 1 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 1 (lc0IVField (I := I) (M := M) g₀ g₁ gB)
    (connDiffSection (I := I) g₁ g₀)

omit [SigmaCompactSpace M] in
private lemma lc0b_cdV_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) om =
    slotInsertEndoFib (I := I) (M := M) 1 0 x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x)) om := by
  set V : TangentSpace I x :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Π b : M, TangentSpace I b) x with hV
  have hstep : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) om) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V
        (connDiffFib (I := I) g₁ g₀ x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) om) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
          (lc0IVField (I := I) (M := M) g₀ g₁ gB).toSection x)
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (connDiffSection (I := I) g₁ g₀).toSection x) om) from rfl]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) om from rfl]
    exact lc0b_iV_fiber (I := I) (M := M) g₀ g₁ gB x
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om)
  rw [hstep]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [lc0b_interior_product_toModel_eval (I := I) (M := M) 1 x V
    (connDiffFib (I := I) g₁ g₀ x om) w]
  rw [slotInsertEndoFib_apply_eval]
  have hLHS : Tensor0SSpace.toModel (connDiffFib (I := I) g₁ g₀ x om)
      (Fin.cons (show E from V) (fun k => (show E from w k))) =
      om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x V (w 0)) := by
    rw [show Tensor0SSpace.toModel (connDiffFib (I := I) g₁ g₀ x om)
        (Fin.cons (show E from V) (fun k => (show E from w k))) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) g₁ g₀ x) om)
          (Fin.cons V (fun k => w k)) from rfl]
    rw [connDiffFib_apply_eval (I := I) g₁ g₀ x om (Fin.cons V (fun k => w k))]
    congr 1
  rw [hLHS]
  rw [lc0b_toModel_om_single (I := I) (M := M) x om
    (Function.update (fun k => (show E from w k)) 0
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x V ((fun k => (show E from w k)) 0)))]
  rw [Function.update_self]
  rw [show (om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x V (w 0)) : ℝ) =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x V (w 0)) from
    (cotangentToDual_apply (I := I) om _).symm]

end LieCorr0BoundsE2

section LieCorr0BoundsE3

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (modelDoubleTrace_apply
  cometricLmodel)

noncomputable def lc0Tr (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) : SmoothCcTensor g₀ (p + 2) p :=
  reindexCoeffGen (I := I) (M := M) g₀ (p + 2) p (lc0PureDT (I := I) (M := M) g₀ g₁ p) σ

def lc0SwapOutPerm : Equiv.Perm (Fin 4) :=
  ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_swapOut_traceStep (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) (Z : Tensor0SSpace 4 I x) :
    domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x
      (lieCorr0TraceStep (I := I) g₁ 2 σ x Z) =
    lieCorr0TraceStep (I := I) g₁ 2 (lc0SwapOutPerm * σ) x Z := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [domDomCongrFibRank_apply (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show lieCorr0TraceStep (I := I) g₁ 2 σ x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 σ x Z) from rfl]
  rw [show lieCorr0TraceStep (I := I) g₁ 2 (lc0SwapOutPerm * σ) x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 (lc0SwapOutPerm * σ) x Z) from rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x, cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x),
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [domDomCongrFibRank_apply (I := I) 4 σ x Z, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [domDomCongrFibRank_apply (I := I) 4 (lc0SwapOutPerm * σ) x Z, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  have hpt : ∀ t : Fin 4,
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k)
          (fun j : Fin 2 => w ((Equiv.swap (0 : Fin 2) 1) j))) : Fin 4 → E) t =
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) w) : Fin 4 → E) (lc0SwapOutPerm t) := by
    intro t
    fin_cases t <;> rfl
  rw [hpt (σ i)]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lc0RiemRest_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 4 ℝ E)
        (E := fun z : M => TensorRSSpace 2 4 I z) x
        (TensorRSSpace.ofCLM
          ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x))))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => (lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorr0RiemLoweredFib (I := I) g₀ x)))
  intro Y
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorr0RiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorr0RiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr1 := lieCorr0TraceStep_section_contMDiff (I := I) g₀ 4 lieCorr0RiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))
    hprod
  refine htr1.congr (fun x => ?_)
  rfl

noncomputable def lc0RiemRestField (g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from TensorRSSpace.ofCLM
          ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x))))
      contMDiff_toFun := lc0RiemRest_contMDiff (I := I) (M := M) g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

noncomputable def lc0InsertField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)
    + reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1)

noncomputable def lc0VBField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
      (lc0IVField (I := I) (M := M) g₀ g₁ g₀))

noncomputable def lc0AMixHalfField (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (lc0Tr (I := I) (M := M) g₀ g₁ 2 σlast)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))))

noncomputable def lc0AMixField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) • (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2
    + lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2))

noncomputable def lc0RiemField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2) (lc0RiemRestField (I := I) (M := M) g₀)

omit [SigmaCompactSpace M] in
private lemma lc0b_vb_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0VBField (I := I) (M := M) g₀ g₁).toSection x) D =
    lieCorr0VBFib (I := I) g₀ g₁ x D := by
  have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0VBField (I := I) (M := M) g₀ g₁).toSection x) D) =
      (2 : ℝ) • ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)).toSection x)
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
            (lc0IVField (I := I) (M := M) g₀ g₁ g₀).toSection x) D))) := rfl
  rw [h1]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0IVField (I := I) (M := M) g₀ g₁ g₀).toSection x) D) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D from
    lc0b_iV_fiber (I := I) (M := M) g₀ g₁ g₀ x D]
  rw [lc0b_KLift_fiber_13 (I := I) (M := M) g₀ (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) x _]
  rw [lc0b_kappa_fiber (I := I) (M := M) g₀ g₁ g₀ x]
  have h2 := lc0b_traceStep_fiber (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm x
  rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm).toSection x)
      (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D))) =
      lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
        (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D)) from
    congrFun (congrArg DFunLike.coe h2) _]
  rw [show lieCorr0VBFib (I := I) g₀ g₁ x D =
      (2 : ℝ) • (lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
        ((tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x))
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D))) from by
    rw [lieCorr0VBFib]
    rw [ContinuousLinearMap.smul_apply]
    rfl]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lc0b_amixhalf_fiber (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg σlast).toSection x) D =
    lieCorr0TraceStep (I := I) g₁ 2 σlast x
      ((lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x)
        ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
          ((lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x)
            ((tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
                (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)) D)))) := by
  have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg σlast).toSection x) D) =
      ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0Tr (I := I) (M := M) g₀ g₁ 2 σlast).toSection x)
        ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
          (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1).toSection x)
          ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
            ((show Tensor0SSpace 5 I x →L[ℝ] Tensor0SSpace 3 I x from
              (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ).toSection x)
              ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
                (slotExtendIter (I := I) (M := M) g₀ 0 3 2
                  (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)).toSection x) D))))) := rfl
  rw [h1]
  rw [lc0b_KLift_fiber_23 (I := I) (M := M) g₀ (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) x D]
  rw [lc0b_kappa_fiber (I := I) (M := M) g₀ g₁ g₀ x]
  rw [show ((show Tensor0SSpace 5 I x →L[ℝ] Tensor0SSpace 3 I x from
      (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ).toSection x)
      ((tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)) D)) =
      lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
        ((tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)) D) from
    congrFun (congrArg DFunLike.coe
      (lc0b_traceStep_fiber (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ x)) _]
  rw [lc0b_KLift_fiber_33 (I := I) (M := M) g₀ (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg) x _]
  rw [lc0b_kappa_fiber (I := I) (M := M) g₀ g₁ g_bg x]
  rw [show ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
      (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1).toSection x)
      ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
        (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
          ((tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
              (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)) D)))) =
      lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
        ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
          (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
            ((tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
                (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)) D))) from
    congrFun (congrArg DFunLike.coe
      (lc0b_traceStep_fiber (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1 x)) _]
  exact congrFun (congrArg DFunLike.coe
    (lc0b_traceStep_fiber (I := I) (M := M) g₀ g₁ 2 σlast x)) _

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lc0b_amix_fiber (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
    lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D := by
  have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
      (2 : ℝ) • (((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2).toSection x) D) +
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg
            (lc0SwapOutPerm * lieCorr0AMixPerm2)).toSection x) D)) := rfl
  rw [h1]
  rw [lc0b_amixhalf_fiber (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2 x D]
  rw [lc0b_amixhalf_fiber (I := I) (M := M) g₀ g₁ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2) x D]
  rw [← lc0b_swapOut_traceStep (I := I) (M := M) g₁ lieCorr0AMixPerm2 x _]
  rw [show lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D =
      (2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D +
        (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x)
          (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D)) from by
    rw [lieCorr0AMixFib]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply]]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma lc0b_riem_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0RiemField (I := I) (M := M) g₀ g₁).toSection x) D =
    lieCorr0RiemFib (I := I) g₀ g₁ x D := by
  have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0RiemField (I := I) (M := M) g₀ g₁).toSection x) D) =
      (-1 : ℝ) • ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2).toSection x)
        ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x)
          ((tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x)) D))) := rfl
  rw [h1]
  rw [show ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2).toSection x)
      ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x)
        ((tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
            (lieCorr0RiemLoweredFib (I := I) g₀ x)) D))) =
      lieCorr0TraceStep (I := I) g₁ 2 lieCorr0RiemPerm2 x
        ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x)
          ((tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x)) D)) from
    congrFun (congrArg DFunLike.coe
      (lc0b_traceStep_fiber (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2 x)) _]
  rw [show lieCorr0RiemFib (I := I) g₀ g₁ x D =
      (-1 : ℝ) • (lieCorr0TraceStep (I := I) g₁ 2 lieCorr0RiemPerm2 x
        ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x)
          ((tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x)) D))) from by
    rw [lieCorr0RiemFib]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_insert_fiber (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) m =
    Tensor0SSpace.toModel (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D) m := by
  have hsplit : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D) +
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) := rfl
  rw [hsplit, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [lieCorr0InsertFib_toModel (I := I) g₀ g₁ g_bg x D m]
  have hterm1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D) m =
      Tensor0SSpace.toModel D
        (Function.update m 0 (lieCorr0NEndo (I := I) g₀ g₁ g_bg x (m 0))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D) =
        slotInsertEndoFib (I := I) (M := M) 2 0 x
          (lieCorr0NEndo (I := I) g₀ g₁ g_bg x) D from rfl]
    rw [slotInsertEndoFib_apply_eval]
  have hterm2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel D
        (Function.update m 1 (lieCorr0NEndo (I := I) g₀ g₁ g_bg x (m 1))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))).toSection x) D from rfl]
    rw [reindexCoeffFibGen_apply (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x _ D]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) =
        tensorRS_domDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
          ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
      ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) =
        slotInsertEndoFib (I := I) (M := M) 2 0 x
          (lieCorr0NEndo (I := I) g₀ g₁ g_bg x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
      (lieCorr0NEndo (I := I) g₀ g₁ g_bg x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))
      (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
    rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    have harg : (fun k => Function.update (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
          (lieCorr0NEndo (I := I) g₀ g₁ g_bg x
            ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
          ((Equiv.swap (0 : Fin 2) 1) k))
        = Function.update m 1 (lieCorr0NEndo (I := I) g₀ g₁ g_bg x (m 1)) := by
      funext k
      have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := Equiv.swap_apply_left 0 1
      have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := Equiv.swap_apply_right 0 1
      simp only [Function.update_apply]
      rw [hswap0, Equiv.swap_apply_self]
      have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
        apply propext
        constructor
        · intro h
          have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
          rwa [Equiv.swap_apply_self, hswap0] at h2
        · intro h
          rw [h, hswap1]
      simp only [hcond]
    rw [harg]
  rw [hterm1, hterm2]

theorem lc0b_total_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg =
      lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁
        + lc0AMixField (I := I) (M := M) g₀ g₁ g_bg + lc0RiemField (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have hRHS : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁
        + lc0AMixField (I := I) (M := M) g₀ g₁ g_bg
        + lc0RiemField (I := I) (M := M) g₀ g₁).toSection x)) D) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) +
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0VBField (I := I) (M := M) g₀ g₁).toSection x) D) +
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) +
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0RiemField (I := I) (M := M) g₀ g₁).toSection x) D) := rfl
  have hLHS : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
      lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D + lieCorr0VBFib (I := I) g₀ g₁ x D
        + lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D + lieCorr0RiemFib (I := I) g₀ g₁ x D := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
        lieCorr0TotalFib (I := I) g₀ g₁ g_bg x D from rfl]
    rw [lieCorr0TotalFib]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.add_apply]
  rw [hRHS, hLHS]
  rw [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add,
    Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  rw [lc0b_insert_fiber (I := I) (M := M) g₀ g₁ g_bg x D m]
  rw [lc0b_vb_fiber (I := I) (M := M) g₀ g₁ x D]
  rw [lc0b_amix_fiber (I := I) (M := M) g₀ g₁ g_bg x D]
  rw [lc0b_riem_fiber (I := I) (M := M) g₀ g₁ x D]

end LieCorr0BoundsE3

section LieCorr0BoundsF1

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lc0b_rfns_neg (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_icg_sub (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s q (A - B) =
      iteratedCovGrad (I := I) g r s q A - iteratedCovGrad (I := I) g r s q B := by
  rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, sub_eq_add_neg]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_normSq_icg_sub_le (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q (A - B)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g r s q A‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g r s q B‖ ^ 2 := by
  have h := lc0b_normSq_icg_add_le (I := I) (M := M) g r s q A (-B)
  rw [show A + -B = A - B from (sub_eq_add_neg A B).symm] at h
  rw [iteratedCovGrad_neg, norm_neg] at h
  exact h

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_rfns_toSection_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((A - B).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x (B.toSection x) := by
  rw [show (A - B).toSection x = A.toSection x + (-(B.toSection x)) from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r s x _ _) ?_
  rw [lc0b_rfns_neg (I := I) (M := M) g r s x (B.toSection x)]

omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_rfns_icg_reindex_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ : Equiv.Perm (Fin r)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + q) x
        ((iteratedCovGrad (I := I) g₀ r s q
          (reindexCoeffGen (I := I) (M := M) g₀ r s R σ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + q) x
        ((iteratedCovGrad (I := I) g₀ r s q R).toSection x) := by
  rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ r s R σ q]
  rw [reindexCoeffGen_toSection]
  exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ r (s + q) x σ _

omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_normSq_icg_reindex_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ : Equiv.Perm (Fin r)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ r s q (reindexCoeffGen (I := I) (M := M) g₀ r s R σ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s q R‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lc0b_rfns_icg_reindex_eq (I := I) (M := M) g₀ r s R σ q x

private lemma lc0b_rfns_icg_slotExtendIter_le (g₀ : SmoothRiemannianMetric I M)
    (b₀ s₀ : ℕ) (w : ℕ) (K : SmoothCcTensor g₀ b₀ s₀) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (b₀ + w) ((s₀ + w) + q) x
        ((iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
          (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + q) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ q K).toSection x) := by
  induction w with
  | zero =>
      rw [pow_zero, one_mul]
      exact le_rfl
  | succ w ih =>
      have hstep := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ (b₀ + w) (s₀ + w)
        (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K) q x
      have hmul : (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ (b₀ + w) ((s₀ + w) + q) x
            ((iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
              (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)).toSection x) ≤
          (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) ^ w *
            riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + q) x
              ((iteratedCovGrad (I := I) g₀ b₀ s₀ q K).toSection x)) :=
        mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)
      refine le_trans hstep (le_trans hmul (le_of_eq ?_))
      rw [pow_succ]
      ring

private lemma lc0b_normSq_icg_slotExtendIter_le (g₀ : SmoothRiemannianMetric I M)
    (b₀ s₀ : ℕ) (w : ℕ) (K : SmoothCcTensor g₀ b₀ s₀) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
        (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ w * ‖iteratedCovGrad (I := I) g₀ b₀ s₀ q K‖ ^ 2 :=
  lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀ (b₀ + w) ((s₀ + w) + q) b₀ (s₀ + q)
    (iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
      (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K))
    (iteratedCovGrad (I := I) g₀ b₀ s₀ q K)
    ((Module.finrank ℝ E : ℝ) ^ w) (by positivity)
    (fun x => lc0b_rfns_icg_slotExtendIter_le (I := I) (M := M) g₀ b₀ s₀ w K q x)

lemma lc0b_NEndoIns_decomp (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg) =
      lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg
        - DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert
            (I := I) (M := M) g₀ g₁ g₀ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      ((lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg
        - DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert
            (I := I) (M := M) g₀ g₁ g₀).toSection x)) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀).toSection x) om) -
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg).toSection x) om) -
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert
          (I := I) (M := M) g₀ g₁ g₀).toSection x) om) := rfl
  rw [hRHS]
  rw [lc0b_cdV_fiber (I := I) (M := M) g₀ g₁ g₀ x om,
    lc0b_cdV_fiber (I := I) (M := M) g₀ g₁ g_bg x om]
  have hWfib : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert
        (I := I) (M := M) g₀ g₁ g₀).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x (deTurckLieWEndo (I := I) g₁ g₀ x) om := rfl
  rw [hWfib]
  have hLHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (lieCorr0NEndo (I := I) g₀ g₁ g_bg x) om := rfl
  rw [hLHS]
  rw [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  rw [lc0b_toModel_om_single (I := I) (M := M) x om _,
    lc0b_toModel_om_single (I := I) (M := M) x om _,
    lc0b_toModel_om_single (I := I) (M := M) x om _,
    lc0b_toModel_om_single (I := I) (M := M) x om _]
  rw [Function.update_self, Function.update_self, Function.update_self, Function.update_self]
  rw [show lieCorr0NEndo (I := I) g₀ g₁ g_bg x (w 0) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (w 0)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x) (w 0)
        - deTurckLieWEndo (I := I) g₁ g₀ x (w 0) from by
    rw [lieCorr0NEndo]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]]
  rw [show cotangentToDual (I := I) (x := x) om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (w 0)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x) (w 0)
        - deTurckLieWEndo (I := I) g₁ g₀ x (w 0)) =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (w 0))
      - cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x) (w 0))
      - cotangentToDual (I := I) (x := x) om
          (deTurckLieWEndo (I := I) g₁ g₀ x (w 0)) from by
    rw [show cotangentToDual (I := I) (x := x) om =
        (cotangentToDualLinear (I := I) (x := x) om : TangentSpace I x →ₗ[ℝ] ℝ) from rfl]
    rw [map_sub, map_sub]]

end LieCorr0BoundsF1

section LieCorr0BoundsF2

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

theorem lc0b_comp_feed_step (g₀ : SmoothRiemannianMetric I M)
    (p a b : ℕ) (amax : ℕ)
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
    (ΛΦ ΛW : ℝ) (FΦ FW : ℕ → ℝ) (hΛΦ : 0 ≤ ΛΦ) (hΛW : 0 ≤ ΛW)
    (hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) ≤ ΛΦ)
    (hW0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (W.toSection x) ≤ ΛW)
    (hFΦ : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ a b q Φ‖ ^ 2 ≤ FΦ i)
    (hFW : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ p a q W‖ ^ 2 ≤ FW i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p b x
        ((ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W).toSection x) ≤ ΛΦ * ΛW) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ p b q (ccOperatorFieldComp (I := I) (M := M) g₀ p a b Φ W)‖ ^ 2 ≤
      ∑ q ∈ Finset.range (i + 1),
        diagonalGridGrowthFactor (E := E) q * (C2 q * (ΛW * FΦ q + ΛΦ * FW q))) := by
  constructor
  · intro x
    rw [appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ p a b x
      (show TensorRSSpace a b I x from Φ.toSection x)
      (show TensorRSSpace p a I x from W.toSection x)) ?_
    exact mul_le_mul (hΦ0 x) (hW0 x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ p a x _) hΛΦ
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ amax := by have := Finset.mem_range.mp hq; omega
    exact lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ p a b Φ W q
      (C2 q) ΛΦ ΛW (FΦ q) (FW q) (hC2_nn q) hΛΦ hΛW hΦ0 hW0
      (hFΦ q hq_le) (hFW q hq_le) (htwo q)

omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_reindex_feed_transfer (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ : Equiv.Perm (Fin r)) (Λ : ℝ) (F : ℕ → ℝ) (amax : ℕ)
    (h0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (R.toSection x) ≤ Λ)
    (hF : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q R‖ ^ 2 ≤ F i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((reindexCoeffGen (I := I) (M := M) g₀ r s R σ).toSection x) ≤ Λ) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ r s q
          (reindexCoeffGen (I := I) (M := M) g₀ r s R σ)‖ ^ 2 ≤ F i) := by
  constructor
  · intro x
    have h := lc0b_rfns_icg_reindex_eq (I := I) (M := M) g₀ r s R σ 0 x
    simp only [iteratedCovGrad_zero] at h
    exact le_of_eq_of_le h (h0 x)
  · intro i hi
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
      lc0b_normSq_icg_reindex_eq (I := I) (M := M) g₀ r s R σ q)) (hF i hi)

theorem lc0b_slotExtendIter_feed_transfer (g₀ : SmoothRiemannianMetric I M)
    (b₀ s₀ w : ℕ) (K : SmoothCcTensor g₀ b₀ s₀) (Λ : ℝ) (F : ℕ → ℝ) (amax : ℕ)
    (h0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (K.toSection x) ≤ Λ)
    (hF : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ b₀ s₀ q K‖ ^ 2 ≤ F i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (b₀ + w) (s₀ + w) x
        ((slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ w * Λ) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
          (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ w * F i) := by
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ w := by positivity
  constructor
  · intro x
    have h := lc0b_rfns_icg_slotExtendIter_le (I := I) (M := M) g₀ b₀ s₀ w K 0 x
    simp only [iteratedCovGrad_zero] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (h0 x) hfr_nn
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ (b₀ + w) (s₀ + w) q
          (slotExtendIter (I := I) (M := M) g₀ b₀ s₀ w K)‖ ^ 2 ≤
        (Module.finrank ℝ E : ℝ) ^ w * ‖iteratedCovGrad (I := I) g₀ b₀ s₀ q K‖ ^ 2 :=
      fun q _ => lc0b_normSq_icg_slotExtendIter_le (I := I) (M := M) g₀ b₀ s₀ w K q
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hF i hi) hfr_nn

theorem lc0b_vflat_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x
            ((lc0VFlat (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 1 q
              (lc0VFlat (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt, Fdt, hΛdt_nn, hFdt_nn, hdt⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 1 a ha_super hR hδ₀
  obtain ⟨Λκ, Fκ, hΛκ_nn, hFκ_nn, hκ⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 0 1 3
  refine ⟨Λdt * Λκ,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λκ * Fdt q + Λdt * Fκ q)),
    mul_nonneg hΛdt_nn hΛκ_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛκ_nn (hFdt_nn q))
        (mul_nonneg hΛdt_nn (hFκ_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt0, hdtL2⟩ := hdt g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ0, hκL2⟩ := hκ g₁ P htie hδ_le hδ0 hδ hPball
  exact lc0b_comp_feed_step (I := I) (M := M) g₀ 0 3 1 a
    (lc0PureDT (I := I) (M := M) g₀ g₁ 1) (lc0Kappa (I := I) (M := M) g₀ g₁ gB)
    C2 hC2_nn hC2 Λdt Λκ Fdt Fκ hΛdt_nn hΛκ_nn hdt0 hκ0 hdtL2 hκL2

theorem lc0b_iVField_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 1 x
            ((lc0IVField (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 1 q
              (lc0IVField (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt, Fdt, hΛdt_nn, hFdt_nn, hdt⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 1 a ha_super hR hδ₀
  obtain ⟨Λvf, Fvf, hΛvf_nn, hFvf_nn, hvf⟩ :=
    lc0b_vflat_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 2 1 3
  set fr2 : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 with hfr2
  have hfr2_nn : 0 ≤ fr2 := by positivity
  refine ⟨Λdt * (fr2 * Λvf),
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * ((fr2 * Λvf) * Fdt q + Λdt * (fr2 * Fvf q))),
    mul_nonneg hΛdt_nn (mul_nonneg hfr2_nn hΛvf_nn),
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg
        (mul_nonneg (mul_nonneg hfr2_nn hΛvf_nn) (hFdt_nn q))
        (mul_nonneg hΛdt_nn (mul_nonneg hfr2_nn (hFvf_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt0, hdtL2⟩ := hdt g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hvf0, hvfL2⟩ := hvf g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hre0, hreL2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 3 1
    (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm Λdt Fdt a hdt0 hdtL2
  obtain ⟨hse0, hseL2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 1 2
    (lc0VFlat (I := I) (M := M) g₀ g₁ gB) Λvf Fvf a hvf0 hvfL2
  exact lc0b_comp_feed_step (I := I) (M := M) g₀ 2 3 1 a
    (reindexCoeffGen (I := I) (M := M) g₀ 3 1 (lc0PureDT (I := I) (M := M) g₀ g₁ 1) lc0IVPerm)
    (slotExtendIter (I := I) (M := M) g₀ 0 1 2 (lc0VFlat (I := I) (M := M) g₀ g₁ gB))
    C2 hC2_nn hC2 Λdt (fr2 * Λvf) Fdt (fun q => fr2 * Fvf q) hΛdt_nn
    (mul_nonneg hfr2_nn hΛvf_nn) hre0 hse0 hreL2 hseL2

theorem lc0b_cdVField_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((lc0CdVField (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q
              (lc0CdVField (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λiv, Fiv, hΛiv_nn, hFiv_nn, hiv⟩ :=
    lc0b_iVField_feed (I := I) (M := M) g₀ gB a ha_super hR hδ₀
  obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
    lc0b_cds_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 2 1 1 2
  refine ⟨Λiv * Λcd,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λcd * Fiv q + Λiv * Fcd q)),
    mul_nonneg hΛiv_nn hΛcd_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛcd_nn (hFiv_nn q))
        (mul_nonneg hΛiv_nn (hFcd_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hiv0, hivL2⟩ := hiv g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hcd0, hcdL2⟩ := hcd g₁ P htie hδ_le hδ0 hδ hPball
  exact lc0b_comp_feed_step (I := I) (M := M) g₀ 1 2 1 a
    (lc0IVField (I := I) (M := M) g₀ g₁ gB) (connDiffSection (I := I) g₁ g₀)
    C2 hC2_nn hC2 Λiv Λcd Fiv Fcd hΛiv_nn hΛcd_nn hiv0 hcd0 hivL2 hcdL2

end LieCorr0BoundsF2

section LieCorr0BoundsF3

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_smul_feed_transfer (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (F : SmoothCcTensor g₀ r s) (Λ : ℝ) (Fn : ℕ → ℝ) (amax : ℕ)
    (h0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (F.toSection x) ≤ Λ)
    (hF : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q F‖ ^ 2 ≤ Fn i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((c • F).toSection x) ≤
      c ^ 2 * Λ) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q (c • F)‖ ^ 2 ≤
      c ^ 2 * Fn i) := by
  have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
  constructor
  · intro x
    rw [show (c • F).toSection x = c • (F.toSection x) from rfl]
    rw [lc0b_rfns_smul (I := I) (M := M) g₀ r s x c (F.toSection x)]
    exact mul_le_mul_of_nonneg_left (h0 x) hc2
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ r s q (c • F)‖ ^ 2 =
        c ^ 2 * ‖iteratedCovGrad (I := I) g₀ r s q F‖ ^ 2 := by
      intro q _
      rw [lc0b_icg_smul (I := I) (M := M) g₀ r s q c F, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hF i hi) hc2

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_add_feed_transfer (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g₀ r s) (ΛA ΛB : ℝ) (FA FB : ℕ → ℝ) (amax : ℕ)
    (hA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (A.toSection x) ≤ ΛA)
    (hB0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x (B.toSection x) ≤ ΛB)
    (hFA : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q A‖ ^ 2 ≤ FA i)
    (hFB : ∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q B‖ ^ 2 ≤ FB i) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((A + B).toSection x) ≤
      2 * ΛA + 2 * ΛB) ∧
    (∀ i : ℕ, i ≤ amax →
      ∑ q ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ r s q (A + B)‖ ^ 2 ≤
      2 * FA i + 2 * FB i) := by
  constructor
  · intro x
    refine le_trans (lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ r s A B x) ?_
    have h1 := hA0 x
    have h2 := hB0 x
    linarith
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ r s q (A + B)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ r s q A‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ r s q B‖ ^ 2 :=
      fun q _ => lc0b_normSq_icg_add_le (I := I) (M := M) g₀ r s q A B
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hFA i hi) (by norm_num : (0:ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left (hFB i hi) (by norm_num : (0:ℝ) ≤ 2)
    linarith

private theorem lc0b_vbField_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0VBField (I := I) (M := M) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt2, Fdt2, hΛdt2_nn, hFdt2_nn, hdt2⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λκ, Fκ, hΛκ_nn, hFκ_nn, hκ⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Λiv, Fiv, hΛiv_nn, hFiv_nn, hiv⟩ :=
    lc0b_iVField_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨C2i, hC2i_nn, hC2i⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 2 4 1
  obtain ⟨C2o, hC2o_nn, hC2o⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set ΛK : ℝ := fr ^ 1 * Λκ with hΛK
  have hΛK_nn : 0 ≤ ΛK := mul_nonneg (by positivity) hΛκ_nn
  set FK : ℕ → ℝ := fun q => fr ^ 1 * Fκ q with hFK
  have hFK_nn : ∀ q, 0 ≤ FK q := fun q => mul_nonneg (by positivity) (hFκ_nn q)
  set Λin : ℝ := ΛK * Λiv with hΛin
  have hΛin_nn : 0 ≤ Λin := mul_nonneg hΛK_nn hΛiv_nn
  set Fin' : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2i q * (Λiv * FK q + ΛK * Fiv q)) with hFin'
  have hFin'_nn : ∀ i, 0 ≤ Fin' i := fun i =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2i_nn q) (add_nonneg (mul_nonneg hΛiv_nn (hFK_nn q))
        (mul_nonneg hΛK_nn (hFiv_nn q))))
  refine ⟨(2 : ℝ) ^ 2 * (Λdt2 * Λin),
    fun i => (2 : ℝ) ^ 2 * ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2o q * (Λin * Fdt2 q + Λdt2 * Fin' q)),
    by positivity,
    fun i => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
        (mul_nonneg (hC2o_nn q) (add_nonneg (mul_nonneg hΛin_nn (hFdt2_nn q))
          (mul_nonneg hΛdt2_nn (hFin'_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt20, hdt2L2⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ0, hκL2⟩ := hκ g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hiv0, hivL2⟩ := hiv g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hK0, hKL2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 1
    (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) Λκ Fκ a hκ0 hκL2
  obtain ⟨hin0, hinL2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 1 4 a
    (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
    (lc0IVField (I := I) (M := M) g₀ g₁ g₀)
    C2i hC2i_nn hC2i ΛK Λiv FK Fiv hΛK_nn hΛiv_nn hK0 hiv0 hKL2 hivL2
  obtain ⟨htr0, htrL2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
    (lc0PureDT (I := I) (M := M) g₀ g₁ 2) lieCorr0VBPerm Λdt2 Fdt2 a hdt20 hdt2L2
  obtain ⟨hout0, houtL2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 4 2 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
      (lc0IVField (I := I) (M := M) g₀ g₁ g₀))
    C2o hC2o_nn hC2o Λdt2 Λin Fdt2 Fin' hΛdt2_nn hΛin_nn htr0 hin0 htrL2 hinL2
  obtain ⟨hs0, hsL2⟩ := lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (2 : ℝ)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0VBPerm)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
        (lc0IVField (I := I) (M := M) g₀ g₁ g₀)))
    (Λdt2 * Λin)
    (fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2o q * (Λin * Fdt2 q + Λdt2 * Fin' q)))
    a hout0 houtL2
  exact ⟨hs0, hsL2⟩

theorem lc0b_amixHalf_feed (g₀ g_bg : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg σlast).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg σlast)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt2, Fdt2, hΛdt2_nn, hFdt2_nn, hdt2⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λdt3, Fdt3, hΛdt3_nn, hFdt3_nn, hdt3⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 3 a ha_super hR hδ₀
  obtain ⟨Λdt4, Fdt4, hΛdt4_nn, hFdt4_nn, hdt4⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 4 a ha_super hR hδ₀
  obtain ⟨Λκ0, Fκ0, hΛκ0_nn, hFκ0_nn, hκ0f⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Λκb, Fκb, hΛκb_nn, hFκb_nn, hκbf⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨C2a, hC2a_nn, hC2a⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 5 2 3 5
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 3 2 6 3
  obtain ⟨C2c, hC2c_nn, hC2c⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 6 2 4 6
  obtain ⟨C2d, hC2d_nn, hC2d⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  set ΛK0 : ℝ := fr ^ 2 * Λκ0 with hΛK0
  have hΛK0_nn : 0 ≤ ΛK0 := mul_nonneg (by positivity) hΛκ0_nn
  set FK0 : ℕ → ℝ := fun q => fr ^ 2 * Fκ0 q with hFK0
  have hFK0_nn : ∀ q, 0 ≤ FK0 q := fun q => mul_nonneg (by positivity) (hFκ0_nn q)
  set ΛKb : ℝ := fr ^ 3 * Λκb with hΛKb
  have hΛKb_nn : 0 ≤ ΛKb := mul_nonneg (by positivity) hΛκb_nn
  set FKb : ℕ → ℝ := fun q => fr ^ 3 * Fκb q with hFKb
  have hFKb_nn : ∀ q, 0 ≤ FKb q := fun q => mul_nonneg (by positivity) (hFκb_nn q)
  set Λ1 : ℝ := Λdt3 * ΛK0 with hΛ1
  have hΛ1_nn : 0 ≤ Λ1 := mul_nonneg hΛdt3_nn hΛK0_nn
  set F1 : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2a q * (ΛK0 * Fdt3 q + Λdt3 * FK0 q)) with hF1
  have hF1_nn : ∀ i, 0 ≤ F1 i := fun i =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2a_nn q) (add_nonneg (mul_nonneg hΛK0_nn (hFdt3_nn q))
        (mul_nonneg hΛdt3_nn (hFK0_nn q))))
  set Λ2 : ℝ := ΛKb * Λ1 with hΛ2
  have hΛ2_nn : 0 ≤ Λ2 := mul_nonneg hΛKb_nn hΛ1_nn
  set F2 : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2b q * (Λ1 * FKb q + ΛKb * F1 q)) with hF2
  have hF2_nn : ∀ i, 0 ≤ F2 i := fun i =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hΛ1_nn (hFKb_nn q))
        (mul_nonneg hΛKb_nn (hF1_nn q))))
  set Λ3 : ℝ := Λdt4 * Λ2 with hΛ3
  have hΛ3_nn : 0 ≤ Λ3 := mul_nonneg hΛdt4_nn hΛ2_nn
  set F3 : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    diagonalGridGrowthFactor (E := E) q * (C2c q * (Λ2 * Fdt4 q + Λdt4 * F2 q)) with hF3
  have hF3_nn : ∀ i, 0 ≤ F3 i := fun i =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2c_nn q) (add_nonneg (mul_nonneg hΛ2_nn (hFdt4_nn q))
        (mul_nonneg hΛdt4_nn (hF2_nn q))))
  refine ⟨Λdt2 * Λ3,
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2d q * (Λ3 * Fdt2 q + Λdt2 * F3 q)),
    mul_nonneg hΛdt2_nn hΛ3_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2d_nn q) (add_nonneg (mul_nonneg hΛ3_nn (hFdt2_nn q))
        (mul_nonneg hΛdt2_nn (hF3_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt20, hdt2L2⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hdt30, hdt3L2⟩ := hdt3 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hdt40, hdt4L2⟩ := hdt4 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκ00, hκ0L2⟩ := hκ0f g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hκb0, hκbL2⟩ := hκbf g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hK00, hK0L2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 2
    (lc0Kappa (I := I) (M := M) g₀ g₁ g₀) Λκ0 Fκ0 a hκ00 hκ0L2
  obtain ⟨hKb0, hKbL2⟩ := lc0b_slotExtendIter_feed_transfer (I := I) (M := M) g₀ 0 3 3
    (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg) Λκb Fκb a hκb0 hκbL2
  obtain ⟨htr30, htr3L2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 5 3
    (lc0PureDT (I := I) (M := M) g₀ g₁ 3) lieCorr0AMixPermQ Λdt3 Fdt3 a hdt30 hdt3L2
  obtain ⟨h10, h1L2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 5 3 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
    (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))
    C2a hC2a_nn hC2a Λdt3 ΛK0 Fdt3 FK0 hΛdt3_nn hΛK0_nn htr30 hK00 htr3L2 hK0L2
  obtain ⟨h20, h2L2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 3 6 a
    (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
      (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))
    C2b hC2b_nn hC2b ΛKb Λ1 FKb F1 hΛKb_nn hΛ1_nn hKb0 h10 hKbL2 h1L2
  obtain ⟨htr40, htr4L2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 6 4
    (lc0PureDT (I := I) (M := M) g₀ g₁ 4) lieCorr0AMixPerm1 Λdt4 Fdt4 a hdt40 hdt4L2
  obtain ⟨h30, h3L2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 6 4 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
        (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 (lc0Kappa (I := I) (M := M) g₀ g₁ g₀))))
    C2c hC2c_nn hC2c Λdt4 Λ2 Fdt4 F2 hΛdt4_nn hΛ2_nn htr40 h20 htr4L2 h2L2
  obtain ⟨htr20, htr2L2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
    (lc0PureDT (I := I) (M := M) g₀ g₁ 2) σlast Λdt2 Fdt2 a hdt20 hdt2L2
  exact lc0b_comp_feed_step (I := I) (M := M) g₀ 2 4 2 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 σlast)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4
      (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg))
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 5 3
          (lc0Tr (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀)))))
    C2d hC2d_nn hC2d Λdt2 Λ3 Fdt2 F3 hΛdt2_nn hΛ3_nn htr20 h30 htr2L2 h3L2

private theorem lc0b_amixField_feed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛhA, FhA, hΛhA_nn, hFhA_nn, hhA⟩ :=
    lc0b_amixHalf_feed (I := I) (M := M) g₀ g_bg lieCorr0AMixPerm2 a ha_super hR hδ₀
  obtain ⟨ΛhB, FhB, hΛhB_nn, hFhB_nn, hhB⟩ :=
    lc0b_amixHalf_feed (I := I) (M := M) g₀ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2)
      a ha_super hR hδ₀
  refine ⟨(2 : ℝ) ^ 2 * (2 * ΛhA + 2 * ΛhB),
    fun i => (2 : ℝ) ^ 2 * (2 * FhA i + 2 * FhB i),
    by positivity,
    fun i => by
      have := hFhA_nn i
      have := hFhB_nn i
      positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hA0, hAL2⟩ := hhA g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hB0, hBL2⟩ := hhB g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hadd0, haddL2⟩ := lc0b_add_feed_transfer (I := I) (M := M) g₀ 2 2
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2)
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2))
    ΛhA ΛhB FhA FhB a hA0 hB0 hAL2 hBL2
  exact lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (2 : ℝ)
    (lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg lieCorr0AMixPerm2
      + lc0AMixHalfField (I := I) (M := M) g₀ g₁ g_bg (lc0SwapOutPerm * lieCorr0AMixPerm2))
    (2 * ΛhA + 2 * ΛhB) (fun i => 2 * FhA i + 2 * FhB i) a hadd0 haddL2

private theorem lc0b_riemField_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((lc0RiemField (I := I) (M := M) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 q
              (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λdt2, Fdt2, hΛdt2_nn, hFdt2_nn, hdt2⟩ :=
    lc0b_pureDT_feed (I := I) (M := M) g₀ 2 a ha_super hR hδ₀
  obtain ⟨Λrr, hΛrr_nn, hΛrr⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 4
      (lc0RiemRestField (I := I) (M := M) g₀)
  set Frr : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 2 4 q (lc0RiemRestField (I := I) (M := M) g₀)‖ ^ 2 with hFrr
  have hFrr_nn : ∀ i, 0 ≤ Frr i := fun i => Finset.sum_nonneg fun q _ => sq_nonneg _
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 4 2 2 4
  refine ⟨(-1 : ℝ) ^ 2 * (Λdt2 * Λrr),
    fun i => (-1 : ℝ) ^ 2 * ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λrr * Fdt2 q + Λdt2 * Frr q)),
    by positivity,
    fun i => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
        (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛrr_nn (hFdt2_nn q))
          (mul_nonneg hΛdt2_nn (hFrr_nn q))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hdt20, hdt2L2⟩ := hdt2 g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨htr0, htrL2⟩ := lc0b_reindex_feed_transfer (I := I) (M := M) g₀ 4 2
    (lc0PureDT (I := I) (M := M) g₀ g₁ 2) lieCorr0RiemPerm2 Λdt2 Fdt2 a hdt20 hdt2L2
  obtain ⟨hcomp0, hcompL2⟩ := lc0b_comp_feed_step (I := I) (M := M) g₀ 2 4 2 a
    (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2) (lc0RiemRestField (I := I) (M := M) g₀)
    C2 hC2_nn hC2 Λdt2 Λrr Fdt2 Frr hΛdt2_nn hΛrr_nn htr0 hΛrr htrL2 (fun i _ => le_rfl)
  exact lc0b_smul_feed_transfer (I := I) (M := M) g₀ 2 2 (-1 : ℝ)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2 (lc0Tr (I := I) (M := M) g₀ g₁ 2 lieCorr0RiemPerm2)
      (lc0RiemRestField (I := I) (M := M) g₀))
    (Λdt2 * Λrr)
    (fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (C2 q * (Λrr * Fdt2 q + Λdt2 * Frr q)))
    a hcomp0 hcompL2

end LieCorr0BoundsF3

section LieCorr0BoundsF4

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound_abs realizedFam_inner_of_mem)

lemma lc0b_normSq_icg_bothCongr_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ' : Equiv.Perm (Fin r)) (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g₀ r s) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ r s q
        (reindexCoeffGen (I := I) (M := M) g₀ r s
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ R) σ')‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s q R‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ r s σ' σ R q x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma lc0b_gFibreOpBound_mono (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ')
    (hb : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀ h δ' := by
  intro x v w
  refine le_trans (hb x v w) ?_
  have h1 : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h1) h2
  linarith

theorem lieCorr0Field_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
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
              (lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Λvb, Fvb, hΛvb_nn, hFvb_nn, hvb⟩ :=
    lc0b_vbField_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λam, Fam, hΛam_nn, hFam_nn, ham⟩ :=
    lc0b_amixField_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨Λri, Fri, hΛri_nn, hFri_nn, hri⟩ :=
    lc0b_riemField_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λc0, Fc0, hΛc0_nn, hFc0_nn, hc0⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λcb, Fcb, hΛcb_nn, hFcb_nn, hcb⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨PW, hPW_nn, hPW⟩ :=
    DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform
      (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 8 * (4 * (fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i)))
      + 8 * Fvb i + 4 * Fam i + 2 * Fri i,
    fun i => by
      have h1 := hFc0_nn i
      have h2 := hFcb_nn i
      have h3 := hPW_nn i
      have h4 := hFvb_nn i
      have h5 := hFam_nn i
      have h6 := hFri_nn i
      have hin : 0 ≤ fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i) := by positivity
      linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc) δP :=
    lc0b_gFibreOpBound_mono (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def]
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, lc0b_icg_smul, lc0b_icg_smul]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  obtain ⟨hvb0, hvbL2⟩ := hvb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨ham0, hamL2⟩ := ham g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hri0, hriL2⟩ := hri g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hc00, hc0L2⟩ := hc0 g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hcb0, hcbL2⟩ := hcb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  have hWi : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert
        (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤ PW i := by
    rw [hg₁_def]
    exact hPW T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hdecomp := lc0b_total_decomp (I := I) (M := M) g₀ g₁ g_bg
  have hsplit : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      8 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 +
      8 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2 +
      4 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 +
      2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2 := by
    rw [hdecomp]
    have k1 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁
        + lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)
      (lc0RiemField (I := I) (M := M) g₀ g₁)
    have k2 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁)
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)
    have k3 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg) (lc0VBField (I := I) (M := M) g₀ g₁)
    linarith [k1, k2, k3]
  have hIns : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      4 * (fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i)) := by
    have hswapEq : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1))‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 :=
      lc0b_normSq_icg_bothCongr_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)) i
    have hsplitI := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 2 2 i
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1))
    have hle_endo : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
        fr * ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 := by
      refine lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀ 2 (2 + i) 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        (iteratedCovGrad (I := I) g₀ 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        fr hfr_nn ?_
      intro x
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg) i x
      rw [pow_one] at h
      exact h
    have hzero : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
        4 * Fc0 i + 4 * Fcb i + 2 * PW i := by
      rw [lc0b_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g_bg]
      have k1 := lc0b_normSq_icg_sub_le (I := I) (M := M) g₀ 1 1 i
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)
        (DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert
          (I := I) (M := M) g₀ g₁ g₀)
      have k2 := lc0b_normSq_icg_sub_le (I := I) (M := M) g₀ 1 1 i
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀) (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)
      have hc0i : ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (lc0CdVField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤ Fc0 i := by
        refine le_trans ?_ (hc0L2 i hi)
        exact Finset.single_le_sum (f := fun q =>
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (lc0CdVField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2)
          (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
      have hcbi : ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ Fcb i := by
        refine le_trans ?_ (hcbL2 i hi)
        exact Finset.single_le_sum (f := fun q =>
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
          (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
      linarith [k1, k2, hc0i, hcbi, hWi]
    have hfr_step : fr * ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
        fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i) :=
      mul_le_mul_of_nonneg_left hzero hfr_nn
    calc ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
        ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1))‖ ^ 2 := hsplitI
      _ = 4 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 := by
          rw [hswapEq]; ring
      _ ≤ 4 * (fr * ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2) := by
          have := mul_le_mul_of_nonneg_left hle_endo (by norm_num : (0:ℝ) ≤ 4)
          linarith
      _ ≤ 4 * (fr * (4 * Fc0 i + 4 * Fcb i + 2 * PW i)) := by
          have := mul_le_mul_of_nonneg_left hfr_step (by norm_num : (0:ℝ) ≤ 4)
          linarith
  have hVBi : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Fvb i := by
    refine le_trans ?_ (hvbL2 i hi)
    exact Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (lc0VBField (I := I) (M := M) g₀ g₁)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  have hAMi : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ Fam i := by
    refine le_trans ?_ (hamL2 i hi)
    exact Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  have hRIi : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ Fri i := by
    refine le_trans ?_ (hriL2 i hi)
    exact Finset.single_le_sum (f := fun q =>
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (lc0RiemField (I := I) (M := M) g₀ g₁)‖ ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
  refine le_trans hsplit ?_
  have e1 := mul_le_mul_of_nonneg_left hIns (by norm_num : (0:ℝ) ≤ 8)
  have e2 := mul_le_mul_of_nonneg_left hVBi (by norm_num : (0:ℝ) ≤ 8)
  have e3 := mul_le_mul_of_nonneg_left hAMi (by norm_num : (0:ℝ) ≤ 4)
  have e4 := mul_le_mul_of_nonneg_left hRIi (by norm_num : (0:ℝ) ≤ 2)
  linarith

theorem lieCorr0Field_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨Λvb, Fvb, hΛvb_nn, hFvb_nn, hvb⟩ :=
    lc0b_vbField_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λam, Fam, hΛam_nn, hFam_nn, ham⟩ :=
    lc0b_amixField_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨Λri, Fri, hΛri_nn, hFri_nn, hri⟩ :=
    lc0b_riemField_feed (I := I) (M := M) g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λc0, Fc0, hΛc0_nn, hFc0_nn, hc0⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ g₀ a ha_super hR hδ₁_lt
  obtain ⟨Λcb, Fcb, hΛcb_nn, hFcb_nn, hcb⟩ :=
    lc0b_cdVField_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₁_lt
  obtain ⟨ΛW, hΛW_nn, hΛW⟩ :=
    DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert_realizedFam_order0_ballUniform
      (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨8 * (4 * (fr * (4 * Λc0 + 4 * Λcb + 2 * ΛW)))
      + 8 * Λvb + 4 * Λam + 2 * Λri,
    by
      have hin : 0 ≤ fr * (4 * Λc0 + 4 * Λcb + 2 * ΛW) := by positivity
      linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc) δP :=
    lc0b_gFibreOpBound_mono (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def]
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, lc0b_icg_smul, lc0b_icg_smul]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  obtain ⟨hvb0, hvbL2⟩ := hvb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨ham0, hamL2⟩ := ham g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hri0, hriL2⟩ := hri g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hc00, hc0L2⟩ := hc0 g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  obtain ⟨hcb0, hcbL2⟩ := hcb g₁ Pc htie hδP_le hδP_nn hδP_bound hPball
  have hWx : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
      ((DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert
        (I := I) (M := M) g₀ g₁ g₀).toSection x) ≤ ΛW := by
    rw [hg₁_def]
    exact hΛW T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have hdecomp := lc0b_total_decomp (I := I) (M := M) g₀ g₁ g_bg
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤
      8 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) +
      8 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((lc0VBField (I := I) (M := M) g₀ g₁).toSection x) +
      4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((lc0AMixField (I := I) (M := M) g₀ g₁ g_bg).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((lc0RiemField (I := I) (M := M) g₀ g₁).toSection x) := by
    rw [hdecomp]
    have k1 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁
        + lc0AMixField (I := I) (M := M) g₀ g₁ g_bg)
      (lc0RiemField (I := I) (M := M) g₀ g₁) x
    have k2 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg + lc0VBField (I := I) (M := M) g₀ g₁)
      (lc0AMixField (I := I) (M := M) g₀ g₁ g_bg) x
    have k3 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (lc0InsertField (I := I) (M := M) g₀ g₁ g_bg) (lc0VBField (I := I) (M := M) g₀ g₁) x
    linarith [k1, k2, k3]
  have hIns : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤
      4 * (fr * (4 * Λc0 + 4 * Λcb + 2 * ΛW)) := by
    have hsplitI := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg))
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1)) x
    have hswapEq : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
      have h := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)) 0 x
      simp only [iteratedCovGrad_zero] at h
      exact h
    have hle_endo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
          ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg) 0 x
      simp only [iteratedCovGrad_zero] at h
      rw [pow_one] at h
      exact h
    have hzero : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        4 * Λc0 + 4 * Λcb + 2 * ΛW := by
      rw [lc0b_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g_bg]
      have k1 := lc0b_rfns_toSection_sub_le (I := I) (M := M) g₀ 1 1
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀ - lc0CdVField (I := I) (M := M) g₀ g₁ g_bg)
        (DifferentialGeometry.Integral.Connection.deTurckLieWEndoInsert
          (I := I) (M := M) g₀ g₁ g₀) x
      have k2 := lc0b_rfns_toSection_sub_le (I := I) (M := M) g₀ 1 1
        (lc0CdVField (I := I) (M := M) g₀ g₁ g₀) (lc0CdVField (I := I) (M := M) g₀ g₁ g_bg) x
      linarith [k1, k2, hc00 x, hcb0 x, hWx]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((lc0InsertField (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                  (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) := hsplitI
      _ = 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
          rw [hswapEq]; ring
      _ ≤ 4 * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (lc0NEndoSec (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) := by
          have := mul_le_mul_of_nonneg_left hle_endo (by norm_num : (0:ℝ) ≤ 4)
          linarith
      _ ≤ 4 * (fr * (4 * Λc0 + 4 * Λcb + 2 * ΛW)) := by
          have hstep := mul_le_mul_of_nonneg_left hzero hfr_nn
          have := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 4)
          linarith
  refine le_trans hsplit ?_
  have e1 := mul_le_mul_of_nonneg_left hIns (by norm_num : (0:ℝ) ≤ 8)
  have e2 := mul_le_mul_of_nonneg_left (hvb0 x) (by norm_num : (0:ℝ) ≤ 8)
  have e3 := mul_le_mul_of_nonneg_left (ham0 x) (by norm_num : (0:ℝ) ≤ 4)
  have e4 := mul_le_mul_of_nonneg_left (hri0 x) (by norm_num : (0:ℝ) ≤ 2)
  linarith

end LieCorr0BoundsF4

end LieCorr0BoundsAll

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
