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


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem mixed_continuous_rfns
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem mixed_real_holder_two_nonneg
    (g : SmoothRiemannianMetric I M) (φ ψ : M → ℝ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hψ0 : ∀ x, 0 ≤ ψ x)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫ x, φ x * ψ x ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (∫ x, φ x ^ p ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / p) *
      (∫ x, ψ x ^ q ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / q) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hp_pos : 0 < p := hpq.left_pos
  have hq_pos : 0 < q := hpq.right_pos
  have hφm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) μ :=
    (hφc.measurable.ennreal_ofReal).aemeasurable
  have hψm : AEMeasurable (fun x => ENNReal.ofReal (ψ x)) μ :=
    (hψc.measurable.ennreal_ofReal).aemeasurable
  have hint_prod : Integrable (fun x => φ x * ψ x) μ :=
    (hφc.mul hψc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_φp : Integrable (fun x => φ x ^ p) μ :=
    ((hφc.rpow_const (fun x => Or.inr hp_pos.le)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hint_ψq : Integrable (fun x => ψ x ^ q) μ :=
    ((hψc.rpow_const (fun x => Or.inr hq_pos.le)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hφp0 : ∀ x, 0 ≤ φ x ^ p := fun x => Real.rpow_nonneg (hφ0 x) _
  have hψq0 : ∀ x, 0 ≤ ψ x ^ q := fun x => Real.rpow_nonneg (hψ0 x) _
  have hIφp_nn : 0 ≤ ∫ x, φ x ^ p ∂μ := integral_nonneg hφp0
  have hIψq_nn : 0 ≤ ∫ x, ψ x ^ q ∂μ := integral_nonneg hψq0
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) hpq hφm hψm
  have hLHS_lint : (∫⁻ x, ((fun x => ENNReal.ofReal (φ x)) * (fun x => ENNReal.ofReal (ψ x))) x ∂μ)
      = ENNReal.ofReal (∫ x, φ x * ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_prod
      (Eventually.of_forall (fun x => mul_nonneg (hφ0 x) (hψ0 x)))]
    refine lintegral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hφ0 x)]
  have hφp_pt : ∀ x, (ENNReal.ofReal (φ x)) ^ p = ENNReal.ofReal (φ x ^ p) :=
    fun x => ENNReal.ofReal_rpow_of_nonneg (hφ0 x) hp_pos.le
  have hψq_pt : ∀ x, (ENNReal.ofReal (ψ x)) ^ q = ENNReal.ofReal (ψ x ^ q) :=
    fun x => ENNReal.ofReal_rpow_of_nonneg (hψ0 x) hq_pos.le
  have hφp_lint : (∫⁻ x, (ENNReal.ofReal (φ x)) ^ p ∂μ) = ENNReal.ofReal (∫ x, φ x ^ p ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_φp (Eventually.of_forall hφp0)]
    exact lintegral_congr_ae (Eventually.of_forall hφp_pt)
  have hψq_lint : (∫⁻ x, (ENNReal.ofReal (ψ x)) ^ q ∂μ) = ENNReal.ofReal (∫ x, ψ x ^ q ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_ψq (Eventually.of_forall hψq0)]
    exact lintegral_congr_ae (Eventually.of_forall hψq_pt)
  rw [hLHS_lint, hφp_lint, hψq_lint] at hHolder
  rw [ENNReal.ofReal_rpow_of_nonneg hIφp_nn (by positivity),
    ENNReal.ofReal_rpow_of_nonneg hIψq_nn (by positivity),
    ← ENNReal.ofReal_mul (by positivity)] at hHolder
  have hrhs_nn : 0 ≤ (∫ x, φ x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ^ q ∂μ) ^ (1 / q) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp hHolder


private theorem mixed_young_arm_split
    (wi wl CS CT ΛS ΛT NS NT Iφp Iψq : ℝ)
    (hwi_nn : 0 ≤ wi) (hwl_nn : 0 ≤ wl) (hwsum : wi + wl = 1)
    (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hΛS : 0 ≤ ΛS) (hΛT : 0 ≤ ΛT)
    (hNS : 0 ≤ NS) (hNT : 0 ≤ NT) (_hIφp : 0 ≤ Iφp) (hIψq : 0 ≤ Iψq)
    (hS : Iφp ^ wi ≤ CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi))
    (hT : Iψq ^ wl ≤ CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :
    Iφp ^ wi * Iψq ^ wl ≤
      CS * CT * (wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2)) := by
  have hT_nn : 0 ≤ Iψq ^ wl := Real.rpow_nonneg hIψq _
  have hprod : Iφp ^ wi * Iψq ^ wl ≤
      (CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi)) *
      (CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :=
    mul_le_mul hS hT hT_nn (by positivity)
  have h1wi : (1 : ℝ) - wi = wl := by rw [← hwsum]; ring
  have h1wl : (1 : ℝ) - wl = wi := by rw [← hwsum]; ring
  rw [h1wi, h1wl] at hprod
  have hsq_rpow : ∀ (b : ℝ), 0 ≤ b → ∀ w : ℝ, b ^ (2 * w) = (b ^ 2) ^ w := by
    intro b hb w
    rw [Real.rpow_mul hb 2 w, Real.rpow_two]
  have hregroup :
      (CS * ΛS ^ (2 * wl) * NS ^ (2 * wi)) * (CT * ΛT ^ (2 * wi) * NT ^ (2 * wl))
        = CS * CT * ((ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      hsq_rpow ΛS hΛS wl, hsq_rpow NS hNS wi, hsq_rpow ΛT hΛT wi, hsq_rpow NT hNT wl]
    ring
  rw [hregroup] at hprod
  have hyoung : (ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl ≤
      wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2) :=
    Real.geom_mean_le_arith_mean2_weighted hwi_nn hwl_nn (by positivity) (by positivity) hwsum
  calc Iφp ^ wi * Iψq ^ wl
      ≤ CS * CT * ((ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl) := hprod
    _ ≤ CS * CT * (wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2)) :=
        mul_le_mul_of_nonneg_left hyoung (by positivity)

open DifferentialGeometry.Analysis.Sobolev.Tensor in

private theorem appCc_integrated_grid_twoArm_mixed
    (g : SmoothRiemannianMetric I M) (r s₁ s₂ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g r s₁) (T : Integral.L2.SmoothCcTensor g 0 s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        (∫ x, (∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (s₁ + i) x
                ((iteratedCovGrad (I := I) g r s₁ i S).toSection x)
              * ∑ l ∈ Finset.range (k + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                    ((iteratedCovGrad (I := I) g 0 s₂ l T).toSection x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2
              + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  set CSf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs (I := I) (M := M) g r s₁ m h).choose
    else 0 with hCSf
  set CTf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs (I := I) (M := M) g 0 s₂ m h).choose
    else 0 with hCTf
  have hCSf_nn : ∀ m, 0 ≤ CSf m := by
    intro m; rw [hCSf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g r s₁ m h).choose_spec.1
    · exact le_refl 0
  have hCTf_nn : ∀ m, 0 ≤ CTf m := by
    intro m; rw [hCTf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g 0 s₂ m h).choose_spec.1
    · exact le_refl 0
  set Cbig : ℝ := 1 + ∑ m ∈ Finset.range (k + 1), CSf m * CTf m with hCbig
  have hCbig1 : (1 : ℝ) ≤ Cbig := by
    rw [hCbig]
    have : (0 : ℝ) ≤ ∑ m ∈ Finset.range (k + 1), CSf m * CTf m :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (hCSf_nn m) (hCTf_nn m))
    linarith
  have hCbig_nn : (0 : ℝ) ≤ Cbig := le_trans zero_le_one hCbig1
  have hCSCT_le : ∀ m, m ≤ k → CSf m * CTf m ≤ Cbig := by
    intro m hm
    rw [hCbig]
    have hmem : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have hterm : CSf m * CTf m ≤ ∑ m' ∈ Finset.range (k + 1), CSf m' * CTf m' :=
      Finset.single_le_sum (fun m' _ => mul_nonneg (hCSf_nn m') (hCTf_nn m')) hmem
    linarith
  refine ⟨(k + 1) ^ 2 * Cbig, by positivity, ?_⟩
  intro S T ΛS ΛT hΛS hΛT hSsup hTsup
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set Sj : ℕ → M → ℝ := fun a x =>
    riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) x
      ((iteratedCovGrad (I := I) g r s₁ a S).toSection x) with hSj
  set Tj : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
      ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) with hTj
  have hSnorm : ∀ a, ∫ x, Sj a x ∂μ =
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by
    intro a
    rw [hSj, hμ,
      ← (show Integral.L2.tensorL2Norm (I := I) (M := M) g r (s₁ + a)
            (iteratedCovGrad (I := I) g r s₁ a S).toFun ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) x
            ((iteratedCovGrad (I := I) g r s₁ a S).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
        have hfun : (iteratedCovGrad (I := I) g r s₁ a S).toFun =
            fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
              (M := M) (r := r) (s := s₁ + a) (x := x)
              ((iteratedCovGrad (I := I) g r s₁ a S).toSection x) := rfl
        rw [hfun]
        exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) _),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g r s₁ a S)]
  have hTnorm : ∀ b, ∫ x, Tj b x ∂μ =
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
    intro b
    rw [hTj, hμ,
      ← (show Integral.L2.tensorL2Norm (I := I) (M := M) g 0 (s₂ + b)
            (iteratedCovGrad (I := I) g 0 s₂ b T).toFun ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
            ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
        have hfun : (iteratedCovGrad (I := I) g 0 s₂ b T).toFun =
            fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
              (M := M) (r := 0) (s := s₂ + b) (x := x)
              ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) := rfl
        rw [hfun]
        exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) _),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g 0 s₂ b T)]
  have hSj_cont : ∀ a, Continuous (Sj a) := fun a => by
    rw [hSj]; exact mixed_continuous_rfns g r (s₁ + a) _
  have hTj_cont : ∀ b, Continuous (Tj b) := fun b => by
    rw [hTj]; exact mixed_continuous_rfns g 0 (s₂ + b) _
  have hSj_nn : ∀ a x, 0 ≤ Sj a x := fun a x => by
    rw [hSj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s₁ + a) x _
  have hTj_nn : ∀ b x, 0 ≤ Tj b x := fun b x => by
    rw [hTj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₂ + b) x _
  have hSj_int : ∀ a, Integrable (Sj a) μ := fun a => by
    rw [hμ]; exact (hSj_cont a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTj_int : ∀ b, Integrable (Tj b) μ := fun b => by
    rw [hμ]; exact (hTj_cont b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_cell : ∀ a b, Integrable (fun x => Sj a x * Tj b x) μ := fun a b => by
    rw [hμ]
    exact ((hSj_cont a).mul (hTj_cont b)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSsup0 : ∀ x, Sj 0 x ≤ ΛS ^ 2 := by
    intro x; rw [hSj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g r s₁ S]
    exact hSsup x
  have hTsup0 : ∀ x, Tj 0 x ≤ ΛT ^ 2 := by
    intro x; rw [hTj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g 0 s₂ T]
    exact hTsup x
  have hAS_nn : 0 ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by positivity
  have hAT_nn : 0 ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by positivity
  have hcell : ∀ i, i ≤ k → ∀ l, i + l ≤ k →
      ∫ x, Sj i x * Tj l x ∂μ ≤ Cbig *
        ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    intro i hik l hilk
    have hSi_in : ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2 ≤
        ∑ a ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun a => ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
    have hTl_in : ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 ≤
        ∑ b ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun b => ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
        (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)))
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hbound : ∫ x, Sj 0 x * Tj l x ∂μ ≤ ΛS ^ 2 * ∫ x, Tj l x ∂μ := by
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
          (Eventually.of_forall (fun x => ?_))
        · exact mul_nonneg (hSj_nn 0 x) (hTj_nn l x)
        · exact (hTj_int l).const_mul _
        · exact mul_le_mul_of_nonneg_right (hSsup0 x) (hTj_nn l x)
      rw [hTnorm l] at hbound
      calc ∫ x, Sj 0 x * Tj l x ∂μ
          ≤ ΛS ^ 2 * ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 := hbound
        _ ≤ Cbig * (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2) := by
              rw [← mul_assoc, mul_comm (Cbig) (ΛS ^ 2), mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (le_trans hTl_in (le_mul_of_one_le_left (Finset.sum_nonneg
                  (fun b _ => sq_nonneg _)) hCbig1)) (by positivity)
        _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
            + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
              apply mul_le_mul_of_nonneg_left _ hCbig_nn
              linarith [hAS_nn]
    · rcases Nat.eq_zero_or_pos l with hl0 | hlpos
      · subst hl0
        have hbound : ∫ x, Sj i x * Tj 0 x ∂μ ≤ ΛT ^ 2 * ∫ x, Sj i x ∂μ := by
          rw [← integral_const_mul]
          refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
            (Eventually.of_forall (fun x => ?_))
          · exact mul_nonneg (hSj_nn i x) (hTj_nn 0 x)
          · exact (hSj_int i).const_mul _
          · calc Sj i x * Tj 0 x
                ≤ Sj i x * ΛT ^ 2 := mul_le_mul_of_nonneg_left (hTsup0 x) (hSj_nn i x)
              _ = ΛT ^ 2 * Sj i x := mul_comm _ _
        rw [hSnorm i] at hbound
        calc ∫ x, Sj i x * Tj 0 x ∂μ
            ≤ ΛT ^ 2 * ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2 := hbound
          _ ≤ Cbig * (ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2) := by
                rw [← mul_assoc, mul_comm (Cbig) (ΛT ^ 2), mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (le_trans hSi_in (le_mul_of_one_le_left (Finset.sum_nonneg
                    (fun a _ => sq_nonneg _)) hCbig1)) (by positivity)
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
                apply mul_le_mul_of_nonneg_left _ hCbig_nn
                linarith [hAT_nn]
      · set m : ℕ := i + l with hm
        have hmk : m ≤ k := by rw [hm]; exact hilk
        have hm1 : 1 ≤ m := by omega
        have hmi : i < m := by omega
        have hml : l < m := by omega
        have hm_posR : 0 < (m : ℝ) := by positivity
        set wi : ℝ := (i : ℝ) / m with hwi
        set wl : ℝ := (l : ℝ) / m with hwl
        have hwi_nn : 0 ≤ wi := by rw [hwi]; positivity
        have hwl_nn : 0 ≤ wl := by rw [hwl]; positivity
        have hwsum : wi + wl = 1 := by
          rw [hwi, hwl, ← add_div, show (i : ℝ) + l = (m : ℝ) by push_cast [hm]; ring]
          exact div_self (ne_of_gt hm_posR)
        have hi_posR : 0 < (i : ℝ) := by exact_mod_cast hipos
        have hl_posR : 0 < (l : ℝ) := by exact_mod_cast hlpos
        set p : ℝ := (m : ℝ) / i with hp
        set q : ℝ := (m : ℝ) / l with hq
        have hp_one : 1 < p := by rw [hp, lt_div_iff₀ hi_posR, one_mul]; exact_mod_cast hmi
        have hpq : p.HolderConjugate q := by
          rw [Real.holderConjugate_iff]
          refine ⟨hp_one, ?_⟩
          rw [hp, hq, inv_div, inv_div, ← add_div,
            show (i : ℝ) + l = (m : ℝ) by push_cast [hm]; ring]
          exact div_self (ne_of_gt hm_posR)
        have hHolder := mixed_real_holder_two_nonneg g (Sj i) (Tj l)
          (hSj_cont i) (hTj_cont l) (hSj_nn i) (hTj_nn l) hpq
        have h1p : (1 : ℝ) / p = wi := by rw [hp, one_div_div, hwi]
        have h1q : (1 : ℝ) / q = wl := by rw [hq, one_div_div, hwl]
        rw [h1p, h1q] at hHolder
        have hSe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g r s₁ m hm1).choose_spec.2 S ΛS hΛS hSsup i hipos hmi
        have hTe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g 0 s₂ m hm1).choose_spec.2 T ΛT hΛT hTsup l hlpos hml
        have hCSf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g r s₁ m hm1).choose = CSf m := by
          simp only [hCSf, dif_pos hm1]
        have hCTf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g 0 s₂ m hm1).choose = CTf m := by
          simp only [hCTf, dif_pos hm1]
        rw [hCSf_m] at hSe
        rw [hCTf_m] at hTe
        rw [mul_div_assoc 2 (i : ℝ) m, ← hwi] at hSe
        rw [mul_div_assoc 2 (l : ℝ) m, ← hwl] at hTe
        rw [show Integral.L2.tensorL2Norm (I := I) g r (s₁ + m)
              (iteratedCovGrad (I := I) g r s₁ m S).toFun =
              ‖iteratedCovGrad (I := I) g r s₁ m S‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g r s₁ m S)).symm] at hSe
        rw [show Integral.L2.tensorL2Norm (I := I) g 0 (s₂ + m)
              (iteratedCovGrad (I := I) g 0 s₂ m T).toFun =
              ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g 0 s₂ m T)).symm] at hTe
        set Iφp : ℝ := ∫ x, Sj i x ^ p ∂μ with hIφp
        set Iψq : ℝ := ∫ x, Tj l x ^ q ∂μ with hIψq
        have hIφp_nn : 0 ≤ Iφp := by
          rw [hIφp]; exact integral_nonneg (fun x => Real.rpow_nonneg (hSj_nn i x) _)
        have hIψq_nn : 0 ≤ Iψq := by
          rw [hIψq]; exact integral_nonneg (fun x => Real.rpow_nonneg (hTj_nn l x) _)
        have hys := mixed_young_arm_split wi wl (CSf m) (CTf m) ΛS ΛT
          ‖iteratedCovGrad (I := I) g r s₁ m S‖
          ‖iteratedCovGrad (I := I) g 0 s₂ m T‖
          Iφp Iψq hwi_nn hwl_nn hwsum (hCSf_nn m) (hCTf_nn m) hΛS hΛT
          (norm_nonneg _) (norm_nonneg _) hIφp_nn hIψq_nn hSe hTe
        have hNS_sum : ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2 ≤
            ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun a => ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hNT_sum : ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 ≤
            ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun b => ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
            (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hwi_le1 : wi ≤ 1 := by rw [← hwsum]; linarith
        have hwl_le1 : wl ≤ 1 := by rw [← hwsum]; linarith
        calc ∫ x, Sj i x * Tj l x ∂μ
            ≤ Iφp ^ wi * Iψq ^ wl := hHolder
          _ ≤ CSf m * CTf m * (wi * (ΛT ^ 2 *
                ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
              + wl * (ΛS ^ 2 *
                ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)) := hys
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
              refine le_trans (mul_le_mul_of_nonneg_right (hCSCT_le m hmk) ?_) ?_
              · have : 0 ≤ wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
                  + wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) := by positivity
                exact this
              · refine mul_le_mul_of_nonneg_left ?_ hCbig_nn
                have harm1 : wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2) ≤
                    ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by
                  calc wi * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
                      ≤ 1 * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwi_le1 (by positivity)
                    _ = ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2 := one_mul _
                    _ ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNS_sum (by positivity)
                have harm2 : wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) ≤
                    ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
                  calc wl * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)
                      ≤ 1 * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwl_le1 (by positivity)
                    _ = ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 := one_mul _
                    _ ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNT_sum (by positivity)
                linarith
  have hrw : (∫ x, ∑ i ∈ Finset.range (k + 1), Sj i x *
        ∑ l ∈ Finset.range (k + 1 - i), Tj l x ∂μ)
      = ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
          ∫ x, Sj i x * Tj l x ∂μ := by
    rw [MeasureTheory.integral_finset_sum _
      (fun i _ => by
        rw [hμ]
        exact ((hSj_cont i).mul (continuous_finset_sum _
          (fun l _ => hTj_cont l))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ x, Sj i x * ∑ l ∈ Finset.range (k + 1 - i), Tj l x ∂μ)
          = ∫ x, ∑ l ∈ Finset.range (k + 1 - i), Sj i x * Tj l x ∂μ from by
        simp only [Finset.mul_sum],
      MeasureTheory.integral_finset_sum _ (fun l _ => hint_cell i l)]
  rw [hrw]
  have hsum_le : ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
        ∫ x, Sj i x * Tj l x ∂μ ≤
      ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
        Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun l hl => ?_))
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hilk : i + l ≤ k := by
      rw [Finset.mem_range] at hi hl; omega
    exact hcell i hik l hilk
  refine le_trans hsum_le ?_
  set c : ℝ := Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
    + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) with hc
  have hc_nn : 0 ≤ c := by
    rw [hc]; exact mul_nonneg hCbig_nn (by linarith [hAS_nn, hAT_nn])
  have hinner : ∀ i ∈ Finset.range (k + 1),
      (∑ _l ∈ Finset.range (k + 1 - i), c) ≤ (k + 1 : ℝ) * c := by
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (k + 1) i) hc_nn
  have hdouble : (∑ i ∈ Finset.range (k + 1), ∑ _l ∈ Finset.range (k + 1 - i), c)
      ≤ (k + 1 : ℝ) * ((k + 1 : ℝ) * c) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ _l ∈ Finset.range (k + 1 - i), c)
        ≤ ∑ _i ∈ Finset.range (k + 1), (k + 1 : ℝ) * c := Finset.sum_le_sum hinner
      _ = (k + 1 : ℝ) * ((k + 1 : ℝ) * c) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]; push_cast; ring
  refine le_trans hdouble (le_of_eq ?_)
  rw [hc]
  ring

theorem ccTensorContract_topOrder_l2_twoArm_mixed_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ k
            (operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀

  obtain ⟨Cgrid, hCgrid_nn, hCgrid⟩ :=
    appCc_integrated_grid_twoArm_mixed (I := I) g₀ b₀ s₀ b₀ k

  set Gk : ℝ := diagonalGridGrowthFactor (E := E) k with hGk
  have hGk_nn : 0 ≤ Gk := appCcGdiag_nonneg (E := E) k
  refine ⟨Gk * Cgrid, by positivity, ?_⟩
  intro Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  set P : SmoothCcTensor g₀ 0 s₀ := operatorFieldApply (I := I) (M := M) g₀ b₀ s₀ Φ W with hP

  have hLHS_eq : ‖iteratedCovGrad (I := I) g₀ 0 s₀ k P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ := by
    rw [hμ, Integral.L2.SmoothCcTensor.norm_def
        (iteratedCovGrad (I := I) g₀ 0 s₀ k P)]
    have hfun : (iteratedCovGrad (I := I) g₀ 0 s₀ k P).toFun =
        fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
          (M := M) (r := 0) (s := s₀ + k) (x := x)
          ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) _

  set grid : M → ℝ := fun x => ∑ i ∈ Finset.range (k + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)
        * ∑ l ∈ Finset.range (k + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
              ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x) with hgrid

  have hptwise : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ≤ Gk * grid x := by
    intro x
    rw [hGk, hgrid, hP]
    exact riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) g₀ b₀ s₀ Φ W k x

  have hgrid_cont : Continuous grid := by
    rw [hgrid]
    refine continuous_finset_sum _ (fun i _ => (mixed_continuous_rfns g₀ b₀ (s₀ + i) _).mul ?_)
    exact continuous_finset_sum _ (fun l _ => mixed_continuous_rfns g₀ 0 (b₀ + l) _)
  have hgrid_int : Integrable grid μ := by
    rw [hμ]; exact hgrid_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

  have hmono : ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ ≤
      Gk * ∫ x, grid x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s₀ + k) x _)) ?_
      (Eventually.of_forall hptwise)
    exact hgrid_int.const_mul _

  have hgrid_bound := hCgrid Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  rw [hLHS_eq]
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ
      ≤ Gk * ∫ x, grid x ∂μ := hmono
    _ ≤ Gk * (Cgrid * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
          + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hGk_nn
        rw [hgrid]; exact hgrid_bound
    _ = Gk * Cgrid * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
          + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma jetTowerSum_add_le (g₀ : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g₀ r s) :
    (∑ i ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ r s i (A + B)‖ ^ 2) ≤
      2 * (∑ i ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2) +
        2 * (∑ i ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2) := by
  have hterm : ∀ i ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g₀ r s i (A + B)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 := by
    intro i _
    rw [iteratedCovGrad_add (I := I) g₀ r s i A B]
    have htri := norm_add_le (iteratedCovGrad (I := I) g₀ r s i A)
      (iteratedCovGrad (I := I) g₀ r s i B)
    have hnnA : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r s i A‖ := norm_nonneg _
    have hnnB : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r s i B‖ := norm_nonneg _
    have hnnsum : 0 ≤ ‖iteratedCovGrad (I := I) g₀ r s i A +
        iteratedCovGrad (I := I) g₀ r s i B‖ := norm_nonneg _
    have hsq : ‖iteratedCovGrad (I := I) g₀ r s i A +
          iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2 ≤
        (‖iteratedCovGrad (I := I) g₀ r s i A‖ +
          ‖iteratedCovGrad (I := I) g₀ r s i B‖) ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul htri htri hnnsum (by positivity)
    nlinarith [hsq, hnnA, hnnB, sq_nonneg (‖iteratedCovGrad (I := I) g₀ r s i A‖ -
      ‖iteratedCovGrad (I := I) g₀ r s i B‖)]
  calc (∑ i ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ r s i (A + B)‖ ^ 2)
      ≤ ∑ i ∈ Finset.range n, (2 * ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2) := Finset.sum_le_sum hterm
    _ = 2 * (∑ i ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ r s i A‖ ^ 2) +
          2 * (∑ i ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ r s i B‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedCovGrad_smul' (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armField_covGrad_step_jointSmooth
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r sIdx (Ψ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_step_jointContMDiffOn
    (I := I) (M := M) g₀ r sIdx Ψ S hjoint

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armField_jointSmooth_rfns_jointContinuous
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hSI : Set.Icc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
  have hIccprod : (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ _, hSI ht⟩
  have hswapCont : Continuous (fun p : ℝ × M => (p.2, p.1)) := by fun_prop
  have hv : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) p.2 ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswapCont.continuousOn hIccprod).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hψ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel r sIdx ℝ E →L[ℝ] TensorRSModel r sIdx ℝ E →L[ℝ] ℝ)
        (E := fun x : M => TensorRSSpace r sIdx I x →L[ℝ] TensorRSSpace r sIdx I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSRiemannianInnerCLM_continuous
      (I := I) (M := M) g₀ r sIdx).comp continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂ (F₁ := TensorRSModel r sIdx ℝ E)
      (F₂ := TensorRSModel r sIdx ℝ E) (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hψ hv hv
  have hscalar : ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    intro p hp
    have hp2 := ((FiberBundle.continuousWithinAt_totalSpace ℝ
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2
          ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2)))).mp (happ p hp)).2
    exact hp2
  refine hscalar.congr ?_
  rintro ⟨t, x⟩ -
  simp only
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r sIdx x
      ((Ψ t).toSection x),
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armField_covGrad_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hjg : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r sIdx (Ψ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    covGrad (I := I) (M := M) g₀ r sIdx
        (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ S hS hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (sIdx + 1)
        (fun t => covGrad (I := I) (M := M) g₀ r sIdx (Ψ t)) S hS hSI hjg :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_pathIntegral_comm
    (I := I) (M := M) g₀ r sIdx Ψ S hS hSI hjoint hjg

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem pathIntegralCoeffField_congr
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ₁ Ψ₂ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hj₁ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ₁ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hj₂ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ₂ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hΨ : Ψ₁ = Ψ₂) :
    pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ₁ S hS hSI hj₁ =
      pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ₂ S hS hSI hj₂ := by
  subst hΨ
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armField_iteratedCovGrad_jointSmooth
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction i with
  | zero => exact hjoint
  | succ j ih =>
    exact armField_covGrad_step_jointSmooth (I := I) g₀ r (sIdx + j)
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S ih

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armField_iteratedCovGrad_rfns_jointContinuous
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (sIdx + i) p.2
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ p.1)).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
  armField_jointSmooth_rfns_jointContinuous (I := I) g₀ r (sIdx + i)
    (fun t => iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)) S
    (by rw [Set.uIcc_of_le (zero_le_one (α := ℝ))] at hSI; exact hSI)
    (armField_iteratedCovGrad_jointSmooth (I := I) g₀ r sIdx i Φ S hjoint)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armField_iteratedCovGrad_normSq_intervalIntegrable
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    IntervalIntegrable
      (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)‖ ^ 2) volume 0 1 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set F : ℝ × M → ℝ := fun p : ℝ × M =>
    riemannianFiberNormSq (I := I) (M := M) g₀ r (sIdx + i) p.2
      ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ p.1)).toSection p.2) with hF
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    armField_iteratedCovGrad_rfns_jointContinuous (I := I) g₀ r sIdx i Φ S hSI hjoint
  have hnormsq : ∀ t : ℝ,
      ‖iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)‖ ^ 2 = ∫ x, F (t, x) ∂μ := by
    intro t
    rw [SmoothCcTensor.norm_def]
    have hsec : (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := sIdx + i) (x := x)
          ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)).toSection x)) =
        (iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)).toFun := by
      funext x
      rw [SmoothCcTensor.toFun_apply]
    rw [← hsec,
      tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ r (sIdx + i)
        (fun x => (iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)).toSection x)]
  have hcontInt : ContinuousOn (fun t : ℝ => ∫ x, F (t, x) ∂μ) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_integral_of_compact_support (μ := μ) isCompact_univ hFcont
      (fun _ x _ hx => absurd (Set.mem_univ x) hx)
  have heq : (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)‖ ^ 2) =
      fun t : ℝ => ∫ x, F (t, x) ∂μ := funext hnormsq
  rw [heq]
  exact hcontInt.intervalIntegrable_of_Icc (by norm_num)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem armField_iteratedCovGrad_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hji : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    iteratedCovGrad (I := I) g₀ r sIdx i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (sIdx + i)
        (fun t => iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)) S hS hSI hji := by
  induction i with
  | zero =>
    rw [iteratedCovGrad_zero]
    exact pathIntegralCoeffField_congr (I := I) g₀ r sIdx Φ
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx 0 (Φ t)) S hS hSI hjoint hji
      (by funext t; rw [iteratedCovGrad_zero])
  | succ j ih =>
    have hjg_j : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + j) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + j) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + j) I z) q.1
          ((iteratedCovGrad (I := I) g₀ r sIdx j (Φ q.2)).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
      armField_iteratedCovGrad_jointSmooth (I := I) g₀ r sIdx j Φ S hjoint
    have hjgsucc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + j + 1) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + j + 1) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + j + 1) I z) q.1
          ((covGrad (I := I) (M := M) g₀ r (sIdx + j)
              (iteratedCovGrad (I := I) g₀ r sIdx j (Φ q.2))).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
      armField_covGrad_step_jointSmooth (I := I) g₀ r (sIdx + j)
        (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S hjg_j
    rw [iteratedCovGrad_succ, ih hjg_j]
    rw [armField_covGrad_pathIntegral_comm (I := I) g₀ r (sIdx + j)
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S hS hSI hjg_j hjgsucc]
    exact pathIntegralCoeffField_congr (I := I) g₀ r (sIdx + j + 1)
      (fun t => covGrad (I := I) (M := M) g₀ r (sIdx + j)
        (iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)))
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx (j + 1) (Φ t)) S hS hSI hjgsucc hji
      (by funext t; rw [iteratedCovGrad_succ])

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem pathIntegralCoeffField_jetL2_tower_le
    (g₀ : SmoothRiemannianMetric I M) (r a : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ'))
    (hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')))
    (hjoint : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r Φ (δ := δ) (δ' := δ'))
    {B : ℝ} (hB : 0 ≤ B)
    (hΦjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2) ≤ B ^ 2) :
    (∑ i ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ r 2 i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ
          (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint)‖ ^ 2) ≤ B ^ 2 := by
  have hjointC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
        (E := fun z : M => TensorRSSpace r 2 I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := hjoint
  have hji : ∀ i ∈ Finset.range (a + 1),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (2 + i) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (2 + i) ℝ E)
          (E := fun z : M => TensorRSSpace r (2 + i) I z) q.1
          ((iteratedCovGrad (I := I) g₀ r 2 i (Φ q.2)).toSection q.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun i _ => armField_iteratedCovGrad_jointSmooth (I := I) g₀ r 2 i Φ
      (realizedSmallSet (δ := δ) (δ' := δ')) hjointC
  have hci : ∀ i ∈ Finset.range (a + 1), ∀ x : M,
      ContinuousOn (fun t : ℝ =>
        TensorRSSpace.toModel ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x))
        (Set.Icc (0 : ℝ) 1) := by
    intro i hi x
    exact (jointContMDiff_toModel_continuous_slice (I := I) g₀ r (2 + i)
      (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t))
      (realizedSmallSet (δ := δ) (δ' := δ')) (hji i hi) x).mono
      (by rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]; exact hSI)
  have hri : ∀ i ∈ Finset.range (a + 1),
      ContinuousOn (fun p : ℝ × M =>
        riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) p.2
          ((iteratedCovGrad (I := I) g₀ r 2 i (Φ p.1)).toSection p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    fun i _ => armField_iteratedCovGrad_rfns_jointContinuous (I := I) g₀ r 2 i Φ
      (realizedSmallSet (δ := δ) (δ' := δ')) hSI hjointC
  have hii : ∀ i ∈ Finset.range (a + 1),
      IntervalIntegrable
        (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2) volume 0 1 :=
    fun i _ => armField_iteratedCovGrad_normSq_intervalIntegrable (I := I) g₀ r 2 i Φ
      (realizedSmallSet (δ := δ) (δ' := δ')) hSI hjointC
  have hcomm : ∀ (i : ℕ) (hi : i ∈ Finset.range (a + 1)),
      iteratedCovGrad (I := I) g₀ r 2 i
          (pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ
            (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint) =
        pathIntegralCoeffField (I := I) (M := M) g₀ r (2 + i)
          (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t))
          (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI (hji i hi) :=
    fun i hi => armField_iteratedCovGrad_pathIntegral_comm (I := I) g₀ r 2 i Φ
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjointC (hji i hi)
  exact iteratedCovGrad_pathIntegralCoeffField_jetL2_le (I := I) (M := M) g₀ r 2 a Φ B hB
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint hΦjet hji hci hri hii hcomm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
