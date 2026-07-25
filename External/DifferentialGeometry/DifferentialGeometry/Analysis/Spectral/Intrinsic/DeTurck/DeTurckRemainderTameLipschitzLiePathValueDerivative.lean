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

private noncomputable def realizedDeTurckLiePathValue
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  lieDerivMetricClm (I := I)
    (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (le_max_left 0 (min s 1))
      (max_le zero_le_one (min_le_right s 1)))
    (deTurckVF (I := I)
      (smoothRiemannianMetricToInfty (I := I)
        (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le zero_le_one (min_le_right s 1))))
      (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w

omit [CompactSpace M] in
private theorem realizedDeTurckLiePathValue_one
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 1 =
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w := by
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (1 : ℝ) 1))
          (max_le zero_le_one (min_le_right (1 : ℝ) 1)) =
        tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      tensorSectionRealizeMetric_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 1 1) = 1 := by norm_num
    rw [this]; ring
  rw [realizedDeTurckLiePathValue, hmetric]

omit [CompactSpace M] in
private theorem realizedDeTurckLiePathValue_zero
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 0 =
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w := by
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (0 : ℝ) 1))
          (max_le zero_le_one (min_le_right (0 : ℝ) 1)) =
        tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      tensorSectionRealizeMetric_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 0 1) = 0 := by norm_num
    rw [this]; ring
  rw [realizedDeTurckLiePathValue, hmetric]

noncomputable def linearizedDeTurckLieAt
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s₀ : ℝ) : ℝ :=
  deriv (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀

noncomputable def realizedDeTurckLieChartSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ j,
    ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
      DeTurckCoefficients.chartLieDeTurckComp (I := I)
        (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
          (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private theorem realizedDeTurckLieChartSum_contDiffAt
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s₀ := by
  have hG := DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam_genJointGram
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold realizedDeTurckLieChartSum
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => ?_))
  refine contDiffAt_const.mul ?_
  have hjoint := DifferentialGeometry.PDE.DeTurck.RicciLinearization.gen_joint_chartLieDeTurckComp
    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
      (I := I) g₀ T T' hδ hδ') x hG g_bg i j hs hy
  have hcomp : (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
            (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) =
      (fun p : ℝ × E =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
            (I := I) g₀ T T' hδ hδ' p.1) g_bg x i j p.2) ∘
        (fun s : ℝ => (s, extChartAt I x x)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

omit [CompactSpace M] in
private theorem realizedDeTurckLiePathValue_eq_chartSum_on_Icc
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w s := by
  obtain ⟨h0, h1⟩ := hs
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨h0, h1⟩
  have hclamp : max 0 (min s 1) = s := by rw [min_eq_left h1, max_eq_right h0]
  have hxgood : x ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) x :=
    DifferentialGeometry.Integral.Connection.self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le zero_le_one (min_le_right s 1)) =
        DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
          (I := I) g₀ T T' hδ hδ' s := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam_inner_of_mem
        (I := I) g₀ T T' hδ hδ' hmem, hclamp]
  rw [realizedDeTurckLiePathValue, hmetric, lieDerivMetricClm_apply,
    realizedDeTurckLieChartSum]
  rw [DifferentialGeometry.PDE.DeTurck.lieDerivMetric_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [smoothRiemannianMetricToInfty]
  rw [DifferentialGeometry.PDE.DeTurck.lieDerivMetricMatrix_def_chart,
    DeTurckCoefficients.chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp
      (I := I)
      (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam
        (I := I) g₀ T T' hδ hδ' s) g_bg x i j hxgood]

omit [CompactSpace M] in
private theorem realizedDeTurckLiePathValue_differentiableAt_Ioo
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0:ℝ) 1) :
    DifferentiableAt ℝ
      (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀ := by
  have heq : realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s₀] realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w (Set.mem_Icc_of_Ioo hs)
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  exact ((realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
    hmem).differentiableAt (by simp)).congr_of_eventuallyEq heq

omit [CompactSpace M] in
theorem linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s := by
  have heq : realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s] realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w (Set.mem_Icc_of_Ioo ht)
  rw [linearizedDeTurckLieAt]
  exact Filter.EventuallyEq.deriv_eq heq

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private theorem deriv_realizedDeTurckLieChartSum_continuousOn
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hcd : ContDiffOn ℝ ∞ (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun s hs =>
    (realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
      hs).contDiffWithinAt
  exact hcd.continuousOn_deriv_of_isOpen realizedSmallSet_isOpen (by exact_mod_cast le_top)

omit [CompactSpace M] in
theorem linearizedDeTurckLieAt_intervalIntegrable
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
      MeasureTheory.volume 0 1 := by
  have hcont : ContinuousOn (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      (Set.Icc (0:ℝ) 1) :=
    (deriv_realizedDeTurckLieChartSum_continuousOn (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w).mono
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
  have hii : IntervalIntegrable
      (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  refine hii.congr_ae ?_
  have hsub : Set.Ioo (0:ℝ) 1 ⊆
      {s | deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s =
        linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s} := by
    intro s hs
    exact (linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs).symm
  have hnull : (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) (Set.Ioo (0:ℝ) 1)ᶜ = 0 := by
    rw [Set.uIoc_of_le zero_le_one]
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
    have hsub1 : (Set.Ioo (0:ℝ) 1)ᶜ ∩ Set.Ioc 0 1 ⊆ {1} := by
      intro t ht
      obtain ⟨htc, ht0, ht1⟩ := ht
      rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at htc
      rcases htc with h | h
      · exact absurd ht0 (not_lt.mpr h)
      · exact (le_antisymm ht1 h) ▸ rfl
    exact MeasureTheory.measure_mono_null hsub1 (by simp)
  refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
  exact fun hs' => hs (hsub hs')

omit [CompactSpace M] in
private theorem realizedDeTurckLiePathValue_continuousOn_Icc
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
      (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.congr
    (f := realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) ?_ ?_
  · exact fun s hs =>
      (realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs

omit [CompactSpace M] in
private theorem hasDerivAt_lieDeTurck_realizedMetricPath
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    (∀ s₀ ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
          (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s₀) s₀) ∧
      IntervalIntegrable
        (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
        MeasureTheory.volume 0 1 := by
  refine ⟨fun s₀ hs₀ => ?_, ?_⟩
  · rw [linearizedDeTurckLieAt]
    exact (realizedDeTurckLiePathValue_differentiableAt_Ioo (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs₀).hasDerivAt
  · exact linearizedDeTurckLieAt_intervalIntegrable (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w

omit [CompactSpace M] in
theorem lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w -
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w =
      ∫ s in (0 : ℝ)..1,
        linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  obtain ⟨hderiv, hint⟩ :=
    hasDerivAt_lieDeTurck_realizedMetricPath (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hcont :=
    realizedDeTurckLiePathValue_continuousOn_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hFTC :
      ∫ s in (0 : ℝ)..1,
          linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
        realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 1 -
          realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [hFTC, realizedDeTurckLiePathValue_one, realizedDeTurckLiePathValue_zero]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem hasDerivAt_realizedDeTurckLieChartSum_general
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          deriv (fun s : ℝ =>
            DeTurckCoefficients.chartLieDeTurckComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s₀) s₀ := by
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  have hG := DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedFam_genJointGram
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hbody : (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) =
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) := by
    funext s; rw [realizedDeTurckLieChartSum]
  rw [hbody]
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  refine HasDerivAt.fun_sum (fun j _ => ?_)
  have hcontdiff : ContDiffAt ℝ ∞
      (fun s : ℝ => DeTurckCoefficients.chartLieDeTurckComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s₀ := by
    have hjoint := DifferentialGeometry.PDE.DeTurck.RicciLinearization.gen_joint_chartLieDeTurckComp
      (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') x hG g_bg i j hmem hy
    have hcomp : (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) =
        (fun p : ℝ × E =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.1) g_bg x i j p.2) ∘
          (fun s : ℝ => (s, extChartAt I x x)) := by funext s; rfl
    rw [hcomp]
    exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)
  exact ((hcontdiff.differentiableAt (by simp)).hasDerivAt).const_mul _

private noncomputable def deTurckLieArm0Field
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M)
    g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg

private theorem deTurckLieArm0Field_eq_coeffField
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckLieArm0Field (I := I) g₀ g_bg T T' hδ hδ' s =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M)
        g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg :=
  rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
