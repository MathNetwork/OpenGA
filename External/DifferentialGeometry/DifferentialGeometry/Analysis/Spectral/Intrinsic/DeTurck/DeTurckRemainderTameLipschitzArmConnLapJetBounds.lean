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

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_neg_value
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

private theorem rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
            ((rawTensorConnLapSmooth (I := I) g₀ 0 s S).toSection x) ≤
          C * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 2) x
            ((iteratedCovGrad (I := I) g₀ 0 s 2 S).toSection x) := by
  refine ⟨((Module.finrank ℝ E : ℝ)) ^ 2, by positivity, fun S x => ?_⟩
  have hbase := rawConnLap_fiberNormSq_le_secondCovGrad (I := I) (M := M) g₀ s S x

  simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using hbase

private theorem pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ s S)).toSection x) ≤
          K p * ∑ a ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) := by
  classical
  obtain ⟨H_R, H_dR, hsec⟩ :=
    exists_pointwiseTensorCurv_firstOrder_homField_section (I := I) (M := M) g₀ s
  obtain ⟨ccR, hccR_nn, hccR⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 (s + 1) (s + 1) H_R
  obtain ⟨ccdR, hccdR_nn, hccdR⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 s (s + 1) H_dR
  refine ⟨fun p => 2 * ccR p + 2 * ccdR p,
    fun p => by have := hccR_nn p; have := hccdR_nn p; positivity, fun p S x => ?_⟩
  set rfnsS : ℕ → ℝ := fun a =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
      ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) with hrfnsS_def
  have hrfnsS_nn : ∀ a, 0 ≤ rfnsS a := fun a =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _
  set FULL : ℝ := ∑ a ∈ Finset.range (p + 2), rfnsS a with hFULL_def
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun a _ => hrfnsS_nn a)

  set AR : SmoothCcTensor g₀ 0 (s + 1) :=
    homTensorRSFieldApply (I := I) (M := M) g₀ 0 (s + 1) (s + 1) H_R (covGrad (I := I) (M := M) g₀ 0 s S)
    with hAR_def
  set AdR : SmoothCcTensor g₀ 0 (s + 1) :=
    homTensorRSFieldApply (I := I) (M := M) g₀ 0 s (s + 1) H_dR S with hAdR_def
  have hgradsplit :
      iteratedCovGrad (I := I) g₀ 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g₀ s S) =
        iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR + iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR := by
    rw [hsec S, ← hAR_def, ← hAdR_def, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + 1) p]
  have happ :
      (iteratedCovGrad (I := I) g₀ 0 (s + 1) p
          (pointwiseTensorCurv (I := I) (M := M) g₀ s S)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x := by
    rw [hgradsplit, SmoothCcTensor.toSection_add]; rfl
  rw [happ]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((s + 1) + p) x
    ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x)) ?_

  have hAR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) ≤
        ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) := by

    have hcov1 : covGrad (I := I) (M := M) g₀ 0 s S = iteratedCovGrad (I := I) g₀ 0 s 1 S := rfl
    have h := hccR (iteratedCovGrad (I := I) g₀ 0 s 1 S) p x
    rw [hAR_def, hcov1]
    refine h.trans_eq ?_
    refine congrArg (ccR p * ·) (Finset.sum_congr rfl (fun i _ => ?_))
    have hcomp := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s 1 i S x

    have harg : rfnsS (1 + i) = rfnsS (i + 1) := by rw [Nat.add_comm 1 i]
    rw [← harg, hrfnsS_def]
    exact hcomp
  have hAdR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x) ≤
        ccdR p * ∑ i ∈ Finset.range (p + 1), rfnsS i := by
    have h := hccdR S p x
    rw [hAdR_def]
    exact h.trans_eq (by rw [hrfnsS_def])

  have hsubR : ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) ≤ FULL := by
    rw [hFULL_def]
    have hIco : ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) =
        ∑ a ∈ Finset.Ico 1 (1 + (p + 1)), rfnsS a := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1; omega) (fun i _ => by rw [Nat.add_comm 1 i])
    rw [hIco]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a)
    intro a ha; rw [Finset.mem_Ico] at ha; rw [Finset.mem_range]; omega
  have hsubdR : ∑ i ∈ Finset.range (p + 1), rfnsS i ≤ FULL := by
    rw [hFULL_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a)
    intro a ha; rw [Finset.mem_range] at ha ⊢; omega
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x)
      ≤ 2 * (ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1)) +
          2 * (ccdR p * ∑ i ∈ Finset.range (p + 1), rfnsS i) :=
        add_le_add (by linarith [hAR_w]) (by linarith [hAdR_w])
    _ ≤ 2 * (ccR p * FULL) + 2 * (ccdR p * FULL) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsubR (hccR_nn p)) (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsubdR (hccdR_nn p)) (by norm_num)
    _ = (2 * ccR p + 2 * ccdR p) * FULL := by ring


private theorem iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + m) p
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                  (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s S))).toSection x) ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) := by
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S x => ?_⟩

    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0) (iteratedCovGrad (I := I) g₀ 0 s 0 S) -
            iteratedCovGrad (I := I) g₀ 0 s 0 (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          (0 : SmoothCcTensor g₀ 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad (I := I) g₀ 0 (s + 0) p (0 : SmoothCcTensor g₀ 0 (s + 0)) =
        (0 : SmoothCcTensor g₀ 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 0) p
        (0 : SmoothCcTensor g₀ 0 (s + 0)) (0 : SmoothCcTensor g₀ 0 (s + 0))
      simpa using this
    rw [hz]
    have hzero : ((0 : SmoothCcTensor g₀ 0 (s + 0 + p)).toSection x :
        TensorRSSpace 0 ((s + 0) + p) I x) = 0 := rfl
    rw [show ((0 : SmoothCcTensor g₀ 0 (s + 0 + p)).toSection x) =
        (0 : TensorRSSpace 0 ((s + 0) + p) I x) from hzero]
    rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 0 ((s + 0) + p) x]
    exact mul_nonneg (le_refl 0)
      (Finset.sum_nonneg (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _))
  | succ m ih =>
    intro s
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le (I := I) (M := M) g₀ (s + m)
    refine ⟨fun p => 2 * K p + 2 * Cm (p + 1),
      fun p => by have := hK_nn p; have := hCm_nn (p + 1); positivity, fun p S x => ?_⟩

    have hsplit :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
              (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
            iteratedCovGrad (I := I) g₀ 0 s (m + 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) +
            covGrad (I := I) (M := M) g₀ 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S)]
      change rawTensorConnLapSmooth (I := I) g₀ 0 (s + m + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S)) -
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) +
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S),
        covGrad_sub (I := I) (M := M) g₀ 0 (s + m)]
      abel
    set comm_m : SmoothCcTensor g₀ 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
        iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g₀ 0 (s + m) := iteratedCovGrad (I := I) g₀ 0 s m S with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
        ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _)

    have happ :
        (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
                (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
              iteratedCovGrad (I := I) g₀ 0 s (m + 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))).toSection x =
          (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x +
            (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x := by
      rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + (m + 1)) p,
        SmoothCcTensor.toSection_add]
      rfl
    rw [happ]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
      ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
        (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x)
      ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
        (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x)) ?_

    have harm1 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) ≤
          K p * fullSum := by
      have hKb := hK p gradm x

      have hreindex : ∀ a,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + a) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) := by
        intro a
        rw [hgradm]
        exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s m a S x
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb

      refine hKb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hK_nn p)

      have hIco : ∑ a ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) =
          ∑ b ∈ Finset.Ico m (m + (p + 2)),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + b) x
              ((iteratedCovGrad (I := I) g₀ 0 s b S).toSection x) := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr (by congr 1; omega) (fun a _ => by rw [show m + a = m + a from rfl])
      rw [hfullSum, hIco]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun b _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + b) x _)
      intro b hb; rw [Finset.mem_Ico] at hb; rw [Finset.mem_range]; omega

    have harm2 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x) ≤
          Cm (p + 1) * fullSum := by

      have hCmb := hCm (p + 1) S x
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb

      have h := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 (s + m) 1 p comm_m x
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 (s + m) 0 comm_m,
        iteratedCovGrad_zero] at h

      rw [Nat.add_comm 1 p] at h
      exact h.trans_le hCmb

    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
                (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
                (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x)
        ≤ 2 * (K p * fullSum) + 2 * (Cm (p + 1) * fullSum) :=
          add_le_add (mul_le_mul_of_nonneg_left harm1 (by norm_num))
            (mul_le_mul_of_nonneg_left harm2 (by norm_num))
      _ = (2 * K p + 2 * Cm (p + 1)) * fullSum := by ring

private theorem rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x) ≤
          C * ∑ q ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) := by
  classical

  obtain ⟨Cpost, hCpost_nn, hCpost⟩ :=
    rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet (I := I) (M := M) g₀ (2 + a)

  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux (I := I) (M := M) g₀ a 2
  refine ⟨2 * Cpost + 2 * Cfun 0, by have := hCfun_nn 0; positivity, fun W x => ?_⟩
  set Scol : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _

  set Comm : SmoothCcTensor g₀ 0 (2 + a) :=
    rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W) -
      iteratedCovGrad (I := I) g₀ 0 2 a (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) with hComm_def
  have hsplit :
      iteratedCovGrad (I := I) g₀ 0 2 a (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) =
        rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W) +
          (-Comm) := by
    rw [hComm_def]; abel
  have hsec :
      (iteratedCovGrad (I := I) g₀ 0 2 a
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x =
        (rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x +
          (-Comm).toSection x := by
    rw [hsplit, SmoothCcTensor.toSection_add]; rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + a) x
    ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x)
    ((-Comm).toSection x)) ?_

  have hΔarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
            (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) ≤ Cpost * Scol := by
    refine (hCpost (iteratedCovGrad (I := I) g₀ 0 2 a W) x).trans ?_

    have hreindex :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + a) + 2) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + a) 2 (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (a + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (a + 2) W).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 a 2 W x
    rw [hreindex]
    refine mul_le_mul_of_nonneg_left ?_ hCpost_nn
    rw [hScol_def]
    refine Finset.single_le_sum
      (f := fun q => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _) ?_
    rw [Finset.mem_range]; omega

  have hCommarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) ≤
        Cfun 0 * Scol := by

    have hneg : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x) := by
      rw [SmoothCcTensor.toSection_neg]
      rw [show ((-Comm.toSection) x : TensorRSSpace 0 (2 + a) I x) = -(Comm.toSection x) from rfl]
      exact riemannianFiberNormSq_neg_value (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x)
    rw [hneg]

    have hC := hCfun 0 W x
    rw [iteratedCovGrad_zero] at hC
    refine hC.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCfun_nn 0)
    rw [hScol_def]

    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun q _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)
    intro q hq; rw [Finset.mem_range] at hq ⊢; omega
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
              (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x)
      ≤ 2 * (Cpost * Scol) + 2 * (Cfun 0 * Scol) :=
        add_le_add (mul_le_mul_of_nonneg_left hΔarm (by norm_num))
          (mul_le_mul_of_nonneg_left hCommarm (by norm_num))
    _ = (2 * Cpost + 2 * Cfun 0) * Scol := by ring

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma norm_iteratedFDerivWithin_rawCompOnE_le_iteratedFDeriv_rawPullR
    (g : SmoothRiemannianMetric I M)
    (S : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDerivWithin ℝ m
        (DeTurckCoefficients.tensorChartComponentOnModel (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖ ≤
      ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ m *
        ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α
            (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) ((toEuclidean (E := E)) y)‖ := by
  classical
  set e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean (E := E) with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hUD : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn

  have hcompose :
      DeTurckCoefficients.tensorChartComponentOnModel (I := I) (M := M) g S α Jdx =
        tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx ∘ ⇑e := by
    have hpull := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have := congrArg (fun f => f (e z)) hpull
    simp only [Function.comp_apply, he_def, ContinuousLinearEquiv.symm_apply_apply] at this ⊢
    rw [← this]
  rw [hcompose]

  have himg_open : IsOpen (e '' O) := e.isOpenMap _ hO_open
  have hey_mem : e y ∈ e '' O := ⟨y, hy, rfl⟩
  have hOeq : O = e ⁻¹' (e '' O) := by
    ext z; constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩; rwa [e.injective hwz] at hw

  have hcomp := e.iteratedFDerivWithin_comp_right
    (f := tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    himg_open.uniqueDiffOn (x := y) hey_mem m
  rw [← hOeq] at hcomp
  rw [hcomp]

  have hplain : iteratedFDerivWithin ℝ m
      (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
      (e '' O) (e y) =
      iteratedFDeriv ℝ m
        (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (e y) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m himg_open hey_mem
  rw [hplain]

  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he_norm : ‖(e : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ =
      ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ := rfl
  rw [he_norm, mul_comm]

omit [BoundarylessManifold I M] in
private lemma bareChartJetContent_le_sqrt_fiberNormSq_sum_uniform
    (g : SmoothRiemannianMetric I M) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : SmoothCcTensor g 0 2) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))},
        y ∈ DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel (I := I) (M := M) α →
        bareChartJetContent (I := I) (M := M) g 0 2 D α N y ≤
          C * ∑ i ∈ Finset.range (N + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((iteratedCovGrad (I := I) g 0 2 i D).toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    DifferentialGeometry.PDE.RicciFlow.iteratedFDeriv_rawPullR_le_zeroContent_sum
      (I := I) (M := M) g 0 2 α N N (le_refl N)
  obtain ⟨Cfib0, hCfib0_nn, hCfib0⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_zeroContentR_le_fiberNorm_on_pouKernel
      (I := I) (M := M) g 0 2 α

  have h_fib : ∀ i : ℕ, ∃ Ci : ℝ, 0 ≤ Ci ∧
      ∀ (D : SmoothCcTensor g 0 2)
        {z : EuclideanSpace ℝ (Fin n)},
        z ∈ DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel (I := I) (M := M) α →
        tensorComponentAbsSum (I := I) (M := M) g 0 (2 + i)
          (iteratedCovGrad (I := I) g 0 2 i D) α z ≤
          Ci * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
            ((iteratedCovGrad (I := I) g 0 2 i D).toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))) := by
    intro i
    obtain ⟨Ci, hCi_nn, hCi⟩ :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_zeroContentR_le_fiberNorm_on_pouKernel
        (I := I) (M := M) g 0 (2 + i) α
    refine ⟨Ci, hCi_nn, fun D {z} hz => ?_⟩
    refine (hCi (iteratedCovGrad (I := I) g 0 2 i D) hz).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCi_nn
    letI : Bundle.RiemannianBundle (fun w : M => TensorRSSpace 0 (2 + i) I w) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (2 + i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      ((iteratedCovGrad (I := I) g 0 2 i D).toSection
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))]
    exact norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g 0 (2 + i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      ((iteratedCovGrad (I := I) g 0 2 i D).toSection
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
  choose Cfib hCfib_nn hCfib using h_fib
  set Cfibmax : ℝ := (Finset.range (N + 1)).sup' (by simp) Cfib with hCfibmax_def
  have hCfibmax_nn : 0 ≤ Cfibmax :=
    le_trans (hCfib_nn 0) (Finset.le_sup' Cfib (by simp))
  set Npair : ℝ := (Fintype.card ((Fin 0 → Fin n) × (Fin 2 → Fin n)) : ℝ) with hNpair_def
  have hNpair_nn : 0 ≤ Npair := by positivity
  refine ⟨Npair * (Cpeel * (((N : ℝ) + 1) * Cfibmax)), by positivity, ?_⟩
  intro D y hyK
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  set Fib : ℕ → ℝ := fun i => Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
    ((iteratedCovGrad (I := I) g 0 2 i D).toSection b)) with hFib_def
  have hFib_nn : ∀ i, 0 ≤ Fib i := fun i => Real.sqrt_nonneg _
  set FibSum : ℝ := ∑ i ∈ Finset.range (N + 1), Fib i with hFibSum_def
  have hFibSum_nn : 0 ≤ FibSum := Finset.sum_nonneg fun i _ => hFib_nn i
  have hyK' : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartImagePOUTsupport
      (I := I) (M := M) α := hyK
  have h_zc : ∀ i ∈ Finset.range (N + 1),
      tensorComponentAbsSum (I := I) (M := M) g 0 (2 + i)
        (iteratedCovGrad (I := I) g 0 2 i D) α y ≤ Cfibmax * Fib i := by
    intro i hi
    have hiN : i < N + 1 := Finset.mem_range.mp hi
    have hzc := hCfib i D hyK
    refine hzc.trans ?_
    rw [hFib_def, hb_def]
    exact mul_le_mul_of_nonneg_right
      (Finset.le_sup' Cfib (Finset.mem_range.mpr hiN)) (Real.sqrt_nonneg _)
  have h_each : ∀ q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
      (∑ m ∈ Finset.range (N + 1),
        ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖) ≤
      (Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum := by
    intro q'
    have h_per : ∀ m ∈ Finset.range (N + 1),
        ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖ ≤
          Cpeel * (Cfibmax * FibSum) := by
      intro m hm
      have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hpeel := hCpeel D m hmN 0 (by omega) q'.1 q'.2 y hyK'
      have h0eq : (iteratedCovGrad (I := I) g 0 2 0 D) = D :=
        DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero (I := I) g 0 2 D
      rw [h0eq] at hpeel
      have hreindex : (∑ i ∈ Finset.range (m + 1),
            tensorComponentAbsSum (I := I) (M := M) g 0 (2 + (0 + i))
              (iteratedCovGrad (I := I) g 0 2 (0 + i) D) α y) =
          ∑ i ∈ Finset.range (m + 1),
            tensorComponentAbsSum (I := I) (M := M) g 0 (2 + i)
              (iteratedCovGrad (I := I) g 0 2 i D) α y := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        congr 1 <;> rw [Nat.zero_add]
      rw [hreindex] at hpeel
      refine hpeel.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCpeel_nn
      calc (∑ i ∈ Finset.range (m + 1),
            tensorComponentAbsSum (I := I) (M := M) g 0 (2 + i)
              (iteratedCovGrad (I := I) g 0 2 i D) α y)
          ≤ ∑ i ∈ Finset.range (m + 1), Cfibmax * Fib i :=
            Finset.sum_le_sum (fun i hi => h_zc i
              (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi)
                (Nat.succ_le_succ hmN))))
        _ = Cfibmax * ∑ i ∈ Finset.range (m + 1), Fib i := by rw [Finset.mul_sum]
        _ ≤ Cfibmax * FibSum := by
            refine mul_le_mul_of_nonneg_left ?_ hCfibmax_nn
            rw [hFibSum_def]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (by omega)) (fun i _ _ => hFib_nn i)
    refine (Finset.sum_le_sum h_per).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  calc bareChartJetContent (I := I) (M := M) g 0 2 D α N y
      = ∑ q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          ∑ m ∈ Finset.range (N + 1),
            ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖ := rfl
    _ ≤ ∑ _q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          (Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum :=
        Finset.sum_le_sum (fun q' _ => h_each q')
    _ = Npair * ((Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNpair_def]
    _ = (Npair * (Cpeel * (((N : ℝ) + 1) * Cfibmax))) * FibSum := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_toSection_congr
    (g g' : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (S' : SmoothCcTensor g' r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M)
    (hSS' : S.toSection x = S'.toSection x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g r s S α Idx Jdx x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g' r s S' α Idx Jdx x := by
  unfold DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj
  rw [hSS']

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma tensorChartComponentRaw_sub'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s S₁ α Idx Jdx x -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s S₂ α Idx Jdx x := by
  have hsub : S₁ - S₂ = S₁ + (-1 : ℝ) • S₂ := by
    rw [neg_one_smul]; abel
  rw [hsub,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_add
      (I := I) (M := M) g r s S₁ ((-1 : ℝ) • S₂) α Idx Jdx x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul
      (I := I) (M := M) g r s (-1 : ℝ) S₂ α Idx Jdx x]
  rw [smul_eq_mul]; ring

private lemma deTurckRHSArm_toSection_eq
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')).toSection =
      ((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
        (deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')).toSection) := by
  classical
  rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub]
  rw [rawTensorConnLapSmooth_sub (I := I) g₀ 0 2 T T']

  change (((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection) -
      ((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T').toSection)) +
      ((rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T').toSection) =
      _
  abel

private lemma tensorChartComponentRaw_deTurckRHSArm_eq_chartDeTurckRicciRHS_diff
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) {b : M}
    (hb : b ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2
        ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))
        α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) g_bg α (Jdx 0) (Jdx 1)
          (extChartAt I α b) -
        DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') g_bg α (Jdx 0) (Jdx 1)
          (extChartAt I α b) := by
  classical
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁_def
  set g₂ := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₂_def
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  set S₁ : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSectionBg (I := I) g_bg g₁).toSection
      hasCompactSupport := (deTurckRHSSectionBg (I := I) g_bg g₁).hasCompactSupport } with hS₁_def
  set S₂ : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSectionBg (I := I) g_bg g₂).toSection
      hasCompactSupport := (deTurckRHSSectionBg (I := I) g_bg g₂).hasCompactSupport } with hS₂_def

  have hsec : RHSarm.toSection = (S₁ - S₂).toSection := by
    rw [SmoothCcTensor.toSection_sub]
    exact deTurckRHSArm_toSection_eq (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  have hRHSeq : RHSarm = S₁ - S₂ := by
    apply DifferentialGeometry.Integral.L2.SmoothCcTensor.ext
    exact hsec
  rw [hRHSeq]

  rw [tensorChartComponentRaw_sub' (I := I) (M := M) g₀ 0 2 S₁ S₂ α _ Jdx b]
  have hS₁comp : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 S₁ α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₁ g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
    rw [tensorChartComponentRaw_toSection_congr (I := I) (M := M) g₀ g_bg 0 2 S₁
      (deTurckRHSSectionBg (I := I) g_bg g₁) α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b rfl]
    rw [DeTurckCoefficients.chartDeTurckRicciRHS_def]
    rw [← DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) g_bg g₁ α hb (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx]
  have hS₂comp : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 S₂ α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₂ g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
    rw [tensorChartComponentRaw_toSection_congr (I := I) (M := M) g₀ g_bg 0 2 S₂
      (deTurckRHSSectionBg (I := I) g_bg g₂) α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b rfl]
    rw [DeTurckCoefficients.chartDeTurckRicciRHS_def]
    rw [← DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) g_bg g₂ α hb (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx]
  rw [hS₁comp, hS₂comp]

end InnerProductSpaceModel

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem ccTensorBilinSymm_symmS_app
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T) x v w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilin_symmS, ccTensorBilin_symmS,
    ccTensorBilinSymm_symm (I := I) g₀ T x w v, ccTensorBilinSymm_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem gFibreOpBound_ccTensorBilinSymm_symmS
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T)) δ := by
  intro x v w
  rw [ccTensorBilinSymm_symmS_app (I := I) g₀ T x v w]
  exact hδ x v w

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorBilin_symmS_symm
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (v w : TangentSpace I x) :
    smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T) x v w =
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T) x w v := by
  rw [ccTensorBilin_symmS, ccTensorBilin_symmS, ccTensorBilinSymm_symm]

omit [BoundarylessManifold I M] in
theorem tensorSectionRealizeMetric_symmS_eq
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ₁ : ℝ} (hδ₁_lt : δ₁ < 1)
    (hδ₁ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T)) δ₁) :
    tensorSectionRealizeMetric (I := I) g₀ (ccTensor02Symm (I := I) g₀ T) hδ₁_lt hδ₁ =
      tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
  refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
    _ _ (fun b u z => ?_)
  rw [tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner,
    ccTensorBilinSymm_symmS_app (I := I) g₀ T b u z]

end NormedSpaceModel

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorL2Norm_iteratedCovGrad_domDomCongrSection_eq
    (g₀ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 2))
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ_def
  have hbridge : ∀ (W : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 k W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k W).toSection x) ∂μ := by
    intro W
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 k W), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + k)
      (iteratedCovGrad (I := I) g₀ 0 2 k W)
  have hintegrand : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g₀ (s := 2) σ T k x
  have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ ^ 2 := by
    rw [hbridge (domDomCongrSection (I := I) g₀ σ T), hbridge T]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hintegrand)
  have hnnA : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ :=
    norm_nonneg _
  have hnnB : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := norm_nonneg _
  exact (sq_eq_sq₀ hnnA hnnB).mp hsq

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Norm_iteratedCovGrad_symmS_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) g₀ T)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := by
  classical
  set Tsw : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T with hTsw_def
  have hiter_eq : iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k Tsw := by
    rw [hTsw_def]; exact iteratedCovGrad_symmS_eq (I := I) g₀ T k
  rw [hiter_eq]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by rw [Real.norm_eq_abs]; norm_num
  rw [habs, hTsw_def,
    tensorL2Norm_iteratedCovGrad_domDomCongrSection_eq (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T k]
  have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := norm_nonneg _
  linarith

end NormedSpaceModel

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def deTurckRHSArmG0 (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport

omit [BoundarylessManifold I M] in
theorem deTurckRHSArmG0_symmS_eq
    (g₀ g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ₁ : ℝ} (hδ₁_lt : δ₁ < 1)
    (hδ₁ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) g₀ T)) δ₁) :
    deTurckRHSArmG0 (I := I) g₀ g_bg (ccTensor02Symm (I := I) g₀ T) hδ₁_lt hδ₁ =
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ := by
  refine SmoothCcTensor.ext ?_
  change (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ (ccTensor02Symm (I := I) g₀ T) hδ₁_lt hδ₁)).toSection =
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
  rw [tensorSectionRealizeMetric_symmS_eq (I := I) g₀ T hδ_lt hδ hδ₁_lt hδ₁]

private theorem deTurckSmoothRemainder_eq_arm_sub_connLap
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ =
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 T :=
  rfl

theorem deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' =
      (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
          deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') := by
  rw [deTurckSmoothRemainder_eq_arm_sub_connLap (I := I) g₀ g_bg T hδ_lt hδ,
    deTurckSmoothRemainder_eq_arm_sub_connLap (I := I) g₀ g_bg T' hδ'_lt hδ',
    rawTensorConnLapSmooth_sub (I := I) g₀ 0 2 T T']
  abel

end NormedSpaceModel

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem l2RootSum_of_pointwise_iteratedCovGrad_jet
    (g₀ : SmoothRiemannianMetric I M) (q N : ℕ)
    (P W : SmoothCcTensor g₀ 0 2) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ≤
        C * ∑ i ∈ Finset.range (N + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ≤
      Real.sqrt C * Real.sqrt (∑ i ∈ Finset.range (N + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ_def

  have hbridgeP : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 q P), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + q)
      (iteratedCovGrad (I := I) g₀ 0 2 q P)
  have hbridgeW : ∀ i, ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) ∂μ := by
    intro i
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 i W), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i W)

  have hintW : ∀ i, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) μ := by
    intro i; rw [hμ_def]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i W)

  set Scol : ℝ := ∑ i ∈ Finset.range (N + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2
    with hScol_def
  have hScol_nn : 0 ≤ Scol := Finset.sum_nonneg fun i _ => sq_nonneg _

  set RHS : M → ℝ := fun x =>
    C * ∑ i ∈ Finset.range (N + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) with hRHS_def
  have hsum_int : MeasureTheory.Integrable
      (fun x => ∑ i ∈ Finset.range (N + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) μ :=
    MeasureTheory.integrable_finset_sum (Finset.range (N + 1)) (fun i _ => hintW i)
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def]; exact hsum_int.const_mul C
  have hP_nn_ae : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)

  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hP_nn_ae hRHS_int
      (Filter.Eventually.of_forall (fun x => by rw [hRHS_def]; exact hpt x))
  have hRHS_integral : (∫ x, RHS x ∂μ) = C * Scol := by
    rw [hRHS_def, MeasureTheory.integral_const_mul, hScol_def,
      MeasureTheory.integral_finset_sum (Finset.range (N + 1)) (fun i _ => hintW i)]
    refine congrArg (C * ·) (Finset.sum_congr rfl (fun i _ => (hbridgeW i).symm))

  have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤ C * Scol := by
    rw [hbridgeP]; exact hint_le.trans_eq hRHS_integral

  have hPq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ := norm_nonneg _
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖
      = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := (Real.sqrt_sq hPq_nn).symm
    _ ≤ Real.sqrt (C * Scol) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt C * Real.sqrt Scol := Real.sqrt_mul hC Scol

theorem rawTensorConnLapSmooth_iteratedCovGrad_l2_tame
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (q : ℕ), q ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)‖ ≤
          C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) := by
  classical

  choose Cfam hCfam_nn hCfam using
    (fun q : ℕ => rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le
      (I := I) (M := M) g₀ q)
  set Cunif : ℝ := ∑ q ∈ Finset.range (a + 1), Cfam q with hCunif_def
  have hCunif_nn : 0 ≤ Cunif :=
    Finset.sum_nonneg fun q _ => hCfam_nn q
  refine ⟨Real.sqrt Cunif, Real.sqrt_nonneg _, fun W q hq => ?_⟩

  have hCfam_le_Cunif : Cfam q ≤ Cunif := by
    rw [hCunif_def]
    exact Finset.single_le_sum (f := Cfam) (fun i _ => hCfam_nn i)
      (Finset.mem_range.mpr (by omega))
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x) ≤
        Cunif * ∑ i ∈ Finset.range (a + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) := by
    intro x
    refine (hCfam q W x).trans ?_

    have hqle : q + 2 + 1 ≤ a + 2 + 1 := by omega
    have hwindow : (∑ i ∈ Finset.range (q + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) ≤
        ∑ i ∈ Finset.range (a + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hqle)
        (fun i _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
      Finset.sum_nonneg fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _
    calc Cfam q * ∑ i ∈ Finset.range (q + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)
        ≤ Cfam q * ∑ i ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
          mul_le_mul_of_nonneg_left hwindow (hCfam_nn q)
      _ ≤ Cunif * ∑ i ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
          mul_le_mul_of_nonneg_right hCfam_le_Cunif hsum_nn

  exact l2RootSum_of_pointwise_iteratedCovGrad_jet (I := I) g₀ q (a + 2)
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) W Cunif hCunif_nn hpt

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem deTurckArmDiff_supercritical_pointwise_jet_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (∑ q ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
          Cemb ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  classical

  set k : ℕ := Module.finrank ℝ E / 2 + 3 with hk_def
  have hk_super : 2 * k > Module.finrank ℝ E + 4 := by rw [hk_def]; omega
  have h4k_le : 4 * k ≤ a + 2 := by rw [hk_def]; omega

  obtain ⟨Cc, hCc_pos, hCc⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_singleNorm (I := I) (M := M) g₀ k hk_super
  obtain ⟨Ch, hCh_nn, hCh⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * k)
  refine ⟨Real.sqrt (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)), Real.sqrt_nonneg _,
    fun W x => ?_⟩
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _

  set Mn : ℝ := ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) (2 * k) W‖ with hMn_def
  have hMn_nn : 0 ≤ Mn := norm_nonneg _
  have hCol := hCc W x

  have hHebey : Mn ≤ Ch * ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    refine le_trans (hCh W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCh_nn
    refine le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))
    exact (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm

  set Jsum : ℝ := ∑ j ∈ Finset.range (2 * (2 * k) + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ with hJsum_def
  have hJsum_nn : 0 ≤ Jsum := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hwin : (2 * (2 * k) + 1) ≤ a + 2 + 1 := by omega
  have hcol_sq_le : (∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2) ≤ S := by
    rw [hS_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
      (fun i _ _ => sq_nonneg _)
  have hJsq : Jsum ^ 2 ≤ ((4 * k + 1 : ℕ) : ℝ) * S := by
    have hcs : Jsum ^ 2 ≤
        ((2 * (2 * k) + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (2 * (2 * k) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2 := by
      rw [hJsum_def]
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range (2 * (2 * k) + 1))
        (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hcard_eq : (2 * (2 * k) + 1 : ℕ) = (4 * k + 1 : ℕ) := by omega
    rw [hcard_eq] at hcs hcol_sq_le
    refine le_trans hcs ?_
    exact mul_le_mul_of_nonneg_left hcol_sq_le (by positivity)

  have hMn_sq : Mn ^ 2 ≤ Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S) := by
    have hstep : Mn ^ 2 ≤ (Ch * Jsum) ^ 2 := pow_le_pow_left₀ hMn_nn hHebey 2
    calc Mn ^ 2 ≤ (Ch * Jsum) ^ 2 := hstep
      _ = Ch ^ 2 * Jsum ^ 2 := by ring
      _ ≤ Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S) :=
          mul_le_mul_of_nonneg_left hJsq (by positivity)

  letI inst0 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI inst1 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI inst2 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 2) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  have hcolsq_le : (∑ q ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤ 3 * (Cc * Mn) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add,
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add] at hCol
    have h0 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x‖ := norm_nonneg _
    have h1 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x‖ := norm_nonneg _
    have h2 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x‖ := norm_nonneg _
    nlinarith [hCol, h0, h1, h2, hMn_nn, hCc_pos.le, mul_nonneg hCc_pos.le hMn_nn]

  have hsqrt_sq : Real.sqrt (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)) ^ 2 =
      3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [hsqrt_sq]
  calc (∑ q ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      ≤ 3 * (Cc * Mn) ^ 2 := hcolsq_le
    _ = 3 * Cc ^ 2 * Mn ^ 2 := by ring
    _ ≤ 3 * Cc ^ 2 * (Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S)) :=
        mul_le_mul_of_nonneg_left hMn_sq (by positivity)
    _ = (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)) * S := by ring

end NormedSpaceModel

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
