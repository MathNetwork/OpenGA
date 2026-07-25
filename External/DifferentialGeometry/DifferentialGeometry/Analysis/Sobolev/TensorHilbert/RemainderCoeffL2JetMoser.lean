import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurckArmCoeffPerOrderJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmOrder1KoszulTameEnvelope
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurckArm0CurvatureDifferenceJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureArm1KoszulTopSeparation


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (linearizedRicciArm0BaseCoeff linearizedRicciArm1BaseCoeff ricciArmPrincipalCoeff
    traceHessianCoeff traceHessianCoeff_toSection traceHessianFib traceHessianSlotPerm
    domDomCongrFib domDomCongrFib_apply deTurckPrincipalCometricCoeff
    deTurckPrincipalCometricCoeff_toSection_clm_eq
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff
    reindexCoeffGen reindexCoeffGen_toSection reindexCoeffFibGen_apply
    ricciArmOrder0RiemannCoeff ricciArmOrder0CurvCoeff ricciArmOrder1KoszulCoeff raisedKoszul)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
theorem linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
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
              (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i := by
  obtain ⟨K, hK_nn, hK⟩ := ricciArmOrder0BaseCoeff_perOrder_l2_ballUniform_generic
    (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
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
  exact hK (realizedFam (I := I) g₀ T T' hδ hδ' s) (convexPerturbation (I := I) g₀ T T' s)
    hδP_le hδP htie hPball i hi

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
theorem linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
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
              (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i := by
  obtain ⟨K, hK_nn, hK⟩ := ricciArmOrder1KoszulCoeff_perOrder_l2_ballUniform_generic
    (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
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
  exact hK (realizedFam (I := I) g₀ T T' hδ hδ' s) (convexPerturbation (I := I) g₀ T T' s)
    hδP_le hδP htie hPball i hi

theorem ricciArmPrincipalCoeff_sub_background_perOrder_riemannianFiberNormSq_le_gInvDiffSlotCoeff_riemannianFiberNormSq
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeff_sub_perOrder_rfns_le_gInvDiffSlotCoeff
    g₀

theorem ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
  obtain ⟨C, hC_nn, hP⟩ :=
    ricciArmPrincipalCoeff_sub_background_perOrder_riemannianFiberNormSq_le_gInvDiffSlotCoeff_riemannianFiberNormSq
      (I := I) (M := M) g₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ i
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i
      (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
        - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hP g₁ i x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm

theorem ricciArmPrincipalCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ D : ℕ → ℝ, (∀ i, 0 ≤ D i) ∧
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
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ D i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    gInvDiffSlotCoeff_realizedFam_perOrder_l2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨C, hC_nn, hC⟩ :=
    ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  refine ⟨fun i => C i * ∑ j ∈ Finset.range (i + 1), K j,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun j _ => hK_nn j), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
      ≤ C i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
        hC (realizedFam (I := I) g₀ T T' hδ hδ' s) i
    _ ≤ C i * ∑ j ∈ Finset.range (i + 1), K j := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (hC_nn i)
        intro j hj
        exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball j
          (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi) s hs

theorem ricciArmPrincipalCoeff_realizedFam_jetL2_perOrder_ballUniform
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
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i := by
  obtain ⟨D, hD_nn, hD⟩ :=
    ricciArmPrincipalCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
      (I := I) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + 2 * D i,
    fun i => add_nonneg (by positivity) (by linarith [hD_nn i]), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hq2 := hD T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  set A := ricciArmPrincipalCoeff (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) with hA
  set B := ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀ with hB
  have hgrad : iteratedCovGrad (I := I) g₀ 4 2 i A
      = iteratedCovGrad (I := I) g₀ 4 2 i B + iteratedCovGrad (I := I) g₀ 4 2 i (A - B) := by
    have h := iteratedCovGrad_add (I := I) g₀ 4 2 i B (A - B)
    have hBA : B + (A - B) = A := by abel
    rw [hBA] at h
    exact h
  have htri : ‖iteratedCovGrad (I := I) g₀ 4 2 i A‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 4 2 i B‖ + ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖ := by
    rw [hgrad]
    exact norm_add_le _ _
  have hp_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i B‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖ := norm_nonneg _
  have hA_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i A‖ := norm_nonneg _
  nlinarith [htri, hq2, hp_nn, hq_nn, hA_nn,
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i B‖
      - ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖),
    mul_le_mul htri htri hA_nn (add_nonneg hp_nn hq_nn)]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem traceHessianCoeff_sub_eq_reindex_deTurckPrincipalCometricCoeff
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g₀ g₁ - traceHessianCoeff (I := I) (M := M) g₀ g₀ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    traceHessianCoeff_toSection, traceHessianCoeff_toSection, reindexCoeffGen_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    deTurckPrincipalCometricCoeff_toSection_clm_eq, ContinuousLinearMap.sub_apply,
    traceHessianFib, traceHessianFib, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, domDomCongrFib_apply]

theorem traceHessianCoeff_sub_background_perOrder_riemannianFiberNormSq_le_gInvDiffSlotCoeff_riemannianFiberNormSq
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ i x
  rw [traceHessianCoeff_sub_eq_reindex_deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁,
    riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) traceHessianSlotPerm i x]
  exact hC g₁ i x

theorem traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (traceHessianCoeff (I := I) (M := M) g₀ g₁
              - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
  obtain ⟨C, hC_nn, hP⟩ :=
    traceHessianCoeff_sub_background_perOrder_riemannianFiberNormSq_le_gInvDiffSlotCoeff_riemannianFiberNormSq
      (I := I) (M := M) g₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ i
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i
      (traceHessianCoeff (I := I) (M := M) g₀ g₁
        - traceHessianCoeff (I := I) (M := M) g₀ g₀))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hP g₁ i x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm

theorem traceHessianCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ D : ℕ → ℝ, (∀ i, 0 ≤ D i) ∧
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
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ D i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    gInvDiffSlotCoeff_realizedFam_perOrder_l2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨C, hC_nn, hC⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  refine ⟨fun i => C i * ∑ j ∈ Finset.range (i + 1), K j,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun j _ => hK_nn j), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
      ≤ C i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
        hC (realizedFam (I := I) g₀ T T' hδ hδ' s) i
    _ ≤ C i * ∑ j ∈ Finset.range (i + 1), K j := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (hC_nn i)
        intro j hj
        exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball j
          (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi) s hs

theorem traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform
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
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i := by
  obtain ⟨D, hD_nn, hD⟩ :=
    traceHessianCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
      (I := I) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + 2 * D i,
    fun i => add_nonneg (by positivity) (by linarith [hD_nn i]), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hq2 := hD T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  set A := traceHessianCoeff (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) with hA
  set B := traceHessianCoeff (I := I) (M := M) g₀ g₀ with hB
  have hgrad : iteratedCovGrad (I := I) g₀ 4 2 i A
      = iteratedCovGrad (I := I) g₀ 4 2 i B + iteratedCovGrad (I := I) g₀ 4 2 i (A - B) := by
    have h := iteratedCovGrad_add (I := I) g₀ 4 2 i B (A - B)
    have hBA : B + (A - B) = A := by abel
    rw [hBA] at h
    exact h
  have htri : ‖iteratedCovGrad (I := I) g₀ 4 2 i A‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 4 2 i B‖ + ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖ := by
    rw [hgrad]
    exact norm_add_le _ _
  have hp_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i B‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖ := norm_nonneg _
  have hA_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i A‖ := norm_nonneg _
  nlinarith [htri, hq2, hp_nn, hq_nn, hA_nn,
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i B‖
      - ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖),
    mul_le_mul htri htri hA_nn (add_nonneg hp_nn hq_nn)]

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
theorem linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨K, hK_nn, hK⟩ := ricciArmOrder0BaseCoeff_perOrder_l2_tameEnvelope_generic
    (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
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
  have hwin : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤
        (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
    nlinarith [mul_le_mul hnorm_le hnorm_le (norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  have hmain := hK (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2
      = ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := rfl
    _ ≤ K i * (1 + ∑ j ∈ Finset.range (i + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) := hmain
    _ ≤ K i * (1 + ∑ j ∈ Finset.range (i + 3),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (hK_nn i)
        have hsum := Finset.sum_le_sum
          (fun j (_ : j ∈ Finset.range (i + 3)) => hwin j)
        linarith

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
theorem linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨K, hK_nn, hK⟩ := ricciArmOrder1KoszulCoeff_perOrder_l2_tameEnvelope_generic
    (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
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
  have hwin : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤
        (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
    nlinarith [mul_le_mul hnorm_le hnorm_le (norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  have hmain := hK (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  calc ‖iteratedCovGrad (I := I) g₀ 3 2 i
          (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2
      = ‖iteratedCovGrad (I := I) g₀ 3 2 i
          (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := rfl
    _ ≤ K i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) := hmain
    _ ≤ K i * (1 + ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (hK_nn i)
        have hsum := Finset.sum_le_sum
          (fun j (_ : j ∈ Finset.range (i + 2)) => hwin j)
        linarith

section TopSeparatedRealizedFamily

open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsmRfns_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsmRfns_order_congr (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad (I := I) g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad (I := I) g r s n' S).toSection x) := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma tsmAppCcRS_coeffCorner_split (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) (W : SmoothCcTensor g₀ a b) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ a c j (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j)
          (iteratedCovGrad (I := I) g₀ b c j Φ) W +
        ∑ k ∈ Finset.range j,
          ccOperatorFieldComp (I := I) (M := M) g₀ a (b + (k + 1)) (c + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j (k + 1))
            (iteratedCovGrad (I := I) g₀ a b (k + 1) W) := by
  rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ a b c Φ W j]
  rw [Finset.sum_range_succ' (fun k =>
    ccOperatorFieldComp (I := I) (M := M) g₀ a (b + k) (c + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j k)
      (iteratedCovGrad (I := I) g₀ a b k W)) j]
  have hf0 : ccOperatorFieldComp (I := I) (M := M) g₀ a (b + 0) (c + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j 0)
      (iteratedCovGrad (I := I) g₀ a b 0 W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j)
        (iteratedCovGrad (I := I) g₀ b c j Φ) W :=
    congrArg (fun Z : SmoothCcTensor g₀ b (c + j) =>
      ccOperatorFieldComp (I := I) (M := M) g₀ a b (c + j) Z W)
      (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ b c Φ j)
  rw [hf0]
  exact add_comm _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma tsmNormSq_eq_integral (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) :
    ‖C‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsmNormSq_covGrad_shift (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + 1) n (covGrad (I := I) (M := M) g r s Φ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (n + 1) Φ‖ ^ 2 := by
  rw [tsmNormSq_eq_integral (I := I) (M := M) g r ((s + 1) + n), tsmNormSq_eq_integral
    (I := I) (M := M) g r (s + (n + 1))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g r s n Φ x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem ricciArmOrder1KoszulCoeff_perOrder_l2_topSeparated_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ∃ Hd : SmoothCcTensor g₀ 3 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
                (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨ΛA, FA, hΛA_nn, hFA_nn, hAfeed⟩ :=
    raisedKoszul_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛB, FB, hΛB_nn, hFB_nn, hBfeed⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set ΛS : ℝ := Real.sqrt (10 * (Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2)) with hΛS_def
  have hΛS_nn : 0 ≤ ΛS := Real.sqrt_nonneg _
  have hΛS_sq : ΛS ^ 2 = 10 * (Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) := by
    rw [hΛS_def]
    exact Real.sq_sqrt (by positivity)
  set Cta : ℕ → ℝ := fun i =>
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 3 3 1 (i - 1)).choose with hCta_def
  have hCta_nn : ∀ i, 0 ≤ Cta i := fun i =>
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 3 3 1 (i - 1)).choose_spec.1
  refine ⟨10 * ΛB ^ 2, by positivity, ?_⟩
  refine ⟨fun i => (i : ℝ) ^ 2 * diagonalGridGrowthFactor (E := E) i *
      (ΛA ^ 2 * FB i + Cta i * (ΛB ^ 2 * FA i + ΛS ^ 2 * FB i)),
    fun i => mul_nonneg (mul_nonneg (sq_nonneg _) (appCcGdiag_nonneg (E := E) i))
      (add_nonneg (mul_nonneg (sq_nonneg ΛA) (hFB_nn i))
        (mul_nonneg (hCta_nn i)
          (add_nonneg (mul_nonneg (sq_nonneg ΛB) (hFA_nn i))
            (mul_nonneg (sq_nonneg ΛS) (hFB_nn i))))), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hia
  obtain ⟨hAsup, hAsum⟩ := hAfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hBsup, hBsum⟩ := hBfeed g₁ P hδ_le hδ htie hPball
  set K1 : SmoothCcTensor g₀ 1 2 := raisedKoszul (I := I) g₀ g₁ with hK1_def
  set W1 : SmoothCcTensor g₀ 3 1 := cometricDoubleTraceCastG0 (I := I) g₀ g₁ with hW1_def
  have hP2sup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤
      Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
    intro x
    have h1 := hCemb P x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤
        ∑ m ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) :=
      Finset.single_le_sum
        (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
        (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _)
        (Finset.mem_range.mpr (by omega))
    have h3 : (∑ j ∈ Finset.range (a + 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
      calc (∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            rw [Finset.mem_range] at hj
            have hb := hPball j (by omega)
            nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P)]
        _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x)
        ≤ ∑ m ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := h2
      _ ≤ Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := h1
      _ ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
  have hSsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 3 x
        ((covGrad (I := I) (M := M) g₀ 1 2 K1).toSection x) ≤ ΛS ^ 2 := by
    intro x
    have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 0 K1 x
    rw [iteratedCovGrad_zero] at hcomm
    have hK1jet := rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M)
      g₀ g₁ P htie 1 x
    rw [hΛS_sq]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 3 x
          ((covGrad (I := I) (M := M) g₀ 1 2 K1).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (0 + 1)) x
            ((iteratedCovGrad (I := I) g₀ 1 2 (0 + 1) K1).toSection x) := hcomm
      _ ≤ 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (1 + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (1 + 1) P).toSection x) := by
          have h := hK1jet
          rw [hK1_def]
          exact h
      _ ≤ 10 * (Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact hP2sup x
  set Hd : SmoothCcTensor g₀ 3 (2 + i) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 (2 + i)
      (iteratedCovGrad (I := I) g₀ 1 2 i K1) W1 with hHd_def
  have hsplit : iteratedCovGrad (I := I) g₀ 3 2 i
        (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) - Hd =
      ∑ k ∈ Finset.range i,
        ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 K1 i (k + 1))
          (iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1) := by
    rw [show (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) =
        ccOperatorFieldComp (I := I) (M := M) g₀ 3 1 2 K1 W1 from by
      rw [hK1_def, hW1_def]
      exact ricciArmOrder1KoszulCoeff_eq_raisedKoszul_contract_cometricDoubleTraceCastG0 (I := I) (M := M) g₀ g₁]
    rw [tsmAppCcRS_coeffCorner_split (I := I) (M := M) g₀ 3 1 2 K1 W1 i]
    rw [hHd_def]
    exact add_sub_cancel_left _ _
  refine ⟨Hd, ?_, ?_, ?_⟩
  · intro x
    rw [hHd_def]
    rw [appCcRS_toSection (I := I) (M := M) g₀ 3 1 (2 + i)
      (iteratedCovGrad (I := I) g₀ 1 2 i K1) W1 x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 1
      (2 + i) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i K1).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by
      have h := rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M)
        g₀ g₁ P htie i x
      rw [hK1_def]
      exact h
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (W1.toSection x) ≤
        ΛB ^ 2 := by
      have h := hBsup x
      rw [hW1_def]
      exact h
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i K1).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (W1.toSection x)
        ≤ (10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) * ΛB ^ 2 := by
          refine mul_le_mul h1 h2
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 1 x _) ?_
          have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)
          positivity
      _ = 10 * ΛB ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by ring
  · have hpt : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x (Hd.toSection x) ≤
          10 * ΛB ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by
      intro x
      rw [hHd_def]
      rw [appCcRS_toSection (I := I) (M := M) g₀ 3 1 (2 + i)
        (iteratedCovGrad (I := I) g₀ 1 2 i K1) W1 x]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 1
        (2 + i) x _ _) ?_
      have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i K1).toSection x) ≤
          10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by
        have h := rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M)
          g₀ g₁ P htie i x
        rw [hK1_def]
        exact h
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (W1.toSection x) ≤
          ΛB ^ 2 := by
        have h := hBsup x
        rw [hW1_def]
        exact h
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i K1).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (W1.toSection x)
          ≤ (10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) * ΛB ^ 2 := by
            refine mul_le_mul h1 h2
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 1 x _) ?_
            have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)
            positivity
        _ = 10 * ΛB ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by ring
    have hF_int : MeasureTheory.Integrable
        (fun x => 10 * ΛB ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 1))
        (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P)).const_mul _
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
      g₀ 3 (2 + i) Hd _ hF_int hpt
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    rw [← tsmNormSq_eq_integral (I := I) (M := M) g₀ 0 (2 + (i + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P)]
  · by_cases hi0 : i = 0
    · subst hi0
      rw [hsplit, Finset.sum_range_zero]
      have hz0 : ‖(0 : SmoothCcTensor g₀ 3 (2 + 0))‖ ^ 2 = 0 := by
        rw [tsmNormSq_eq_integral (I := I) (M := M) g₀ 3 (2 + 0)
          (0 : SmoothCcTensor g₀ 3 (2 + 0))]
        rw [show (fun x : M => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + 0) x
            ((0 : SmoothCcTensor g₀ 3 (2 + 0)).toSection x)) = (fun _ : M => (0 : ℝ))
            from funext (fun x => by
          rw [SmoothCcTensor.toSection_zero]
          simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
          exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 3 (2 + 0) x)]
        simp
      rw [hz0]
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (0 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hKcC_nn : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ 2 * diagonalGridGrowthFactor (E := E) 0 *
          (ΛA ^ 2 * FB 0 + Cta 0 * (ΛB ^ 2 * FA 0 + ΛS ^ 2 * FB 0)) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (appCcGdiag_nonneg (E := E) 0))
          (add_nonneg (mul_nonneg (sq_nonneg ΛA) (hFB_nn 0))
            (mul_nonneg (hCta_nn 0) (add_nonneg (mul_nonneg (sq_nonneg ΛB) (hFA_nn 0))
              (mul_nonneg (sq_nonneg ΛS) (hFB_nn 0)))))
      nlinarith [hKcC_nn, hsum_nn]
    · have hipos : 1 ≤ i := Nat.pos_of_ne_zero hi0
      set grid : M → ℝ := fun x =>
        ∑ n ∈ Finset.range ((i - 1) + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 3 n
                (covGrad (I := I) (M := M) g₀ 1 2 K1)).toSection x)
            * ∑ l ∈ Finset.range ((i - 1) + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 l W1).toSection x) with hgrid_def
      obtain ⟨hgrid_int, hgrid_bound⟩ :=
        (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
          (I := I) (M := M) g₀ 1 3 3 1 (i - 1)).choose_spec.2
          (covGrad (I := I) (M := M) g₀ 1 2 K1) W1 ΛS ΛB hΛS_nn hΛB_nn hSsup
          (fun x => by
            have h := hBsup x
            rw [hW1_def]
            exact h)
      have hgrid_nn : ∀ x : M, 0 ≤ grid x := by
        intro x
        refine Finset.sum_nonneg (fun n _ => ?_)
        refine mul_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + n) x _)
          (Finset.sum_nonneg (fun l _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (1 + l) x _))
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 3 2 i
                (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) - Hd).toSection x) ≤
            (i : ℝ) ^ 2 * diagonalGridGrowthFactor (E := E) i *
              (ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) +
                grid x) := by
        intro x
        rw [hsplit]
        rw [SmoothCcTensor.toSection_sum_apply]
        refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 3
          (2 + i) x (Finset.range i) _) ?_
        rw [Finset.card_range]
        have hterm : ∀ k ∈ Finset.range i,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x
              ((ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 K1 i (k + 1))
                (iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1)).toSection x) ≤
            diagonalGridGrowthFactor (E := E) i *
              (ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) +
                grid x) := by
          intro k hk
          rw [Finset.mem_range] at hk
          rw [appCcRS_toSection (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 K1 i (k + 1))
            (iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1) x]
          refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3
            (1 + (k + 1)) (2 + i) x _ _) ?_
          have hPsi : riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (2 + i) x
              ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 K1 i (k + 1)).toSection x) ≤
              diagonalGridGrowthFactor (E := E) i *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 (i - (k + 1)) K1).toSection x) := by
            have hw := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M)
              g₀ 1 2 K1 i (k + 1) 0 (by omega) x
            rw [iteratedCovGrad_zero] at hw
            rw [tsmRfns_order_congr (I := I) (M := M) g₀ 1 2
              (show (i - (k + 1)) + 0 = i - (k + 1) from by omega) K1 x] at hw
            exact hw
          have hprod : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i - (k + 1))) x
                ((iteratedCovGrad (I := I) g₀ 1 2 (i - (k + 1)) K1).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1).toSection x) ≤
              ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) +
                grid x := by
            by_cases hki : k + 1 = i
            · have hzero : i - (k + 1) = 0 := by omega
              rw [hzero, iteratedCovGrad_zero]
              have hKsup : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
                  (K1.toSection x) ≤ ΛA ^ 2 := by
                have h := hAsup x
                rw [hK1_def]
                exact h
              have hle1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
                    (K1.toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1).toSection x) ≤
                  ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) := by
                rw [hki]
                refine mul_le_mul_of_nonneg_right hKsup ?_
                exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (1 + i) x _
              linarith [hgrid_nn x]
            · have hk2 : k + 2 ≤ i := by omega
              have hcomm : riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  (2 + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 (i - (k + 1)) K1).toSection x) =
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + (i - (k + 2))) x
                    ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 2))
                      (covGrad (I := I) (M := M) g₀ 1 2 K1)).toSection x) := by
                have h := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2
                  (i - (k + 2)) K1 x
                rw [tsmRfns_order_congr (I := I) (M := M) g₀ 1 2
                  (show (i - (k + 2)) + 1 = i - (k + 1) from by omega) K1 x] at h
                exact h.symm
              rw [hcomm]
              have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 1
                    (3 + (i - (k + 2))) x
                    ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 2))
                      (covGrad (I := I) (M := M) g₀ 1 2 K1)).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1).toSection x) ≤
                  grid x := by
                rw [hgrid_def]
                have hmem : i - (k + 2) ∈ Finset.range ((i - 1) + 1) :=
                  Finset.mem_range.mpr (by omega)
                have hinner : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1).toSection x) ≤
                    ∑ l ∈ Finset.range ((i - 1) + 1 - (i - (k + 2))),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                        ((iteratedCovGrad (I := I) g₀ 3 1 l W1).toSection x) :=
                  Finset.single_le_sum
                    (f := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 1 l W1).toSection x))
                    (fun l _ =>
                      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (1 + l) x _)
                    (Finset.mem_range.mpr (by omega))
                refine le_trans (mul_le_mul_of_nonneg_left hinner
                  (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1
                    (3 + (i - (k + 2))) x _)) ?_
                exact Finset.single_le_sum
                  (f := fun n =>
                    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + n) x
                        ((iteratedCovGrad (I := I) g₀ 1 3 n
                          (covGrad (I := I) (M := M) g₀ 1 2 K1)).toSection x)
                      * ∑ l ∈ Finset.range ((i - 1) + 1 - n),
                          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + l) x
                            ((iteratedCovGrad (I := I) g₀ 3 1 l W1).toSection x))
                  (fun n _ => mul_nonneg
                    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + n) x _)
                    (Finset.sum_nonneg (fun l _ =>
                      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (1 + l) x _)))
                  hmem
              have hA_nn : 0 ≤ ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3
                  (1 + i) x ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) :=
                mul_nonneg (sq_nonneg ΛA)
                  (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (1 + i) x _)
              linarith
          calc riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (2 + i) x
                ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 K1 i (k + 1)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1).toSection x)
              ≤ (diagonalGridGrowthFactor (E := E) i *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i - (k + 1))) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 (i - (k + 1)) K1).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1).toSection x) := by
                refine mul_le_mul_of_nonneg_right hPsi ?_
                exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (1 + (k + 1)) x _
            _ = diagonalGridGrowthFactor (E := E) i *
                (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i - (k + 1))) x
                    ((iteratedCovGrad (I := I) g₀ 1 2 (i - (k + 1)) K1).toSection x) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1).toSection x)) := by ring
            _ ≤ diagonalGridGrowthFactor (E := E) i *
                (ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                    ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) +
                  grid x) :=
              mul_le_mul_of_nonneg_left hprod (appCcGdiag_nonneg (E := E) i)
        calc ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x
                ((ccOperatorFieldComp (I := I) (M := M) g₀ 3 (1 + (k + 1)) (2 + i)
                  (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 K1 i (k + 1))
                  (iteratedCovGrad (I := I) g₀ 3 1 (k + 1) W1)).toSection x)
            ≤ ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
                diagonalGridGrowthFactor (E := E) i *
                  (ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                      ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) +
                    grid x) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg i)
          _ = (i : ℝ) ^ 2 * diagonalGridGrowthFactor (E := E) i *
              (ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) +
                grid x) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      have hF_int : MeasureTheory.Integrable
          (fun x => (i : ℝ) ^ 2 * diagonalGridGrowthFactor (E := E) i *
            (ΛA ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x) +
              grid x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        refine MeasureTheory.Integrable.const_mul ?_ _
        refine MeasureTheory.Integrable.add ?_ hgrid_int
        exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (1 + i)
          (iteratedCovGrad (I := I) g₀ 3 1 i W1)).const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 3 (2 + i)
        (iteratedCovGrad (I := I) g₀ 3 2 i
          (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) - Hd)
        _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_add ((integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g₀ 3 (1 + i)
        (iteratedCovGrad (I := I) g₀ 3 1 i W1)).const_mul _) hgrid_int]
      rw [MeasureTheory.integral_const_mul]
      have hW1i : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ FB i := by
        rw [← tsmNormSq_eq_integral (I := I) (M := M) g₀ 3 (1 + i)
          (iteratedCovGrad (I := I) g₀ 3 1 i W1)]
        have h1 : ‖iteratedCovGrad (I := I) g₀ 3 1 i W1‖ ^ 2 ≤
            ∑ l ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 3 1 l W1‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun l => ‖iteratedCovGrad (I := I) g₀ 3 1 l W1‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
        refine le_trans h1 ?_
        have h := hBsum i hia
        rw [hW1_def]
        exact h
      have hgridI : (∫ x, grid x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Cta i * (ΛB ^ 2 * FA i + ΛS ^ 2 * FB i) := by
        refine le_trans hgrid_bound ?_
        rw [hCta_def]
        refine mul_le_mul_of_nonneg_left ?_ (hCta_nn i)
        have hKsum : (∑ n ∈ Finset.range ((i - 1) + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 3 n
              (covGrad (I := I) (M := M) g₀ 1 2 K1)‖ ^ 2) ≤ FA i := by
          have hshift : (∑ n ∈ Finset.range ((i - 1) + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 3 n
                (covGrad (I := I) (M := M) g₀ 1 2 K1)‖ ^ 2) =
              ∑ n ∈ Finset.range ((i - 1) + 1),
                ‖iteratedCovGrad (I := I) g₀ 1 2 (n + 1) K1‖ ^ 2 :=
            Finset.sum_congr rfl (fun n _ =>
              tsmNormSq_covGrad_shift (I := I) (M := M) g₀ 1 2 n K1)
          rw [hshift]
          have hsub : (∑ n ∈ Finset.range ((i - 1) + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 2 (n + 1) K1‖ ^ 2) ≤
              ∑ m ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 1 2 m K1‖ ^ 2 := by
            have himg : (∑ n ∈ Finset.range ((i - 1) + 1),
                ‖iteratedCovGrad (I := I) g₀ 1 2 (n + 1) K1‖ ^ 2) =
                ∑ m ∈ (Finset.range ((i - 1) + 1)).image (fun n => n + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 m K1‖ ^ 2 := by
              rw [Finset.sum_image (fun n₁ _ n₂ _ h => by omega)]
            rw [himg]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => sq_nonneg _)
            intro m hm
            rw [Finset.mem_image] at hm
            obtain ⟨n, hn, rfl⟩ := hm
            rw [Finset.mem_range] at hn ⊢
            omega
          refine le_trans hsub ?_
          have h := hAsum i hia
          rw [hK1_def]
          exact h
        have hWsum : (∑ l ∈ Finset.range ((i - 1) + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 1 l W1‖ ^ 2) ≤ FB i := by
          have hsub : (∑ l ∈ Finset.range ((i - 1) + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 1 l W1‖ ^ 2) ≤
              ∑ l ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 3 1 l W1‖ ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by omega)) (fun l _ _ => sq_nonneg _)
          refine le_trans hsub ?_
          have h := hBsum i hia
          rw [hW1_def]
          exact h
        exact add_le_add (mul_le_mul_of_nonneg_left hKsum (sq_nonneg ΛB))
          (mul_le_mul_of_nonneg_left hWsum (sq_nonneg ΛS))
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hfin : (i : ℝ) ^ 2 * diagonalGridGrowthFactor (E := E) i *
          (ΛA ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
              ((iteratedCovGrad (I := I) g₀ 3 1 i W1).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) +
            ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          (i : ℝ) ^ 2 * diagonalGridGrowthFactor (E := E) i *
            (ΛA ^ 2 * FB i + Cta i * (ΛB ^ 2 * FA i + ΛS ^ 2 * FB i)) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (sq_nonneg _) (appCcGdiag_nonneg (E := E) i))
        exact add_le_add (mul_le_mul_of_nonneg_left hW1i (sq_nonneg ΛA)) hgridI
      refine le_trans hfin ?_
      have hKcC_nn : (0 : ℝ) ≤ (i : ℝ) ^ 2 * diagonalGridGrowthFactor (E := E) i *
          (ΛA ^ 2 * FB i + Cta i * (ΛB ^ 2 * FA i + ΛS ^ 2 * FB i)) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (appCcGdiag_nonneg (E := E) i))
          (add_nonneg (mul_nonneg (sq_nonneg ΛA) (hFB_nn i))
            (mul_nonneg (hCta_nn i) (add_nonneg (mul_nonneg (sq_nonneg ΛB) (hFA_nn i))
              (mul_nonneg (sq_nonneg ΛS) (hFB_nn i)))))
      nlinarith [hKcC_nn, hsum_nn]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tsmConvex_jet_eq (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s) =
      (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T' +
        s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
  rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
    iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsmConvex_rfns_le (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T').toSection x) := by
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  rw [tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s j]
  rw [show (((1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T' +
        s • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) =
      ((1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T').toSection x +
        (s • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x _ _) ?_
  rw [show (((1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T').toSection x) =
      (1 - s) • ((iteratedCovGrad (I := I) g₀ 0 2 j T').toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) =
      s • ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [tsmRfns_smul (I := I) (M := M) g₀ 0 (2 + j) x (1 - s) _]
  rw [tsmRfns_smul (I := I) (M := M) g₀ 0 (2 + j) x s _]
  have h1 : (1 - s) ^ 2 ≤ 1 := by nlinarith
  have h2 : s ^ 2 ≤ 1 := by nlinarith
  have hT_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)
  have hT'_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T').toSection x)
  nlinarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tsmConvex_normSq_le (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hnorm : ‖iteratedCovGrad (I := I) g₀ 0 2 j
      (convexPerturbation (I := I) g₀ T T' s)‖ ≤
      (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
        s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
    rw [tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s j]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg h1ms, abs_of_nonneg hs0]
  have hnn := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j
    (convexPerturbation (I := I) g₀ T T' s))
  have hT_nn := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j T)
  have hT'_nn := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j T')
  have hle : (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
      s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
    nlinarith [mul_nonneg hs0 hT'_nn, mul_nonneg h1ms hT_nn]
  have hP2 : ‖iteratedCovGrad (I := I) g₀ 0 2 j
      (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖) ^ 2 :=
    pow_le_pow_left₀ hnn (le_trans hnorm hle) 2
  nlinarith [hP2, sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ -
    ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖)]

theorem linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T').toSection x))) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Kt, hKt_nn, Kc, hKc_nn, hgen⟩ :=
    ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  refine ⟨2 * Kt, by linarith, ?_⟩
  refine ⟨fun i => 2 * Kc i, fun i => by have := hKc_nn i; linarith, ?_⟩
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    rw [tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s j]
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
  obtain ⟨Hd, hpt, hL2h, hres⟩ := hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
  refine ⟨Hd, ?_, ?_, ?_⟩
  · intro x
    refine le_trans (hpt x) ?_
    have hsplit := tsmConvex_rfns_le (I := I) (M := M) g₀ T T' hs (i + 2) x
    calc Kt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
            (convexPerturbation (I := I) g₀ T T' s)).toSection x)
        ≤ Kt * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T').toSection x)) :=
          mul_le_mul_of_nonneg_left hsplit hKt_nn
      _ = 2 * Kt * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T').toSection x)) := by ring
  · refine le_trans hL2h ?_
    have hsplit := tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs (i + 2)
    calc Kt * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
          (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2
        ≤ Kt * (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsplit hKt_nn
      _ = 2 * Kt * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by ring
  · refine le_trans hres ?_
    have hsum : (∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 2),
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
      Finset.sum_le_sum (fun j _ => tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs j)
    have hKc_i := hKc_nn i
    have hsum2 : (∑ j ∈ Finset.range (i + 2),
        (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) =
        2 * ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
      Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    calc Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2)
        ≤ Kc i * (1 + 2 * ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKc_i
          rw [← hsum2]
          linarith [hsum]
      _ ≤ 2 * Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
          nlinarith [hKc_i, hsum_nn]

theorem linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∃ Hd : SmoothCcTensor g₀ 3 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x (Hd.toSection x) ≤
                Ktop * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) +
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T').toSection x))) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) ∧
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
                (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Kt, hKt_nn, Kc, hKc_nn, hgen⟩ :=
    ricciArmOrder1KoszulCoeff_perOrder_l2_topSeparated_generic (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  refine ⟨2 * Kt, by linarith, ?_⟩
  refine ⟨fun i => 2 * Kc i, fun i => by have := hKc_nn i; linarith, ?_⟩
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    rw [tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s j]
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
  obtain ⟨Hd, hpt, hL2h, hres⟩ := hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
  refine ⟨Hd, ?_, ?_, ?_⟩
  · intro x
    refine le_trans (hpt x) ?_
    have hsplit := tsmConvex_rfns_le (I := I) (M := M) g₀ T T' hs (i + 1) x
    calc Kt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1)
            (convexPerturbation (I := I) g₀ T T' s)).toSection x)
        ≤ Kt * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T').toSection x)) :=
          mul_le_mul_of_nonneg_left hsplit hKt_nn
      _ = 2 * Kt * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T').toSection x)) := by ring
  · refine le_trans hL2h ?_
    have hsplit := tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs (i + 1)
    calc Kt * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1)
          (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2
        ≤ Kt * (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsplit hKt_nn
      _ = 2 * Kt * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) := by ring
  · refine le_trans hres ?_
    have hsum : (∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 1),
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
      Finset.sum_le_sum (fun j _ => tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs j)
    have hKc_i := hKc_nn i
    have hsum2 : (∑ j ∈ Finset.range (i + 1),
        (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) =
        2 * ∑ j ∈ Finset.range (i + 1),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
      Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    calc Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2)
        ≤ Kc i * (1 + 2 * ∑ j ∈ Finset.range (i + 1),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKc_i
          rw [← hsum2]
          linarith [hsum]
      _ ≤ 2 * Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
          nlinarith [hKc_i, hsum_nn]

theorem linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_topSeparated_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T').toSection x))) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
                Kleak * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by
  classical
  obtain ⟨Kt, hKt_nn, Kc, hKc_nn, hgen⟩ :=
    ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic_allOrders (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  refine ⟨2 * Kt, by linarith, ?_⟩
  refine ⟨fun i => 2 * Kc i, fun i => by have := hKc_nn i; linarith, 0, le_refl 0, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    rw [tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s j]
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
  obtain ⟨Hd, hpt, hL2h, hres⟩ := hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  refine ⟨Hd, ?_, ?_, ?_⟩
  · intro x
    refine le_trans (hpt x) ?_
    have hsplit := tsmConvex_rfns_le (I := I) (M := M) g₀ T T' hs (i + 2) x
    calc Kt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
            (convexPerturbation (I := I) g₀ T T' s)).toSection x)
        ≤ Kt * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T').toSection x)) :=
          mul_le_mul_of_nonneg_left hsplit hKt_nn
      _ = 2 * Kt * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T').toSection x)) := by ring
  · refine le_trans hL2h ?_
    have hsplit := tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs (i + 2)
    calc Kt * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
          (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2
        ≤ Kt * (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsplit hKt_nn
      _ = 2 * Kt * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) := by ring
  · rw [zero_mul, add_zero]
    refine le_trans hres ?_
    have hsum : (∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 2),
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
      Finset.sum_le_sum (fun j _ => tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs j)
    have hKc_i := hKc_nn i
    have hsum2 : (∑ j ∈ Finset.range (i + 2),
        (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) =
        2 * ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
      Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    calc Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2)
        ≤ Kc i * (1 + 2 * ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKc_i
          rw [← hsum2]
          linarith [hsum]
      _ ≤ 2 * Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
          nlinarith [hKc_i, hsum_nn]

theorem linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_topSeparated_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∃ Hd : SmoothCcTensor g₀ 3 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x (Hd.toSection x) ≤
                Ktop * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) +
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T').toSection x))) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) ∧
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
                (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
                Kleak * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) := by
  classical
  obtain ⟨Kt, hKt_nn, Kc, hKc_nn, Kleak, hKleak_nn, hgen⟩ :=
    ricciArmOrder1KoszulCoeff_perOrder_l2_topSeparated_generic_allOrders (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  refine ⟨2 * Kt, by linarith, ?_⟩
  refine ⟨fun i => 2 * Kc i, fun i => by have := hKc_nn i; linarith, 2 * Kleak,
    by linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
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
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    rw [tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s j]
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
  obtain ⟨Hd, hpt, hL2h, hres⟩ := hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  refine ⟨Hd, ?_, ?_, ?_⟩
  · intro x
    refine le_trans (hpt x) ?_
    have hsplit := tsmConvex_rfns_le (I := I) (M := M) g₀ T T' hs (i + 1) x
    calc Kt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1)
            (convexPerturbation (I := I) g₀ T T' s)).toSection x)
        ≤ Kt * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T').toSection x)) :=
          mul_le_mul_of_nonneg_left hsplit hKt_nn
      _ = 2 * Kt * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T').toSection x)) := by ring
  · refine le_trans hL2h ?_
    have hsplit := tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs (i + 1)
    calc Kt * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1)
          (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2
        ≤ Kt * (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsplit hKt_nn
      _ = 2 * Kt * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) := by ring
  · refine le_trans hres ?_
    have hsum : (∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (i + 1),
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
      Finset.sum_le_sum (fun j _ => tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs j)
    have hleak : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1)
        (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2 :=
      tsmConvex_normSq_le (I := I) (M := M) g₀ T T' hs (i + 1)
    have hKc_i := hKc_nn i
    have hsum2 : (∑ j ∈ Finset.range (i + 1),
        (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) =
        2 * ∑ j ∈ Finset.range (i + 1),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
      Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hleakT_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    calc Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) +
          Kleak * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1)
            (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2
        ≤ Kc i * (1 + 2 * ∑ j ∈ Finset.range (i + 1),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kleak * (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ hKc_i)
            (mul_le_mul_of_nonneg_left hleak hKleak_nn)
          rw [← hsum2]
          linarith [hsum]
      _ ≤ 2 * Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            2 * Kleak * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) := by
          nlinarith [hKc_i, hsum_nn, hKleak_nn, hleakT_nn]

end TopSeparatedRealizedFamily

end DifferentialGeometry.Integral.Connection

end
