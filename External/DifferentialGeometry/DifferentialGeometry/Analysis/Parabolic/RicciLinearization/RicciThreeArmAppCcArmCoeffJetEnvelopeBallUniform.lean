import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamLinearizedChristoffel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldTameEnvelope
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamCurvatureJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCcFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCcArmReadoutCovDeriv


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jetEnvelope_covGrad_one_le (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (x : M) (B : ℝ)
    (henv : (∑ j ∈ Finset.range 3,
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B) :
    (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
    ‖(iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x‖) ≤ B := by
  refine le_trans ?_ henv
  exact Finset.single_le_sum (f := fun j =>
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)
      (fun j _ =>
        letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x))
      (by simp : (1 : ℕ) ∈ Finset.range 3)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_perMetric_linearizedRicciArm1Fib_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              (show TensorRSSpace 3 2 I x from
                linearizedRicciArm1Fib (I := I) g₀ g₁ x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ (by norm_num)
  obtain ⟨Ckos, hCkos_nn, hKos⟩ :=
    riemannianFiberNormSq_raisedKoszul_le_of_lt_one (I := I) (M := M) g₀ hδ₁_nn hδ₁_lt
  refine ⟨Ckos ^ 2 * B ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ₁)) ^ 2),
    by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv
  set δ' : ℝ := max δ 0 with hδ'_def
  have hδ'_nn : 0 ≤ δ' := le_max_right _ _
  have hδ'_le_δ₁ : δ' ≤ δ₁ := by
    rw [hδ'_def]
    exact (max_le_max hδ_le (le_refl 0)).trans (le_of_eq (max_eq_left hδ₁_nn))
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le_δ₁ hδ₁_lt
  have hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ' :=
    gFibreOpBound_mono_local (I := I) g₀ _ (le_max_left _ _) hδ
  have hcoeff₁ : 0 < 1 - δ₁ := by linarith
  have hcoeff' : 0 < 1 - δ' := by linarith
  have hcomp := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 1 2 x
    (raisedKoszulFib (I := I) g₀ g₁ x) (cometricDoubleTraceFib (I := I) g₁ 1 x)
  have hlin_eq : (show TensorRSSpace 3 2 I x from linearizedRicciArm1Fib (I := I) g₀ g₁ x) =
      (show TensorRSSpace 3 2 I x from
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            raisedKoszulFib (I := I) g₀ g₁ x).comp
          (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
            cometricDoubleTraceFib (I := I) g₁ 1 x)) := rfl
  rw [hlin_eq]
  refine hcomp.trans ?_
  letI instTens12 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  set N : ℝ := ‖(iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have hnorm_le : N ≤ B := jetEnvelope_covGrad_one_le (I := I) g₀ P x B henv
  have hsq : N ^ 2 ≤ B ^ 2 := by nlinarith [hnorm_le, hN_nn, hB]
  have hkosB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      (raisedKoszulFib (I := I) g₀ g₁ x) ≤ Ckos ^ 2 * B ^ 2 := by
    have hKosx := hKos g₁ P htie hδ'_le_δ₁ hδ'_nn hδ' x
    rw [raisedKoszul_toSection] at hKosx
    refine hKosx.trans ?_
    have hCkos_sq_nn : 0 ≤ Ckos ^ 2 := sq_nonneg _
    have hgoal : Ckos ^ 2 * N ^ 2 ≤ Ckos ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hCkos_sq_nn
    exact hgoal
  have hcometB : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
      (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ₁)) ^ 2 := by
    have hcm := riemannianFiberNormSq_cometricDoubleTraceFib_le (I := I) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ P) htie hδ'_lt hδ'_nn hδ' x
    refine hcm.trans ?_
    have hmono : 1 / (1 - δ') ≤ 1 / (1 - δ₁) :=
      div_le_div_of_nonneg_left (by norm_num) hcoeff₁ (by linarith)
    have hinv_nn : 0 ≤ 1 / (1 - δ') := by positivity
    have hsq_le : (1 / (1 - δ')) ^ 2 ≤ (1 / (1 - δ₁)) ^ 2 := by
      have hinv₁_nn : 0 ≤ 1 / (1 - δ₁) := by positivity
      nlinarith [hmono, hinv_nn, hinv₁_nn]
    have hfin_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left hsq_le hfin_nn
  have hrfns_kos_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      (raisedKoszulFib (I := I) g₀ g₁ x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _
  have hrfns_com_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
      (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 1 x _
  have hCkosB_nn : 0 ≤ Ckos ^ 2 * B ^ 2 := by positivity
  have hfinal : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        (raisedKoszulFib (I := I) g₀ g₁ x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
          (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
      ≤ Ckos ^ 2 * B ^ 2 *
          ((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ₁)) ^ 2) :=
    mul_le_mul hkosB hcometB hrfns_com_nn hCkosB_nn
  exact hfinal

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannianFiberNormSq_linearizedRicciArm1Fib_realizedFam_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              (show TensorRSSpace 3 2 I x from
                linearizedRicciArm1Fib (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) x) ≤ Λ := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    exists_perMetric_linearizedRicciArm1Fib_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨Λ, hΛ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w := by
    intro y v w
    rw [hg₁, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w]
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      (|1 - s| * δ' + |s| * δ) :=
    convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ δ₁ := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ :=
      mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ :=
      mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ δ₁ := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) δ₁ := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hsv : 0 ≤ Real.sqrt (g₀.inner y v v) := Real.sqrt_nonneg _
    have hsw : 0 ≤ Real.sqrt (g₀.inner y w w) := Real.sqrt_nonneg _
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg hsv hsw
    have hle' : |1 - s| * δ' + |s| * δ ≤ δ₁ := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  exact hΛ g₁ (convexPerturbation (I := I) g₀ T T' s) (le_of_eq hδ₁_def) hδs htie x henv

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_arm1Koszul_realizedFam_pointwise_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λarm1 : ℝ, 0 ≤ Λarm1 ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λarm1 := by
  classical
  obtain ⟨Λarm1, hΛarm1_nn, hΛarm1⟩ :=
    exists_riemannianFiberNormSq_linearizedRicciArm1Fib_realizedFam_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨Λarm1, hΛarm1_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  rw [ricciArmOrder1KoszulCoeff_toSection]
  exact hΛarm1 T T' hδ_le hδ hδ'_le hδ' s hs x henv


theorem exists_arm1Koszul_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λarm1 : ℝ, 0 ≤ Λarm1 ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λarm1 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  obtain ⟨Λarm1, hΛarm1_nn, hΛarm1⟩ :=
    exists_arm1Koszul_realizedFam_pointwise_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀
      (Csob * R) (by positivity)
  refine ⟨Λarm1, hΛarm1_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  refine hΛarm1 T T' hδ_le hδ hδ'_le hδ' s hs x ?_
  exact hCsob T T' hR hTball hT'ball s hs x

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannArm0_curvCoeff_realizedFam_pointwise_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λcurv : ℝ, 0 ≤ Λcurv ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcurv ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcurv := by
  classical
  obtain ⟨Λ1, hΛ1_nn, hΛ1⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_riemannBiContrFib_riemannianFiberNormSq_le_of_realizedFam_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  obtain ⟨Λ2, hΛ2_nn, hΛ2⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_ricciArmOrder0CurvCoeffFib_riemannianFiberNormSq_le_of_realizedFam_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨max Λ1 Λ2, le_trans hΛ1_nn (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  refine ⟨?_, ?_⟩
  · rw [ricciArmOrder0RiemannCoeff_toSection]
    exact le_trans (hΛ1 T T' hδ_le hδ hδ'_le hδ' s hs x henv) (le_max_left _ _)
  · rw [ricciArmOrder0CurvCoeff_toSection]
    exact le_trans (hΛ2 T T' hδ_le hδ hδ'_le hδ' s hs x henv) (le_max_right _ _)


theorem exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λcurv : ℝ, 0 ≤ Λcurv ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcurv ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcurv := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  obtain ⟨Λcurv, hΛcurv_nn, hΛcurv⟩ :=
    exists_riemannArm0_curvCoeff_realizedFam_pointwise_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀
      (Csob * R) (by positivity)
  refine ⟨Λcurv, hΛcurv_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  refine hΛcurv T T' hδ_le hδ hδ'_le hδ' s hs x ?_
  exact hCsob T T' hR hTball hT'ball s hs x

noncomputable def corrFieldChristoffelBound (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ) (R δ₀ : ℝ) : ℝ :=
  if h : 2 * Module.finrank ℝ E + 10 ≤ a ∧ (0 : ℝ) ≤ R ∧ δ₀ < 1 then
    Classical.choose (exists_uniformBound_sqrt_riemannianFiberNormSq_linearizedRicciConnDiffCoeff_realizedFam_of_jetEnvelope
        (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2)
      + (Real.sqrt (Classical.choose
            (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
              (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2))
          + Real.sqrt (Classical.choose
            (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
              (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2)))
      + Real.sqrt (Classical.choose (exists_arm1Koszul_realizedFam_rfns_ballUniform
        (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2))
  else 0

theorem corrFieldChristoffelBound_nonneg (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ) (R δ₀ : ℝ) : 0 ≤ corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀ := by
  unfold corrFieldChristoffelBound
  split
  next h =>
    have hΛ := (Classical.choose_spec
      (exists_uniformBound_sqrt_riemannianFiberNormSq_linearizedRicciConnDiffCoeff_realizedFam_of_jetEnvelope
        (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2)).1
    have h1 : (0 : ℝ) ≤ Real.sqrt (Classical.choose
        (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
          (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2)) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (Classical.choose
        (exists_arm1Koszul_realizedFam_rfns_ballUniform
          (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2)) := Real.sqrt_nonneg _
    linarith
  next => exact le_refl 0

noncomputable def corrFieldTameJetBound (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ) (R δ₀ : ℝ) (i : ℕ) : ℝ :=
  if h : 2 * Module.finrank ℝ E + 10 ≤ a ∧ (0 : ℝ) ≤ R ∧ δ₀ < 1 then
    2 * Classical.choose (exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
        (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2) i
      + 2 * Classical.choose (exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
        (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2) i
  else 0

theorem corrFieldTameJetBound_nonneg (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ) (R δ₀ : ℝ) (i : ℕ) :
    0 ≤ corrFieldTameJetBound (I := I) (M := M) g₀ a R δ₀ i := by
  unfold corrFieldTameJetBound
  split
  next h =>
    have h0 := (Classical.choose_spec (exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
        (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2)).1 i
    have h1 := (Classical.choose_spec (exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
        (I := I) (M := M) g₀ a h.1 h.2.1 h.2.2)).1 i
    linarith
  next => exact le_refl 0


omit [BoundarylessManifold I M] in
theorem exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (_hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λcom : ℝ, 0 ≤ Λcom ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcom ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((traceHessianCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcom := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  have hcoeff : 0 < 1 - δ₁ := by linarith
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ₁))) ^ 2, sq_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set hpert : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    fun y => ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y with hpert_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + hpert y v w := by
    intro y v w
    rw [hg₁, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w]
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ hpert (|1 - s| * δ' + |s| * δ) :=
    convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ δ₁ := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ :=
      mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ :=
      mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ δ₁ := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : metricCauchySchwarzBound (I := I) (M := M) g₀ hpert δ₁ := by
    refine gFibreOpBound_mono_local (I := I) g₀ hpert ?_ hδs_raw
    rw [habs_eq]; exact hsmall_le
  have hbP := riemannianFiberNormSq_ricciArmPrincipalCoeffFib_le
    (I := I) g₀ g₁ hpert htie hδ₁_lt hδ₁_nn hδs x
  have hbH := riemannianFiberNormSq_traceHessianFib_le
    (I := I) g₀ g₁ hpert htie hδ₁_lt hδ₁_nn hδs x
  refine ⟨?_, ?_⟩
  · rw [ricciArmPrincipalCoeff_toSection]; exact hbP
  · rw [traceHessianCoeff_toSection]; exact hbH

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
