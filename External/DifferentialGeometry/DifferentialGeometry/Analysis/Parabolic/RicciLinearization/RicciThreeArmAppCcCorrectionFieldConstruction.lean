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
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCcArmCoeffJetEnvelopeBallUniform


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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma appCc_zero_left_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) W =
      (0 : SmoothCcTensor g 0 s) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection]
  rw [show ((0 : SmoothCcTensor g r s).toSection x : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) =
      (0 : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) from rfl]
  rw [ContinuousLinearMap.zero_comp]
  rw [show ((0 : SmoothCcTensor g 0 s).toSection x : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) =
      (0 : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) from rfl]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma linearizedRicciThreeArmHjoint_zero (g₀ : SmoothRiemannianMetric I M)
    {δ δ' : ℝ} :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun _ : ℝ => (0 : SmoothCcTensor g₀ 3 2)) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint]
  have heq : (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        (((fun _ : ℝ => (0 : SmoothCcTensor g₀ 3 2)) p.2).toSection p.1)) =
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
          (0 : Tensor0SBundle.TensorRSSpace 3 2 I p.1)) := by
    funext p
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 t) ?_
    rw [show ((0 : SmoothCcTensor g₀ 3 2).toSection : ContMDiffSection I _ ∞ _) = 0 from rfl]
    rfl
  rw [heq]
  have hzero : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (Bundle.zeroSection (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z)) :=
    Bundle.contMDiff_zeroSection ℝ (fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z)
  exact (hzero.comp contMDiff_fst).contMDiffOn

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
theorem exists_Csob_sub_pointwise_jet3_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csub : ℝ, 0 ≤ Csub ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ x : M,
          (∑ j ∈ Finset.range 3,
              (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
                Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
              ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖)) ≤ Csub * R := by
  classical
  set k : ℕ := Module.finrank ℝ E / 2 + 3 with hk_def
  have hk_super : 2 * k > Module.finrank ℝ E + 4 := by rw [hk_def]; omega
  have h4k_le : 4 * k ≤ a + 2 := by rw [hk_def]; omega
  obtain ⟨Cc, hCc_pos, hCc⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_singleNorm (I := I) (M := M) g₀ k hk_super
  obtain ⟨Ch, hCh_nn, hCh⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * k)
  refine ⟨Cc * Ch * ((4 * k + 1 : ℕ) : ℝ) * 2, by positivity, ?_⟩
  intro T T' R _hR hbudgetT hbudgetT' x
  set W : SmoothCcTensor g₀ 0 2 := T - T' with hW_def
  have hWbudget : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ 2 * R := by
    intro j hj
    rw [hW_def, iteratedCovGrad_sub]
    refine le_trans (norm_sub_le _ _) ?_
    have := hbudgetT j hj
    have := hbudgetT' j hj
    linarith
  have hCol := hCc W x
  set Mn : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) W‖
    with hMn_def
  have hMn_nn : 0 ≤ Mn := norm_nonneg _
  have hHebey : Mn ≤ Ch * ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    refine le_trans (hCh W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCh_nn
    refine le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))
    exact (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm
  have hSumBudget : ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ ((4 * k + 1 : ℕ) : ℝ) * (2 * R) := by
    have hterm : ∀ j ∈ Finset.range (2 * (2 * k) + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ 2 * R := by
      intro j hj
      have hjle : j ≤ a + 2 := by
        have := Finset.mem_range.mp hj; omega
      exact hWbudget j hjle
    calc ∑ j ∈ Finset.range (2 * (2 * k) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖
        ≤ ∑ _j ∈ Finset.range (2 * (2 * k) + 1), (2 * R) := Finset.sum_le_sum hterm
      _ = ((2 * (2 * k) + 1 : ℕ) : ℝ) * (2 * R) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((4 * k + 1 : ℕ) : ℝ) * (2 * R) := by
          congr 2
          omega
  have hMn_le : Mn ≤ Ch * (((4 * k + 1 : ℕ) : ℝ) * (2 * R)) := by
    refine le_trans hHebey ?_
    exact mul_le_mul_of_nonneg_left hSumBudget hCh_nn
  calc (∑ j ∈ Finset.range 3,
          (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
          ‖(iteratedCovGrad (I := I) g₀ 0 2 j W).toSection x‖))
      ≤ Cc * Mn := hCol
    _ ≤ Cc * (Ch * (((4 * k + 1 : ℕ) : ℝ) * (2 * R))) :=
        mul_le_mul_of_nonneg_left hMn_le hCc_pos.le
    _ = (Cc * Ch * ((4 * k + 1 : ℕ) : ℝ) * 2) * R := by ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciArmOrder1KoszulCoeff_appCc_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 3)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2 (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            (Fin.cons (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![(Module.finBasis ℝ E) k,
                raisedKoszulVec (I := I) g₀ g₁ x (v 0) (v 1)]) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder1KoszulCoeff_toSection]
  change Tensor0SBundle.Tensor0SSpace.toModel
      (linearizedRicciArm1Fib (I := I) g₀ g₁ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) v = _
  rw [linearizedRicciArm1Fib_apply, raisedKoszulFib_apply]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (raisedKoszulPairing (I := I) g₀ g₁ x
          (cometricDoubleTraceFib (I := I) g₁ 1 x
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x)))) v =
      (raisedKoszulPairing (I := I) g₀ g₁ x
          (cometricDoubleTraceFib (I := I) g₁ 1 x
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x)))) v from rfl]
  rw [raisedKoszulPairing_apply]
  change Tensor0SBundle.Tensor0SSpace.toModel
      (cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)))
      (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (v 0) (v 1)) = _
  rw [cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  funext j
  fin_cases j <;> rfl

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
def corrFieldDataSpec (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (C0 : ℝ → SmoothCcTensor g₀ 2 2) (C1 : ℝ → SmoothCcTensor g₀ 3 2) : Prop :=
  linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s + C0 s)
      (δ := δ) (δ' := δ') ∧
  linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s + C1 s)
      (δ := δ) (δ' := δ') ∧
  (∀ {a : ℕ}, 2 * Module.finrank ℝ E + 10 ≤ a → ∀ {R : ℝ}, 0 ≤ R →
      ∀ {δ₀ : ℝ}, δ₀ < 1 → δ ≤ δ₀ → δ' ≤ δ₀ →
      (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
      (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
      (∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0 s).toSection x)) ≤
          corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀ ∧
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((C1 s).toSection x)) ≤
          corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀) ∧
      (∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (C0 s
              + (3 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
          corrFieldTameJetBound (I := I) (M := M) g₀ a R δ₀ i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) ∧
        ‖iteratedCovGrad (I := I) g₀ 3 2 i (C1 s)‖ ^ 2 ≤
          corrFieldTameJetBound (I := I) (M := M) g₀ a R δ₀ i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)))) ∧
  ((∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v) →
    (∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v) →
    ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (x : M) (v : Fin 2 → TangentSpace I x)
        (hδ_lt : δ < 1) (hδ'_lt : δ' < 1),
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2
                (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s + C0 s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 3 2
                (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s + C1 s)
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + operatorFieldApply (I := I) (M := M) g₀ 4 2
                (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
  (∀ s : ℝ, C0 s =
    linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
      - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s) ∧
  (∀ s : ℝ, C1 s =
    linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
      - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_corrFieldChristoffelConst (g₀ : SmoothRiemannianMetric I M) :
    ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        ∃ (C0 : ℝ → SmoothCcTensor g₀ 2 2) (C1 : ℝ → SmoothCcTensor g₀ 3 2),
          corrFieldDataSpec (I := I) (M := M) g₀ T T' hδ hδ' C0 C1 := by
  classical
  intro T T' δ hδ δ' hδ'
  refine ⟨fun s => linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
      - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s,
    fun s => linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
      - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hfun : (fun s => linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s +
        (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
          - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)) =
        fun s => linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s := by
      funext s
      exact (linearizedRicciConnDiffOrder0Coeff_eq_base_add_sub (I := I) g₀ T T' hδ hδ' s).symm
    change linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s +
        (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
          - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s))
      (δ := δ) (δ' := δ')
    rw [hfun]
    exact linearizedRicciConnDiffOrder0Coeff_jointContMDiffOn_smallPerturbationSet (I := I) g₀ T T' hδ hδ'
  · have hfun : (fun s => linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s +
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
          - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)) =
        fun s => linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s := by
      funext s
      exact (linearizedRicciConnDiffOrder1Coeff_eq_base_add_sub (I := I) g₀ T T' hδ hδ' s).symm
    change linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s +
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
          - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s))
      (δ := δ) (δ' := δ')
    rw [hfun]
    exact linearizedRicciConnDiffOrder1Coeff_jointContMDiffOn_smallPerturbationSet (I := I) g₀ T T' hδ hδ'
  · intro a ha_super R hR δ₀ hδ₀ hδ_le hδ'_le hTball hT'ball
    constructor
    · intro s hs x
      have hcond : 2 * Module.finrank ℝ E + 10 ≤ a ∧ (0 : ℝ) ≤ R ∧ δ₀ < 1 := ⟨ha_super, hR, hδ₀⟩
      have hbnd : corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀ =
          Classical.choose (exists_uniformBound_sqrt_riemannianFiberNormSq_linearizedRicciConnDiffCoeff_realizedFam_of_jetEnvelope
              (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)
            + (Real.sqrt (Classical.choose
                  (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
                    (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2))
                + Real.sqrt (Classical.choose
                  (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
                    (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)))
            + Real.sqrt (Classical.choose (exists_arm1Koszul_realizedFam_rfns_ballUniform
              (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)) := by
        unfold corrFieldChristoffelBound
        rw [dif_pos hcond]
      have hconn := (Classical.choose_spec
          (exists_uniformBound_sqrt_riemannianFiberNormSq_linearizedRicciConnDiffCoeff_realizedFam_of_jetEnvelope
            (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)).2
          T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
      have hcurv := (Classical.choose_spec
          (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
            (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)).2
          T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
      have harm1 := (Classical.choose_spec
          (exists_arm1Koszul_realizedFam_rfns_ballUniform
            (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)).2
          T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
      constructor
      · change Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
              - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
          corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀
        have htri : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
                ((linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s).toSection x))
              + (Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
                    ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x))
                  + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
                    ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x))) := by
          letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
          rw [← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _,
            ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _,
            ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _,
            ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _]
          have hsec : ((linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x :
                TensorRSSpace 2 2 I x) =
              (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s).toSection x
                - ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x
                    - (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) := by
            rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
              linearizedRicciArm0BaseCoeff, SmoothCcTensor.toSection_sub,
              ContMDiffSection.coe_sub, Pi.sub_apply]
          rw [hsec]
          refine le_trans (norm_sub_le _ _) ?_
          have h2 := norm_sub_le
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
            ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          linarith
        rw [hbnd]
        have hb1 := hconn.1
        have hb2 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) ≤
            Real.sqrt (Classical.choose
              (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
                (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)) :=
          Real.sqrt_le_sqrt hcurv.1
        have hb3 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) ≤
            Real.sqrt (Classical.choose
              (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
                (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)) :=
          Real.sqrt_le_sqrt hcurv.2
        have hb4 : (0 : ℝ) ≤ Real.sqrt (Classical.choose
            (exists_arm1Koszul_realizedFam_rfns_ballUniform
              (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)) := Real.sqrt_nonneg _
        linarith
      · change Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
              - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
          corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀
        have htri : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
                ((linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s).toSection x))
              + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
                ((ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) := by
          letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 3 2 I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 3 2
          rw [← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _,
            ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _,
            ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _]
          have hsec : ((linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x :
                TensorRSSpace 3 2 I x) =
              (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s).toSection x
                - (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x := by
            rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
              linearizedRicciArm1BaseCoeff]
          rw [hsec]
          exact norm_sub_le _ _
        rw [hbnd]
        have hb1 := hconn.2
        have hb2 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) ≤
            Real.sqrt (Classical.choose
              (exists_arm1Koszul_realizedFam_rfns_ballUniform
                (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)) :=
          Real.sqrt_le_sqrt harm1
        have hb3 : (0 : ℝ) ≤ Real.sqrt (Classical.choose
            (exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
              (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)) := Real.sqrt_nonneg _
        linarith
    · intro i hi s hs
      have hcond : 2 * Module.finrank ℝ E + 10 ≤ a ∧ (0 : ℝ) ≤ R ∧ δ₀ < 1 := ⟨ha_super, hR, hδ₀⟩
      have hbnd : corrFieldTameJetBound (I := I) (M := M) g₀ a R δ₀ i =
          2 * Classical.choose (exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
              (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2) i
            + 2 * Classical.choose (exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
              (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2) i := by
        unfold corrFieldTameJetBound
        rw [dif_pos hcond]
      have hK0_nn := (Classical.choose_spec (exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
          (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)).1 i
      have hK1_nn := (Classical.choose_spec (exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
          (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)).1 i
      have h0 := (Classical.choose_spec (exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
          (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)).2
        T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
      have h1 := (Classical.choose_spec (exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
          (I := I) (M := M) g₀ a hcond.1 hcond.2.1 hcond.2.2)).2
        T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i s hs
      have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
        Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      have h1w : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) := by linarith
      rw [hbnd]
      constructor
      · exact le_trans h0 (mul_le_mul_of_nonneg_right (by linarith) h1w)
      · exact le_trans h1 (mul_le_mul_of_nonneg_right (by linarith) h1w)
  · intro hTsymm hT'symm s hs x v hδ_lt hδ'_lt
    exact linearizedRicciAt_eq_threeArm_connDiffCoeff (I := I) g₀ T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ' s hs x v
  · exact fun s => rfl
  · exact fun s => rfl

theorem exists_arm0_arm1_corrField_data (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (C0 : ℝ → SmoothCcTensor g₀ 2 2) (C1 : ℝ → SmoothCcTensor g₀ 3 2),
      corrFieldDataSpec (I := I) (M := M) g₀ T T' hδ hδ' C0 C1 :=
  exists_corrFieldChristoffelConst (I := I) (M := M) g₀ T T' hδ hδ'

noncomputable def linearizedRicciArm0CorrField (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ℝ → SmoothCcTensor g₀ 2 2 :=
  (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose

noncomputable def linearizedRicciArm1CorrField (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ℝ → SmoothCcTensor g₀ 3 2 :=
  (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose

def linearizedRicciArm0Field (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
    + linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s

def linearizedRicciArm1Field (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s
    + linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s

theorem linearizedRicci_arm0Field_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') :=
  (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec.1

theorem linearizedRicci_arm1Field_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') :=
  (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec.2.1

set_option maxHeartbeats 3200000 in

theorem ricciArmBaseFields_lichnerowicz_uniform_rfns_ballUniform
    (g₀ _g_bg : SmoothRiemannianMetric I M) (a : ℕ)
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
            ((linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC := by
  classical
  obtain ⟨Λcurv, hΛcurv_nn, hcurv⟩ :=
    exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λcom, hΛcom_nn, hcom⟩ :=
    exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  set K : ℝ := max Λcurv Λcom with hK_def
  have hK_nn : 0 ≤ K := le_trans hΛcurv_nn (le_max_left _ _)
  refine ⟨Real.sqrt (4 * K), Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hRm, hCurvFib⟩ := hcurv T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hPrin, hTH⟩ := hcom T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have hRm' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K :=
    le_trans hRm (le_max_left _ _)
  have hCurvFib' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K :=
    le_trans hCurvFib (le_max_left _ _)
  have hPrin' : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K :=
    le_trans hPrin (le_max_right _ _)
  have hTH' : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((traceHessianCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K :=
    le_trans hTH (le_max_right _ _)
  constructor
  · have hsec : (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x =
        ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) := by
      rw [linearizedRicciArm0BaseCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
        Pi.sub_apply]
    rw [hsec]
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
      ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
    have hbound : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) ≤ 4 * K := by
      nlinarith [hsub, hRm', hCurvFib', hK_nn]
    refine Real.sqrt_le_sqrt hbound
  · have hsec : (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x =
        ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - (1 / 2 : ℝ) • ((traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) := by
      rw [linearizedRicciArm2FieldLichnerowicz, SmoothCcTensor.toSection_sub,
        ContMDiffSection.coe_sub, Pi.sub_apply, SmoothCcTensor.toSection_smul,
        ContMDiffSection.coe_smul, Pi.smul_apply]
    rw [hsec]
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 2 x
      ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
      ((1 / 2 : ℝ) • ((traceHessianCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x))
    have hsmul : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((1 / 2 : ℝ) • ((traceHessianCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) =
        (1 / 2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) :=
      riemannianFiberNormSq_smul_value_appCc (I := I) (M := M) g₀ 4 2 x (1 / 2 : ℝ) _
    have hbound : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (((ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - (1 / 2 : ℝ) • ((traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) ≤ 4 * K := by
      rw [hsmul] at hsub
      nlinarith [hsub, hPrin', hTH', hK_nn]
    refine Real.sqrt_le_sqrt hbound

theorem exists_arm1Base_realizedFam_rfns_ballUniform
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
              ((linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x) ≤ Λarm1 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  obtain ⟨Λarm1, hΛarm1_nn, hΛarm1⟩ :=
    exists_arm1Koszul_realizedFam_pointwise_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀
      (Csob * R) (by positivity)
  refine ⟨Λarm1, hΛarm1_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  rw [linearizedRicciArm1BaseCoeff]
  refine hΛarm1 T T' hδ_le hδ hδ'_le hδ' s hs x ?_
  exact hCsob T T' hR hTball hT'ball s hs x

set_option maxHeartbeats 3200000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_arm0_arm1_corrField_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λcorr : ℝ, 0 ≤ Λcorr ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ Λcorr ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ Λcorr := by
  classical
  obtain ⟨ΛCbase, hΛCbase_nn, hbase⟩ :=
    ricciArmBaseFields_lichnerowicz_uniform_rfns_ballUniform
      (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Λarm1, hΛarm1_nn, harm1⟩ :=
    exists_arm1Base_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hCΓ_nn : 0 ≤ corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀ :=
    corrFieldChristoffelBound_nonneg (I := I) (M := M) g₀ a R δ₀
  refine ⟨(ΛCbase + Real.sqrt Λarm1) +
    corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀, ?_, ?_⟩
  · have h2 : 0 ≤ Real.sqrt Λarm1 := Real.sqrt_nonneg _
    linarith
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hbase0, _hbase2⟩ := hbase T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have harm1' := harm1 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨_hj0, _hj1, hbound, _hident⟩ :=
    (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
  obtain ⟨hb0, hb1⟩ := (hbound ha_super hR hδ₀ hδ_le hδ'_le hTball hT'ball).1 s hs x
  have harm1sqrt_nn : 0 ≤ Real.sqrt Λarm1 := Real.sqrt_nonneg _
  constructor
  · have htri : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) +
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            (((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose s).toSection x)) := by
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
      rw [← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _,
        ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _,
        ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _]
      have hfield_eq : (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x =
          (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x +
            ((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose s).toSection x := by
        rw [linearizedRicciArm0Field, linearizedRicciArm0CorrField,
          SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      rw [hfield_eq]
      exact norm_add_le _ _
    refine le_trans htri ?_
    have hcorr0 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose s).toSection x)) ≤
        corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀ := hb0
    linarith [hbase0, hcorr0, harm1sqrt_nn]
  · have htri : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) +
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            (((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose s).toSection
              x)) := by
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 3 2 I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 3 2
      rw [← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _,
        ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _,
        ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _]
      have hfield_eq : (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x =
          (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x +
            ((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose
              s).toSection x := by
        rw [linearizedRicciArm1Field, linearizedRicciArm1CorrField,
          SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      rw [hfield_eq]
      exact norm_add_le _ _
    refine le_trans htri ?_
    have hbase1' : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
        Real.sqrt Λarm1 := Real.sqrt_le_sqrt harm1'
    have hcorr1 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        (((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose s).toSection
          x)) ≤
        corrFieldChristoffelBound (I := I) (M := M) g₀ a R δ₀ := hb1
    linarith [hbase1', hcorr1, hΛCbase_nn]

set_option maxHeartbeats 3200000 in

theorem ricciArmFields_concrete_lichnerowicz_uniform_rfns_ballUniform
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
            ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC := by
  classical
  obtain ⟨ΛCbase, hΛCbase_nn, hbase⟩ :=
    ricciArmBaseFields_lichnerowicz_uniform_rfns_ballUniform (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λcorr, hΛcorr_nn, hcorr⟩ :=
    exists_arm0_arm1_corrField_rfns_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨max ΛCbase Λcorr, le_trans hΛCbase_nn (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨_hbase0, hbase2⟩ := hbase T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hcorr0, hcorr1⟩ := hcorr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  exact ⟨le_trans hcorr0 (le_max_right _ _), le_trans hcorr1 (le_max_right _ _),
    le_trans hbase2 (le_max_left _ _)⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
