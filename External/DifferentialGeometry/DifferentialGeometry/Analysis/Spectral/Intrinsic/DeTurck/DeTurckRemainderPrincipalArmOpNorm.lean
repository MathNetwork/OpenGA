import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmSpectralGarding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnLapCommutatorCoefficientTame
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.ChartH2GardingConstant
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricPathResolventFactorization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2WeitzenbockRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormCometricCoeffFibreSup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormArmFieldPathIntegralJetL2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateJetLadder


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem smoothCcToTensorHs_rawTensorConnLapSmooth_le
    (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set lam : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
      (I := I) (M := M) i with hlam_def
  set c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i
    with hc_def
  have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := norm_nonneg _
  have hlam_nn : ∀ i, 0 ≤ lam i := fun i =>
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg
      (I := I) (M := M) i
  have hLHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)) i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ h_compact T i]
    rw [show (- lam i * c i) ^ 2 = (lam i) ^ 2 * (c i) ^ 2 by ring]
    ring
  have hRHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i (σ + 2) * (c i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2]
    have hw2 : tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) = (1 + lam i) ^ 2 := by
      unfold tensorSobolevWeight
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hw2]
  have hsummable_RHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2) := by
    have hw := (ccSpectralEmbed (I := I) (M := M) g₀ (σ + 2) T).weighted_summable
    refine hw.congr (fun i => ?_)
    rw [ccSpectralEmbed_coeff,
      show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
    exact hRHS_term i
  have hsummable_LHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsummable_RHS
    · have := tensorSobolevWeight_pos (I := I) (M := M) i σ
      have := hlam_nn i
      positivity
    · have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
      have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
        have := hlam_nn i; nlinarith
      have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def]
      exact hLHS_term i]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def,
        show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
      exact hRHS_term i]
    refine Summable.tsum_le_tsum (fun i => ?_) hsummable_LHS hsummable_RHS
    have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
    have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
      have := hlam_nn i; nlinarith
    have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  exact le_of_sq_le_sq hsq hnn

theorem exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_principal_le
      (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨Clower, hClower_nn, fun m T₀ hball => ?_⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ∀ (τ : ℝ) (X : SmoothCcTensor g₀ 0 2),
        smoothCcToTensorHs (I := I) (M := M) g₀ τ X = 0 := by
      intro τ X
      have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
          DifferentialGeometry.Integral.L2.tensorL2Norm,
          DifferentialGeometry.Integral.L2.tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
        hL2, tensorL2Coeff_eq_inner, inner_zero_right]
    rw [hzero, hzero, hzero]
    simp
  · have hδ_nn : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hCEκ_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
      mul_nonneg (deTurckArmFibreConst_nonneg _) hκ_nn
    refine le_trans (hbound m T₀ hball) ?_
    have hshift : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀ (m : ℝ) T₀
    have htop : deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
      mul_le_mul_of_nonneg_left hshift hCEκ_nn
    linarith

theorem exists_coeffAction_iteratedCovGrad_l2_dataJetWindow_le
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ Cgrid : ℕ → ℝ, (∀ q, 0 ≤ Cgrid q) ∧
      ∀ (q : ℕ) (C : SmoothCcTensor g₀ (2 + m) 2) (Kc : ℝ) (T₀ : SmoothCcTensor g₀ 0 2),
        0 ≤ Kc →
        (∀ (i : ℕ), i ≤ q → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) ≤ Kc ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
          Cgrid q * Kc * Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  refine ⟨fun q => Real.sqrt (diagonalGridGrowthFactor (E := E) q * ((q : ℝ) + 1)) *
      Real.sqrt ((q + m + 1 : ℕ) : ℝ),
    fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    fun q C Kc T₀ hKc hjet => ?_⟩
  have hG_nn : 0 ≤ diagonalGridGrowthFactor (E := E) q := appCcGdiag_nonneg (E := E) q
  have hGq_nn : 0 ≤ diagonalGridGrowthFactor (E := E) q * ((q : ℝ) + 1) :=
    mul_nonneg hG_nn (by positivity)
  set Cpk : ℝ := Kc * Real.sqrt (diagonalGridGrowthFactor (E := E) q * ((q : ℝ) + 1)) with hCpk_def
  have hCpk_nn : 0 ≤ Cpk := mul_nonneg hKc (Real.sqrt_nonneg _)
  have hCpksq : Cpk ^ 2 = Kc ^ 2 * (diagonalGridGrowthFactor (E := E) q * ((q : ℝ) + 1)) := by
    rw [hCpk_def, mul_pow, Real.sq_sqrt hGq_nn]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀))).toSection x) ≤
        Cpk ^ 2 * ∑ i ∈ Finset.range (q + m + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x) := by
    intro x
    set Sfull : ℝ := ∑ i ∈ Finset.range (q + m + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x) with hSfull_def
    have hshift : ∀ (F : ℕ → ℝ), (∀ i, 0 ≤ F i) →
        (∑ l ∈ Finset.range (q + 1), F (m + l)) ≤ ∑ i ∈ Finset.range (q + m + 1), F i := by
      intro F hF
      have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
          m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
      have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆
          Finset.range (q + m + 1) := by
        intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨l, hl, rfl⟩ := hi
        rw [Finset.mem_range] at hl ⊢; omega
      calc (∑ l ∈ Finset.range (q + 1), F (m + l))
          = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), F i :=
            (Finset.sum_image hinj).symm
        _ ≤ ∑ i ∈ Finset.range (q + m + 1), F i :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hF i)
    have hWfull : (∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤ Sfull := by
      rw [show (∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) =
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀).toSection x) from
        Finset.sum_congr rfl (fun l _ =>
          riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l T₀ x)]
      rw [hSfull_def]
      exact hshift (fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x))
        (fun i => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
    have hterm : ∀ i ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) ≤
          Kc ^ 2 * Sfull := by
      intro i hi
      have hi_le : i ≤ q := by rw [Finset.mem_range] at hi; omega
      have hgC := hjet i hi_le x
      have hsub : Finset.range (q + 1 - i) ⊆ Finset.range (q + 1) :=
        Finset.range_mono (by omega)
      have hWi : (∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 ((2 + m) + l) x _)
      have hWi_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) :=
        Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 ((2 + m) + l) x _)
      exact mul_le_mul hgC (le_trans hWi hWfull) hWi_nn (sq_nonneg Kc)
    have hmono : (∑ i ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
              ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
            ∑ l ∈ Finset.range (q + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
                ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤
        ((q : ℝ) + 1) * (Kc ^ 2 * Sfull) := by
      refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀ (2 + m) 2 C
        (iteratedCovGrad (I := I) g₀ 0 2 m T₀) q x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hmono hG_nn) ?_
    rw [hCpksq]
    apply le_of_eq; ring
  have hpack := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (q + m + 1) (fun i => 2 + i) (fun i => iteratedCovGrad (I := I) g₀ 0 2 i T₀)
    (iteratedCovGrad (I := I) g₀ 0 2 q
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C (iteratedCovGrad (I := I) g₀ 0 2 m T₀)))
    Cpk hCpk_nn hpt
  refine le_trans hpack ?_
  have hCS : ∑ i ∈ Finset.range (q + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
      Real.sqrt ((q + m + 1 : ℕ) : ℝ) *
        Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (q + m + 1))
      (fun _ => (1 : ℝ)) (fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hcs0
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (q + m + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    rw [← Real.sqrt_sq hsum_nn,
      show Real.sqrt ((q + m + 1 : ℕ) : ℝ) *
          Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) =
        Real.sqrt (((q + m + 1 : ℕ) : ℝ) *
          ∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) from
        (Real.sqrt_mul (by positivity) _).symm]
    exact Real.sqrt_le_sqrt hcs0
  refine le_trans (mul_le_mul_of_nonneg_left hCS hCpk_nn) ?_
  rw [hCpk_def]
  apply le_of_eq; ring

theorem exists_smoothCcToTensorHs_real_le_of_iteratedCovGrad_jet_window
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    (Clow : ℕ → ℝ) (hClow_nn : ∀ q, 0 ≤ Clow q) :
    ∃ Ctame : ℕ → ℝ, (∀ k, 0 ≤ Ctame k) ∧
      ∀ (k : ℕ) (U V : SmoothCcTensor g₀ 0 2),
        (∀ q : ℕ, ‖iteratedCovGrad (I := I) g₀ 0 2 q U‖ ≤
          Clow q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2)) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) U‖ ≤
          Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) V‖ := by
  classical
  set C1 : ℕ → ℝ := fun k =>
    (exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀
      (a + k - 1)).choose with hC1_def
  set C2 : ℕ → ℝ := fun k =>
    (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀
      (a + k - 1 + 1)).choose with hC2_def
  have hC1_spec : ∀ k, 0 ≤ C1 k ∧ ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 : ℕ) : ℝ) S‖ ≤
        C1 k * ∑ j ∈ Finset.range (a + k - 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
    fun k => (exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀
      (a + k - 1)).choose_spec
  have hC2_spec : ∀ k, 0 ≤ C2 k ∧ ∀ S : SmoothCcTensor g₀ 0 2,
      ∑ j ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        C2 k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) S‖ :=
    fun k => (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀
      (a + k - 1 + 1)).choose_spec
  refine ⟨fun k => C1 k * (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * C2 k,
    fun k => ?_, fun k U V hU => ?_⟩
  · exact mul_nonneg (mul_nonneg (hC1_spec k).1
      (Finset.sum_nonneg (fun j _ => hClow_nn j))) (hC2_spec k).1
  · have hUexp : (a : ℝ) + (k : ℝ) - 1 = ((a + k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ a + k by omega)]; push_cast; ring
    have hVexp : (a : ℝ) + (k : ℝ) = ((a + k - 1 + 1 : ℕ) : ℝ) := by
      rw [show a + k - 1 + 1 = a + k by omega]; push_cast; ring
    rw [hUexp, hVexp]
    set SV : ℝ := ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ with hSV_def
    have hSV_nn : 0 ≤ SV := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hsq_le : ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 ≤ SV ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
    have hsqrtV_le : Real.sqrt (∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2) ≤ SV :=
      le_trans (Real.sqrt_le_sqrt hsq_le) (le_of_eq (Real.sqrt_sq hSV_nn))
    have hUj : ∀ j ∈ Finset.range (a + k - 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ ≤ Clow j * SV := by
      intro j hj
      have hj_le : j ≤ a + k - 1 := by rw [Finset.mem_range] at hj; omega
      refine le_trans (hU j) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hClow_nn j)
      have hsub : Finset.range (j + 1 + 1) ⊆ Finset.range (a + k - 1 + 1 + 1) :=
        Finset.range_mono (by omega)
      have hwin : ∑ i ∈ Finset.range (j + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 ≤
          ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
      exact le_trans (Real.sqrt_le_sqrt hwin) hsqrtV_le
    have hUsum : ∑ j ∈ Finset.range (a + k - 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ ≤
        (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * SV := by
      refine le_trans (Finset.sum_le_sum hUj) ?_
      rw [Finset.sum_mul]
    have hb1 := (hC1_spec k).2 U
    have hb2 := (hC2_spec k).2 V
    have hSV_le : SV ≤ C2 k *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) V‖ := hb2
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 : ℕ) : ℝ) U‖
        ≤ C1 k * ∑ j ∈ Finset.range (a + k - 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ := hb1
      _ ≤ C1 k * ((∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * SV) :=
          mul_le_mul_of_nonneg_left hUsum (hC1_spec k).1
      _ ≤ C1 k * ((∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) *
            (C2 k * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((a + k - 1 + 1 : ℕ) : ℝ) V‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hC1_spec k).1
          exact mul_le_mul_of_nonneg_left hSV_le
            (Finset.sum_nonneg (fun j _ => hClow_nn j))
      _ = C1 k * (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * C2 k *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) V‖ := by
          ring

def deTurckArmContractionThreshold' (n : ℕ) : ℝ :=
  1 / (1 + 2 * (deTurckArmFibreConst n + deTurckArmFibreConst n ^ 3))

lemma deTurckArmContractionThreshold'_le {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n ≤ deTurckArmContractionThreshold n := by
  have hC := one_le_deTurckArmFibreConst hn
  unfold deTurckArmContractionThreshold' deTurckArmContractionThreshold
  have hC3 : 0 ≤ deTurckArmFibreConst n ^ 3 := by positivity
  apply one_div_le_one_div_of_le (by linarith)
  linarith

lemma deTurckArmContractionThreshold'_le_third {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n ≤ 1 / 3 :=
  le_trans (deTurckArmContractionThreshold'_le hn)
    (deTurckArmContractionThreshold_le_third hn)

lemma deTurckArmContractionThreshold'_lt_one {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n < 1 :=
  lt_of_le_of_lt (deTurckArmContractionThreshold'_le_third hn)
    (by norm_num : (1 : ℝ) / 3 < 1)

lemma deTurckArmContractionThreshold'_le_third' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold' n ≤ 1 / 3 :=
  deTurckArmContractionThreshold'_le_third (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmContractionThreshold'_lt_one' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold' n < 1 :=
  deTurckArmContractionThreshold'_lt_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmFibreConst_cube_mul_div_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ_le : δ ≤ deTurckArmContractionThreshold' n) :
    deTurckArmFibreConst n ^ 3 * (δ / (1 - δ)) ≤
      deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) := by
  have hC := one_le_deTurckArmFibreConst hn
  set C := deTurckArmFibreConst n with hC_def
  set K : ℝ := C + C ^ 3 with hK_def
  have hC3_nn : (0 : ℝ) ≤ C ^ 3 := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; linarith
  have hden : (0 : ℝ) < 1 + 2 * K := by linarith
  have hthr_lt : deTurckArmContractionThreshold' n < 1 :=
    deTurckArmContractionThreshold'_lt_one hn
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le hthr_lt
  have h1δ_pos : (0 : ℝ) < 1 - δ := by linarith
  have hRHS_pos : (0 : ℝ) <
      C ^ 2 / (2 * (1 + C ^ 2)) := by positivity
  by_cases hδ0 : δ ≤ 0
  · have hratio_np : δ / (1 - δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ0 h1δ_pos.le
    have : C ^ 3 * (δ / (1 - δ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hratio_np
    linarith
  · have hδ_mul : δ * (1 + 2 * K) ≤ 1 := by
      have := (le_div_iff₀ hden).mp
        (show δ ≤ 1 / (1 + 2 * K) from hδ_le)
      linarith
    have hratio : δ / (1 - δ) ≤ 1 / (2 * K) := by
      rw [div_le_div_iff₀ h1δ_pos (by linarith : (0 : ℝ) < 2 * K)]
      nlinarith
    have hkey : C ^ 3 / (2 * K) = C ^ 2 / (2 * (1 + C ^ 2)) := by
      rw [hK_def]
      have hCpos : (0 : ℝ) < C := by linarith
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    calc C ^ 3 * (δ / (1 - δ)) ≤ C ^ 3 * (1 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = C ^ 3 / (2 * K) := by ring
      _ = C ^ 2 / (2 * (1 + C ^ 2)) := hkey

lemma deTurckBudget_half_add_lt_one (n : ℕ) :
    (1 / 2 : ℝ) + deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) < 1 := by
  have hC2 : (0 : ℝ) ≤ deTurckArmFibreConst n ^ 2 := sq_nonneg _
  have hden : (0 : ℝ) < 2 * (1 + deTurckArmFibreConst n ^ 2) := by linarith
  have hlt : deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) <
      1 / 2 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

lemma deTurckArmFibreConst_cube_mul_div_le_thirtyTwo {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ_le : δ ≤ deTurckArmContractionThresholdSharp n) :
    32 * deTurckArmFibreConst n ^ 3 * (δ / (1 - δ)) ≤
      32 * deTurckArmFibreConst n ^ 2 / (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) := by
  have hC := one_le_deTurckArmFibreConst hn
  set C := deTurckArmFibreConst n with hC_def
  set K : ℝ := C + 32 * C ^ 3 with hK_def
  have hC3_nn : (0 : ℝ) ≤ C ^ 3 := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; nlinarith
  have hden : (0 : ℝ) < 1 + 2 * K := by linarith
  have hthr_lt : deTurckArmContractionThresholdSharp n < 1 :=
    deTurckArmContractionThreshold''_lt_one hn
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le hthr_lt
  have h1δ_pos : (0 : ℝ) < 1 - δ := by linarith
  by_cases hδ0 : δ ≤ 0
  · have hratio_np : δ / (1 - δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ0 h1δ_pos.le
    have hL : 32 * C ^ 3 * (δ / (1 - δ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hratio_np
    have hR : (0 : ℝ) ≤ 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := by positivity
    linarith
  · have hδ_mul : δ * (1 + 2 * K) ≤ 1 := by
      have := (le_div_iff₀ hden).mp
        (show δ ≤ 1 / (1 + 2 * K) from hδ_le)
      linarith
    have hratio : δ / (1 - δ) ≤ 1 / (2 * K) := by
      rw [div_le_div_iff₀ h1δ_pos (by linarith : (0 : ℝ) < 2 * K)]
      nlinarith
    have hkey : 32 * C ^ 3 / (2 * K) = 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := by
      rw [hK_def]
      have hCpos : (0 : ℝ) < C := by linarith
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    calc 32 * C ^ 3 * (δ / (1 - δ)) ≤ 32 * C ^ 3 * (1 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 32 * C ^ 3 / (2 * K) := by ring
      _ = 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := hkey

lemma deTurckBudget_half_add_thirtyTwo_lt_one (n : ℕ) :
    (1 / 2 : ℝ) + 32 * deTurckArmFibreConst n ^ 2 /
        (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) < 1 := by
  have hC2 : (0 : ℝ) ≤ 32 * deTurckArmFibreConst n ^ 2 := by positivity
  have hden : (0 : ℝ) < 2 * (1 + 32 * deTurckArmFibreConst n ^ 2) := by linarith
  have hlt : 32 * deTurckArmFibreConst n ^ 2 /
      (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) < 1 / 2 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Integral.Measure in
theorem exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kg : ℕ → ℝ, (∀ i, 0 ≤ Kg i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        ∀ (i : ℕ),
          (∫ x, (∑ n' ∈ Finset.range (i + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) ≤
          Kg i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Λ₀ : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * B with hΛ₀_def
  have hΛ₀_nn : 0 ≤ Λ₀ := by rw [hΛ₀_def]; positivity
  set L : ℝ := max (Λ₀ ^ 2) 1 with hL_def
  have hL_one : (1 : ℝ) ≤ L := le_max_right _ _
  have hL_nn : (0 : ℝ) ≤ L := le_trans zero_le_one hL_one
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn_def
  set Cg1 : ℕ → ℝ := fun k => max (Cgn k) 1 with hCg1_def
  have hCg1_one : ∀ k, (1 : ℝ) ≤ Cg1 k := fun k => le_max_right _ _
  have hCgL_one : ∀ k, (1 : ℝ) ≤ Cg1 k * L :=
    fun k => le_trans (hCg1_one k) (le_mul_of_one_le_right
      (le_trans zero_le_one (hCg1_one k)) hL_one)
  set Cbig : ℕ → ℝ := fun k => L ^ k * (Cg1 k * L) ^ k with hCbig_def
  have hCbig_nn : ∀ k, 0 ≤ Cbig k := fun k =>
    mul_nonneg (pow_nonneg hL_nn k)
      (pow_nonneg (le_trans zero_le_one (hCgL_one k)) k)
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal
    with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n' ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n' k).card : ℝ)) * Cbig k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _) (hCbig_nn k)) hvol_nn
  · intro T₀ hball i
    have hS_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have h1S : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by linarith
    have hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      exact le_trans
        (Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))) hsumB
    have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        (T₀.toSection x) ≤ Λ₀ ^ 2 := by
      intro x
      have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
        calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2
            ≤ ∑ j ∈ Finset.range (a + 1 + 1), B ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
              nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j T₀),
                hPball j hjle, hB_nn]
          _ = ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
          ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x) := by
        have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
        have hsl := Finset.single_le_sum
          (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x))
          (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
        simpa using hsl
      have hLam2 : Λ₀ ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
        rw [hΛ₀_def, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x) ≤ Λ₀ ^ 2 := by
        refine le_trans (hCemb T₀ x) ?_
        rw [hLam2]
        calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2
            ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * B ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by ring
      exact le_trans hsingle hchain
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n' ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n' 0, ∏ m : Fin n',
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) =
          (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, ← hvol_def]
      have hvolKg : vol ≤ (∑ n' ∈ Finset.range (0 + 1),
          ((Finset.Nat.antidiagonalTuple n' 0).card : ℝ)) * Cbig 0 + vol :=
        le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _) (hCbig_nn 0))
      calc vol = vol * 1 := (mul_one _).symm
        _ ≤ ((∑ n' ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n' 0).card : ℝ)) * Cbig 0 + vol) *
            (1 + ∑ j ∈ Finset.range (0 + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
          mul_le_mul hvolKg h1S zero_le_one
            (add_nonneg (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _)
              (hCbig_nn 0)) hvol_nn)
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hi0
      have hN2_le : ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
          1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
        have hmem : i ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
        have := Finset.single_le_sum
          (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)
          (fun j _ => sq_nonneg _) hmem
        linarith
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hCgn_i : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
        rw [hCgn_def]; simp only [dif_pos hi1]
      have hLbound : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 2 → Λ₀ ^ θ ≤ L := by
        intro θ hθ0 hθ2
        rcases le_or_gt 1 Λ₀ with hΛ1 | hΛ1
        · calc Λ₀ ^ θ ≤ Λ₀ ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ1 hθ2
            _ = Λ₀ ^ 2 := Real.rpow_two Λ₀
            _ ≤ L := le_max_left _ _
        · calc Λ₀ ^ θ ≤ 1 := Real.rpow_le_one hΛ₀_nn (le_of_lt hΛ1) hθ0
            _ ≤ L := hL_one
      have hcont_prod : ∀ (n' : ℕ) (e : Fin n' → ℕ), Continuous (fun x : M =>
          ∏ m : Fin n', riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
        intro n' e
        refine continuous_finset_prod _ fun m _ => ?_
        have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
          (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
        refine hc.congr fun x => ?_
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
          ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
      have hint_prod : ∀ (n' : ℕ) (e : Fin n' → ℕ), MeasureTheory.Integrable
          (fun x : M => ∏ m : Fin n',
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        fun n' e => integrable_of_continuous_compactSpace (I := I) (M := M) g₀
          (hcont_prod n' e)
      have hPT : ∀ n' ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n' i,
          (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
        intro n' hn' e he
        have hn'_le : n' ≤ i := by have := Finset.mem_range.mp hn'; omega
        have hsum_univ : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hem_le : ∀ m : Fin n', e m ≤ i := by
          intro m
          have h1 := Finset.single_le_sum (f := fun m' => e m')
            (fun m' _ => Nat.zero_le (e m')) (Finset.mem_univ m)
          rw [hsum_univ] at h1
          exact h1
        have hΛzero : ∀ m ∈ (Finset.univ : Finset (Fin n')), e m = 0 → ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) ≤ Λ₀ ^ 2 := by
          intro m _ hm0 x
          revert hm0
          generalize e m = j
          intro hj
          subst hj
          simpa [iteratedCovGrad_zero] using hsup x
        have hHold := holder_integral_prod_riemannianFiberNormSq_natWeight_le_of_sup_bound
          (I := I) (M := M) g₀ (Finset.univ : Finset (Fin n')) (fun _ => 0)
          (fun m => 2 + e m) (fun m => iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) e i
          hi1 hsum_univ (fun _ => Λ₀ ^ 2) (fun m _ _ => sq_nonneg _) hΛzero
        beta_reduce at hHold
        have hsum_pos_nat : ∑ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m), e m = i := by
          rw [← hsum_univ]
          refine Finset.sum_subset (Finset.filter_subset _ _) fun m _ hm => ?_
          by_contra h0
          exact hm (Finset.mem_filter.mpr ⟨Finset.mem_univ m, Nat.pos_of_ne_zero h0⟩)
        have h2sum : ∑ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (2 * (e m : ℝ) / (i : ℝ)) = 2 := by
          have hterm : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
              2 * (e m : ℝ) / (i : ℝ) = (e m : ℝ) * (2 / (i : ℝ)) := fun m _ => by ring
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum, hsum_pos_nat]
          field_simp
        have hposcard : (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card ≤ i := by
          calc (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card
              ≤ (Finset.univ : Finset (Fin n')).card := Finset.card_filter_le _ _
            _ = n' := by simp
            _ ≤ i := hn'_le
        have hzercard : (Finset.univ.filter (fun m : Fin n' => e m = 0)).card ≤ i := by
          calc (Finset.univ.filter (fun m : Fin n' => e m = 0)).card
              ≤ (Finset.univ : Finset (Fin n')).card := Finset.card_filter_le _ _
            _ = n' := by simp
            _ ≤ i := hn'_le
        have hFG : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) ≤
            Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
              ^ (2 * (e m : ℝ) / (i : ℝ)) := by
          intro m hm
          have hem_pos : 0 < e m := (Finset.mem_filter.mp hm).2
          rcases eq_or_lt_of_le (hem_le m) with hemi | hemi
          · subst hemi
            have hd1 : ((e m : ℝ) / (e m : ℝ)) = 1 := div_self (ne_of_gt hiR_pos)
            rw [hd1, Real.rpow_one, mul_div_assoc, hd1, mul_one, Real.rpow_two]
            simp only [Real.rpow_one]
            have hbr := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
              (I := I) (M := M) g₀ 0 (2 + e m)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
            rw [← SmoothCcTensor.norm_def] at hbr
            rw [← hbr]
            have h1 : (1 : ℝ) ≤ Cg1 (e m) * L := hCgL_one (e m)
            nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀‖]
          · have hb := hGNspec T₀ Λ₀ hΛ₀_nn hsup (e m) hem_pos hemi
            rw [hCgn_i] at hb
            refine le_trans hb ?_
            have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
                (iteratedCovGrad (I := I) g₀ 0 2 i T₀).toFun =
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
              (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i T₀)).symm
            rw [hnorm]
            have hθL_nn : (0 : ℝ) ≤ 2 * (1 - (e m : ℝ) / (i : ℝ)) := by
              have : (e m : ℝ) / (i : ℝ) ≤ 1 :=
                (div_le_one hiR_pos).mpr (by exact_mod_cast hem_le m)
              linarith
            have hθL_le2 : 2 * (1 - (e m : ℝ) / (i : ℝ)) ≤ 2 := by
              have : (0 : ℝ) ≤ (e m : ℝ) / (i : ℝ) := by positivity
              linarith
            have hΛfac : Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) ≤ L :=
              hLbound _ hθL_nn hθL_le2
            have hNfac_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                ^ (2 * (e m : ℝ) / (i : ℝ)) :=
              Real.rpow_nonneg (norm_nonneg _) _
            calc Cgn i * Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) *
                  ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 * (e m : ℝ) / (i : ℝ))
                ≤ Cg1 i * Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) *
                  ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 * (e m : ℝ) / (i : ℝ)) := by
                  refine mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (le_max_left _ _)
                      (Real.rpow_nonneg hΛ₀_nn _)) hNfac_nn
              _ ≤ Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                  ^ (2 * (e m : ℝ) / (i : ℝ)) := by
                  refine mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hΛfac
                      (le_trans zero_le_one (hCg1_one i))) hNfac_nn
        have hF_nn : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (0 : ℝ) ≤ (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) :=
          fun m _ => Real.rpow_nonneg
            (MeasureTheory.integral_nonneg fun x => Real.rpow_nonneg
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _) _) _
        have hprodF_le : (∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ))) ≤
            ∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
              (Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                ^ (2 * (e m : ℝ) / (i : ℝ))) :=
          Finset.prod_le_prod hF_nn hFG
        have hprodG : (∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
              ^ (2 * (e m : ℝ) / (i : ℝ)))) =
            (Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            ← Real.rpow_sum_of_nonneg (norm_nonneg _) (fun m _ => by positivity), h2sum]
        have hzer_le : ((Λ₀ ^ 2) ^ (Finset.univ.filter
            (fun m : Fin n' => e m = 0)).card : ℝ) ≤ L ^ i :=
          le_trans (pow_le_pow_left₀ (sq_nonneg _) (le_max_left _ _) _)
            (pow_le_pow_right₀ hL_one hzercard)
        have hpos_le : ((Cg1 i * L) ^ (Finset.univ.filter
            (fun m : Fin n' => 0 < e m)).card : ℝ) ≤ (Cg1 i * L) ^ i :=
          pow_le_pow_right₀ (hCgL_one i) hposcard
        calc (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
            ≤ (∏ _m ∈ Finset.univ.filter (fun m : Fin n' => e m = 0), Λ₀ ^ 2) *
              ∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
                (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                      ^ ((i : ℝ) / (e m : ℝ))
                  ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) :=
            hHold
          _ ≤ (∏ _m ∈ Finset.univ.filter (fun m : Fin n' => e m = 0), Λ₀ ^ 2) *
              ((Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (le_of_le_of_eq hprodF_le hprodG) ?_
            exact Finset.prod_nonneg fun _ _ => sq_nonneg _
          _ = (Λ₀ ^ 2) ^ (Finset.univ.filter (fun m : Fin n' => e m = 0)).card *
              ((Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
            rw [Finset.prod_const, Real.rpow_two]
          _ ≤ L ^ i * ((Cg1 i * L) ^ i *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
            refine mul_le_mul hzer_le
              (mul_le_mul_of_nonneg_right hpos_le (sq_nonneg _))
              (mul_nonneg (pow_nonneg (le_trans zero_le_one (hCgL_one i)) _)
                (sq_nonneg _))
              (pow_nonneg hL_nn i)
          _ = Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
            simp only [hCbig_def]
            ring
      rw [MeasureTheory.integral_finset_sum _
        (fun n' _ => MeasureTheory.integrable_finset_sum _ (fun e _ => hint_prod n' e))]
      have hinner : ∀ n' ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n' i, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
            ∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀) :=
        fun n' _ => MeasureTheory.integral_finset_sum _ (fun e _ => hint_prod n' e)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n' ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
            (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) ≤
          ∑ n' ∈ Finset.range (i + 1), ∑ _e ∈ Finset.Nat.antidiagonalTuple n' i,
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
        refine Finset.sum_le_sum fun n' hn' => Finset.sum_le_sum fun e he => ?_
        exact hPT n' hn' e he
      refine le_trans hle1 ?_
      have heq2 : ∑ n' ∈ Finset.range (i + 1), ∑ _e ∈ Finset.Nat.antidiagonalTuple n' i,
          (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) =
          (∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n' _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [heq2]
      have hcard_nn : (0 : ℝ) ≤ ∑ n' ∈ Finset.range (i + 1),
          ((Finset.Nat.antidiagonalTuple n' i).card : ℝ) :=
        Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _
      calc (∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2)
          = ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i) * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by ring
        _ ≤ ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i) * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hN2_le (mul_nonneg hcard_nn (hCbig_nn i))
        _ ≤ ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i + vol) * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hvol_nn)
              (le_trans zero_le_one h1S)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Integral.Measure in
theorem exists_deTurckPrincipalCometricCoeff_realize_coeffJetEnvelope_le
    (g₀ _g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder (I := I) (M := M) g₀ a ha_super hR₀
  obtain ⟨Cd, hCd_nn, hCd⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Klo, hKlo_nn, hKlo⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hB_nn
      (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀
      (by norm_num : (1 : ℝ) / 3 < 1)
  set KcF : ℕ → ℝ := fun i => Cd i * ∑ j ∈ Finset.range (i + 1),
    (Klo j + Cg j * Kg j) with hKcF_def
  have hKcF_nn : ∀ i, 0 ≤ KcF i := fun i =>
    mul_nonneg (hCd_nn i) (Finset.sum_nonneg fun j _ =>
      add_nonneg (hKlo_nn j) (mul_nonneg (hCg_nn j) (hKg_nn j)))
  refine ⟨KcF, hKcF_nn, ?_⟩
  intro T₀ hTsymm hball i
  set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T₀
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) with hg₁_def
  have hS_nn : 0 ≤ ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have h1S_nn : (0 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, DifferentialGeometry.Integral.L2.tensorL2Norm,
        DifferentialGeometry.Integral.L2.tensorL2Inner, MeasureTheory.integral_of_isEmpty,
        Real.sqrt_zero]
    rw [hzero]
    have hpos : (0 : ℝ) ≤ KcF i * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := mul_nonneg (hKcF_nn i) h1S_nn
    simpa using hpos
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
      intro y v w
      rw [hg₁_def]
      exact tensorSectionRealizeMetric_inner (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ :=
        Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      exact le_trans hsingle hsumB
    have hint_slot : ∀ j : ℕ, MeasureTheory.Integrable
        (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      fun j => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j) _
    have hL2trans : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
        Cd i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
      have hF_int : MeasureTheory.Integrable
          (fun x => Cd i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (MeasureTheory.integrable_finset_sum _ (fun j _ => hint_slot j)).const_mul (Cd i)
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        (2 + 2) (2 + i)
        (iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
        (fun x => Cd i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 2 2 j
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
        hF_int (fun x => hCd g₁ i x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (hCd_nn i)
      rw [MeasureTheory.integral_finset_sum _ (fun j _ => hint_slot j)]
      refine Finset.sum_le_sum fun j _ => ?_
      have hbr := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
        g₀ 2 (2 + j) (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
      rw [← SmoothCcTensor.norm_def] at hbr
      exact le_of_eq hbr.symm
    have hslot : ∀ j : ℕ, j ≤ i →
        ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
          (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro j hj
      have h1S_ge : (1 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
      rcases le_or_gt j a with hja | hja
      · have hlo := hKlo g₁ T₀ hδ_le (hδ_fibre T₀ hball) htie hPball j hja
        calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
            ≤ Klo j := hlo
          _ = Klo j * 1 := (mul_one _).symm
          _ ≤ Klo j * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1S_ge (hKlo_nn j)
          _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ h1S_nn
            exact le_add_of_nonneg_right (mul_nonneg (hCg_nn j) (hKg_nn j))
      · have hpt : ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
            Cg j * ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) :=
          fun x => hCg g₁ T₀ htie hδ_le hδ0 (hδ_fibre T₀ hball) j x
        have hcont_grid : Continuous (fun x : M =>
            ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
          refine continuous_finset_sum _ fun n' _ => continuous_finset_sum _ fun e _ =>
            continuous_finset_prod _ fun m _ => ?_
          have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
          refine hc.congr fun x => ?_
          rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
            ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
        have hint_grid : MeasureTheory.Integrable
            (fun x : M => ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
          integrable_of_continuous_compactSpace (I := I) (M := M) g₀ hcont_grid
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
          2 (2 + j)
          (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
          (fun x => Cg j * ∑ n' ∈ Finset.range (j + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
              ∏ m : Fin n',
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
          (hint_grid.const_mul (Cg j)) hpt
        have hgridE := hKg T₀ hball j
        have hwin : ∑ l ∈ Finset.range (j + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
            ∑ l ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (hrsub _ _ (by omega))
            (fun l _ _ => sq_nonneg _)
        calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
            ≤ ∫ x, (Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := hkey
          _ = Cg j * ∫ x, (∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
            rw [MeasureTheory.integral_const_mul]
          _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (j + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hgridE (hCg_nn j)
          _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (hCg_nn j)
            refine mul_le_mul_of_nonneg_left ?_ (hKg_nn j)
            linarith
          _ = Cg j * Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by ring
          _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ h1S_nn
            exact le_add_of_nonneg_left (hKlo_nn j)
    calc ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
        ≤ Cd i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
          hL2trans
      _ ≤ Cd i * ∑ j ∈ Finset.range (i + 1),
            ((Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (hCd_nn i)
          exact hslot j (by have := Finset.mem_range.mp hj; omega)
      _ = KcF i * (1 + ∑ l ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
          simp only [hKcF_def]
          rw [← Finset.sum_mul]
          ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pje_icg_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma riemannianFiberNormSq_toSection_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (V : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((c • V).toSection x) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x (V.toSection x) := by
  rw [show ((c • V).toSection x) = c • (V.toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
      (c • V.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (V.toSection x)]
  rw [Tensor0SBundle.TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pje_normSq_icg_reindex_eq (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i R‖ ^ 2 := by
  have h1 := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
    g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ))
  have h2 := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
    g₀ 4 (2 + i) (iteratedCovGrad (I := I) g₀ 4 2 i R)
  rw [← SmoothCcTensor.norm_def] at h1 h2
  rw [h1, h2]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2 R ρ i x

set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization in
open DifferentialGeometry.Integral.Measure in
theorem exists_deTurckPhiTotPathIntegral_sub_background_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder (I := I) (M := M) g₀ a ha_super hR₀
  obtain ⟨Cth, hCth_nn, hCth⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  obtain ⟨Cr, hCr_nn, hCr⟩ :=
    ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Klo, hKlo_nn, hKlo⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hB_nn
      (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀
      (by norm_num : (1 : ℝ) / 3 < 1)
  set KdevF : ℕ → ℝ := fun i => (6 * Cth i + 12 * Cr i) * ∑ j ∈ Finset.range (i + 1),
    (Klo j + Cg j * Kg j) with hKdevF_def
  have hKdevF_nn : ∀ i, 0 ≤ KdevF i := fun i =>
    mul_nonneg (by have := hCth_nn i; have := hCr_nn i; linarith)
      (Finset.sum_nonneg fun j _ =>
        add_nonneg (hKlo_nn j) (mul_nonneg (hCg_nn j) (hKg_nn j)))
  set cB : ℕ → ℝ := fun i =>
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 with hcB_def
  have hcB_nn : ∀ i, 0 ≤ cB i := fun i => sq_nonneg _
  refine ⟨fun i => 4 * KdevF i + 6 * cB i,
    fun i => by have := hKdevF_nn i; have := hcB_nn i; linarith, ?_⟩
  intro T₀ hTsymm hball i
  change ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
    (4 * KdevF i + 6 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)
  have hS_nn : 0 ≤ ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have h1S_nn : (0 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  have h1S_ge : (1 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, DifferentialGeometry.Integral.L2.tensorL2Norm,
        DifferentialGeometry.Integral.L2.tensorL2Inner, MeasureTheory.integral_of_isEmpty,
        Real.sqrt_zero]
    rw [hzero]
    have hpos : (0 : ℝ) ≤ (4 * KdevF i + 6 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_nonneg (by have := hKdevF_nn i; have := hcB_nn i; linarith) h1S_nn
    simpa using hpos
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
    have hZn : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R₀ := by
      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
          from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
      simpa using hR₀
    have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ)) := realizedSmallSet_isOpen
    have hj2 := deTurckPhiMetTotal_jointSmooth_along_realizedFam (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2) (hδ_fibre T₀ hball) (hδ_fibre 0 hZn)
    have hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ :=
        Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      exact le_trans hsingle hsumB
    have hdev : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
        KdevF i * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro s hs
      set g₁ : SmoothRiemannianMetric I M :=
        realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s with hg₁_def
      have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
        Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
      have htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s) y v w := by
        intro y v w
        rw [hg₁_def]
        exact realizedFam_inner_of_mem (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) hsmem y v w
      have hcp : convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s = s • T₀ := by
        simp [convexPerturbation, smul_zero, zero_add]
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have hs1 : s ≤ 1 := hs.2
      have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s)) δ := by
        have h := convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T₀
          (0 : SmoothCcTensor g₀ 0 2) (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) hs0 hs1
        rwa [show (1 - s) * δ + s * δ = δ by ring] at h
      have hPball : ∀ j : ℕ, j ≤ a + 2 →
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s)‖ ≤ B := by
        intro j hj
        rw [hcp, pje_icg_smul (I := I) g₀ 0 2 j s T₀, norm_smul]
        have habs : ‖s‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs1
        calc ‖s‖ * ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖
            ≤ 1 * B := mul_le_mul habs (hTball j hj) (norm_nonneg _) zero_le_one
          _ = B := one_mul B
      have hslot : ∀ j : ℕ, j ≤ i →
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
            (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
        intro j hj
        rcases le_or_gt j a with hja | hja
        · have hlo := hKlo g₁ (convexPerturbation (I := I) g₀ T₀
            (0 : SmoothCcTensor g₀ 0 2) s) hδ_le hδP htie hPball j hja
          calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
              ≤ Klo j := hlo
            _ = Klo j * 1 := (mul_one _).symm
            _ ≤ Klo j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h1S_ge (hKlo_nn j)
            _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
              refine mul_le_mul_of_nonneg_right ?_ h1S_nn
              exact le_add_of_nonneg_right (mul_nonneg (hCg_nn j) (hKg_nn j))
        · have hpt0 : ∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 2 2 j
                  (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
              Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                        (convexPerturbation (I := I) g₀ T₀
                          (0 : SmoothCcTensor g₀ 0 2) s)).toSection x) :=
            fun x => hCg g₁ (convexPerturbation (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) s) htie hδ_le hδ0 hδP j x
          have hgm : ∀ x : M,
              (∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                        (convexPerturbation (I := I) g₀ T₀
                          (0 : SmoothCcTensor g₀ 0 2) s)).toSection x)) ≤
              ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
            intro x
            refine Finset.sum_le_sum fun n' _ => Finset.sum_le_sum fun e _ => ?_
            have hfac : ∀ m : Fin n',
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                    (convexPerturbation (I := I) g₀ T₀
                      (0 : SmoothCcTensor g₀ 0 2) s)).toSection x) =
                s ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
              intro m
              rw [hcp, pje_icg_smul (I := I) g₀ 0 2 (e m) s T₀,
                riemannianFiberNormSq_toSection_smul (I := I) (M := M) g₀ 0 (2 + e m) s
                  (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
            calc (∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                      (convexPerturbation (I := I) g₀ T₀
                        (0 : SmoothCcTensor g₀ 0 2) s)).toSection x))
                = ∏ m : Fin n', (s ^ 2 *
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) :=
                  Finset.prod_congr rfl fun m _ => hfac m
              _ = (s ^ 2) ^ (n' : ℕ) * ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
                  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
                    Fintype.card_fin]
              _ ≤ 1 * ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
                  refine mul_le_mul_of_nonneg_right ?_
                    (Finset.prod_nonneg fun m _ =>
                      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _)
                  exact pow_le_one₀ (sq_nonneg s) (by nlinarith)
              _ = ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := one_mul _
          have hpt : ∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 2 2 j
                  (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
              Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) :=
            fun x => le_trans (hpt0 x) (mul_le_mul_of_nonneg_left (hgm x) (hCg_nn j))
          have hcont_grid : Continuous (fun x : M =>
              ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
            refine continuous_finset_sum _ fun n' _ => continuous_finset_sum _ fun e _ =>
              continuous_finset_prod _ fun m _ => ?_
            have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
            refine hc.congr fun x => ?_
            rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
              ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
                (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
          have hint_grid : MeasureTheory.Integrable
              (fun x : M => ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
            integrable_of_continuous_compactSpace (I := I) (M := M) g₀ hcont_grid
          have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
            2 (2 + j)
            (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
            (fun x => Cg j * ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            (hint_grid.const_mul (Cg j)) hpt
          have hgridE := hKg T₀ hball j
          have hwin : ∑ l ∈ Finset.range (j + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
              ∑ l ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (hrsub _ _ (by omega))
              (fun l _ _ => sq_nonneg _)
          calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
              ≤ ∫ x, (Cg j * ∑ n' ∈ Finset.range (j + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                    ∏ m : Fin n',
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := hkey
            _ = Cg j * ∫ x, (∑ n' ∈ Finset.range (j + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                    ∏ m : Fin n',
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
                rw [MeasureTheory.integral_const_mul]
            _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (j + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hgridE (hCg_nn j)
            _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
                refine mul_le_mul_of_nonneg_left ?_ (hCg_nn j)
                refine mul_le_mul_of_nonneg_left ?_ (hKg_nn j)
                linarith
            _ = Cg j * Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by ring
            _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
                refine mul_le_mul_of_nonneg_right ?_ h1S_nn
                exact le_add_of_nonneg_left (hKlo_nn j)
      have hslotSum : ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
          (∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
            (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
        calc (∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2)
            ≤ ∑ j ∈ Finset.range (i + 1), ((Klo j + Cg j * Kg j) *
                (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
              Finset.sum_le_sum fun j hj =>
                hslot j (by have := Finset.mem_range.mp hj; omega)
          _ = (∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
                (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
              rw [Finset.sum_mul]
      have hdev_eq :
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ =
          reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
            + reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
            - ((ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
              + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)) := by
        rw [deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₁,
          deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀,
          reindexCoeffGen_map_sub (I := I) (M := M) g₀ _ _
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA),
          reindexCoeffGen_map_sub (I := I) (M := M) g₀ _ _
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)]
        abel
      have hreiA := pje_normSq_icg_reindex_eq (I := I) (M := M) g₀
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)
        (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA) i
      have hreiB := pje_normSq_icg_reindex_eq (I := I) (M := M) g₀
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)
        (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT) i
      have hth := hCth g₁ i
      have hr := hCr g₁ i
      have htri : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ +
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ +
          2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ := by
        rw [hdev_eq, iteratedCovGrad_sub, iteratedCovGrad_add, iteratedCovGrad_add]
        have h1 := norm_sub_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)) +
            iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) +
           iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
        have h2 := norm_add_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)))
        have h3 := norm_add_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
        linarith
      have hsq : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
          3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ ^ 2 +
          3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ ^ 2 +
          12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := by
        nlinarith [htri,
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ -
            ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ -
            2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ -
            2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖)]
      calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2
          ≤ 3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ ^ 2 +
            3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ ^ 2 +
            12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := hsq
        _ = 6 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 +
            12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := by
            rw [hreiA, hreiB]; ring
        _ ≤ (6 * Cth i + 12 * Cr i) * (∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) := by
            nlinarith [hth, hr]
        _ ≤ (6 * Cth i + 12 * Cr i) * ((∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
              (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hslotSum
              (by have := hCth_nn i; have := hCr_nn i; linarith)
        _ = KdevF i * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            simp only [hKdevF_def]; ring
    have hbare : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖ ^ 2 ≤
        (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro s hs
      have hsplit1 : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ +
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by
        have hid : deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) =
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ := (sub_add_cancel _ _).symm
        calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖
            = ‖iteratedCovGrad (I := I) g₀ 4 2 i
                ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                      (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by rw [← hid]
          _ = ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                      (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
                iteratedCovGrad (I := I) g₀ 4 2 i
                  (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by
              rw [iteratedCovGrad_add]
          _ ≤ _ := norm_add_le _ _
      have hd := hdev s hs
      have hcBi : cB i = ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 := rfl
      have hcmul : cB i * 1 ≤ cB i * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1S_ge (hcB_nn i)
      nlinarith [hsplit1, hd, hcBi, hcmul,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ -
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖)]
    have hprod2_nn : (0 : ℝ) ≤ (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_nonneg (by have := hKdevF_nn i; have := hcB_nn i; linarith) h1S_nn
    let Φ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s)
    let B₂ : ℝ := Real.sqrt ((2 * KdevF i + 2 * cB i) *
      (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2))
    have hB₂_sq : B₂ ^ 2 = (2 * KdevF i + 2 * cB i) *
        (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      change Real.sqrt ((2 * KdevF i + 2 * cB i) *
        (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) ^ 2 = _
      exact Real.sq_sqrt hprod2_nn
    have hj2' : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ
        (δ := δ) (δ' := δ) := by
      simpa only [Φ] using hj2
    have hΦjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i (Φ s)‖ ^ 2 ≤ B₂ ^ 2 := by
      intro s hs
      rw [hB₂_sq]
      exact hbare s hs
    have htower := armField_pathIntegral_jetL2_perOrder_le (I := I) (M := M) g₀ 4 Φ
      hSI hSopen hj2' i (B := B₂) (Real.sqrt_nonneg _) hΦjet
    rw [hB₂_sq] at htower
    have hPeq : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) =
        pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Φ
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj2 := rfl
    have htower' : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)))‖ ^ 2 ≤
        (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      rw [hPeq]; exact htower
    have hsplit : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)))‖ ^ 2 +
        2 * cB i := by
      have h := norm_sub_le
        (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀))))
        (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀))
      rw [← iteratedCovGrad_sub] at h
      have hcBi : cB i = ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 := rfl
      nlinarith [h,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)))),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) =
                      (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)))‖ -
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖)]
    have hcmul : cB i * 1 ≤ cB i * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1S_ge (hcB_nn i)
    nlinarith [hsplit, htower', hcmul, hKdevF_nn i, hcB_nn i, h1S_nn, hS_nn]

theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  obtain ⟨K1, hK1_nn, h1⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨K2, hK2_nn, h2⟩ :=
    exists_deTurckPrincipalCometricCoeff_realize_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨fun i => 2 * K1 i + 2 * K2 i,
    fun i => by have := hK1_nn i; have := hK2_nn i; linarith,
    fun T₀ hTsymm hball i => ?_⟩
  have hsub := iteratedCovGrad_sub (I := I) g₀ (2 + 2) 2 i
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
      (tensorSectionRealizeMetric (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre T₀ hball)))
  rw [show (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball))) =
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) from rfl, hsub]
  have hA := h1 T₀ hTsymm hball i
  have hB := h2 T₀ hTsymm hball i
  set nA := ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ with hnA
  set nB := ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
      (tensorSectionRealizeMetric (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre T₀ hball)))‖ with hnB
  have hnA_nn : 0 ≤ nA := by rw [hnA]; exact norm_nonneg _
  have hnB_nn : 0 ≤ nB := by rw [hnB]; exact norm_nonneg _
  have hn : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))‖ ≤ nA + nB :=
    norm_sub_le _ _
  have hsq : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))‖ ^ 2 ≤ 2 * nA ^ 2 + 2 * nB ^ 2 := by
    have hlhs_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
        iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)))‖ := norm_nonneg _
    nlinarith [sq_nonneg (nA - nB), mul_le_mul hn hn hlhs_nn (by linarith : (0:ℝ) ≤ nA + nB)]
  refine le_trans hsq ?_
  have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by positivity
  nlinarith [hA, hB, hSig_nn, hK1_nn i, hK2_nn i]

theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSmall_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCD : ℝ, 0 ≤ εCD ∧
      (0 ≤ δ → εCD ≤ 3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball))).toSection x) ≤ εCD ^ 2) ∧
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCD, hεCD_nn, hεCD_cap, hsup⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSup_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Kc, hKc_nn, henv⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  exact ⟨εCD, hεCD_nn, hεCD_cap, Kc, hKc_nn, fun T₀ hTsymm hball =>
    ⟨hsup T₀ hTsymm hball, henv T₀ hTsymm hball⟩⟩

set_option maxHeartbeats 1000000 in
theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmCoeffAction_endpointResidual_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCr : ℝ, 0 ≤ εCr ∧
      (0 ≤ δ → εCr ≤ 19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (C₁ : SmoothCcTensor g₀ (2 + 1) 2)
          (C₂r : SmoothCcTensor g₀ (2 + 2) 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀)) -
              deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀) =
            operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                      (0 : SmoothCcTensor g₀ 0 2)
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                        (by
                          rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                              from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                            tensorHs_norm_smul]
                          simpa using hR₀)) -
                    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                    deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                      (tensorSectionRealizeMetric (I := I) g₀ T₀
                        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                        (hδ_fibre T₀ hball))) + C₂r)
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂r.toSection x) ≤
              εCr ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) 2 x (C₁.toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 1) 2 i C₁‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂r‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCr, hεCr_nn, hεCr_cap, Kc1, hKc1_nn, εar, hεar_nn, hεar_cap, Λ₁, hΛ₁_nn, harm⟩ :=
    exists_deTurckRHSArmDiff_zero_canonicalTop_curvatureRefold_coeffSup_jetEnvelope_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨K₀, hK₀fold⟩ :=
    exists_deTurckPhiMetTotal_background_curvatureFold_of_symm (I := I) (M := M) g₀ g_bg
  obtain ⟨ΛK, hΛK_nn, hΛK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 K₀
  have hεa_cap : 2 * Real.sqrt (Module.finrank ℝ E) * ((3 : ℝ) / 2 * εar) ≤
      32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 := by
    calc 2 * Real.sqrt (Module.finrank ℝ E) * ((3 : ℝ) / 2 * εar)
        = 3 * Real.sqrt (Module.finrank ℝ E) * εar := by ring
      _ ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 := hεar_cap
  refine ⟨εCr, hεCr_nn, hεCr_cap,
    fun i => 2 * Kc1 i + 2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2,
    fun i => add_nonneg (mul_nonneg (by norm_num) (hKc1_nn i)) (by positivity),
    (3 : ℝ) / 2 * εar, by linarith, hεa_cap,
    Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) + Λ₁,
    add_nonneg (Real.sqrt_nonneg _) hΛ₁_nn,
    fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₀k, C₁k, C₂r, hidArm, hC₀sup, hC₁sup, hC₂rsup, hC₀env, hC₁env, hC₂renv⟩ :=
    harm T₀ hTsymm hball
  have hsqA : Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) ^ 2 = 2 * Λ₁ ^ 2 + 2 * ΛK :=
    Real.sq_sqrt (by nlinarith [hΛ₁_nn, hΛK_nn])
  refine ⟨C₀k + K₀, C₁k, C₂r, ?_, hC₂rsup, ?_, ?_, ?_, ?_, ?_⟩
  · have h884 := deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff (I := I) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀))
    rw [sub_zero] at h884
    have hidArm' : deTurckRHSArmG0 (I := I) g₀ g_bg T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
        deTurckRHSArmG0 (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀k (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
          operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁k (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
          operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
            (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)))
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) +
          operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂r (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) :=
      hidArm
    have hfold := hK₀fold T₀ hTsymm
    have hfold' : operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 K₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) := by
      rw [← appCc_sub_left]
      exact hfold
    have hlift : rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀ =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
          (I := I) (M := M) g₀ T₀ x v
    have hArm : deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) T₀ =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) := rfl
    have hPCC : deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)) -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀ := rfl
    rw [h884, hlift, hArm, hidArm']
    rw [appCc_add_left (I := I) (M := M) g₀ (2 + 0) 2 C₀k K₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)]
    rw [appCc_add_left (I := I) (M := M) g₀ (2 + 2) 2 _ C₂r
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [show (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))) =
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) from rfl]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)))
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [hPCC]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
        (I := I) (M := M) g₀ g₀)
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [← hfold']
    abel
  · intro x
    have hsec : ((C₀k + K₀).toSection x) = C₀k.toSection x + K₀.toSection x := by
      rw [SmoothCcTensor.toSection_add]; rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (2 + 0) 2 x _ _) ?_
    have h1 := hC₀sup x
    have h2 := hΛK x
    nlinarith [Real.sqrt_nonneg (2 * Λ₁ ^ 2 + 2 * ΛK), hΛ₁_nn, hsqA]
  · intro x
    have h1 := hC₁sup x
    have hle : Λ₁ ≤ Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) + Λ₁ :=
      le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have := pow_le_pow_left₀ hΛ₁_nn hle 2
    linarith
  · intro i
    have hdist := iteratedCovGrad_add (I := I) g₀ (2 + 0) 2 i C₀k K₀
    rw [hdist]
    have hn := norm_add_le (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k)
      (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀)
    have hAB : 0 ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k +
        iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ := norm_nonneg _
    have htri : ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k +
          iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := by
      nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k‖ -
        ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖),
        mul_le_mul hn hn hAB (by positivity), norm_nonneg
          (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k), norm_nonneg
          (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀)]
    refine le_trans htri ?_
    have hD := hC₀env i
    have hSig_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hKW : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 *
        (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
      mul_nonneg (sq_nonneg _) hSig_nn
    have hεX : (0 : ℝ) ≤ εar ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith [hD, hSig_nn, sq_nonneg ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖,
      hKc1_nn i, hKW, hεX]
  · intro i
    refine le_trans (hC₁env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have h1 := hKc1_nn i
    have h2 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := sq_nonneg _
    linarith
  · intro i
    refine le_trans (hC₂renv i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have h1 := hKc1_nn i
    have h2 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := sq_nonneg _
    linarith

set_option maxHeartbeats 1000000 in
theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmCoeffAction_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (C₁ : SmoothCcTensor g₀ (2 + 1) 2)
          (C₂ : SmoothCcTensor g₀ (2 + 2) 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀)) -
              deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀) =
            operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤
              εC ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) 2 x (C₁.toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 1) 2 i C₁‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCD, hεCD_nn, hεCD_cap, KcD, hKcD_nn, hK2⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSmall_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨εCr, hεCr_nn, hεCr_cap, Kc1, hKc1_nn, εa, hεa_nn, hεa_cap, Λ1, hΛ1_nn, hK1⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmCoeffAction_endpointResidual_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  have hn1 : 1 ≤ Module.finrank ℝ E :=
    Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hC1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst hn1
  refine ⟨Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2), Real.sqrt_nonneg _,
    fun hδ_nn => ?_, fun hδ_nn => ?_,
    fun i => 3 * Kc1 i + 2 * KcD i,
    fun i => by have := hKc1_nn i; have := hKcD_nn i; linarith,
    εa, hεa_nn, hεa_cap,
    Λ1, hΛ1_nn, fun T₀ hTsymm hball => ?_⟩
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    set C : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) with hC_def
    set κ : ℝ := δ / (1 - δ) with hκ_def
    have hd := hεCD_cap hδ_nn
    have hr := hεCr_cap hδ_nn
    have hsq : (2 * εCD ^ 2 + 2 * εCr ^ 2) ≤ (32 * C ^ 2 * κ) ^ 2 := by
      have hεCD_sq : εCD ^ 2 ≤ (3 * C * κ) ^ 2 := by nlinarith
      have hεCr_sq : εCr ^ 2 ≤ (19 * C * κ) ^ 2 := by nlinarith
      have hC2 : (1 : ℝ) ≤ C ^ 2 := by nlinarith
      nlinarith [sq_nonneg (C * κ), sq_nonneg κ]
    calc Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2)
        ≤ Real.sqrt ((32 * C ^ 2 * κ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 32 * C ^ 2 * κ := Real.sqrt_sq (by positivity)
      _ = 32 * C ^ 2 * (δ / (1 - δ)) := by rw [hκ_def]
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hC_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
      deTurckArmFibreConst_nonneg _
    have hd := hεCD_cap hδ_nn
    have hr := hεCr_cap hδ_nn
    have h28_nn : (0 : ℝ) ≤
        28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) := by positivity
    have hsq : 2 * εCD ^ 2 + 2 * εCr ^ 2 ≤
        (28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ^ 2 := by
      nlinarith [hd, hr, hεCD_nn, hεCr_nn, mul_nonneg hC_nn hκ_nn]
    calc Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2)
        ≤ Real.sqrt ((28 * deTurckArmFibreConst (Module.finrank ℝ E) *
            (δ / (1 - δ))) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
          Real.sqrt_sq h28_nn
  obtain ⟨hDsup, hDenv⟩ := hK2 T₀ hTsymm hball
  obtain ⟨C₀, C₁, C₂r, hid, hC₂r_sup, hC₀sup, hC₁sup, hC₀env, hC₁env, hC₂r_env⟩ :=
    hK1 T₀ hTsymm hball
  have hεC_sq : Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2) ^ 2 =
      2 * εCD ^ 2 + 2 * εCr ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨C₀, C₁,
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball))) + C₂r,
    hid, ?_, hC₀sup, hC₁sup, ?_, ?_, ?_⟩
  · intro x
    rw [hεC_sq]
    have hsec : ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))) + C₂r).toSection x =
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))).toSection x + C₂r.toSection x := by
      rw [SmoothCcTensor.toSection_add]; rfl
    rw [hsec]
    refine le_trans
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (2 + 2) 2 x _ _) ?_
    have h1 := hDsup x
    have h2 := hC₂r_sup x
    linarith
  · intro i
    refine le_trans (hC₀env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    have hmono : Kc1 i * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        (3 * Kc1 i + 2 * KcD i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
      refine mul_le_mul_of_nonneg_right ?_ hSig_nn
      have := hKc1_nn i; have := hKcD_nn i
      linarith
    linarith
  · intro i
    refine le_trans (hC₁env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have := hKc1_nn i; have := hKcD_nn i
    linarith
  · intro i
    have hdist := iteratedCovGrad_add (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))
      C₂r
    rw [hdist]
    have htri : ∀ A B : SmoothCcTensor g₀ (2 + 2) (2 + i),
        ‖A + B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
      intro A B
      have hn := norm_add_le A B
      have hA := norm_nonneg A
      have hB := norm_nonneg B
      have hAB : 0 ≤ ‖A + B‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖A‖ - ‖B‖), mul_le_mul hn hn hAB (by linarith)]
    refine le_trans (htri _ _) ?_
    have hD := hDenv i
    have hr := hC₂r_env i
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    have hKc1i := hKc1_nn i
    nlinarith [hD, hr, hSig_nn]

open DifferentialGeometry.Integral.Measure in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_comp_l2_sq_eq_rs
    (g₀ : SmoothRiemannianMetric I M) (r s m l : ℕ) (W : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ r (s + m) l (iteratedCovGrad (I := I) g₀ r s m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ r (s + m) l
        (iteratedCovGrad (I := I) g₀ r s m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r ((s + m) + l) x
        ((iteratedCovGrad (I := I) g₀ r (s + m) l
          (iteratedCovGrad (I := I) g₀ r s m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      ((s + m) + l)
      (iteratedCovGrad (I := I) g₀ r (s + m) l (iteratedCovGrad (I := I) g₀ r s m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ r s (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ r s (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      (s + (m + l)) (iteratedCovGrad (I := I) g₀ r s (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ r s m l W x
  simpa only [Nat.add_assoc] using hrw

theorem exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ, q + (Module.finrank ℝ E / 2 + 3) ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  have hB2 : ∀ m i : ℕ, ∃ Csh : ℝ, 0 ≤ Csh ∧
      ∀ (T : SmoothCcTensor g₀ (2 + m) (2 + i)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x (T.toSection x) ≤
          Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j T‖ ^ 2 :=
    fun m i =>
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ (2 + m) (2 + i)
  choose Csh2 hCsh2_nn hCsh2 using hB2
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  set Lam : ℕ → ℕ → ℝ := fun m i => (Csh2 m i) ^ 2 *
    ((∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j)) * (1 + B ^ 2))
    with hLam_def
  have hLam_nn : ∀ m i, 0 ≤ Lam m i := by
    intro m i
    rw [hLam_def]
    have h1 : 0 ≤ ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j) :=
      Finset.sum_nonneg (fun j _ => hKc_nn _)
    have h2 : (0 : ℝ) ≤ 1 + B ^ 2 := by positivity
    exact mul_nonneg (sq_nonneg _) (mul_nonneg h1 h2)
  set D : ℕ → ℕ → ℝ := fun m q => Real.sqrt (diagonalGridGrowthFactor (E := E) q *
    ∑ i ∈ Finset.range (q + 1), Lam m i) * ((q : ℝ) + 1) with hD_def
  have hD_nn : ∀ m q, 0 ≤ D m q := by
    intro m q
    rw [hD_def]
    exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  refine ⟨fun q => D 0 q + D 1 q, fun q => add_nonneg (hD_nn 0 q) (hD_nn 1 q), ?_⟩
  intro m hm C T₀ hball henv q hband
  set S : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set W : SmoothCcTensor g₀ 0 (2 + m) := iteratedCovGrad (I := I) g₀ 0 2 m T₀ with hW_def
  have hball_sq : (∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) ≤ B ^ 2 := by
    have hsq_le : ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        (∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖) ^ 2 := by
      have hnn : ∀ i ∈ Finset.range (a + 2 + 1),
          (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := fun i _ => norm_nonneg _
      have hstep : ∀ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ *
              (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) := by
        intro i hi
        rw [sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hnn hi) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hjets : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        C2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ := hC2 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hcast] at hjets
    have hjets2 : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        B := by
      rw [hB_def]
      exact le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact pow_le_pow_left₀ hsum_nn hjets2 2
  have hCoeff : ∀ i : ℕ, i ≤ q → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
        ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) ≤ Lam m i := by
    intro i hi x
    refine le_trans (hCsh2 m i (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C) x) ?_
    rw [hLam_def]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hterm : ∀ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j
          (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C)‖ ^ 2 ≤ Kc (i + j) * (1 + B ^ 2) := by
      intro j hj
      rw [iteratedCovGrad_comp_l2_sq_eq_rs (I := I) g₀ (2 + m) 2 i j C]
      refine le_trans (henv (i + j)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn _)
      have hjw : j < Module.finrank ℝ E / 2 + 2 := Finset.mem_range.mp hj
      have hwin : ∑ l ∈ Finset.range (i + j + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show i + j + 2 ≤ a + 2 + 1 by omega))
          (fun l _ _ => sq_nonneg _)
      linarith [hball_sq]
    calc ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j
            (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C)‖ ^ 2
        ≤ ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j) * (1 + B ^ 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j)) * (1 + B ^ 2) := by
          rw [← Finset.sum_mul]
  set Cpt : ℝ := Real.sqrt (diagonalGridGrowthFactor (E := E) q *
    ∑ i ∈ Finset.range (q + 1), Lam m i) with hCpt_def
  have hGq_nn : 0 ≤ diagonalGridGrowthFactor (E := E) q := appCcGdiag_nonneg (E := E) q
  have hSumLam_nn : 0 ≤ ∑ i ∈ Finset.range (q + 1), Lam m i :=
    Finset.sum_nonneg (fun i _ => hLam_nn m i)
  have hCpt_nn : 0 ≤ Cpt := Real.sqrt_nonneg _
  have hCpt_sq : Cpt ^ 2 = diagonalGridGrowthFactor (E := E) q * ∑ i ∈ Finset.range (q + 1), Lam m i := by
    rw [hCpt_def]
    exact Real.sq_sqrt (mul_nonneg hGq_nn hSumLam_nn)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)).toSection x) ≤
      Cpt ^ 2 * ∑ l ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) := by
    intro x
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le (I := I) (M := M) g₀ (2 + m) 2 C W q x) ?_
    rw [hCpt_sq]
    have hb_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
      Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
    have hstep : ∀ i ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
          (∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x)) ≤
        Lam m i * ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) := by
      intro i hi
      have hi' : i ≤ q := by
        have := Finset.mem_range.mp hi
        omega
      have hinner : (∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x)) ≤
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show q + 1 - i ≤ q + 1 by omega))
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
      have hinner_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
        Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
      exact mul_le_mul (hCoeff i hi' x) hinner hinner_nn (hLam_nn m i)
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hGq_nn) ?_
    rw [← Finset.sum_mul, ← mul_assoc]
  have hPTLP := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (q + 1) (fun l => (2 + m) + l)
    (fun l => iteratedCovGrad (I := I) g₀ 0 (2 + m) l W)
    (iteratedCovGrad (I := I) g₀ 0 2 q (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W))
    Cpt hCpt_nn hpt
  have hWl : ∀ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ≤ Real.sqrt S := by
    intro l hl
    have hl' : l ≤ q := by
      have := Finset.mem_range.mp hl
      omega
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2 := by
      rw [hW_def]
      exact iteratedCovGrad_comp_l2_sq_eq_rs (I := I) g₀ 0 2 m l T₀
    have hin : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2 ≤ S := by
      rw [hS_def]
      exact Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2)
        (fun i _ => sq_nonneg _)
        (Finset.mem_range.mpr (show m + l < q + 1 + 1 by omega))
    calc ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖
        = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2) := by rw [hsq]
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hin
  have hsumW : ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ≤
      ((q : ℝ) + 1) * Real.sqrt S := by
    have := Finset.sum_le_card_nsmul (Finset.range (q + 1))
      (fun l => ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖) (Real.sqrt S) hWl
    rw [Finset.card_range, nsmul_eq_mul] at this
    calc ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖
        ≤ ((q + 1 : ℕ) : ℝ) * Real.sqrt S := this
      _ = ((q : ℝ) + 1) * Real.sqrt S := by push_cast; ring
  refine le_trans hPTLP ?_
  have hfin : Cpt * (∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖) ≤ Cpt * (((q : ℝ) + 1) * Real.sqrt S) :=
    mul_le_mul_of_nonneg_left hsumW hCpt_nn
  refine le_trans hfin ?_
  have hDm : Cpt * (((q : ℝ) + 1) * Real.sqrt S) = D m q * Real.sqrt S := by
    rw [hD_def, hCpt_def]
    ring
  rw [hDm]
  have hDle : D m q ≤ D 0 q + D 1 q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h | h
    · rw [h]; have := hD_nn 1 q; linarith
    · rw [h]; have := hD_nn 0 q; linarith
  exact mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)

open DifferentialGeometry.Integral.Measure in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_comp_l2_sq_eq
    (g₀ : SmoothRiemannianMetric I M) (m l : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
        (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
        ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
      (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l W x
  simpa only [Nat.add_assoc] using hrw

open DifferentialGeometry.Integral.Measure in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_comp_jetSum_le
    (g₀ : SmoothRiemannianMetric I M) (p m : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    (∑ l ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (p + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  rw [show (∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) =
      ∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 from
    Finset.sum_congr rfl (fun l _ => iteratedCovGrad_comp_l2_sq_eq (I := I) g₀ m l W)]
  set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hf_def
  have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have himg : (Finset.range (p + 1)).image (fun l => m + l) ⊆ Finset.range (p + m + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rw [Finset.mem_range] at hl ⊢
    omega
  have hinj : ∀ l₁ ∈ Finset.range (p + 1), ∀ l₂ ∈ Finset.range (p + 1),
      m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
  calc (∑ l ∈ Finset.range (p + 1), f (m + l))
      = ∑ i ∈ (Finset.range (p + 1)).image (fun l => m + l), f i :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.range (p + m + 1), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)

theorem exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (C.toSection x) ≤ Λ ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ, a ≤ q + (Module.finrank ℝ E / 2 + 3) →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  have hE : ∀ m q : ℕ, ∃ CE : ℝ, 0 ≤ CE ∧
      ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤
          ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤
          ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          CE * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) :=
    fun m q => ccTensorContract_topOrder_l2_twoArm_mixed_le (I := I) (M := M) g₀ (2 + m) 2 q
  choose CE hCE_nn hCE using hE
  have hB : ∀ m : ℕ, ∃ Csh : ℝ, 0 ≤ Csh ∧
      ∀ (T : SmoothCcTensor g₀ 0 (2 + m)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (T.toSection x) ≤
          Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) j T‖ ^ 2 :=
    fun m =>
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ 0 (2 + m)
  choose Csh hCsh_nn hCsh using hB
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  set D : ℕ → ℕ → ℝ := fun m q => Real.sqrt (CE m q *
    ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) + Λ ^ 2)) with hD_def
  have hD_nn : ∀ m q, 0 ≤ D m q := fun m q => Real.sqrt_nonneg _
  refine ⟨fun q => D 0 q + D 1 q, fun q => add_nonneg (hD_nn 0 q) (hD_nn 1 q), ?_⟩
  intro m hm C T₀ hball hsup henv q hband
  set S : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set W : SmoothCcTensor g₀ 0 (2 + m) := iteratedCovGrad (I := I) g₀ 0 2 m T₀ with hW_def
  set SW : ℝ := ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) j W‖ ^ 2 with hSW_def
  have hSW_nn : 0 ≤ SW := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  set ΛW : ℝ := Csh m * Real.sqrt SW with hΛW_def
  have hΛW_nn : 0 ≤ ΛW := mul_nonneg (hCsh_nn m) (Real.sqrt_nonneg _)
  have hWsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      (W.toSection x) ≤ ΛW ^ 2 := by
    intro x
    have h := hCsh m W x
    rw [hΛW_def, mul_pow, Real.sq_sqrt hSW_nn, hSW_def]
    exact h
  have hMain := hCE m q C W Λ ΛW hΛ_nn hΛW_nn hsup hWsup
  have hSW_case : SW ≤ ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 1 + m + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
    have h := iteratedCovGrad_comp_jetSum_le (I := I) g₀ (Module.finrank ℝ E / 2 + 1) m T₀
    rw [hSW_def, hW_def]
    exact h
  have hSW_le_S : SW ≤ S := by
    refine le_trans hSW_case ?_
    rw [hS_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (hrsub _ _ (show Module.finrank ℝ E / 2 + 1 + m + 1 ≤ q + 1 + 1 by omega))
      (fun i _ _ => sq_nonneg _)
  have hSW_le_B : SW ≤ B ^ 2 := by
    refine le_trans hSW_case ?_
    have hsub : ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 1 + m + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (hrsub _ _ (show Module.finrank ℝ E / 2 + 1 + m + 1 ≤ a + 2 + 1 by omega))
        (fun i _ _ => sq_nonneg _)
    refine le_trans hsub ?_
    have hsq_le : ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        (∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖) ^ 2 := by
      have hnn : ∀ i ∈ Finset.range (a + 2 + 1),
          (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := fun i _ => norm_nonneg _
      have hstep : ∀ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ *
              (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) := by
        intro i hi
        rw [sq]
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum hnn hi) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hjets : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        C2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ := hC2 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hcast] at hjets
    have hjets2 : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        B := by
      rw [hB_def]
      exact le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact pow_le_pow_left₀ hsum_nn hjets2 2
  have hSigC : ∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
      (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + S) := by
    have hstep : ∀ i ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤ Kc i * (1 + S) := by
      intro i hi
      rw [Finset.mem_range] at hi
      refine le_trans (henv i) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn i)
      have hwin : ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤
          S := by
        rw [hS_def]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show i + 2 ≤ q + 1 + 1 by omega))
          (fun j _ _ => sq_nonneg _)
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
  have hSigW : ∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2 ≤ S := by
    have := iteratedCovGrad_comp_jetSum_le (I := I) g₀ q m T₀
    rw [← hW_def] at this
    refine le_trans this ?_
    rw [hS_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (hrsub _ _ (show q + m + 1 ≤ q + 1 + 1 by omega))
      (fun i _ _ => sq_nonneg _)
  have hcore : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2 ≤ (D m q) ^ 2 * S := by
    have hΛW_sq : ΛW ^ 2 = (Csh m) ^ 2 * SW := by
      rw [hΛW_def, mul_pow, Real.sq_sqrt hSW_nn]
    have h1 : ΛW ^ 2 * (∑ i ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2) ≤
        (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) := by
      rw [hΛW_sq]
      have hKcS_nn : 0 ≤ (∑ i ∈ Finset.range (q + 1), Kc i) :=
        Finset.sum_nonneg (fun i _ => hKc_nn i)
      calc (Csh m) ^ 2 * SW * (∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2)
          ≤ (Csh m) ^ 2 * SW * ((∑ i ∈ Finset.range (q + 1), Kc i) * (1 + S)) := by
            refine mul_le_mul_of_nonneg_left hSigC ?_
            positivity
        _ = (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) := by ring
    have h2 : SW + SW * S ≤ (1 + B ^ 2) * S := by
      have ha' : SW * S ≤ B ^ 2 * S := mul_le_mul_of_nonneg_right hSW_le_B hS_nn
      have hb' : SW ≤ S := hSW_le_S
      have : (1 + B ^ 2) * S = S + B ^ 2 * S := by ring
      linarith
    have h3 : (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) ≤
        (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * ((1 + B ^ 2) * S)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine mul_le_mul_of_nonneg_left h2 ?_
      exact Finset.sum_nonneg (fun i _ => hKc_nn i)
    have h4 : Λ ^ 2 * (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) ≤ Λ ^ 2 * S :=
      mul_le_mul_of_nonneg_left hSigW (sq_nonneg _)
    have hD_sq : (D m q) ^ 2 = CE m q *
        ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) + Λ ^ 2) := by
      rw [hD_def]
      refine Real.sq_sqrt ?_
      have hKcS_nn : 0 ≤ ∑ i ∈ Finset.range (q + 1), Kc i :=
        Finset.sum_nonneg (fun i _ => hKc_nn i)
      have h6 : 0 ≤ (Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) := by
        refine mul_nonneg (mul_nonneg (sq_nonneg _) hKcS_nn) ?_
        have := sq_nonneg B
        linarith
      exact mul_nonneg (hCE_nn m q) (by linarith [sq_nonneg Λ])
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2
        ≤ CE m q * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2
            + Λ ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) := hMain
      _ ≤ CE m q * ((Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * ((1 + B ^ 2) * S))
            + Λ ^ 2 * S) := by
          refine mul_le_mul_of_nonneg_left ?_ (hCE_nn m q)
          have := le_trans h1 h3
          linarith
      _ = (CE m q * ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2)
            + Λ ^ 2)) * S := by ring
      _ = (D m q) ^ 2 * S := by rw [hD_sq]
  have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ≤ D m q * Real.sqrt S := by
    have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
          (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1]
    refine le_trans (Real.sqrt_le_sqrt hcore) ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hD_nn m q)]
  refine le_trans hfinal ?_
  have hDle : D m q ≤ D 0 q + D 1 q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h | h
    · rw [h]; have := hD_nn 1 q; linarith
    · rw [h]; have := hD_nn 0 q; linarith
  exact mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)

theorem exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (C.toSection x) ≤ Λ ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (operatorFieldApply (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  obtain ⟨CmA, hCmA_nn, hA⟩ :=
    exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn
  obtain ⟨CmB, hCmB_nn, hB⟩ :=
    exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn Λ hΛ_nn
  refine ⟨fun q => CmA q + CmB q,
    fun q => add_nonneg (hCmA_nn q) (hCmB_nn q), ?_⟩
  intro m hm C T₀ hball hsup henv q
  have hsqrt_nn : 0 ≤ Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := Real.sqrt_nonneg _
  rcases le_total (q + (Module.finrank ℝ E / 2 + 3)) a with hband | hband
  · refine le_trans (hA m hm C T₀ hball henv q hband) ?_
    have := mul_le_mul_of_nonneg_right
      (show CmA q ≤ CmA q + CmB q by have := hCmB_nn q; linarith) hsqrt_nn
    linarith
  · refine le_trans (hB m hm C T₀ hball hsup henv q hband) ?_
    have := mul_le_mul_of_nonneg_right
      (show CmB q ≤ CmA q + CmB q by have := hCmA_nn q; linarith) hsqrt_nn
    linarith

set_option maxHeartbeats 1000000 in

theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_iteratedCovGrad_jet_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λa : ℝ, 0 ≤ Λa ∧
    ∃ Clow : ℕ → ℝ, (∀ q, 0 ≤ Clow q) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (C₀ : SmoothCcTensor g₀ (2 + 0) 2),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λa ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          ∀ q : ℕ,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
                (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
                  deTurckSmoothRemainder (I := I) g₀ g_bg
                    (0 : SmoothCcTensor g₀ 0 2)
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                      (by
                        rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                            from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                          tensorHs_norm_smul]
                        simpa using hR₀)) -
                  deTurckPrincipalCometricArm (I := I) (M := M) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T₀
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre T₀ hball)) T₀ -
                  operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
                  operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                    (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
              Clow q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λ, hΛ_nn, hL1⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmCoeffAction_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cm, hCm_nn, hM2⟩ :=
    exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn Λ hΛ_nn
  refine ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λ, hΛ_nn,
    Cm, hCm_nn, fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₀, C₁, C₂, hid, hC₂sup, hC₀sup, hC₁sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hL1 T₀ hTsymm hball
  refine ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, fun q => ?_⟩
  have hsplit :
      (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
          deTurckSmoothRemainder (I := I) g₀ g_bg
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)) T₀ -
          operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
          operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
            (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)) =
        operatorFieldApply (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) := by
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add, hid]
    abel
  rw [hsplit]
  exact hM2 1 (by omega) C₁ T₀ hball hC₁sup hC₁jet q

set_option maxHeartbeats 1000000 in

theorem exists_smoothCcToTensorHs_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λa : ℝ, 0 ≤ Λa ∧
    ∃ Ctame : ℕ → ℝ, (∀ k, 0 ≤ Ctame k) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (C₀ : SmoothCcTensor g₀ (2 + 0) 2),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λa ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          ∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
                  deTurckSmoothRemainder (I := I) g₀ g_bg
                    (0 : SmoothCcTensor g₀ 0 2)
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                      (by
                        rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                            from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                          tensorHs_norm_smul]
                        simpa using hR₀)) -
                  deTurckPrincipalCometricArm (I := I) (M := M) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T₀
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre T₀ hball)) T₀ -
                  operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
                  operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                    (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
              Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Clow, hClow_nn, hjet⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_iteratedCovGrad_jet_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Ctame, hCtame_nn, hCtame⟩ :=
    exists_smoothCcToTensorHs_real_le_of_iteratedCovGrad_jet_window
      (I := I) (M := M) g₀ a (by omega) Clow hClow_nn
  refine ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Ctame, hCtame_nn, fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, hwin⟩ := hjet T₀ hTsymm hball
  exact ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, fun k => hCtame k _ T₀ hwin⟩

set_option maxHeartbeats 1000000 in
theorem exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le_zero
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (_hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (_hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℝ, 0 ≤ Cop ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
              (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * εC *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
            Cop * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
  classical
  obtain ⟨Ccross, hCcross_nn, hcross⟩ := exists_Ccross_for_secondCovGrad (I := I) (M := M) g₀
  obtain ⟨C21, hC21_nn, hC21⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ 1
  refine ⟨εC * Real.sqrt Ccross * (2 * C21),
    mul_nonneg (mul_nonneg hεC_nn (Real.sqrt_nonneg _)) (by linarith), ?_⟩
  intro C₂ T₀ hball hsup hjets
  set W₂ : SmoothCcTensor g₀ 0 (2 + 2) := iteratedCovGrad (I := I) g₀ 0 2 2 T₀ with hW₂_def
  set P : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ with hP_def
  have hLHS_eq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) P‖ = ‖P‖ := by
    rw [smoothCcToTensorHs_zero_norm_eq (I := I) (M := M) g₀ P, SmoothCcTensor.norm_toL2]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
        εC ^ 2 * ∑ i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x (W₂.toSection x) := by
    intro x
    have hgrid := riemannianFiberNormSq_iteratedCovGrad_comp_diagonalProductGrid_le
      (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ 0 x
    rw [show Finset.range (0 + 1) = Finset.range 1 from rfl, Finset.sum_range_one] at hgrid
    rw [show Finset.range (0 + 1 - 0) = Finset.range 1 from rfl,
      Finset.sum_range_one] at hgrid
    rw [show diagonalGridGrowthFactor (E := E) 0 = 1 by simp [diagonalGridGrowthFactor], one_mul] at hgrid
    rw [Finset.sum_range_one]
    have hW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        (W₂.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _
    refine le_trans hgrid ?_
    exact mul_le_mul_of_nonneg_right (hsup x) hW_nn
  have hprod : ‖P‖ ≤ εC * ‖W₂‖ := by
    have hPTLP := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
      1 (fun _ => 2 + 2) (fun _ => W₂) P εC hεC_nn hpt
    rw [Finset.sum_range_one] at hPTLP
    exact hPTLP
  clear_value W₂ P
  have hweitz := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g₀ 2 T₀
  have hcrossT := hcross T₀
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 (2 + 1 + 1)
    (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toFun with hnHess_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 (2 + 1)
    (covGrad (I := I) (M := M) g₀ 0 2 T₀).toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 2
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 2 T₀.toFun with hnT_def
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + 1 + 1) _
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + 1) _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 2 _
  clear_value nHess nGrad nLap nT
  have hW₂_norm : ‖W₂‖ = nHess := by
    have hW2eq : W₂ = covGrad (I := I) (M := M) g₀ 0 (2 + 1)
        (covGrad (I := I) (M := M) g₀ 0 2 T₀) := by
      rw [hW₂_def]
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 1 T₀,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 0 T₀,
        iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀]
    rw [hW2eq, SmoothCcTensor.norm_def]
    exact hnHess_def.symm
  have hstep1 : nHess ^ 2 ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nT * nGrad) := by
    linarith [hweitz, hcrossT]
  have hstep2 : nHess ^ 2 ≤ (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 := by
    have hsq : Real.sqrt Ccross ^ 2 = Ccross := Real.sq_sqrt hCcross_nn
    have hexp : (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 =
        nLap ^ 2 + 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) +
          Ccross * (nGrad + nT) ^ 2 := by
      rw [show (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 =
        nLap ^ 2 + 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) +
          Real.sqrt Ccross ^ 2 * (nGrad + nT) ^ 2 by ring, hsq]
    rw [hexp]
    have hc1 : 0 ≤ 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) := by positivity
    have hc2 : nGrad ^ 2 + nT * nGrad ≤ (nGrad + nT) ^ 2 := by nlinarith
    have hc3 : Ccross * (nGrad ^ 2 + nT * nGrad) ≤ Ccross * (nGrad + nT) ^ 2 :=
      mul_le_mul_of_nonneg_left hc2 hCcross_nn
    linarith [hstep1]
  have hHess_le : nHess ≤ nLap + Real.sqrt Ccross * (nGrad + nT) := by
    have hrhs_nn : 0 ≤ nLap + Real.sqrt Ccross * (nGrad + nT) := by positivity
    calc nHess = Real.sqrt (nHess ^ 2) := (Real.sqrt_sq hnHess_nn).symm
      _ ≤ Real.sqrt ((nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2) :=
          Real.sqrt_le_sqrt hstep2
      _ = nLap + Real.sqrt Ccross * (nGrad + nT) := Real.sqrt_sq hrhs_nn
  have hLap_le : nLap ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by
    have h1 : nLap = ‖rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀‖ := by
      rw [hnLap_def, SmoothCcTensor.norm_def]
    have h2 : ‖rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ := by
      rw [smoothCcToTensorHs_zero_norm_eq, SmoothCcTensor.norm_toL2]
    have h3 := smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀ (0 : ℝ) T₀
    have h4 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by norm_num) T₀
    rw [h1, h2]
    rw [h4] at h3
    exact h3
  have hjets1 : ∀ j : ℕ, j < 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    intro j hj
    have hsum := hC21 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by norm_num) T₀
    rw [hcast] at hsum
    refine le_trans ?_ hsum
    exact Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hj)
  have hnT_le : nT ≤ C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    have h0 : nT = ‖iteratedCovGrad (I := I) g₀ 0 2 0 T₀‖ := by
      rw [hnT_def, iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀,
        SmoothCcTensor.norm_def]
    rw [h0]
    exact hjets1 0 (by norm_num)
  have hnGrad_le : nGrad ≤ C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    have h1 : iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
        covGrad (I := I) (M := M) g₀ 0 2 T₀ := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 0 T₀,
        iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀]
    have h0 : nGrad = ‖iteratedCovGrad (I := I) g₀ 0 2 1 T₀‖ := by
      rw [hnGrad_def, h1, SmoothCcTensor.norm_def]
    rw [h0]
    exact hjets1 1 (by norm_num)
  have hfibre1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hHs2_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := norm_nonneg _
  have hHs1_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := norm_nonneg _
  have hchain : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) P‖ ≤
      εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
        Real.sqrt Ccross * (2 * C21 *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖)) := by
    rw [hLHS_eq]
    refine le_trans hprod ?_
    rw [hW₂_norm]
    refine le_trans (mul_le_mul_of_nonneg_left hHess_le hεC_nn) ?_
    refine mul_le_mul_of_nonneg_left ?_ hεC_nn
    have hGT : nGrad + nT ≤ 2 * C21 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
      linarith [hnGrad_le, hnT_le]
    have := mul_le_mul_of_nonneg_left hGT (Real.sqrt_nonneg Ccross)
    linarith [hLap_le]
  refine le_trans hchain ?_
  have hexpand : εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
      Real.sqrt Ccross * (2 * C21 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖)) =
      εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
        εC * Real.sqrt Ccross * (2 * C21) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by ring
  rw [hexpand]
  have h1 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * εC *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by
    have h2 : (1 : ℝ) * εC ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC :=
      mul_le_mul_of_nonneg_right hfibre1 hεC_nn
    have h3 := mul_le_mul_of_nonneg_right h2 hHs2_nn
    calc εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖
        = 1 * εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by ring
      _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := h3
  linarith [h1]

theorem exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le_succ
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            deTurckArmFibreConst (Module.finrank ℝ E) * εC *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ := by
  classical
  obtain ⟨Clower, hClower_nn, hfam⟩ :=
    exists_coeffContraction_secondCovGrad_smallFibreCoeff_Hs_family_le (I := I) (M := M) g₀ a
      (by omega) hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨fun m => Clower (m + 1), fun m => hClower_nn (m + 1), ?_⟩
  intro C₂ T₀ hball hsup hjets m
  have hbase := hfam C₂ T₀ hball hsup hjets (m + 1) T₀
    ⟨0, (oneMinusConnLapSmoothIter_zero (I := I) (M := M) (T := T₀)).symm⟩
  have hΔ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
    have h1 := smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀
      (((m + 1 : ℕ) : ℝ)) T₀
    have h2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((m + 1 : ℕ) : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact h1
  have hcastL : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  have hcastQ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
  rw [hcastL, hcastQ] at hbase
  have hfibre1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hH3_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
    norm_nonneg _
  have htop : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * εC *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
    have hstep1 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
      mul_le_mul_of_nonneg_left hΔ hεC_nn
    have hstep2 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ ≤
        deTurckArmFibreConst (Module.finrank ℝ E) * εC *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
      have h2 : (1 : ℝ) * εC ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC :=
        mul_le_mul_of_nonneg_right hfibre1 hεC_nn
      have h3 := mul_le_mul_of_nonneg_right h2 hH3_nn
      calc εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖
          = 1 * εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by ring
        _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := h3
    exact le_trans hstep1 hstep2
  linarith [hbase, htop]

theorem exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            deTurckArmFibreConst (Module.finrank ℝ E) * εC *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop0, hCop0_nn, h0⟩ :=
    exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le_zero
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  obtain ⟨Cops, hCops_nn, hs⟩ :=
    exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le_succ
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨fun m => match m with
    | 0 => Cop0
    | (k + 1) => Cops k, fun m => ?_, fun C₂ T₀ hball hsup hjets m => ?_⟩
  · match m with
    | 0 => exact hCop0_nn
    | (k + 1) => exact hCops_nn k
  · match m with
    | 0 =>
      have hb := h0 C₂ T₀ hball hsup hjets
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))
      have hnorm2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 2 = (2 : ℝ) by norm_num) T₀
      have hnorm1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 1 = (1 : ℝ) by norm_num) T₀
      rw [hnormL, hnorm2, hnorm1]
      exact hb
    | (k + 1) =>
      have hb := hs C₂ T₀ hball hsup hjets k
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring)
        (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))
      have hnorm2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 by push_cast; ring) T₀
      have hnorm1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by push_cast; ring) T₀
      rw [hnormL, hnorm2, hnorm1]
      exact hb

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma gFibreOpBound_delta_nonneg [Nonempty M] (g₀ : SmoothRiemannianMetric I M)
    {δ : ℝ}
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hfb : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) : 0 ≤ δ := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  obtain ⟨n, e, hn, horth, hpars, hexpand, hrfns⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  have hn_pos : 0 < n := by
    rw [hn]
    have : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
    rw [this]
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  set i0 : Fin n := ⟨0, hn_pos⟩ with hi0_def
  have hb := hfb x (e i0) (e i0)
  have hgi : g₀.inner x (e i0) (e i0) = 1 := by
    rw [horth i0 i0, if_pos rfl]
  rw [hgi, Real.sqrt_one, mul_one, mul_one] at hb
  exact le_trans (abs_nonneg _) hb


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_le_of_ccTensorBilinSymm_gFibreOpBound [Nonempty M]
    (g₀ : SmoothRiemannianMetric I M) {δ : ℝ}
    (T₀ : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v)
    (hfibre : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
      (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
  classical
  intro x
  have hop : ∀ v w : TangentSpace I x,
      |smoothCcTensorBilinForm (I := I) g₀ T₀ x v w| ≤
        δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
    intro v w
    have h := hfibre x v w
    have heq : ccTensorBilinSymm (I := I) g₀ T₀ x v w =
        smoothCcTensorBilinForm (I := I) g₀ T₀ x v w := by
      rw [ccTensorBilinSymm_apply, hTsymm x v w]; ring
    rwa [heq] at h
  obtain ⟨n, e, hn, horth, hpars, hexpand, hrfns⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  have hcomp_fiber : ∀ (i j : Fin n),
      smoothCcTensorBilinForm (I := I) g₀ T₀ x (e i) (e j) =
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 2 (T₀.toSection x) n e
          (default : Fin 0 → Fin n) (![i, j] : Fin 2 → Fin n) := by
    intro i j
    have hconst : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e ((default : Fin 0 → Fin n) k))) :
          Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply Tensor0SBundle.tensor0SSpace_ext
      intro u
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e ((default : Fin 0 → Fin n) k)))) u =
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u
      rw [show ((ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) u : ℝ) = 1 from rfl]
      change (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ)
          (fun k => g₀.inner x (e ((default : Fin 0 → Fin n) k)) (u k)) = 1
      rw [ContinuousMultilinearMap.mkPiAlgebra_apply]
      exact Finset.prod_of_isEmpty _
    rw [ccTensorBilin_apply]
    unfold fiberNormSqComponent
    rw [hconst]
    have htuple : (fun k => e ((![i, j] : Fin 2 → Fin n) k)) =
        (![e i, e j] : Fin 2 → TangentSpace I x) := by
      funext k; fin_cases k <;> rfl
    rw [htuple]
    change ccTensorModel (I := I) g₀ T₀ x ![e i, e j] =
      ((T₀.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
        ![e i, e j] : ℝ)
    unfold ccTensorModel
    rw [ccTensorMultilinear_apply]
    rfl
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) =
      ∑ a : Fin n, ∑ b : Fin n, (smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b)) ^ 2 := by
    rw [riemannianFiberNormSq_eq_sum_component_sq (I := I) (M := M) g₀ x e hrfns
      (T₀.toSection x) (default : Fin 0 → Fin n)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hcomp_fiber a b]
  rw [hbridge]
  have hrow : ∀ a : Fin n,
      ∑ b : Fin n, (smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b)) ^ 2 ≤ δ ^ 2 := by
    intro a
    set c : Fin n → ℝ := fun b => smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b) with hc_def
    set S : ℝ := ∑ b : Fin n, (c b) ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun b _ => sq_nonneg _)
    set u : TangentSpace I x := ∑ b : Fin n, c b • e b with hu_def
    have hval : smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) u = S := by
      have hexp : smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) u =
          ∑ b : Fin n, c b * smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b) := by
        rw [hu_def, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [hexp, hS_def]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      change c b * c b = (c b) ^ 2
      ring
    have hgiu : ∀ i : Fin n, g₀.inner x (e i) u = c i := by
      intro i
      have hexp : g₀.inner x (e i) u =
          ∑ b : Fin n, c b * g₀.inner x (e i) (e b) := by
        rw [hu_def, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [hexp]
      rw [Finset.sum_congr rfl (fun b _ => by rw [horth i b])]
      simp
    have hguu : g₀.inner x u u = S := by
      rw [← hpars u, hS_def]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hgiu i]
    have hgee : g₀.inner x (e a) (e a) = 1 := by rw [horth a a, if_pos rfl]
    have hopau := hop (e a) u
    rw [hgee, Real.sqrt_one, mul_one, hguu, hval] at hopau
    have hSle : S ≤ δ * Real.sqrt S := le_trans (le_abs_self S) hopau
    have hsqrtS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS_nn
    nlinarith [hSle, hsqrtS, sq_nonneg (Real.sqrt S - δ), Real.sqrt_nonneg S]
  calc ∑ a : Fin n, ∑ b : Fin n, (smoothCcTensorBilinForm (I := I) g₀ T₀ x (e a) (e b)) ^ 2
      ≤ ∑ _a : Fin n, δ ^ 2 := Finset.sum_le_sum (fun a _ => hrow a)
    _ = (n : ℝ) * δ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
        rw [show n = Module.finrank ℝ E from hn]

set_option maxHeartbeats 1600000 in

private lemma coeffAction_arm0_oneMinusConnLapIter_l2_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (_hΛa_nn : 0 ≤ Λa) :
    ∃ Kop : ℕ → ℝ, (∀ p, 0 ≤ Kop p) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ),
        0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ p : ℕ,
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ +
              Kop p *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 1) T₀‖ ∧
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)))‖ ^ 2 ≤
            (B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ +
              Kop p *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖) ^ 2 := by
  classical
  obtain ⟨KTe, hKTe_nn, hKTe⟩ := exists_connLapIterate_appCc_sobolevHs_bound (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨KTo, hKTo_nn, hKTo⟩ := exists_connLapIterate_appCc_covGrad_sobolevHs_bound_odd (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨KZ, hKZ_nn, hKZ⟩ := exists_deTurckRemainder_connLapIterate_sobolevHs_bound (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  refine ⟨fun p => KTe p + KTo p +
      2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q),
    fun p => by
      have h1 : (0:ℝ) ≤ ∑ q ∈ Finset.range p, KZ q (p - 1 - q) :=
        Finset.sum_nonneg (fun q _ => hKZ_nn q (p - 1 - q))
      have := hKTe_nn p
      have := hKTo_nn p
      linarith, ?_⟩
  intro C₀ T₀ B hB hball hdata _hsup henv p
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  have hKZsum_nn : (0:ℝ) ≤ ∑ q ∈ Finset.range p, KZ q (p - 1 - q) :=
    Finset.sum_nonneg (fun q _ => hKZ_nn q (p - 1 - q))
  have htransport := bal_transport (I := I) (M := M) g₀ C₀ T₀ p
  have hA_eq : oneMinusConnLapSmoothIter (I := I) g₀ 0 2 p
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)) =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀ +
        ∑ q ∈ Finset.range p, oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))) := htransport
  have hStop := hKTe C₀ T₀ B hB hball hdata henv p
  have hSodd := hKTo C₀ T₀ B hB hball hdata henv p
  have hZbound : ∀ q ∈ Finset.range p,
      ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
        KZ q (p - 1 - q) * fT (2 * p + 1) ∧
      ‖covGrad (I := I) (M := M) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
          (-(operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                    (covGrad (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))
            - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                  (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                    (slotExtend (I := I) (M := M) g₀ 2 2
                      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                  (covGrad (I := I) (M := M) g₀ 0 2 T₀))))‖ ≤
        KZ q (p - 1 - q) * fT (2 * p + 2) := by
    intro q hq
    have hqp := Finset.mem_range.mp hq
    have h := hKZ C₀ T₀ hball henv q (p - 1 - q)
    have hidx1 : (2 * (p - 1 - q) + 2 * q + 3 : ℕ) = 2 * p + 1 := by omega
    have hidx2 : (2 * (p - 1 - q) + 2 * q + 4 : ℕ) = 2 * p + 2 := by omega
    rw [hidx1, hidx2] at h
    exact h
  set Zf : ℕ → SmoothCcTensor g₀ 0 2 := fun q =>
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (p - 1 - q)
      (-(operatorFieldApply (I := I) (M := M) g₀ 2 2 (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
        - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                (covGrad (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))
        - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (slotExtend (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀)))
    with hZf_def
  constructor
  · have hgc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hgc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 1) T₀‖ =
        fT (2 * p + 1) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hgc2, hgc1, hA_eq]
    refine le_trans (norm_add_le _ _) ?_
    have hsum : ‖∑ q ∈ Finset.range p, Zf q‖ ≤ ∑ q ∈ Finset.range p, ‖Zf q‖ :=
      norm_sum_le (Finset.range p) Zf
    have hsum2 : ∑ q ∈ Finset.range p, ‖Zf q‖ ≤
        (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun q hq => (hZbound q hq).1)
    have htopfe : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 2) := rfl
    have htopfo : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 1) := rfl
    rw [htopfe, htopfo] at hStop
    have hKTo_extra : (0:ℝ) ≤ KTo p * fT (2 * p + 1) :=
      mul_nonneg (hKTo_nn p) (hfT_nn _)
    have hKZ_extra : (0:ℝ) ≤ (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 1) :=
      mul_nonneg hKZsum_nn (hfT_nn _)
    nlinarith [hStop, le_trans hsum hsum2]
  · have hgc3 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ =
        fT (2 * p + 3) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hgc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ =
        fT (2 * p + 2) :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hgc3, hgc2, hA_eq]
    set Xp : SmoothCcTensor g₀ 0 2 := operatorFieldApply (I := I) (M := M) g₀ 2 2
      (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 p C₀) T₀ with hXp_def
    set S : SmoothCcTensor g₀ 0 2 := ∑ q ∈ Finset.range p, Zf q with hS_def
    have hcovsplit : covGrad (I := I) (M := M) g₀ 0 2 (Xp + S) =
        covGrad (I := I) (M := M) g₀ 0 2 Xp + covGrad (I := I) (M := M) g₀ 0 2 S :=
      covGrad_add (I := I) (M := M) g₀ 0 2 Xp S
    have hnorm1 : ‖Xp + S‖ ≤ ‖Xp‖ + ‖S‖ := norm_add_le _ _
    have hnorm2 : ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ≤
        ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := by
      rw [hcovsplit]
      exact norm_add_le _ _
    have hmono := bal_sqrt_mono_pair (norm_nonneg (Xp + S))
      (norm_nonneg (covGrad (I := I) (M := M) g₀ 0 2 (Xp + S))) hnorm1 hnorm2
    have htwo := bal_sqrt_pair_two ‖Xp‖ ‖S‖ ‖covGrad (I := I) (M := M) g₀ 0 2 Xp‖
      ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _)
    have hSpair : Real.sqrt (‖S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ^ 2) ≤
        ‖S‖ + ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ := by
      have h := bal_sqrt_pair_two ‖S‖ 0 0 ‖covGrad (I := I) (M := M) g₀ 0 2 S‖
        (norm_nonneg _) (le_refl 0) (le_refl 0) (norm_nonneg _)
      simpa using h
    have hSnorm : ‖S‖ ≤ (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      rw [hS_def]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun q hq => ?_)
      refine le_trans (hZbound q hq).1 ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hKZ_nn q (p - 1 - q))
    have hGSnorm : ‖covGrad (I := I) (M := M) g₀ 0 2 S‖ ≤
        (∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      rw [hS_def]
      have hmapc : covGrad (I := I) (M := M) g₀ 0 2 (∑ q ∈ Finset.range p, Zf q) =
          ∑ q ∈ Finset.range p, covGrad (I := I) (M := M) g₀ 0 2 (Zf q) :=
        map_sum (AddMonoidHom.mk' (covGrad (I := I) (M := M) g₀ 0 2)
          (covGrad_add (I := I) (M := M) g₀ 0 2)) Zf (Finset.range p)
      rw [hmapc]
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun q hq => (hZbound q hq).2)
    have htopfo : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 3 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 3) := rfl
    have htopfe : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 2 : ℕ) : ℝ) T₀‖ =
        fT (2 * p + 2) := rfl
    rw [htopfo, htopfe] at hSodd
    have hchain : Real.sqrt (‖Xp + S‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2) ≤
        B * εa * fT (2 * p + 3) +
          (KTe p + KTo p + 2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) *
            fT (2 * p + 2) := by
      refine le_trans hmono (le_trans htwo ?_)
      have hKTe_extra : (0:ℝ) ≤ KTe p * fT (2 * p + 2) :=
        mul_nonneg (hKTe_nn p) (hfT_nn _)
      have h1 := le_trans hSpair (add_le_add hSnorm hGSnorm)
      nlinarith [hSodd, h1]
    have hLHS_nn : 0 ≤ ‖Xp + S‖ ^ 2 +
        ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2 := by positivity
    have hRHS_nn : 0 ≤ B * εa * fT (2 * p + 3) +
        (KTe p + KTo p + 2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
      have h1 : (0:ℝ) ≤ B * εa * fT (2 * p + 3) :=
        mul_nonneg (mul_nonneg hB hεa_nn) (hfT_nn _)
      have h2 : (0:ℝ) ≤ (KTe p + KTo p +
          2 * ∑ q ∈ Finset.range p, KZ q (p - 1 - q)) * fT (2 * p + 2) := by
        have := hKTe_nn p
        have := hKTo_nn p
        exact mul_nonneg (by linarith) (hfT_nn _)
      linarith
    have hsq : ‖Xp + S‖ ^ 2 + ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2 =
        Real.sqrt (‖Xp + S‖ ^ 2 +
          ‖covGrad (I := I) (M := M) g₀ 0 2 (Xp + S)‖ ^ 2) ^ 2 :=
      (Real.sq_sqrt hLHS_nn).symm
    rw [hsq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hchain 2

private lemma exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le_of_dataBound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (B : ℝ),
        0 ≤ B →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤ B ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            B * εa *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Kop, hKop_nn, hKop⟩ :=
    coeffAction_arm0_oneMinusConnLapIter_l2_le (I := I) (M := M) g₀ a ha_super hR₀
      Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨fun m => Kop (m / 2), fun m => hKop_nn (m / 2),
    fun C₀ T₀ B hB_nn hball hdata hsup henv m => ?_⟩
  have hlad := hKop C₀ T₀ B hB_nn hball hdata hsup henv
  rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hm2 : m = 2 * p := by omega
    subst hm2
    have hidx : 2 * p / 2 = p := by omega
    simp only [hidx]
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter (I := I) (M := M) g₀ p
      (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))
    rw [SmoothCcTensor.norm_toL2] at heven
    rw [heven]
    exact (hlad p).1
  · subst hp
    have hidx : (2 * p + 1) / 2 = p := by omega
    simp only [hidx]
    set Y : SmoothCcTensor g₀ 0 2 :=
      operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) with hY_def
    have hodd := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
      (I := I) (M := M) g₀ p Y
    rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2] at hodd
    have h2 := (hlad p).2
    have hc2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    have hc1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p + 1 : ℕ) : ℝ) + 1) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hc2, hc1]
    set R : ℝ := B * εa *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 3) T₀‖ +
      Kop p * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((2 * p : ℕ) : ℝ) + 2) T₀‖
      with hR_def
    have hR_nn : 0 ≤ R := by
      rw [hR_def]
      exact add_nonneg (mul_nonneg (mul_nonneg hB_nn hεa_nn) (norm_nonneg _))
        (mul_nonneg (hKop_nn p) (norm_nonneg _))
    have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖ ^ 2 ≤
        R ^ 2 := by
      rw [hodd]
      exact h2
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖
        = Real.sqrt (‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * p + 1 : ℕ) : ℝ) Y‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hsq
      _ = R := Real.sqrt_sq hR_nn

private lemma exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le_of_gFibreOpBound
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2) (δ : ℝ),
        0 ≤ δ →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤ Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            Real.sqrt (Module.finrank ℝ E) * εa * δ *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hcore⟩ :=
    exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le_of_dataBound (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn
      εa hεa_nn Λa hΛa_nn
  refine ⟨Cop, hCop_nn, fun C₀ T₀ δ hδ_nn hball hTsymm hfibre hsup hjet m => ?_⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ∀ (τ : ℝ) (X : SmoothCcTensor g₀ 0 2),
        smoothCcToTensorHs (I := I) (M := M) g₀ τ X = 0 := by
      intro τ X
      have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
          DifferentialGeometry.Integral.L2.tensorL2Norm,
          DifferentialGeometry.Integral.L2.tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
        hL2, tensorL2Coeff_eq_inner, inner_zero_right]
    rw [hzero, hzero, hzero]
    simp
  · haveI := hM
    have hB_nn : 0 ≤ Real.sqrt (Module.finrank ℝ E) * δ :=
      mul_nonneg (Real.sqrt_nonneg _) hδ_nn
    have hdata : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
          (Real.sqrt (Module.finrank ℝ E) * δ) ^ 2 := by
      intro x
      have h := riemannianFiberNormSq_le_of_ccTensorBilinSymm_gFibreOpBound (I := I) (M := M) g₀ T₀ hTsymm hfibre x
      have hsq : (Real.sqrt (Module.finrank ℝ E) * δ) ^ 2 =
          (Module.finrank ℝ E : ℝ) * δ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [hsq]; exact h
    have hmain := hcore C₀ T₀ (Real.sqrt (Module.finrank ℝ E) * δ) hB_nn hball hdata hsup hjet m
    have htop : Real.sqrt (Module.finrank ℝ E) * δ * εa =
        Real.sqrt (Module.finrank ℝ E) * εa * δ := by ring
    rw [htop] at hmain
    exact hmain

private theorem exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ εB : ℝ, 0 ≤ εB ∧
      (0 ≤ δ → εB ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa * δ) ∧
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
            Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            εB * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hcore⟩ :=
    exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le_of_gFibreOpBound (I := I) (M := M) g₀ a ha_super hR₀
      Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨Real.sqrt (Module.finrank ℝ E) * εa * max δ 0,
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hεa_nn) (le_max_right _ _),
    fun hδ_nn => ?_, Cop, hCop_nn, fun C₀ T₀ hball hTsymm hfibre hsup hjet m => ?_⟩
  · rw [max_eq_left hδ_nn]
    have hnn : 0 ≤ Real.sqrt (Module.finrank ℝ E) * εa * δ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hεa_nn) hδ_nn
    nlinarith [hnn]
  · rcases isEmpty_or_nonempty M with hM | hM
    · have hzero : ∀ (τ : ℝ) (X : SmoothCcTensor g₀ 0 2),
          smoothCcToTensorHs (I := I) (M := M) g₀ τ X = 0 := by
        intro τ X
        have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
          rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
            DifferentialGeometry.Integral.L2.tensorL2Norm,
            DifferentialGeometry.Integral.L2.tensorL2Inner,
            MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
        have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
        refine tensorHs.ext (funext fun i => ?_)
        rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
          hL2, tensorL2Coeff_eq_inner, inner_zero_right]
      rw [hzero, hzero, hzero]
      simp
    · haveI := hM
      have hδ_nn : 0 ≤ δ :=
        gFibreOpBound_delta_nonneg (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T₀) hfibre
      rw [max_eq_left hδ_nn]
      exact hcore C₀ T₀ δ hδ_nn hball hTsymm hfibre hsup hjet m

set_option maxHeartbeats 1000000 in

theorem exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εwrap : ℝ, 0 ≤ εwrap ∧
      (0 ≤ δ → εwrap ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 * (δ / (1 - δ))) ∧
    ∃ Cthird Ctame : ℕ → ℝ, (∀ k, 0 ≤ Cthird k) ∧ (∀ k, 0 ≤ Ctame k) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ third tame : SmoothCcTensor g₀ 0 2,
          deTurckSmoothRemainder (I := I) g₀ g_bg T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
            deTurckSmoothRemainder (I := I) g₀ g_bg
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)) =
            deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀
              + third + tame ∧
          (∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) third‖ ≤
              εwrap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
                Cthird k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) ∧
          (∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) tame‖ ≤
              Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Ctame, hCtame_nn, htame⟩ :=
    exists_smoothCcToTensorHs_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cop, hCop_nn, hH3⟩ :=
    exists_smoothCcToTensorHs_coeffAction_fibreSmallCoeff_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  obtain ⟨εB, hεB_nn, hεB_cap, CopB, hCopB_nn, hB'⟩ :=
    exists_smoothCcToTensorHs_coeffAction_arm0_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ (δ := δ) Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨deTurckArmFibreConst (Module.finrank ℝ E) * εC + εB,
    add_nonneg (mul_nonneg (deTurckArmFibreConst_nonneg _) hεC_nn) hεB_nn,
    fun hδ_nn => ?_,
    fun k => Cop (a + k - 1) + CopB (a + k - 1), Ctame,
    fun k => add_nonneg (hCop_nn _) (hCopB_nn _), hCtame_nn, fun T₀ hTsymm hball => ?_⟩
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hδκ : δ ≤ δ / (1 - δ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
      nlinarith [sq_nonneg δ]
    have hf_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
      deTurckArmFibreConst_nonneg _
    have h1 : deTurckArmFibreConst (Module.finrank ℝ E) * εC ≤
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) := by
      calc deTurckArmFibreConst (Module.finrank ℝ E) * εC
          ≤ deTurckArmFibreConst (Module.finrank ℝ E) *
              (28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) :=
            mul_le_mul_of_nonneg_left (hεC_cap' hδ_nn) hf_nn
        _ = 28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) := by ring
    have h2sq_nn : (0 : ℝ) ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hεa_nn
    have h2 : εB ≤ (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) := by
      refine le_trans (hεB_cap hδ_nn) ?_
      calc 2 * Real.sqrt (Module.finrank ℝ E) * εa * δ
          ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa * (δ / (1 - δ)) :=
            mul_le_mul_of_nonneg_left hδκ h2sq_nn
        _ ≤ (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
              28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) :=
            mul_le_mul_of_nonneg_right hεa_cap hκ_nn
    calc deTurckArmFibreConst (Module.finrank ℝ E) * εC + εB
        ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) +
            (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
              28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) :=
          add_le_add h1 h2
      _ = 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 * (δ / (1 - δ)) := by ring
  obtain ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, hHsbound⟩ := htame T₀ hTsymm hball
  refine ⟨operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) +
      operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀),
    deTurckSmoothRemainder (I := I) g₀ g_bg T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
      deTurckSmoothRemainder (I := I) g₀ g_bg
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀ -
      operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
      operatorFieldApply (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀),
    by abel, fun k => ?_, hHsbound⟩
  · have hm1 : (a : ℝ) + (k : ℝ) - 1 = ((a + k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ a + k by omega)]; push_cast; ring
    have hm2 : (a : ℝ) + (k : ℝ) + 1 = ((a + k - 1 : ℕ) : ℝ) + 2 := by
      rw [← hm1]; ring
    have hm3 : (a : ℝ) + (k : ℝ) = ((a + k - 1 : ℕ) : ℝ) + 1 := by
      rw [← hm1]; ring
    rw [hm1, hm2, hm3, smoothCcToTensorHs_add]
    refine le_trans (norm_add_le _ _) ?_
    have hA := hH3 C₂ T₀ hball hC₂sup hC₂jet (a + k - 1)
    have hB2 := hB' C₀ T₀ hball hTsymm (hδ_fibre T₀ hball) hC₀sup hC₀jet (a + k - 1)
    linarith [hA, hB2]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
