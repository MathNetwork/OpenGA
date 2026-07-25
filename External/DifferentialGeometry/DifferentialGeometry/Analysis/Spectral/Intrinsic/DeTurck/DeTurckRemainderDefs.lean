import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzTruncation
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def deTurckSmoothRemainder (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 :=
  { toSection :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
    hasCompactSupport :=
      (deTurckRHSSection (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport }
  - rawTensorConnLapSmooth (I := I) g₀ 0 2 T

def smoothCcToTensorHs (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    tensorHs (I := I) (M := M) g₀ 0 2 σ where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀ σ T
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

@[simp] theorem smoothCcToTensorHs_coeff (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (smoothCcToTensorHs (I := I) (M := M) g₀ σ T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 T) i :=
  rfl

def deTurckArmFibreConst (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) ^ 3)

lemma deTurckArmFibreConst_nonneg (n : ℕ) : 0 ≤ deTurckArmFibreConst n :=
  Real.sqrt_nonneg _

lemma one_le_deTurckArmFibreConst {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ deTurckArmFibreConst n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := (one_pow 3).symm
      _ ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ zero_le_one hn' 3
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt ((n : ℝ) ^ 3) := Real.sqrt_le_sqrt h1

lemma sq_deTurckArmFibreConst (n : ℕ) :
    deTurckArmFibreConst n ^ 2 = (n : ℝ) ^ 3 :=
  Real.sq_sqrt (by positivity)

def deTurckArmContractionThreshold (n : ℕ) : ℝ :=
  1 / (1 + 2 * deTurckArmFibreConst n)

lemma deTurckArmContractionThreshold_pos (n : ℕ) :
    0 < deTurckArmContractionThreshold n := by
  have h := deTurckArmFibreConst_nonneg n
  unfold deTurckArmContractionThreshold
  positivity

lemma deTurckArmContractionThreshold_le_third {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold n ≤ 1 / 3 := by
  have h1 := one_le_deTurckArmFibreConst hn
  unfold deTurckArmContractionThreshold
  rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 3)]
  linarith

lemma deTurckArmContractionThreshold_lt_one {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold n < 1 :=
  lt_of_le_of_lt (deTurckArmContractionThreshold_le_third hn)
    (by norm_num : (1 : ℝ) / 3 < 1)

lemma deTurckArmContractionThreshold_le_third' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold n ≤ 1 / 3 :=
  deTurckArmContractionThreshold_le_third (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmContractionThreshold_lt_one' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold n < 1 :=
  deTurckArmContractionThreshold_lt_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

def deTurckArmContractionThresholdSharp (n : ℕ) : ℝ :=
  1 / (1 + 2 * (deTurckArmFibreConst n + 32 * deTurckArmFibreConst n ^ 3))

lemma deTurckArmContractionThreshold''_pos (n : ℕ) :
    0 < deTurckArmContractionThresholdSharp n := by
  unfold deTurckArmContractionThresholdSharp
  have hf : 0 ≤ deTurckArmFibreConst n := deTurckArmFibreConst_nonneg n
  have hf3 : 0 ≤ deTurckArmFibreConst n ^ 3 := by positivity
  exact one_div_pos.mpr (by linarith)

lemma deTurckArmContractionThreshold''_le {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThresholdSharp n ≤ deTurckArmContractionThreshold n := by
  have hC := one_le_deTurckArmFibreConst hn
  unfold deTurckArmContractionThresholdSharp deTurckArmContractionThreshold
  have hC3 : 0 ≤ deTurckArmFibreConst n ^ 3 := by positivity
  apply one_div_le_one_div_of_le (by linarith)
  linarith

lemma deTurckArmContractionThreshold''_le_third {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThresholdSharp n ≤ 1 / 3 :=
  le_trans (deTurckArmContractionThreshold''_le hn)
    (deTurckArmContractionThreshold_le_third hn)

lemma deTurckArmContractionThreshold''_lt_one {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThresholdSharp n < 1 :=
  lt_of_le_of_lt (deTurckArmContractionThreshold''_le_third hn)
    (by norm_num : (1 : ℝ) / 3 < 1)

lemma deTurckArmContractionThreshold''_le_third' (n : ℕ) [NeZero n] :
    deTurckArmContractionThresholdSharp n ≤ 1 / 3 :=
  deTurckArmContractionThreshold''_le_third (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmContractionThreshold''_lt_one' (n : ℕ) [NeZero n] :
    deTurckArmContractionThresholdSharp n < 1 :=
  deTurckArmContractionThreshold''_lt_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmFibreConst_mul_div_le_half {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ_le : δ ≤ deTurckArmContractionThreshold n) :
    deTurckArmFibreConst n * (δ / (1 - δ)) ≤ 1 / 2 := by
  have hC := one_le_deTurckArmFibreConst hn
  set C := deTurckArmFibreConst n with hC_def
  have hden : (0 : ℝ) < 1 + 2 * C := by linarith
  have hthr_lt : deTurckArmContractionThreshold n < 1 :=
    deTurckArmContractionThreshold_lt_one hn
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le hthr_lt
  have h1δ_pos : (0 : ℝ) < 1 - δ := by linarith
  by_cases hδ0 : δ ≤ 0
  · have hratio_np : δ / (1 - δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ0 h1δ_pos.le
    have : C * (δ / (1 - δ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hratio_np
    linarith
  · have hδ_mul : δ * (1 + 2 * C) ≤ 1 := by
      have := (le_div_iff₀ hden).mp
        (show δ ≤ 1 / (1 + 2 * C) from hδ_le)
      linarith
    have hratio : δ / (1 - δ) ≤ 1 / (2 * C) := by
      rw [div_le_div_iff₀ h1δ_pos (by linarith : (0 : ℝ) < 2 * C)]
      nlinarith
    calc C * (δ / (1 - δ)) ≤ C * (1 / (2 * C)) :=
          mul_le_mul_of_nonneg_left hratio (by linarith)
      _ = 1 / 2 := by field_simp

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
