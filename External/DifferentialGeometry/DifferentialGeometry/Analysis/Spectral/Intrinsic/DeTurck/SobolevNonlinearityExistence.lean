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
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistenceSpectralCovGradNormEquiv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistenceRemainderDiffBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistenceSymmetrizationNormBounds


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

def deTurckSmoothRemainderTensorHs (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
      (a : ℝ) (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

@[simp] theorem deTurckSmoothN_coeff (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i :=
  rfl

theorem smoothCcToTensorHs_denseRange (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    DenseRange (smoothCcToTensorHs (I := I) (M := M) g₀ σ) := by
  classical
  have hsub :
      (tensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g₀) (r := 0) (s := 2) σ :
          Set (tensorHs (I := I) (M := M) g₀ 0 2 σ)) ⊆
        Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ σ) := by
    intro x hx
    have hxfin : (Function.support x.coeff).Finite :=
      (tensorHs.mem_finiteSupportSubmodule (I := I) (M := M) x).1 hx
    refine ⟨finiteEigenCombo (I := I) (M := M) g₀ hxfin.toFinset x.coeff, ?_⟩
    refine tensorHs.ext ?_
    funext i
    rw [smoothCcToTensorHs_coeff]
    have hcoeff :
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2
              (finiteEigenCombo (I := I) (M := M) g₀ hxfin.toFinset x.coeff)) i =
          (if i ∈ hxfin.toFinset then x.coeff i else 0) := by
      rw [SmoothCcTensor.toL2_apply,
        finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g₀ hxfin.toFinset x.coeff i]
    rw [hcoeff]
    by_cases hi : i ∈ hxfin.toFinset
    · rw [if_pos hi]
    · rw [if_neg hi]
      rw [Set.Finite.mem_toFinset] at hi
      exact (Function.notMem_support.mp hi).symm
  exact (tensorHsFiniteSupportSubmodule_dense (I := I) (M := M)).mono hsub

theorem smoothCcToTensorHs_add (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (S + T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ S +
        smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.add_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (S + T) =
        SmoothCcTensor.toL2 S + SmoothCcTensor.toL2 T from map_add _ _ _,
    tensorL2Coeff_add]

theorem smoothCcToTensorHs_neg (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (-S) =
      -smoothCcToTensorHs (I := I) (M := M) g₀ σ S := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.neg_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (-S) = -SmoothCcTensor.toL2 S from map_neg _ _]
  rw [show (-SmoothCcTensor.toL2 S : TensorL2 0 2 g₀) = (-1 : ℝ) • SmoothCcTensor.toL2 S by
    rw [neg_one_smul]]
  rw [tensorL2Coeff_smul]
  ring

theorem smoothCcToTensorHs_sub (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (S - T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ S -
        smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smoothCcToTensorHs_add, smoothCcToTensorHs_neg]

theorem deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
        deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
          deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') := by
  refine tensorHs.ext ?_
  funext i
  have hsub :
      (deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
          deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ').coeff i =
        (deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ).coeff i -
          (deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ').coeff i := by
    rw [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
    rfl
  have hcoeff_sub :
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')) i =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i -
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')) i := by
    rw [show SmoothCcTensor.toL2
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
          SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) -
            SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')
        from map_sub _ _ _]
    rw [sub_eq_add_neg, tensorL2Coeff_add]
    rw [show (-SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') :
          TensorL2 0 2 g₀) =
        (-1 : ℝ) • SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') by
      rw [neg_one_smul]]
    rw [tensorL2Coeff_smul]
    ring
  rw [hsub, deTurckSmoothN_coeff, deTurckSmoothN_coeff, smoothCcToTensorHs_coeff, hcoeff_sub]



theorem smoothRemainderDiff_ballLipschitz_sobolev
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
  classical

  have hordB : (((a + 2 : ℕ)) : ℝ) = (a : ℝ) + 2 := by push_cast; ring

  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀ a

  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)

  have hR'_nn : (0 : ℝ) ≤ Cb * R := mul_nonneg hCb_nn hR.le
  obtain ⟨Ccol, hCcol_nn, hCcol⟩ :=
    deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR'_nn hδ₀

  refine ⟨Real.toNNReal (Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2))), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set W : SmoothCcTensor g₀ 0 2 := T - T' with hW_def
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def

  set Ndist : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ with hNdist_def
  have hNdist_nn : 0 ≤ Ndist := norm_nonneg _
  have hNdist_eq : Ndist = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) W‖ := by
    rw [hNdist_def, hW_def, smoothCcToTensorHs_sub]

  have hball_conv : ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R →
      ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cb * R := by
    intro S hSball j hj
    have hsum := hCb S
    rw [hordB] at hsum
    have hterm : ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := by
      refine Finset.single_le_sum (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖)
        (fun i _ => norm_nonneg _) ?_
      rw [Finset.mem_range]; omega
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
        ≤ ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := hterm
      _ ≤ Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ := hsum
      _ ≤ Cb * R := mul_le_mul_of_nonneg_left hSball hCb_nn
  have hTcov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ Cb * R :=
    hball_conv T hTball
  have hT'cov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ Cb * R :=
    hball_conv T' hT'ball

  have hcol := hCcol T T' hδ_le hδ hδ'_le hδ' hTcov hT'cov
  rw [← hD_def] at hcol

  have hWsum := hCb W
  rw [hordB, ← hNdist_eq] at hWsum
  set Wsum : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ with hWsum_def
  have hWsum_nn : 0 ≤ Wsum :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hWsumsq_le : Wsum ^ 2 ≤ Cb ^ 2 * Ndist ^ 2 := by
    have := mul_le_mul hWsum hWsum hWsum_nn (by positivity)
    calc Wsum ^ 2 = Wsum * Wsum := by ring
      _ ≤ (Cb * Ndist) * (Cb * Ndist) := this
      _ = Cb ^ 2 * Ndist ^ 2 := by ring

  have hsq_le_sumsq : (∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) ≤ Wsum ^ 2 := by
    rw [hWsum_def]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)

  have hcol' : (∑ q ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2) ≤ Ccol * (Cb ^ 2 * Ndist ^ 2) := by
    refine hcol.trans ?_
    calc Ccol * ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2
        ≤ Ccol * Wsum ^ 2 := mul_le_mul_of_nonneg_left hsq_le_sumsq hCcol_nn
      _ ≤ Ccol * (Cb ^ 2 * Ndist ^ 2) := mul_le_mul_of_nonneg_left hWsumsq_le hCcol_nn

  set Dsum : ℝ := ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ with hDsum_def
  have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hDsum_sq : Dsum ^ 2 ≤ ((a : ℝ) + 1) *
      ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 := by
    rw [hDsum_def]
    have hcheb := sq_sum_le_card_mul_sum_sq (s := Finset.range (a + 1))
      (f := fun q => ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖)
    rw [Finset.card_range] at hcheb
    refine hcheb.trans (le_of_eq ?_)
    congr 1
    push_cast; ring

  have hbridgeA := hCa D
  rw [← hDsum_def] at hbridgeA

  have hDsum_le : Dsum ≤ Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist := by
    have hDsum_sq_le : Dsum ^ 2 ≤ (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by
      calc Dsum ^ 2 ≤ ((a : ℝ) + 1) *
            ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 := hDsum_sq
        _ ≤ ((a : ℝ) + 1) * (Ccol * (Cb ^ 2 * Ndist ^ 2)) :=
            mul_le_mul_of_nonneg_left hcol' (by positivity)
        _ = (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by ring
    have hrhs_nn : 0 ≤ Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist :=
      mul_nonneg (Real.sqrt_nonneg _) hNdist_nn
    have hsqrt_sq : (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) ^ 2 =
        (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hsqle : Dsum ^ 2 ≤ (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) ^ 2 := by
      rw [hsqrt_sq]; exact hDsum_sq_le
    have := Real.sqrt_le_sqrt hsqle
    rwa [Real.sqrt_sq hDsum_nn, Real.sqrt_sq hrhs_nn] at this
  have hKcoe : (Real.toNNReal (Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2))) : ℝ) =
      Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) :=
    Real.coe_toNNReal _ (by positivity)
  rw [hKcoe]
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) D‖
      ≤ Ca * Dsum := hbridgeA
    _ ≤ Ca * (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) :=
        mul_le_mul_of_nonneg_left hDsum_le hCa_nn
    _ = Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist := by ring



theorem deTurckRemainderDiff_iteratedCovGrad_ballLipschitz_dataWeighted_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
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
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * (max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                     ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖
                   * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖) := by
  classical
  obtain ⟨Ccov, hCcov_nn, hCcov⟩ :=
    deTurckSmoothRemainderDiff_iteratedCovGrad_l2_dataWeighted_ballUniform_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Cb2, hCb2_nn, hCb2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  obtain ⟨Cb1, hCb1_nn, hCb1⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 1)
  refine ⟨Ccov * max Cb2 Cb1, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball q hq
  set H2 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ with hH2_def
  set H1 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖ with hH1_def
  have hH2_nn : 0 ≤ H2 := norm_nonneg _
  have hH1_nn : 0 ≤ H1 := norm_nonneg _
  set Dm : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ with hDm_def
  have hDm_nn : 0 ≤ Dm := le_trans (norm_nonneg _) (le_max_left _ _)
  have hsqrt2_le : Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤ max Cb2 Cb1 * H2 := by
    have hsq_le_sum : (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤
        (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
    have hcastord : ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
    have hsum_le : (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ≤ Cb2 * H2 := by
      have h := hCb2 (T - T')
      rw [hcastord] at h
      exact h
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    calc Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)
        ≤ Real.sqrt ((∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ^ 2) := Real.sqrt_le_sqrt hsq_le_sum
      _ = ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ := Real.sqrt_sq hsum_nn
      _ ≤ Cb2 * H2 := hsum_le
      _ ≤ max Cb2 Cb1 * H2 := mul_le_mul_of_nonneg_right (le_max_left _ _) hH2_nn
  have hsqrt1_le : Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤ max Cb2 Cb1 * H1 := by
    have hsq_le_sum : (∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤
        (∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
    have hcastord : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
    have hsum_le : (∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ≤ Cb1 * H1 := by
      have h := hCb1 (T - T')
      rw [hcastord] at h
      exact h
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    calc Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)
        ≤ Real.sqrt ((∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ^ 2) := Real.sqrt_le_sqrt hsq_le_sum
      _ = ∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ := Real.sqrt_sq hsum_nn
      _ ≤ Cb1 * H1 := hsum_le
      _ ≤ max Cb2 Cb1 * H1 := mul_le_mul_of_nonneg_right (le_max_right _ _) hH1_nn
  have hcov := hCcov T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball q hq
  refine hcov.trans ?_
  have hmaxnn : 0 ≤ max Cb2 Cb1 := le_max_of_le_left hCb2_nn
  have hstep : Dm * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
        Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤
      max Cb2 Cb1 * (Dm * H2 + H1) := by
    have ht2 := mul_le_mul_of_nonneg_left hsqrt2_le hDm_nn
    calc Dm * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
          Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)
        ≤ Dm * (max Cb2 Cb1 * H2) + max Cb2 Cb1 * H1 := add_le_add ht2 hsqrt1_le
      _ = max Cb2 Cb1 * (Dm * H2 + H1) := by ring
  calc Ccov * (Dm * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
          Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2))
      ≤ Ccov * (max Cb2 Cb1 * (Dm * H2 + H1)) :=
        mul_le_mul_of_nonneg_left hstep hCcov_nn
    _ = Ccov * max Cb2 Cb1 * (Dm * H2 + H1) := by ring


theorem smoothRemainderDiff_ballLipschitz_sobolev_dataWeighted_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
      (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
      (_hT'symm : ∀ (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
        (K : ℝ) *
          (max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
               ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖
             * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖) := by
  classical
  have hordB : (((a + 2 : ℕ)) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀ a
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  have hR'_nn : (0 : ℝ) ≤ Cb * R := mul_nonneg hCb_nn hR.le
  obtain ⟨Ccol, hCcol_nn, hCcol⟩ :=
    deTurckRemainderDiff_iteratedCovGrad_ballLipschitz_dataWeighted_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR'_nn hδ₀
  refine ⟨Real.toNNReal (Ca * (((a : ℝ) + 1) * Ccol)), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set W : SmoothCcTensor g₀ 0 2 := T - T' with hW_def
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  set rhs : ℝ :=
    max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖
      * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖ with hrhs_def
  have hball_conv : ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R →
      ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cb * R := by
    intro S hSball j hj
    have hsum := hCb S
    rw [hordB] at hsum
    have hterm : ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := by
      refine Finset.single_le_sum (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖)
        (fun i _ => norm_nonneg _) ?_
      rw [Finset.mem_range]; omega
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
        ≤ ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := hterm
      _ ≤ Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ := hsum
      _ ≤ Cb * R := mul_le_mul_of_nonneg_left hSball hCb_nn
  have hTcov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ Cb * R :=
    hball_conv T hTball
  have hT'cov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ Cb * R :=
    hball_conv T' hT'ball
  have hcol := hCcol T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTcov hT'cov
  set Dsum : ℝ := ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ with hDsum_def
  have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hper : ∀ q ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ≤ Ccol * rhs := by
    intro q hq
    have hqa : q ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hb := hcol q hqa
    rw [← hD_def, ← hrhs_def] at hb
    exact hb
  have hDsum_le : Dsum ≤ ((a : ℝ) + 1) * (Ccol * rhs) := by
    calc Dsum = ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ := hDsum_def
      _ ≤ ∑ _q ∈ Finset.range (a + 1), Ccol * rhs := Finset.sum_le_sum hper
      _ = ((a + 1 : ℕ) : ℝ) * (Ccol * rhs) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((a : ℝ) + 1) * (Ccol * rhs) := by push_cast; ring
  have hbridgeA := hCa D
  rw [← hDsum_def] at hbridgeA
  have hKcoe : (Real.toNNReal (Ca * (((a : ℝ) + 1) * Ccol)) : ℝ) =
      Ca * (((a : ℝ) + 1) * Ccol) :=
    Real.coe_toNNReal _ (by positivity)
  rw [hKcoe]
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) D‖
      ≤ Ca * Dsum := hbridgeA
    _ ≤ Ca * (((a : ℝ) + 1) * (Ccol * rhs)) :=
        mul_le_mul_of_nonneg_left hDsum_le hCa_nn
    _ = Ca * (((a : ℝ) + 1) * Ccol) * rhs := by ring

theorem tensorHsInclusion_smoothCcToTensorHs (g₀ : SmoothRiemannianMetric I M)
    {τ σ : ℝ} (hτσ : τ ≤ σ) (T : SmoothCcTensor g₀ 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ τ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]

theorem deTurckSmoothRemainderTensorHs_ballLipschitz (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T (lt_of_le_of_lt hδ_le hδ₀) hδ -
          deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
  obtain ⟨K, hK⟩ :=
    smoothRemainderDiff_ballLipschitz_sobolev (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨K, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  rw [deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (I := I) (M := M) g₀ g_bg a T T' hδ_lt hδ hδ'_lt hδ']
  exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball

theorem deTurckSmoothRemainderTensorHs_ballLipschitz_dataWeighted_of_symm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
      (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
      (_hT'symm : ∀ (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀ T' x v w = smoothCcTensorBilinForm (I := I) g₀ T' x w v),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T (lt_of_le_of_lt hδ_le hδ₀) hδ -
          deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
        (K : ℝ) *
          (max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T)‖
               ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T')‖
             * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
                  smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ +
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
                smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T')‖) := by
  obtain ⟨K, hK⟩ :=
    smoothRemainderDiff_ballLipschitz_sobolev_dataWeighted_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨K, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hbase := hK T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  rw [deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (I := I) (M := M) g₀ g_bg a T T' hδ_lt hδ hδ'_lt hδ']
  refine le_trans hbase (le_of_eq ?_)
  rw [tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ _ T,
    tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ _ T',
    ← smoothCcToTensorHs_sub (I := I) (M := M) g₀ ((a : ℝ) + 2) T T',
    tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ _ (T - T')]

theorem smoothCcToTensorHs_smul (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (c : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (c • T) =
      c • smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.smul_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (c • T) = c • SmoothCcTensor.toL2 T from map_smul _ _ _,
    tensorL2Coeff_smul]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHs_norm_smul (g₀ : SmoothRiemannianMetric I M) {σ : ℝ} (c : ℝ)
    (x : tensorHs (I := I) (M := M) g₀ 0 2 σ) :
    ‖c • x‖ = |c| * ‖x‖ := by
  have h1 : ‖c • x‖ =
      ‖tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (σ := σ) (c • x)‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (σ := σ)).norm_map (c • x) |>.symm
  have h2 : ‖tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (σ := σ) x‖ = ‖x‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (σ := σ)).norm_map x
  rw [h1, map_smul, norm_smul, Real.norm_eq_abs, h2]

theorem sobolevBall_smooth_fibreSmall (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ δ₀ : ℝ, δ₀ ≤ 1 / 3 ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ₀ := by
  classical

  set m : ℕ := 2 * Module.finrank ℝ E + 4 with hm_def
  have hm_lossy : 2 * Module.finrank ℝ E + 4 ≤ m := by rw [hm_def]
  have hm_le : (m : ℕ) ≤ a + 2 := by rw [hm_def]; omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_metricCauchySchwarzBound_le_sobolevHsNorm_lossy_order (I := I) (M := M) g₀ m hm_lossy
  refine ⟨1 / (3 * C), by positivity, 1 / 3, le_refl _, fun T hTball => ?_⟩

  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ := by
    have hembed_m : smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T =
        ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    have hembed_a2 : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
        ccSpectralEmbed (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed_m, hembed_a2]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
    have hcast : (m : ℝ) ≤ (a : ℝ) + 2 := by
      have h2 : (m : ℝ) ≤ (a : ℝ) + (2 : ℕ) := by exact_mod_cast hm_le
      push_cast at h2
      linarith [h2]
    exact hcast

  intro x v w
  have hlossy := hC T x v w
  have hNm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ 1 / (3 * C) :=
    le_trans hmono hTball
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn
  refine hlossy.trans ?_
  have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ 1 / 3 := by
    calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖
        ≤ C * (1 / (3 * C)) := mul_le_mul_of_nonneg_left hNm_le hC_pos.le
      _ = 1 / 3 := by field_simp
  calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
      = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
          (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
    _ ≤ (1 / 3 : ℝ) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
        mul_le_mul_of_nonneg_right hCN_le hmul_nn
    _ = 1 / 3 * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

theorem sobolevBall_smooth_fibreSmall_of_threshold (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {θ : ℝ} (hθ_pos : 0 < θ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ δ₀ : ℝ, δ₀ ≤ θ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ₀ := by
  classical
  set m : ℕ := 2 * Module.finrank ℝ E + 4 with hm_def
  have hm_lossy : 2 * Module.finrank ℝ E + 4 ≤ m := by rw [hm_def]
  have hm_le : (m : ℕ) ≤ a + 2 := by rw [hm_def]; omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_metricCauchySchwarzBound_le_sobolevHsNorm_lossy_order (I := I) (M := M) g₀ m hm_lossy
  refine ⟨θ / C, by positivity, θ, le_refl _, fun T hTball => ?_⟩
  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ := by
    have hembed_m : smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T =
        ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    have hembed_a2 : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
        ccSpectralEmbed (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed_m, hembed_a2]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
    have hcast : (m : ℝ) ≤ (a : ℝ) + (2 : ℕ) := by exact_mod_cast hm_le
    push_cast at hcast
    linarith [hcast]
  intro x v w
  have hlossy := hC T x v w
  have hNm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ θ / C :=
    le_trans hmono hTball
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn
  refine hlossy.trans ?_
  have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ θ := by
    calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖
        ≤ C * (θ / C) := mul_le_mul_of_nonneg_left hNm_le hC_pos.le
      _ = θ := by field_simp
  calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
      = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
          (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
    _ ≤ θ * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
        mul_le_mul_of_nonneg_right hCN_le hmul_nn
    _ = θ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

theorem deTurckSmoothN_embedding_wellDefined (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTT' : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') :
    deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' := by

  set δ₀ : ℝ := max δ δ' with hδ₀_def
  have hδ₀ : δ₀ < 1 := by rw [hδ₀_def]; exact max_lt hδ_lt hδ'_lt
  have hδ_le : δ ≤ δ₀ := by rw [hδ₀_def]; exact le_max_left _ _
  have hδ'_le : δ' ≤ δ₀ := by rw [hδ₀_def]; exact le_max_right _ _
  set R : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ + 1 with hR_def
  have hR_pos : 0 < R := by
    have : (0 : ℝ) ≤ max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    rw [hR_def]; linarith
  obtain ⟨K, hK⟩ :=
    deTurckSmoothRemainderTensorHs_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR_pos hδ₀
  have hTball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R := by
    rw [hR_def]; linarith [le_max_left ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖]
  have hT'ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R := by
    rw [hR_def]; linarith [le_max_right ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖]
  have hbound := hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  rw [hTT', sub_self, norm_zero, mul_zero] at hbound
  have hzero : ‖deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ'‖ = 0 :=
    le_antisymm hbound (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at hzero
  exact hzero

def radialScaleSmooth (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R₀ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 2 :=
  (min 1 (R₀ / ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖)) • T

theorem norm_smoothCcToTensorHs_radialScaleSmooth_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T)‖ ≤ R₀ := by
  set n := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hcnn : 0 ≤ min 1 (R₀ / n) := le_min zero_le_one (div_nonneg hR₀ hn0)
  rw [radialScaleSmooth, smoothCcToTensorHs_smul, tensorHs_norm_smul, abs_of_nonneg hcnn]
  rcases eq_or_lt_of_le hn0 with heq | hpos
  · rw [← heq]; simpa using hR₀
  · have hmin_le : min 1 (R₀ / n) ≤ R₀ / n := min_le_right _ _
    calc min 1 (R₀ / n) * n ≤ (R₀ / n) * n :=
          mul_le_mul_of_nonneg_right hmin_le hn0
      _ = R₀ := by field_simp

theorem smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R₀ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T) =
      ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
  rw [radialScaleSmooth, smoothCcToTensorHs_smul, ballRetraction]

open Classical in

def deTurckSobolevNonlinearity (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun v =>
    if h : ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 ≤ deTurckArmContractionThresholdSharp (Module.finrank ℝ E) ∧
        ∀ (T : SmoothCcTensor g₀ 0 2),
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
          metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 then
      Dense.extend (smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2))
        (fun x =>
          deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
            (radialScaleSmooth (I := I) (M := M) g₀ a (Classical.choose h).1
              (Classical.choose x.2))
            (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
            ((Classical.choose_spec h).2.2 _
              (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
                g₀ a (Classical.choose_spec h).1.le (Classical.choose x.2))))
        (recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (Classical.choose h).1 v)
    else 0

theorem deTurckSobolevNHa2_exists_of_super (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 ≤ deTurckArmContractionThresholdSharp (Module.finrank ℝ E) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
        metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 := by
  obtain ⟨R₀, hR₀, δ₀, hδ₀_le, hball⟩ :=
    sobolevBall_smooth_fibreSmall_of_threshold (I := I) (M := M) g₀ a ha_super
      (deTurckArmContractionThreshold''_pos (Module.finrank ℝ E))
  exact ⟨(R₀, δ₀), hR₀, hδ₀_le, hball⟩

theorem deTurckSobolevNHa2_lipschitzWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ K : ℝ≥0, LipschitzWith K (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a) := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨K, hK⟩ :=
    deTurckSmoothRemainderTensorHs_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR₀
      hδ₀_lt

  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
        hδ₀_lt
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le (Classical.choose x.2))) with hF_def

  have hembed : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) =
          ballRetraction R₀ (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec x.2]

  have hF_lip : ∀ x y : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      ‖F x - F y‖ ≤ (K : ℝ) *
        ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (y : _)‖ := by
    intro x y
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))‖ := hbound
      _ = (K : ℝ) * ‖ballRetraction R₀
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            ballRetraction R₀ (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [hembed x, hembed y]
      _ ≤ (K : ℝ) * ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg

  have hlipF : LipschitzWith K F := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    exact hF_lip x y
  have hF_cont : Continuous F := hlipF.continuous

  have hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
  have hext_eq : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      Dense.extend hdense F (x : _) = F x := fun x => hdense.extend_eq hF_cont x
  have hext_cont : Continuous (Dense.extend hdense F) :=
    (hdense.uniformContinuous_extend hlipF.uniformContinuous).continuous

  have hext_lip_s : LipschitzOnWith K (Dense.extend hdense F)
      (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr (fun p hp q hq => ?_)
    obtain ⟨xp, hxp⟩ := hp
    obtain ⟨xq, hxq⟩ := hq
    have hep : Dense.extend hdense F p = F ⟨p, ⟨xp, hxp⟩⟩ := by
      have := hext_eq ⟨p, ⟨xp, hxp⟩⟩; simpa using this
    have heq : Dense.extend hdense F q = F ⟨q, ⟨xq, hxq⟩⟩ := by
      have := hext_eq ⟨q, ⟨xq, hxq⟩⟩; simpa using this
    rw [dist_eq_norm, hep, heq, dist_eq_norm]
    exact hF_lip ⟨p, ⟨xp, hxp⟩⟩ ⟨q, ⟨xq, hxq⟩⟩
  have hext_lip : LipschitzWith K (Dense.extend hdense F) := by
    have hcl : LipschitzOnWith K (Dense.extend hdense F)
        (closure (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)))) :=
      hext_lip_s.closure (hext_cont.continuousOn)
    rw [hdense.closure_range] at hcl
    rwa [lipschitzOnWith_univ] at hcl

  refine ⟨K, ?_⟩
  have hretr : LipschitzWith 1 (recenteredBallRetraction
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀) :=
    recenteredBallRetraction_lipschitzWith hR₀.le _
  have hcomp : LipschitzWith (K * 1)
      ((Dense.extend hdense F) ∘ (recenteredBallRetraction
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀)) :=
    hext_lip.comp hretr
  rw [mul_one] at hcomp
  have heq_fun : deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a =
      (Dense.extend hdense F) ∘ (recenteredBallRetraction
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀) := by
    funext v
    rw [deTurckSobolevNonlinearity]
    rw [dif_pos h]
    rfl
  rw [heq_fun]
  exact hcomp

theorem deTurckSobolevNHa2_lipschitzOnWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (R : ℝ) (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) :
    ∃ L_R : ℝ≥0, LipschitzOnWith L_R (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a)
      (Metric.closedBall u₀ R) := by
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  exact ⟨K, hK.lipschitzOnWith⟩

theorem deTurckSobolevNHa2_eq_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))

  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2) with hdense_def
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
        (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le (Classical.choose x.2))) with hF_def

  obtain ⟨K, hK⟩ :=
    deTurckSmoothRemainderTensorHs_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR₀
      hδ₀_lt
  have hembed : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) =
          ballRetraction R₀ (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec x.2]
  have hF_cont : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := K) (fun x y => ?_)).continuous
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))‖ := hbound
      _ = (K : ℝ) * ‖ballRetraction R₀
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            ballRetraction R₀ (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [hembed x, hembed y]
      _ ≤ (K : ℝ) * ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg

  have hmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T ∈
      Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) := ⟨T, rfl⟩
  have hunfold : deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      Dense.extend hdense F
        (recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T)) := by
    rw [deTurckSobolevNonlinearity, dif_pos h]

  have hfix : recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T := by
    refine recenteredBallRetraction_eq_self_of_mem ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hball
  rw [hunfold, hfix, hdense.extend_eq hF_cont ⟨_, hmem⟩]

  change deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose hmem)) _ _ =
    deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super _ T _ _ _ _ ?_
  rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec hmem]
  exact ballRetraction_eq_self_of_mem hball

theorem deTurckSobolevNHa2_smoothEmbed_eq (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2) :
    deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a
          (Classical.choose (deTurckSobolevNHa2_exists_of_super
            (I := I) (M := M) g₀ a ha_super)).1 T)
        (lt_of_le_of_lt (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
          (I := I) (M := M) g₀ a ha_super)).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
        ((Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
          (I := I) (M := M) g₀ a ha_super)).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a
            (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
              (I := I) (M := M) g₀ a ha_super)).1.le T)) := by
  classical
  set h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super with hh
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  set S := radialScaleSmooth (I := I) (M := M) g₀ a R₀ T with hS_def
  have hSball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ :=
    norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le T
  have hSfibre := (Classical.choose_spec h).2.2 _ hSball
  have hSeq : deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S) =
        deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a S
          (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
          hSfibre :=
    deTurckSobolevNHa2_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super S
      (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
      hSfibre hSball
  have hbr : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S =
      recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
    rw [hS_def, smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction,
      recenteredBallRetraction, sub_zero, zero_add]
  have hSmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S ∈
      Metric.closedBall (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hSball
  have hrecS : recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S) =
        recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
    rw [recenteredBallRetraction_eq_self_of_mem hSmem, hbr]
  have hNeq : deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
        deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S) := by
    rw [deTurckSobolevNonlinearity, deTurckSobolevNonlinearity, dif_pos h, dif_pos h, hrecS]
  rw [hNeq, hSeq]


theorem exists_norm_smoothCcToTensorHs_symmS_le (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ≤
        C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖ := by
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀ n
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ n
  refine ⟨Ca * Cb, mul_nonneg hCa_nn hCb_nn, fun T => ?_⟩
  have h1 := hCa (ccTensor02Symm (I := I) (M := M) g₀ T)
  have hterm : ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ ≤
      ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
    Finset.sum_le_sum fun j _ => norm_iteratedCovGrad_tensorSymmetrization_le (I := I) (M := M) g₀ T j
  have h2 := hCb T
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) (ccTensor02Symm (I := I) (M := M) g₀ T)‖
      ≤ Ca * ∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)‖ := h1
    _ ≤ Ca * ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
        mul_le_mul_of_nonneg_left hterm hCa_nn
    _ ≤ Ca * (Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖) :=
        mul_le_mul_of_nonneg_left h2 hCa_nn
    _ = Ca * Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖ := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem symmS_eq_self_of_ccTensorBilin_symm (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x u w = smoothCcTensorBilinForm (I := I) g₀ S x w u) :
    ccTensor02Symm (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [ccTensor02Symm, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

open Classical in

def deTurckSobolevNonlinearitySymm (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun v =>
    if h : ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 ≤ deTurckArmContractionThresholdSharp (Module.finrank ℝ E) ∧
        ∀ (T : SmoothCcTensor g₀ 0 2),
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
          metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 then
      Dense.extend (smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2))
        (fun x =>
          deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
            (radialScaleSmooth (I := I) (M := M) g₀ a (Classical.choose h).1
              (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
            (lt_of_le_of_lt (Classical.choose_spec h).2.1
              (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
            ((Classical.choose_spec h).2.2 _
              (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
                g₀ a (Classical.choose_spec h).1.le
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))))
        v
    else 0

theorem deTurckSmoothN_symm_embedding_wellDefined (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T)) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T')) δ')
    (hTT' : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') :
    deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a (ccTensor02Symm (I := I) (M := M) g₀ T) hδ_lt hδ =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a (ccTensor02Symm (I := I) (M := M) g₀ T') hδ'_lt hδ' := by
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super
    (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T') hδ_lt hδ hδ'_lt hδ' ?_
  obtain ⟨Csym, hCsym_nn, hCsym⟩ :=
    exists_norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (a + 2)
  have hcast : ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
  have hkey := hCsym (T - T')
  rw [hcast] at hkey
  have hzero_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))‖ ≤ 0 := by
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))‖
        ≤ Csym * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ := hkey
      _ = Csym * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
          rw [smoothCcToTensorHs_sub]
      _ = 0 := by rw [hTT', sub_self, norm_zero, mul_zero]
  have hzero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) = 0 := by
    have h0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))‖ = 0 :=
      le_antisymm hzero_le (norm_nonneg _)
    rwa [norm_eq_zero] at h0
  have hsub : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ T) -
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ T') = 0 := by
    rw [← smoothCcToTensorHs_sub, ← symmS_sub]
    exact hzero
  exact sub_eq_zero.mp hsub

set_option maxHeartbeats 800000 in
theorem deTurckSobolevNHa2Symm_lipschitzWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ K : ℝ≥0, LipschitzWith K (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a) := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨K, hK⟩ :=
    deTurckSmoothRemainderTensorHs_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ₀_lt
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
        hδ₀_lt
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le
            (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))) with hF_def
  have hembed_rs : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2))) =
          ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2))) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction]
  have hF_lip : ∀ x y : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      ‖F x - F y‖ ≤ (K : ℝ) *
        ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (y : _)‖ := by
    intro x y
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2))) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := hbound
      _ = (K : ℝ) *
            ‖ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2))) -
              ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := by
            rw [hembed_rs x, hembed_rs y]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀
                (Classical.choose x.2 - Classical.choose y.2))‖ := by
            rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (Classical.choose x.2 - Classical.choose y.2)‖ :=
            mul_le_mul_of_nonneg_left
              (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _)
              K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose y.2)‖ := by
            rw [smoothCcToTensorHs_sub]
      _ = (K : ℝ) *
            ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [Classical.choose_spec x.2, Classical.choose_spec y.2]
  have hlipF : LipschitzWith K F := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    exact hF_lip x y
  have hF_cont : Continuous F := hlipF.continuous
  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
    with hdense_def
  have hext_eq : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      Dense.extend hdense F (x : _) = F x := fun x => hdense.extend_eq hF_cont x
  have hext_cont : Continuous (Dense.extend hdense F) :=
    (hdense.uniformContinuous_extend hlipF.uniformContinuous).continuous
  have hext_lip_s : LipschitzOnWith K (Dense.extend hdense F)
      (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr (fun p hp q hq => ?_)
    obtain ⟨xp, hxp⟩ := hp
    obtain ⟨xq, hxq⟩ := hq
    have hep : Dense.extend hdense F p = F ⟨p, ⟨xp, hxp⟩⟩ := by
      have := hext_eq ⟨p, ⟨xp, hxp⟩⟩; simpa using this
    have heq : Dense.extend hdense F q = F ⟨q, ⟨xq, hxq⟩⟩ := by
      have := hext_eq ⟨q, ⟨xq, hxq⟩⟩; simpa using this
    rw [dist_eq_norm, hep, heq, dist_eq_norm]
    exact hF_lip ⟨p, ⟨xp, hxp⟩⟩ ⟨q, ⟨xq, hxq⟩⟩
  have hext_lip : LipschitzWith K (Dense.extend hdense F) := by
    have hcl : LipschitzOnWith K (Dense.extend hdense F)
        (closure (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)))) :=
      hext_lip_s.closure (hext_cont.continuousOn)
    rw [hdense.closure_range] at hcl
    rwa [lipschitzOnWith_univ] at hcl
  refine ⟨K, ?_⟩
  have heq_fun : deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a =
      Dense.extend hdense F := by
    funext v
    change (dite _ _ _) = _
    rw [dif_pos h]
  rw [heq_fun]
  exact hext_lip

theorem deTurckSobolevNHa2Symm_eq_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T)) δ)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (ccTensor02Symm (I := I) (M := M) g₀ T) hδ_lt hδ := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨K, hK⟩ :=
    deTurckSmoothRemainderTensorHs_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ₀_lt
  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
    with hdense_def
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
        hδ₀_lt
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le
            (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))) with hF_def
  have hF_cont : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := K) (fun x y => ?_)).continuous
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2))) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := hbound
      _ = (K : ℝ) *
            ‖ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2))) -
              ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := by
            rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction,
              smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀
                  (Classical.choose x.2 - Classical.choose y.2))‖ := by
            rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2 - Classical.choose y.2)‖ :=
            mul_le_mul_of_nonneg_left
              (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _)
              K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose y.2)‖ := by
            rw [smoothCcToTensorHs_sub]
      _ = (K : ℝ) *
            ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [Classical.choose_spec x.2, Classical.choose_spec y.2]
  have hmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T ∈
      Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) := ⟨T, rfl⟩
  have hunfold : deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      Dense.extend hdense F
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
    change (dite _ _ _) = _
    rw [dif_pos h]
  rw [hunfold, hdense.extend_eq hF_cont ⟨_, hmem⟩]
  change deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem))) _ _ =
    deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a (ccTensor02Symm (I := I) (M := M) g₀ T) hδ_lt hδ
  have hchoose : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (Classical.choose hmem) = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
    Classical.choose_spec hmem
  have hsymm_eq : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem)) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ T) := by
    have hdiff_zero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (Classical.choose hmem - T) = 0 := by
      rw [smoothCcToTensorHs_sub, hchoose, sub_self]
    have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem - T))‖ ≤ 0 := by
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem - T))‖
          ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (Classical.choose hmem - T)‖ :=
            norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _
        _ = 0 := by rw [hdiff_zero, norm_zero]
    have hsymm_zero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem - T)) = 0 := by
      have h0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem - T))‖ = 0 :=
        le_antisymm hnorm_le (norm_nonneg _)
      rwa [norm_eq_zero] at h0
    have hsub : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem)) -
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T) = 0 := by
      rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      exact hsymm_zero
    exact sub_eq_zero.mp hsub
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super
    (radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem)))
    (ccTensor02Symm (I := I) (M := M) g₀ T) _ _ _ _ ?_
  rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, hsymm_eq]
  refine ballRetraction_eq_self_of_mem ?_
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ T)‖
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ :=
        norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) T
    _ ≤ R₀ := hball

theorem deTurckSobolevNHa2Symm_smoothEmbed_eq (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2) :
    deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a
          (Classical.choose (deTurckSobolevNHa2_exists_of_super
            (I := I) (M := M) g₀ a ha_super)).1
          (ccTensor02Symm (I := I) (M := M) g₀ T))
        (lt_of_le_of_lt (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
          (I := I) (M := M) g₀ a ha_super)).2.1
          (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
        ((Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
          (I := I) (M := M) g₀ a ha_super)).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a
            (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
              (I := I) (M := M) g₀ a ha_super)).1.le
            (ccTensor02Symm (I := I) (M := M) g₀ T))) := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨K, hK⟩ :=
    deTurckSmoothRemainderTensorHs_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ₀_lt
  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
    with hdense_def
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
        hδ₀_lt
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le
            (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))) with hF_def
  have hF_cont : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := K) (fun x y => ?_)).continuous
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2))) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := hbound
      _ = (K : ℝ) *
            ‖ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2))) -
              ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := by
            rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction,
              smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose x.2)))
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose y.2)))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀
                  (Classical.choose x.2 - Classical.choose y.2))‖ := by
            rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2 - Classical.choose y.2)‖ :=
            mul_le_mul_of_nonneg_left
              (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _)
              K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose y.2)‖ := by
            rw [smoothCcToTensorHs_sub]
      _ = (K : ℝ) *
            ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [Classical.choose_spec x.2, Classical.choose_spec y.2]
  have hmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T ∈
      Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) := ⟨T, rfl⟩
  have hunfold : deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      Dense.extend hdense F
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
    change (dite _ _ _) = _
    rw [dif_pos h]
  rw [hunfold, hdense.extend_eq hF_cont ⟨_, hmem⟩]
  change deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem))) _ _ =
    deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) _ _
  have hchoose : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (Classical.choose hmem) = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
    Classical.choose_spec hmem
  have hsymm_eq : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem)) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (ccTensor02Symm (I := I) (M := M) g₀ T) := by
    have hdiff_zero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (Classical.choose hmem - T) = 0 := by
      rw [smoothCcToTensorHs_sub, hchoose, sub_self]
    have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem - T))‖ ≤ 0 := by
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem - T))‖
          ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (Classical.choose hmem - T)‖ :=
            norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _
        _ = 0 := by rw [hdiff_zero, norm_zero]
    have hsymm_zero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem - T)) = 0 := by
      have h0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem - T))‖ = 0 :=
        le_antisymm hnorm_le (norm_nonneg _)
      rwa [norm_eq_zero] at h0
    have hsub : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem)) -
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T) = 0 := by
      rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      exact hsymm_zero
    exact sub_eq_zero.mp hsub
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super
    (radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (ccTensor02Symm (I := I) (M := M) g₀ (Classical.choose hmem)))
    (radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (ccTensor02Symm (I := I) (M := M) g₀ T)) _ _ _ _ ?_
  rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction,
    smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, hsymm_eq]

theorem deTurckSobolevNHa2Symm_eq_smoothN_of_symm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  have hEq : ccTensor02Symm (I := I) (M := M) g₀ T = T :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g₀ T hTsymm
  have h1 := deTurckSobolevNHa2Symm_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super T hδ_lt
    (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ T hδ) hball
  rw [h1]
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super
    (ccTensor02Symm (I := I) (M := M) g₀ T) T hδ_lt (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ T hδ)
    hδ_lt hδ ?_
  rw [hEq]

theorem deTurckSobolevNonlinearitySymm_mixed_lipschitz_pointwise
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ C₁ C₂ : ℝ≥0, ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a u -
          deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖ := by
  classical
  set hex := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super with hhex
  set R₀ := (Classical.choose hex).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec hex).1
  have hδ₀_lt : (Classical.choose hex).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec hex).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  set hτσ : (a : ℝ) + 1 ≤ (a : ℝ) + 2 := by linarith with hτσ_def
  set J := tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ with hJ_def
  obtain ⟨Csym1, hCsym1_nn, hCsym1⟩ :=
    exists_norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (a + 1)
  obtain ⟨Csym2, hCsym2_nn, hCsym2⟩ :=
    exists_norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (a + 2)
  have hcast1 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hcast2 : ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
  have hCsym1' : ∀ W : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1)
          (ccTensor02Symm (I := I) (M := M) g₀ W)‖ ≤
        Csym1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) W‖ := by
    intro W
    have hW := hCsym1 W
    rw [hcast1] at hW
    exact hW
  have hCsym2' : ∀ W : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ W)‖ ≤
        Csym2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) W‖ := by
    intro W
    have hW := hCsym2 W
    rw [hcast2] at hW
    exact hW
  have hRbig : 0 < (Csym2 + 1) * R₀ := mul_pos (by linarith) hR₀
  obtain ⟨K, hK⟩ :=
    deTurckSmoothRemainderTensorHs_ballLipschitz_dataWeighted_of_symm (I := I) (M := M) g₀ g_bg a ha_super
      hRbig hδ₀_lt
  have hRinv_nn : (0 : ℝ) ≤ 1 / R₀ := by positivity
  set C₂ : ℝ≥0 := K * Real.toNNReal Csym1 with hC₂_def
  set C₁ : ℝ≥0 := K * Real.toNNReal Csym1 * Real.toNNReal Csym2 +
    K * Real.toNNReal Csym1 * Real.toNNReal Csym2 * Real.toNNReal (1 / R₀) with hC₁_def
  have hC₂coe : (C₂ : ℝ) = (K : ℝ) * Csym1 := by
    rw [hC₂_def]
    push_cast
    rw [Real.coe_toNNReal _ hCsym1_nn]
  have hC₁coe : (C₁ : ℝ) =
      (K : ℝ) * Csym1 * Csym2 + (K : ℝ) * Csym1 * Csym2 * (1 / R₀) := by
    rw [hC₁_def]
    push_cast
    rw [Real.coe_toNNReal _ hCsym1_nn, Real.coe_toNNReal _ hCsym2_nn,
      Real.coe_toNNReal _ hRinv_nn]
  refine ⟨C₁, C₂, ?_⟩
  set D := Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) with hD_def
  have hDdense : Dense D := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
  set lhs : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) ×
      tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) → ℝ :=
    fun p => ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a p.1 -
      deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a p.2‖ with hlhs_def
  set rhs : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) ×
      tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) → ℝ :=
    fun p => (C₁ : ℝ) * max ‖J p.1‖ ‖J p.2‖ * ‖p.1 - p.2‖ +
      (C₂ : ℝ) * ‖J (p.1 - p.2)‖ with hrhs_def
  obtain ⟨KN, hKN⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hNcont : Continuous (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a) :=
    hKN.continuous
  have hlhs_cont : Continuous lhs := by
    rw [hlhs_def]
    exact ((hNcont.comp continuous_fst).sub (hNcont.comp continuous_snd)).norm
  have hrhs_cont : Continuous rhs := by
    rw [hrhs_def]
    refine Continuous.add ?_ ?_
    · refine (Continuous.mul ?_ ?_)
      · exact continuous_const.mul (((J.continuous.comp continuous_fst).norm).max
          ((J.continuous.comp continuous_snd).norm))
      · exact (continuous_fst.sub continuous_snd).norm
    · exact continuous_const.mul ((J.continuous.comp (continuous_fst.sub continuous_snd)).norm)
  have hclosed : IsClosed {p | lhs p ≤ rhs p} := isClosed_le hlhs_cont hrhs_cont
  have hsmooth : ∀ (T T' : SmoothCcTensor g₀ 0 2),
      lhs (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T,
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') ≤
      rhs (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T,
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') := by
    intro T T'
    have hccBilin_smul : ∀ (c : ℝ) (X : SmoothCcTensor g₀ 0 2)
        (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀ (c • X) x v w =
          c * smoothCcTensorBilinForm (I := I) g₀ X x v w := by
      intros c X x v w
      rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hRSSsymm : ∀ (Y : SmoothCcTensor g₀ 0 2)
        (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀
            (radialScaleSmooth (I := I) (M := M) g₀ a R₀
              (ccTensor02Symm (I := I) (M := M) g₀ Y)) x v w =
          smoothCcTensorBilinForm (I := I) g₀
            (radialScaleSmooth (I := I) (M := M) g₀ a R₀
              (ccTensor02Symm (I := I) (M := M) g₀ Y)) x w v := by
      intros Y x v w
      change smoothCcTensorBilinForm (I := I) g₀ (_ • ccTensor02Symm (I := I) (M := M) g₀ Y) x v w =
          smoothCcTensorBilinForm (I := I) g₀ (_ • ccTensor02Symm (I := I) (M := M) g₀ Y) x w v
      rw [hccBilin_smul, hccBilin_smul,
        bilinearForm_of_tensorSymmetrization_symm (I := I) (M := M) g₀ Y x v w]
    set S := radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (ccTensor02Symm (I := I) (M := M) g₀ T) with hS_def
    set S' := radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (ccTensor02Symm (I := I) (M := M) g₀ T') with hS'_def
    have hSball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ :=
      norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le
        (ccTensor02Symm (I := I) (M := M) g₀ T)
    have hS'ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ ≤ R₀ :=
      norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le
        (ccTensor02Symm (I := I) (M := M) g₀ T')
    have hSfibre := (Classical.choose_spec hex).2.2 _ hSball
    have hS'fibre := (Classical.choose_spec hex).2.2 _ hS'ball
    have hSballBig : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤
        (Csym2 + 1) * R₀ := by
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ := hSball
        _ ≤ (Csym2 + 1) * R₀ := by nlinarith [hCsym2_nn, hR₀.le]
    have hS'ballBig : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ ≤
        (Csym2 + 1) * R₀ := by
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ ≤ R₀ := hS'ball
        _ ≤ (Csym2 + 1) * R₀ := by nlinarith [hCsym2_nn, hR₀.le]
    have hNT := deTurckSobolevNHa2Symm_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super T
    have hNT' := deTurckSobolevNHa2Symm_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super T'
    have hbase := hK S S' (le_refl _) hSfibre (le_refl _) hS'fibre
      (hRSSsymm T) (hRSSsymm T') hSballBig hS'ballBig
    have hSembed : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S =
        ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T)) :=
      smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)
    have hS'embed : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S' =
        ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T')) :=
      smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction (I := I) (M := M) g₀ a R₀
        (ccTensor02Symm (I := I) (M := M) g₀ T')
    simp only [hlhs_def, hrhs_def]
    rw [hNT, hNT']
    refine le_trans hbase ?_
    set p := smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T with hp_def
    set p' := smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T' with hp'_def
    have hJembed : ∀ W : SmoothCcTensor g₀ 0 2,
        J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) W) =
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) W := by
      intro W
      rw [hJ_def]
      exact tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ hτσ W
    have hJscale : ∀ (q : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
        ‖J (ballRetraction R₀ q)‖ ≤ ‖J q‖ := by
      intro q
      rw [ballRetraction, map_smul, norm_smul, Real.norm_eq_abs]
      have hfac_nn : 0 ≤ min 1 (R₀ / ‖q‖) := le_min zero_le_one (by positivity)
      have hfac_le : min 1 (R₀ / ‖q‖) ≤ 1 := min_le_left _ _
      rw [abs_of_nonneg hfac_nn]
      calc min 1 (R₀ / ‖q‖) * ‖J q‖ ≤ 1 * ‖J q‖ :=
            mul_le_mul_of_nonneg_right hfac_le (norm_nonneg _)
        _ = ‖J q‖ := one_mul _
    have hJSymT : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ T))‖ ≤ Csym1 * ‖J p‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (ccTensor02Symm (I := I) (M := M) g₀ T))‖
          = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T)‖ := by rw [hJembed]
        _ ≤ Csym1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖ := hCsym1' T
        _ = Csym1 * ‖J p‖ := by rw [hJembed]
    have hJSymT' : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (ccTensor02Symm (I := I) (M := M) g₀ T'))‖ ≤ Csym1 * ‖J p'‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (ccTensor02Symm (I := I) (M := M) g₀ T'))‖
          = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T')‖ := by rw [hJembed]
        _ ≤ Csym1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ := hCsym1' T'
        _ = Csym1 * ‖J p'‖ := by rw [hJembed]
    have hmax1 : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖ ≤
        Csym1 * ‖J p‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
          = ‖J (ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T)))‖ := by rw [hSembed]
        _ ≤ ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T))‖ := hJscale _
        _ ≤ Csym1 * ‖J p‖ := hJSymT
    have hmax1' : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ ≤
        Csym1 * ‖J p'‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖
          = ‖J (ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T')))‖ := by rw [hS'embed]
        _ ≤ ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T'))‖ := hJscale _
        _ ≤ Csym1 * ‖J p'‖ := hJSymT'
    have hmaxle : max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
        ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ ≤
        Csym1 * max ‖J p‖ ‖J p'‖ :=
      max_le
        (hmax1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hCsym1_nn))
        (hmax1'.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hCsym1_nn))
    have hdistSymT_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T) -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (ccTensor02Symm (I := I) (M := M) g₀ T')‖ ≤ Csym2 * ‖p - p'‖ :=
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (ccTensor02Symm (I := I) (M := M) g₀ T) -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T')‖
          = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))‖ := by
              rw [← smoothCcToTensorHs_sub, ← symmS_sub]
        _ ≤ Csym2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ :=
              hCsym2' (T - T')
        _ = Csym2 * ‖p - p'‖ := by rw [smoothCcToTensorHs_sub]
    have hdistle : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ ≤ Csym2 * ‖p - p'‖ :=
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖
          = ‖ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T)) -
            ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T'))‖ := by rw [hSembed, hS'embed]
        _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T) -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T')‖ := by
              have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
                g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀ T))
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (ccTensor02Symm (I := I) (M := M) g₀ T'))
              rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
              exact hlip
        _ ≤ Csym2 * ‖p - p'‖ := hdistSymT_le
    have hmaxSymT_le : max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T))‖
        ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T'))‖ ≤ Csym1 * max ‖J p‖ ‖J p'‖ :=
      max_le
        (hJSymT.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hCsym1_nn))
        (hJSymT'.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hCsym1_nn))
    have hincl_diff_J : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T) -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (ccTensor02Symm (I := I) (M := M) g₀ T'))‖ ≤ Csym1 * ‖J (p - p')‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ T'))‖
            = ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))‖ := by
                rw [← smoothCcToTensorHs_sub, ← symmS_sub]
          _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1)
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))‖ := by rw [hJembed]
          _ ≤ Csym1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖ :=
                hCsym1' (T - T')
          _ = Csym1 * ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T'))‖ := by
                rw [hJembed]
          _ = Csym1 * ‖J (p - p')‖ := by rw [smoothCcToTensorHs_sub]
    have hincl : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ ≤
        Csym1 * ‖J (p - p')‖ +
          Csym1 * Csym2 * (1 / R₀) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖ := by
      have hRinv_le : (0 : ℝ) ≤ 1 / R₀ := hRinv_nn
      have hCsym1max_nn : 0 ≤ Csym1 * max ‖J p‖ ‖J p'‖ :=
        mul_nonneg hCsym1_nn (le_trans (norm_nonneg _) (le_max_left _ _))
      have hbr_diff := norm_map_ballRetraction_sub_le
        (X := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) hR₀ J
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T))
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g₀ T'))
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖
          = ‖J (ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T)) -
            ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (ccTensor02Symm (I := I) (M := M) g₀ T')))‖ := by rw [hSembed, hS'embed]
        _ ≤ _ := hbr_diff
        _ ≤ Csym1 * ‖J (p - p')‖ +
              (1 / R₀) * (Csym1 * max ‖J p‖ ‖J p'‖) * (Csym2 * ‖p - p'‖) := by
              apply add_le_add hincl_diff_J
              apply mul_le_mul _ hdistSymT_le (norm_nonneg _)
                (mul_nonneg hRinv_le hCsym1max_nn)
              exact mul_le_mul_of_nonneg_left hmaxSymT_le hRinv_le
        _ = Csym1 * ‖J (p - p')‖ +
              Csym1 * Csym2 * (1 / R₀) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖ := by ring
    have hmaxP_nn : 0 ≤ max ‖J p‖ ‖J p'‖ := le_trans (norm_nonneg _) (le_max_left _ _)
    have hCM_nn : 0 ≤ Csym1 * max ‖J p‖ ‖J p'‖ := mul_nonneg hCsym1_nn hmaxP_nn
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    have hstep1 : (K : ℝ) *
          (max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
              ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖) ≤
        (K : ℝ) * ((Csym1 * max ‖J p‖ ‖J p'‖) * (Csym2 * ‖p - p'‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hmaxle hdistle (norm_nonneg _) hCM_nn) hKnn
    have hstep2 : (K : ℝ) *
          ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ ≤
        (K : ℝ) * (Csym1 * ‖J (p - p')‖ +
          Csym1 * Csym2 * (1 / R₀) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖) :=
      mul_le_mul_of_nonneg_left hincl hKnn
    calc (K : ℝ) *
          (max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
              ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ +
          ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖)
        = (K : ℝ) *
            (max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
                ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
                smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖) +
          (K : ℝ) * ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ := by ring
      _ ≤ (K : ℝ) * ((Csym1 * max ‖J p‖ ‖J p'‖) * (Csym2 * ‖p - p'‖)) +
          (K : ℝ) * (Csym1 * ‖J (p - p')‖ +
            Csym1 * Csym2 * (1 / R₀) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖) :=
            add_le_add hstep1 hstep2
      _ = ((K : ℝ) * Csym1 * Csym2 + (K : ℝ) * Csym1 * Csym2 * (1 / R₀)) *
            max ‖J p‖ ‖J p'‖ * ‖p - p'‖ + ((K : ℝ) * Csym1) * ‖J (p - p')‖ := by ring
      _ = (C₁ : ℝ) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖ + (C₂ : ℝ) * ‖J (p - p')‖ := by
            rw [hC₁coe, hC₂coe]
  have hsub : (D ×ˢ D) ⊆ {p | lhs p ≤ rhs p} := by
    rintro ⟨p₁, p₂⟩ ⟨⟨T, hT⟩, ⟨T', hT'⟩⟩
    have := hsmooth T T'
    rw [hT, hT'] at this
    exact this
  have huniv : {p | lhs p ≤ rhs p} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (hDdense.prod hDdense).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  intro u u'
  have hmem : ((u, u') : _ × _) ∈ {p | lhs p ≤ rhs p} := by rw [huniv]; trivial
  have := hmem
  rw [Set.mem_setOf_eq, hlhs_def, hrhs_def] at this
  simpa only [hJ_def] using this

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
