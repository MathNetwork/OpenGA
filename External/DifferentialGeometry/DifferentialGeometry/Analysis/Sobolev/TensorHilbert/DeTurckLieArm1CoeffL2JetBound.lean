import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffPieceConnDiffFeed
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffKappaPsiBFeed
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffPointwiseIdentity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open TensorMultilinear
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam convexPerturbation
  convexPerturbation_gFibreOpBound realizedFam_inner_of_mem Icc_subset_realizedSmallSet)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM metricComparisonEndo
  gInvRaisedEndo_apply gInvRaisedEndo_eq_diff_add_id metricComparisonDiffEndo
  cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieArm1Coeff_eq_lieArm1Piece_sum (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
        + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀)
          - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hCLM : ∀ D : Tensor0SSpace 3 I x,
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
      (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)
          + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀))
          + (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
              (connDiffSection (I := I) g₁ g₀)
            - deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
              (connDiffSection (I := I) g₁ g₀))
          + deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
              (connDiffSection (I := I) g₁ g₀)).toSection x) D := by
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ) (I := I) (s := 2) (x := x)
    change Tensor0SSpace.toModel _ = Tensor0SSpace.toModel _
    apply ContinuousMultilinearMap.ext
    intro w
    exact lieArm1_coeff_pieces_pointwise (I := I) (M := M) g₀ g₁ g_bg x D
      (fun j : Fin 2 => ((w j : E) : TangentSpace I x))
  exact ContinuousLinearMap.ext hCLM

theorem lieArm1Piece_connDiff_realizedFam_jetL2_perOrder_ballUniform
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2 ≤
            P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨C2, hC2_nn, hC2⟩ := lieArm1_twoArm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * Λcd) * (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Fcd i))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · exact mul_nonneg (mul_nonneg (by positivity) hΛcd_nn)
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · exact mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (hFcd_nn i))
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hcd0, hcdL2⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieArm1_normSq_icg_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              g₀))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hcd0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * Fcd i := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hcdL2 i hi) (by positivity)
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd))
        (∑ n ∈ Finset.range (i + 1), Q n) ((Module.finrank ℝ E : ℝ) ^ 2 * Fcd i)
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
  · haveI hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)))
    rw [h0]
    norm_num

theorem lieArm1Piece_connDiffBg_realizedFam_jetL2_perOrder_ballUniform
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
    obtain ⟨C2, hC2_nn, hC2⟩ := lieArm1_twoArm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)) *
            (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i +
              2 * ∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2)))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · refine mul_nonneg (mul_nonneg (by positivity) (by linarith))
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · refine mul_nonneg hΛcom_nn (mul_nonneg (by positivity) ?_)
        have h1 : (0 : ℝ) ≤ Fcd i := hFcd_nn i
        have h2 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 :=
          Finset.sum_nonneg fun l _ => sq_nonneg _
        linarith
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hcd0, hcdL2⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hΨ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((lieArm1ConnDiffBgCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
          2 * Λcd + 2 * Λfx := by
        intro x
        rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
        refine le_trans (lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 1 2 _ _ x) ?_
        have h1 := hcd0 x
        have h2 := hΛfx x
        linarith
      have hΨL2 : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 l
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
          2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 +
              2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := by
          intro l _
          rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
          exact lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 1 2 l _ _
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have h1 := mul_le_mul_of_nonneg_left (hcdL2 i hi) (by norm_num : (0:ℝ) ≤ 2)
        linarith
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieArm1_normSq_icg_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hΨ0_nn : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx))) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hΨ0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hΨL2 (by positivity)
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom)
        (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)))
        (∑ n ∈ Finset.range (i + 1), Q n)
        ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Fcd i + 2 * ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 2 l
            (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2))
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom)
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
  · haveI hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
    rw [h0]
    norm_num

theorem lieArm1Piece_psiB_realizedFam_jetL2_perOrder_ballUniform
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1PsiB (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ P i := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Q, hQ_nn, hQ⟩ :=
      traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λpb, Fpb, hΛpb_nn, hFpb_nn, hpb⟩ :=
      lieArm1_psiB_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
    obtain ⟨C2, hC2_nn, hC2⟩ := lieArm1_twoArm_top_fn (I := I) (M := M) g₀ a
    refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
        (C2 i * (((Module.finrank ℝ E : ℝ) ^ 2 * Λpb) * (∑ n ∈ Finset.range (i + 1), Q n)
          + Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Fpb i))), ?_, ?_⟩
    · intro i
      refine mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hC2_nn i) (add_nonneg ?_ ?_))
      · exact mul_nonneg (mul_nonneg (by positivity) hΛpb_nn)
          (Finset.sum_nonneg fun n _ => hQ_nn n)
      · exact mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (hFpb_nn i))
    · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
      haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      obtain ⟨hpb0, hpbL2⟩ := hpb (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          ∑ n ∈ Finset.range (i + 1), Q n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn_le : n ≤ a := by have := Finset.mem_range.mp hn; omega
        rw [lieArm1_normSq_icg_dLTC_eq]
        exact hQ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball n hn_le s hs
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (lieArm1PsiB (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        exact mul_le_mul_of_nonneg_left (hpb0 x) (by positivity)
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (lieArm1PsiB (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * Fpb i := by
        refine le_trans (Finset.sum_le_sum fun l _ =>
          lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hpbL2 i hi) (by positivity)
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (lieArm1PsiB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb))
        (∑ n ∈ Finset.range (i + 1), Q n) ((Module.finrank ℝ E : ℝ) ^ 2 * Fpb i)
        (hC2_nn i) hFS hFT
        (hC2 i hi _ _ (Real.sqrt Λcom) (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
  · haveI hIsE := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs
    have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
      (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
          (lieArm1PsiB (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
    rw [h0]
    norm_num

theorem lieArm1Piece_connDiff_realizedFam_rfns_order0_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
                  g₀)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Λcd),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) hΛcd_nn), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    haveI := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hcd0, _⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieArm1_piece_rfns_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieArm1_rfns_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            g₀).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Λcd :=
      mul_le_mul_of_nonneg_left (hcd0 x) (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · haveI hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

theorem lieArm1Piece_connDiffBg_realizedFam_rfns_order0_ballUniform
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
      lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
    obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
      exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
        (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx)),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) (by linarith)), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    haveI := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hcd0, _⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieArm1_piece_rfns_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieArm1_rfns_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have hΨ0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((lieArm1ConnDiffBgCc (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        2 * Λcd + 2 * Λfx := by
      rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
      refine le_trans (lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 1 2 _ _ x) ?_
      have h2 := hcd0 x
      have h3 := hΛfx x
      linarith
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((lieArm1ConnDiffBgCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * (2 * Λcd + 2 * Λfx) :=
      mul_le_mul_of_nonneg_left hΨ0 (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · haveI hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

theorem lieArm1Piece_psiB_realizedFam_rfns_order0_ballUniform
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (lieArm1PsiB (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤ Λ := by
  by_cases hM : Nonempty M
  · obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
      exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
        ha_super hR hδ₀
    obtain ⟨Λpb, Fpb, hΛpb_nn, hFpb_nn, hpb⟩ :=
      lieArm1_psiB_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
    refine ⟨Λcom * ((Module.finrank ℝ E : ℝ) ^ 2 * Λpb),
      mul_nonneg hΛcom_nn (mul_nonneg (by positivity) hΛpb_nn), ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x
    haveI := hM
    obtain ⟨htie, hδP, hδP_le⟩ :=
      lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
    have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
      lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
    have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
      hTball hT'ball hs
    obtain ⟨hpb0, _⟩ := hpb (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
    refine le_trans (lieArm1_piece_rfns_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
      (lieArm1PsiB (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) x) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckLieTraceCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤ Λcom := by
      rw [lieArm1_rfns_dLTC_toSection_eq]
      exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
    have h2 : (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((lieArm1PsiB (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Λpb :=
      mul_le_mul_of_nonneg_left (hpb0 x) (by positivity)
    refine mul_le_mul h1 h2 ?_ hΛcom_nn
    exact mul_nonneg (by positivity)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _)
  · haveI hIsE := not_nonempty_iff.mp hM
    exact ⟨0, le_rfl, fun T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ s hs x =>
      (hIsE.false x).elim⟩

private theorem lieArm1_norm_block6_le {V : Type*} [SeminormedAddCommGroup V]
    (b1 b2 b3 b4 b5 b6 : V) :
    ‖b1 - b2 - b3 - b4 - b5 - b6‖ ≤ ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by
  calc ‖b1 - b2 - b3 - b4 - b5 - b6‖
      ≤ ‖b1 - b2 - b3 - b4 - b5‖ + ‖b6‖ := norm_sub_le _ _
    _ ≤ (‖b1 - b2 - b3 - b4‖ + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2 - b3 - b4) b5
        linarith
    _ ≤ ((‖b1 - b2 - b3‖ + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2 - b3) b4
        linarith
    _ ≤ (((‖b1 - b2‖ + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2) b3
        linarith
    _ ≤ ((((‖b1‖ + ‖b2‖) + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le b1 b2
        linarith
    _ = ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by ring

private theorem lieArm1_norm_block6_le' {V : Type*} [SeminormedAddCommGroup V]
    (b1 b2 b3 b4 b5 b6 : V) :
    ‖b1 + b2 - b3 - b4 - b5 - b6‖ ≤ ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by
  calc ‖b1 + b2 - b3 - b4 - b5 - b6‖
      ≤ ‖b1 + b2 - b3 - b4 - b5‖ + ‖b6‖ := norm_sub_le _ _
    _ ≤ (‖b1 + b2 - b3 - b4‖ + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2 - b3 - b4) b5
        linarith
    _ ≤ ((‖b1 + b2 - b3‖ + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2 - b3) b4
        linarith
    _ ≤ (((‖b1 + b2‖ + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2) b3
        linarith
    _ ≤ ((((‖b1‖ + ‖b2‖) + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_add_le b1 b2
        linarith
    _ = ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by ring

private theorem lieArm1_norm_sq_le_of_norm_le {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {S : ℝ} (h : ‖v‖ ≤ S) : ‖v‖ ^ 2 ≤ S ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg v) h 2

private theorem lieArm1_norm_le_sqrt {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {P : ℝ} (h : ‖v‖ ^ 2 ≤ P) : ‖v‖ ≤ Real.sqrt P := by
  have h1 : ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
  rw [h1]
  exact Real.sqrt_le_sqrt h

theorem deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform
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
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieArm1Coeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  obtain ⟨Pc, hPc_nn, hPc⟩ :=
    lieArm1Piece_connDiff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Pbg, hPbg_nn, hPbg⟩ :=
    lieArm1Piece_connDiffBg_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Pb, hPb_nn, hPb⟩ :=
    lieArm1Piece_psiB_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨fun i => (11 * Real.sqrt (Pc i) + 2 * Real.sqrt (Pb i) + Real.sqrt (Pbg i)) ^ 2,
    fun i => sq_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ (connDiffSection (I := I) g₁ g₀))‖ ≤
        Real.sqrt (Pc i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  have hbg : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pbg i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pb i) := fun σ' ρ =>
    lieArm1_norm_le_sqrt (hPb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i hi s hs)
  rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg]
  simp only [iteratedCovGrad_add, iteratedCovGrad_sub]
  refine lieArm1_norm_sq_le_of_norm_le ?_
  have hsqrtPc_nn : 0 ≤ Real.sqrt (Pc i) := Real.sqrt_nonneg _
  have hsqrtPb_nn : 0 ≤ Real.sqrt (Pb i) := Real.sqrt_nonneg _
  have hblock1 := lieArm1_norm_block6_le'
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have hblock2 := lieArm1_norm_block6_le'
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have htri1 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
  have htri2 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have htri3 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have h1 := hcd lieArm1SigmaA (Equiv.refl (Fin 3))
  have h2 := hpb lieArm1SigmaA (Equiv.refl (Fin 3))
  have h3 := hcd lieArm1SigmaC (Equiv.refl (Fin 3))
  have h4 := hcd lieArm1SigmaD lieArm1RhoSlot0
  have h5 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have h6 := hcd lieArm1SigmaF (Equiv.refl (Fin 3))
  have h7 := hcd lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h8 := hpb lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h9 := hcd lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have h10 := hcd lieArm1SigmaDSwap lieArm1RhoSlot0
  have h11 := hcd lieArm1SigmaESwap lieArm1RhoSlot1
  have h12 := hcd lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have h13 := hbg lieArm1SigmaC lieArm1RhoSlot0
  have h14 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  linarith [htri1, htri2, htri3, hblock1, hblock2]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_rfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  rw [sub_eq_add_neg]
  have h := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)
  rw [lieArm1_rfns_neg (I := I) (M := M) g r s x b] at h
  exact h

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_rfns_block6_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (b1 b2 b3 b4 b5 b6 : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (b1 - b2 - b3 - b4 - b5 - b6) ≤
      32 * riemannianFiberNormSq (I := I) (M := M) g r s x b1 +
        32 * riemannianFiberNormSq (I := I) (M := M) g r s x b2 +
        16 * riemannianFiberNormSq (I := I) (M := M) g r s x b3 +
        8 * riemannianFiberNormSq (I := I) (M := M) g r s x b4 +
        4 * riemannianFiberNormSq (I := I) (M := M) g r s x b5 +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b6 := by
  have h6 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3 - b4 - b5) b6
  have h5 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3 - b4) b5
  have h4 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2 - b3) b4
  have h3 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 - b2) b3
  have h2 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x b1 b2
  have hn5 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b5
  have hn6 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b6
  linarith

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lieArm1_rfns_block6_le' (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (b1 b2 b3 b4 b5 b6 : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (b1 + b2 - b3 - b4 - b5 - b6) ≤
      32 * riemannianFiberNormSq (I := I) (M := M) g r s x b1 +
        32 * riemannianFiberNormSq (I := I) (M := M) g r s x b2 +
        16 * riemannianFiberNormSq (I := I) (M := M) g r s x b3 +
        8 * riemannianFiberNormSq (I := I) (M := M) g r s x b4 +
        4 * riemannianFiberNormSq (I := I) (M := M) g r s x b5 +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b6 := by
  have h6 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3 - b4 - b5) b6
  have h5 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3 - b4) b5
  have h4 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 + b2 - b3) b4
  have h3 := lieArm1_rfns_sub_le (I := I) (M := M) g r s x (b1 + b2) b3
  have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x b1 b2
  have hn5 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b5
  have hn6 := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x b6
  linarith

theorem deTurckLieArm1Coeff_realizedFam_rfns_order0_ballUniform
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
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((deTurckLieArm1Coeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λc, hΛc_nn, hΛc⟩ :=
    lieArm1Piece_connDiff_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Λbg, hΛbg_nn, hΛbg⟩ :=
    lieArm1Piece_connDiffBg_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Λb, hΛb_nn, hΛb⟩ :=
    lieArm1Piece_psiB_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨8 * Λbg + 800 * Λc + 400 * Λb, by linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' ρ
          (connDiffSection (I := I) g₁ g₀)).toSection x) ≤ Λc := fun σ' ρ =>
    hΛc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ s hs x
  have hbg : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
      ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λbg :=
    hΛbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball lieArm1SigmaC lieArm1RhoSlot0 s hs x
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ σ' (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ Λb := fun σ' =>
    hΛb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' (Equiv.refl (Fin 3)) s hs x
  have hsec := congrArg (fun (W : SmoothCcTensor g₀ 3 2) =>
      (show TensorRSSpace 3 2 I x from W.toSection x))
    (deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg)
  simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply] at hsec
  rw [hsec]
  set A := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
      (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set B1 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B2 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set B3 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B4 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B5 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set B6 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C1 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C2 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
      (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
  set C3 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C4 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C5 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set C6 := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  set Dz := (show TensorRSSpace 3 2 I x from
    (deTurckLieTraceCoeffPiece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
      (connDiffSection (I := I) g₁ g₀)).toSection x)
  have houter1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    (A + (B1 + B2 - B3 - B4 - B5 - B6) + (C1 + C2 - C3 - C4 - C5 - C6)) Dz
  have houter2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    (A + (B1 + B2 - B3 - B4 - B5 - B6)) (C1 + C2 - C3 - C4 - C5 - C6)
  have houter3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 2 x
    A (B1 + B2 - B3 - B4 - B5 - B6)
  have hblkB := lieArm1_rfns_block6_le' (I := I) (M := M) g₀ 3 2 x B1 B2 B3 B4 B5 B6
  have hblkC := lieArm1_rfns_block6_le' (I := I) (M := M) g₀ 3 2 x C1 C2 C3 C4 C5 C6
  have e1 := hcd lieArm1SigmaA (Equiv.refl (Fin 3))
  have e2 := hpb lieArm1SigmaA
  have e3 := hcd lieArm1SigmaC (Equiv.refl (Fin 3))
  have e4 := hcd lieArm1SigmaD lieArm1RhoSlot0
  have e5 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have e6 := hcd lieArm1SigmaF (Equiv.refl (Fin 3))
  have e7 := hcd lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have e8 := hpb lieArm1SigmaASwap
  have e9 := hcd lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have e10 := hcd lieArm1SigmaDSwap lieArm1RhoSlot0
  have e11 := hcd lieArm1SigmaESwap lieArm1RhoSlot1
  have e12 := hcd lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have e14 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  linarith [houter1, houter2, houter3, hblkB, hblkC, hbg, hΛc_nn, hΛb_nn, hΛbg_nn]

end DifferentialGeometry.Integral.Connection

end
