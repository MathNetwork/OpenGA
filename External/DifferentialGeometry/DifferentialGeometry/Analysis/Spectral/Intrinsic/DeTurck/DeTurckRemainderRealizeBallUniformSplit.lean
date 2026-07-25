import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNorm

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

theorem deTurckPrincipalCometricArm_realize_ballUniform_Hs_norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ k, 0 ≤ Clower k) ∧
      ∀ (k : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  classical
  have ha1 : 1 ≤ a := by
    have h1 := Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
    omega
  obtain ⟨Clower, hCl_nn, hb⟩ :=
    exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_principal_le
      (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨fun k => Clower (a - 1 + k), fun k => hCl_nn _, fun k T₀ hball => ?_⟩
  have hσ : ((a - 1 + k : ℕ) : ℝ) = (a : ℝ) + (k : ℝ) - 1 := by
    have hs : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      rw [Nat.cast_sub ha1, Nat.cast_one]
    rw [Nat.cast_add, hs]; ring
  have hσ1 : ((a - 1 + k : ℕ) : ℝ) + 1 = (a : ℝ) + (k : ℝ) := by rw [hσ]; ring
  have hbk := hb (a - 1 + k) T₀ hball
  have h1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ hσ
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀
      (tensorSectionRealizeMetric (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀)
  have h2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ hσ
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)
  have h3 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ hσ1 T₀
  rw [h1, h2, h3] at hbk
  exact hbk

theorem deTurckPrincipalCometricArm_realize_ballUniform_Hs_inner_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ k, 0 ≤ Clower k) ∧
      ∀ (k : ℕ) (φ T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ)
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀)) : ℝ) ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ +
            Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ := by
  classical
  obtain ⟨Clower, hCl_nn, hnorm⟩ :=
    deTurckPrincipalCometricArm_realize_ballUniform_Hs_norm_le (I := I) (M := M)
      g₀ a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨Clower, hCl_nn, fun k φ T₀ hball => ?_⟩
  have hb := hnorm k T₀ hball
  have hCS := real_inner_le_norm
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ)
    (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) T₀))
  have hφ_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ :=
    norm_nonneg _
  calc (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ)
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)) T₀)) : ℝ)
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ := hCS
    _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ *
          (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) :=
        mul_le_mul_of_nonneg_left hb hφ_nn
    _ = deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ +
          Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ := by
        ring

theorem deTurckPrincipalCometricArm_realize_ballUniform_spectralShift_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ deTurckArmContractionThreshold (Module.finrank ℝ E))
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ k, 0 ≤ Clower k) ∧
      ∀ (k : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          (1 / 2 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
            Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  classical
  have hδ_le13 : δ ≤ 1 / 3 :=
    le_trans hδ_le (deTurckArmContractionThreshold_le_third' (Module.finrank ℝ E))
  obtain ⟨Clower, hCl_nn, hnorm⟩ :=
    deTurckPrincipalCometricArm_realize_ballUniform_Hs_norm_le (I := I) (M := M)
      g₀ a ha_super hR₀ hδ_le13 hδ_fibre
  refine ⟨Clower, hCl_nn, fun k T₀ hball => ?_⟩
  have hb := hnorm k T₀ hball
  have hhalf : deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) ≤ 1 / 2 :=
    deTurckArmFibreConst_mul_div_le_half
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))) hδ_le
  have hR_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ := norm_nonneg _
  have hRB : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ := by
    refine le_trans
      (smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀
        ((a : ℝ) + (k : ℝ) - 1) T₀) ?_
    exact le_of_eq (smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (show (a : ℝ) + (k : ℝ) - 1 + 2 = (a : ℝ) + (k : ℝ) + 1 by ring) T₀)
  have htop : deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      (1 / 2 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀
          ((a : ℝ) + (k : ℝ) + 1) T₀‖ :=
    mul_le_mul hhalf hRB hR_nn (by norm_num)
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le
              (deTurckArmContractionThreshold_lt_one' (Module.finrank ℝ E)))
            (hδ_fibre T₀ hball)) T₀)‖
      = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)) T₀)‖ := rfl
    _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
          Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ :=
        hb
    _ ≤ (1 / 2 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀
            ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
          Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
        have h2 : 0 ≤ Clower k *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ :=
          mul_nonneg (hCl_nn k) (norm_nonneg _)
        linarith [htop]

theorem deTurckSmoothRemainderDiff_ballUniform_spectralSplit_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ deTurckArmContractionThresholdSharp (Module.finrank ℝ E))
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.metricCauchySchwarzBound
        (I := I) (M := M) g₀
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.ccTensorBilinSymm
          (I := I) g₀ T₀) δ) :
    ∃ (Cδ₀ : ℝ) (Crem : ℕ → ℝ), 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ (∀ k, 0 ≤ Crem k) ∧
      ∀ (k : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀)))‖ ≤
          Cδ₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
            Crem k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hδ_le_thr : δ ≤ deTurckArmContractionThreshold n :=
    le_trans hδ_le (deTurckArmContractionThreshold''_le hn1)
  have hδ_le13 : δ ≤ 1 / 3 :=
    le_trans hδ_le (deTurckArmContractionThreshold''_le_third hn1)
  set Cbudget : ℝ :=
    32 * deTurckArmFibreConst n ^ 2 / (2 * (1 + 32 * deTurckArmFibreConst n ^ 2))
    with hCbudget_def
  have hCbudget_nn : 0 ≤ Cbudget := by rw [hCbudget_def]; positivity
  obtain ⟨εwrap, hεw_nn, hεw_cap, Cthird, Ctame, hCth_nn, hCt_nn, hmain⟩ :=
    exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame
      (I := I) (M := M) g₀ g_bg a (by omega) hR₀ hδ_le13 hδ_fibre
  obtain ⟨Clower, hCl_nn, harm⟩ :=
    deTurckPrincipalCometricArm_realize_ballUniform_spectralShift_le
      (I := I) (M := M) g₀ a ha_super hR₀ hδ_le_thr hδ_fibre
  refine ⟨1 / 2 + Cbudget, fun k => Cthird k + Ctame k + Clower k,
    by linarith, ?_, fun k => by have := hCth_nn k; have := hCt_nn k; have := hCl_nn k; linarith,
    fun k T₀ hTsymm hball => ?_⟩
  · rw [hCbudget_def]
    exact deTurckBudget_half_add_thirtyTwo_lt_one n
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
    simp only [norm_zero, mul_zero, add_zero]
    exact le_refl 0
  · have hδ_nn : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hεw_le : εwrap ≤ Cbudget := by
      refine le_trans (hεw_cap hδ_nn) ?_
      rw [hCbudget_def]
      exact deTurckArmFibreConst_cube_mul_div_le_thirtyTwo hn1 hδ_le
    obtain ⟨third, tame, hid, hthird, htame⟩ := hmain T₀ hTsymm hball
    have hb3 := hthird k
    have hbt := htame k
    have hbarm := harm k T₀ hball
    have hnn1 : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ :=
      norm_nonneg _
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
              (lt_of_le_of_lt hδ_le
                (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
              (hδ_fibre T₀ hball) -
            deTurckSmoothRemainder (I := I) g₀ g_bg
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le
                (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)))‖
        = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀
              + third + tame)‖ := by rw [show
            (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀))) =
            deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀
              + third + tame from hid]
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀)‖ +
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) third‖ +
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) tame‖ := by
          rw [smoothCcToTensorHs_add, smoothCcToTensorHs_add]
          exact le_trans (norm_add_le _ _) (by
            have := norm_add_le
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)) T₀))
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) third)
            linarith)
      _ ≤ ((1 / 2 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀
                ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
              Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) +
            (εwrap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
              Cthird k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) +
            Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
          have harm' : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀)‖ ≤
              (1 / 2 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀
                  ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
                Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀
                  ((a : ℝ) + (k : ℝ)) T₀‖ := hbarm
          exact add_le_add (add_le_add harm' hb3) hbt
      _ ≤ (1 / 2 + Cbudget) * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
            (Cthird k + Ctame k + Clower k) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
          have hε := mul_le_mul_of_nonneg_right hεw_le hnn1
          nlinarith [hε, norm_nonneg
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀)]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
