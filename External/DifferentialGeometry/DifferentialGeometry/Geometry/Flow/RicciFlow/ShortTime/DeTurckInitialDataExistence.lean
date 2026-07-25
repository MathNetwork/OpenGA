import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRealizedSolutionFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.QuasilinearAbstractShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm domDomCongrSection)

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private theorem rawTensorConnLapSmooth_symmS
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) =
      ccTensor02Symm (I := I) (M := M) g₀ (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
  have hhalf : ∀ W : SmoothCcTensor g₀ 0 2,
      (1 / 2 : ℝ) • W + (1 / 2 : ℝ) • W = W := fun W => by
    rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
  have hzero : rawTensorConnLapSmooth (I := I) g₀ 0 2 (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 S S
    rwa [sub_self, sub_self] at h
  have hadd : ∀ A B : SmoothCcTensor g₀ 0 2,
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (A + B) =
        rawTensorConnLapSmooth (I := I) g₀ 0 2 A +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 B := by
    intro A B
    have hAB : A + B = A - (0 - B) := by rw [zero_sub, sub_neg_eq_add]
    rw [hAB, rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 A (0 - B),
      rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 0 B, hzero, zero_sub, sub_neg_eq_add]
  have hLV : rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) =
      rawTensorConnLapSmooth (I := I) g₀ 0 2 S +
        domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
    rw [← hadd, ccTensor02Symm, hhalf, hadd,
      rawTensorConnLapSmooth_domDomCongrSection (I := I) (M := M) g₀
        (Equiv.swap (0 : Fin 2) 1) S]
  have hgoal : ccTensor02Symm (I := I) (M := M) g₀ (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) =
      (1 / 2 : ℝ) • (rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) +
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S)) := by
    rw [ccTensor02Symm, ← hLV]
  rw [hgoal, smul_add, hhalf]

theorem deTurckRicci_solution_with_jointReg
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  have ha_super : 2 * Module.finrank ℝ E + 10 ≤ 4 * Module.finrank ℝ E + 10 := by omega
  have hRepr : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ S) δ)
      (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀
          (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
              (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ) +
            rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w := by
    intro S δ hδ_lt hδ x v w
    have hlap : ccTensorBilinSymm (I := I) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        ccTensorBilinSymm (I := I) g₀
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S)) x v w := by
      rw [rawTensorConnLapSmooth_symmS (I := I) (M := M) g₀ S,
        symmetricBilinearForm_of_tensorSymmetrization_eq_self (I := I) (M := M) g₀
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w]
    rw [ccTensorBilinSymm_add (I := I) g₀
        (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
          (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ))
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w,
      hlap,
      ← ccTensorBilinSymm_add (I := I) g₀
        (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
          (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ))
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S)) x v w]
    set gDT := tensorSectionRealizeMetric (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
      (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ) with hgDT_def
    set R : SmoothCcTensor g₀ 0 2 :=
      { toSection := (deTurckRHSSection (I := I) g_bg gDT).toSection
        hasCompactSupport := (deTurckRHSSection (I := I) g_bg gDT).hasCompactSupport }
      with hR_def
    have hsum_eq : deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
        (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ) +
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) = R := by
      rw [deTurckSmoothRemainder, sub_add_cancel]
    rw [hsum_eq,
      ccTensorBilinSymm_toSection_congr R (deTurckRHSSectionBg (I := I) g_bg gDT)
        (by rw [hR_def, deTurckRHSSectionBg_toSection]) x v w]
    have hreal : gDT = tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ :=
      tensorSectionRealizeMetric_symmS_eq (I := I) g₀ S hδ_lt hδ hδ_lt
        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ)
    rw [← hreal]
    exact deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS (I := I) g_bg gDT x v w
  exact quasilinear_strictlyParabolic_2ndOrder_shortTimeExistence (I := I)
    (deTurckRicciRHS (I := I) g_bg) g₀ (4 * Module.finrank ℝ E + 10) ha_super rfl
    (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg (4 * Module.finrank ℝ E + 10))
    (fun S {δ} hδ_lt hδ => deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
      (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ))
    (fun g x v w => deTurckRicciRHS_symm (I := I) g_bg g x v w)
    (deTurckRicciRHS_isStrictlyParabolic_at_self (I := I) g₀ g_bg)
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      (4 * Module.finrank ℝ E + 10) ha_super)
    (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
      (g_bg := g_bg) (4 * Module.finrank ℝ E + 10) ha_super)
    (deTurckRicciRHS_isSmoothQuasilinear (I := I) g_bg)
    hRepr
    (deTurckRicci_forcingBootstrap_symm (I := I) (M := M) g₀ g_bg
      (4 * Module.finrank ℝ E + 10) (by omega))

theorem deturck_ricci_flow_parabolic_short_time_existence
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ (chartAt H α).source)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) := by
  obtain ⟨T, g_DT, hsol, hJ⟩ := deTurckRicci_solution_with_jointReg (I := I) g₀ g_bg
  obtain ⟨h2, h3, h4, h5, h6, h7⟩ :=
    deTurckRicci_chartRegularity_of_jointChartGramSmooth (I := I) g_bg T g_DT hJ
  exact ⟨T, g_DT, hsol, h2, h3, h4, h5, h6, h7⟩

end DifferentialGeometry.PDE.RicciFlow
