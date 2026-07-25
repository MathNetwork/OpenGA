import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Geometry.Flow.VectorField
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric
import DifferentialGeometry.Analysis.Parabolic.StrictParabolicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckShortTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckVFTimeFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckSolutionC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.GlobalFlowOnClosed
import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciTensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Naturality.LieDerivativeMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ChainRule
import Mathlib.Analysis.Calculus.Deriv.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.ConjugatingDiffeoFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.FlatInteriorRicciFlowPde
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.ConjugatingFlowProperties
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Integral.Connection

theorem ricci_flow_short_time_existence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
      g_fam 0 = g₀ ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor
              (I := I) (g_fam t) x v w) (Set.Ici 0) t) := by
  obtain ⟨T_DT, g_DT, hDT, hJ⟩ :=
    DifferentialGeometry.PDE.RicciFlow.deTurckRicci_solution_with_jointReg
      (I := I) (M := M) g₀ g₀
  obtain ⟨h_reg, h_smooth0, h_gram_DT, -, h_gramOnE0_DT, h_C2_DT⟩ :=
    deTurckRicci_chartRegularity_of_jointChartGramSmooth (I := I) g₀ T_DT g_DT hJ
  obtain ⟨hT_DT_pos, hDT_init, hDT_deriv⟩ := hDT
  have h_construct :
      ∃ T : ℝ, 0 < T ∧ ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
        g_fam 0 = g₀ ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
            (fun p : ℝ × M =>
              Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
            (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
            ((-2 : ℝ) *
              DifferentialGeometry.Integral.Connection.ricciTensor
                (I := I) (g_fam t) x v w) (Set.Ici 0) t) := by
    have hDT_deriv' : ∀ t ∈ Set.Ico (0 : ℝ) T_DT, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
          (deTurckRicciRHS (I := I) g₀ (g_DT t) x v w)
          (Set.Ici 0) t := hDT_deriv
    obtain ⟨T, hT0, hT_le, Φ_fam, hΦ0, hΦode, hΦorbit0, hΦmfderiv0,
        -, -, hΦjoint⟩ :=
      conjugating_diffeo_family_jointsmooth
        (I := I) g_DT g₀ T_DT hT_DT_pos h_smooth0
    have hΦode' : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
          (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT t) g₀ ((Φ_fam t : M → M) x)))) :=
      fun x t ht => hΦode x t ht
    have h_gram_DT_T : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      exact (h_gram_DT x₀ i j).mono
        (Set.prod_mono_left (Set.Ioo_subset_Ioo_right hT_le))
    have h_gramIcc_T : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      exact (hJ x₀ i j).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_gramOnE0_T : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ (chartAt H α).source) := by
      intro α i j
      exact (h_gramOnE0_DT α i j).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_C2_T : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      intro α i j k hk
      exact (h_C2_DT α i j k hk).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_reg_T : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g₀ q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
      h_reg.mono (Set.prod_mono_left (Set.Ioo_subset_Ioo_right hT_le))
    obtain ⟨hΦ_orbit, hΦ_total⟩ :=
      conjugating_flow_orbit_pushforward_continuity_data (I := I) g_DT g₀ T hT0 Φ_fam hΦode'
        h_reg_T hΦorbit0 hΦmfderiv0
    have h_gram_fam :=
      conjugating_flow_pullback_jointGram_onesided (I := I) g_DT T Φ_fam hΦjoint h_gramIcc_T
    refine ⟨T, hT0, fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s),
      ?_, h_gram_fam, ?_⟩
    · change Diffeomorph.pullbackMetric (g_DT 0) (Φ_fam 0) = g₀
      rw [hΦ0, Diffeomorph.pullbackMetric_refl, hDT_init]
    · have hDT_deriv_Ico : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
          HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
            (deTurckRicciRHS (I := I) g₀ (g_DT s) y a b) (Set.Ici 0) s := by
        intro s hs y a b
        exact hDT_deriv' s ⟨hs.1, lt_of_lt_of_le hs.2 hT_le⟩ y a b
      have h_interior :=
        conjugating_flow_flat_data (I := I) g_DT g₀ T Φ_fam hDT_deriv_Ico hΦode h_reg_T
          h_gram_DT_T
      intro t ht x v w
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · obtain ⟨h_cont, h_ric_cont⟩ :=
          conjugating_flow_t0_continuity_data (I := I) g_DT g₀ T hT0 Φ_fam hΦode
            hΦ0 hDT_init h_gramOnE0_T h_C2_T hΦ_orbit hΦ_total x v w
        subst_vars
        exact DifferentialGeometry.PDE.RicciFlow.ricci_flow_pde_at_zero
          (I := I) (fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) hT0 x v w
          h_cont h_ric_cont (fun s hs => h_interior s hs x v w)
      · exact h_interior t ⟨h0, ht.2⟩ x v w
  exact h_construct

#print axioms ricci_flow_short_time_existence
theorem short_time_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
      g_fam 0 = g₀ ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor
              (I := I) (g_fam t) x v w) (Set.Ici 0) t) := by
  obtain ⟨T_DT, g_DT, hDT, hJ⟩ :=
    DifferentialGeometry.PDE.RicciFlow.deTurckRicci_solution_with_jointReg
      (I := I) (M := M) g₀ g₀
  obtain ⟨h_reg, h_smooth0, h_gram_DT, -, h_gramOnE0_DT, h_C2_DT⟩ :=
    deTurckRicci_chartRegularity_of_jointChartGramSmooth (I := I) g₀ T_DT g_DT hJ
  obtain ⟨hT_DT_pos, hDT_init, hDT_deriv⟩ := hDT
  have h_construct :
      ∃ T : ℝ, 0 < T ∧ ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
        g_fam 0 = g₀ ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
            (fun p : ℝ × M =>
              Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
            (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
            ((-2 : ℝ) *
              DifferentialGeometry.Integral.Connection.ricciTensor
                (I := I) (g_fam t) x v w) (Set.Ici 0) t) := by
    have hDT_deriv' : ∀ t ∈ Set.Ico (0 : ℝ) T_DT, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
          (deTurckRicciRHS (I := I) g₀ (g_DT t) x v w)
          (Set.Ici 0) t := hDT_deriv
    obtain ⟨T, hT0, hT_le, Φ_fam, hΦ0, hΦode, hΦorbit0, hΦmfderiv0,
        -, -, hΦjoint⟩ :=
      conjugating_diffeo_family_jointsmooth
        (I := I) g_DT g₀ T_DT hT_DT_pos h_smooth0
    have hΦode' : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
          (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT t) g₀ ((Φ_fam t : M → M) x)))) :=
      fun x t ht => hΦode x t ht
    have h_gram_DT_T : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      exact (h_gram_DT x₀ i j).mono
        (Set.prod_mono_left (Set.Ioo_subset_Ioo_right hT_le))
    have h_gramIcc_T : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      exact (hJ x₀ i j).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_gramOnE0_T : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ (chartAt H α).source) := by
      intro α i j
      exact (h_gramOnE0_DT α i j).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_C2_T : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      intro α i j k hk
      exact (h_C2_DT α i j k hk).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_reg_T : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g₀ q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
      h_reg.mono (Set.prod_mono_left (Set.Ioo_subset_Ioo_right hT_le))
    obtain ⟨hΦ_orbit, hΦ_total⟩ :=
      conjugating_flow_orbit_pushforward_continuity_data (I := I) g_DT g₀ T hT0 Φ_fam hΦode'
        h_reg_T hΦorbit0 hΦmfderiv0
    have h_gram_fam :=
      conjugating_flow_pullback_jointGram_onesided (I := I) g_DT T Φ_fam hΦjoint h_gramIcc_T
    refine ⟨T, hT0, fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s),
      ?_, h_gram_fam, ?_⟩
    · change Diffeomorph.pullbackMetric (g_DT 0) (Φ_fam 0) = g₀
      rw [hΦ0, Diffeomorph.pullbackMetric_refl, hDT_init]
    · have hDT_deriv_Ico : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
          HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
            (deTurckRicciRHS (I := I) g₀ (g_DT s) y a b) (Set.Ici 0) s := by
        intro s hs y a b
        exact hDT_deriv' s ⟨hs.1, lt_of_lt_of_le hs.2 hT_le⟩ y a b
      have h_interior :=
        conjugating_flow_flat_data (I := I) g_DT g₀ T Φ_fam hDT_deriv_Ico hΦode h_reg_T
          h_gram_DT_T
      intro t ht x v w
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · obtain ⟨h_cont, h_ric_cont⟩ :=
          conjugating_flow_t0_continuity_data (I := I) g_DT g₀ T hT0 Φ_fam hΦode
            hΦ0 hDT_init h_gramOnE0_T h_C2_T hΦ_orbit hΦ_total x v w
        subst_vars
        exact DifferentialGeometry.PDE.RicciFlow.ricci_flow_pde_at_zero
          (I := I) (fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) hT0 x v w
          h_cont h_ric_cont (fun s hs => h_interior s hs x v w)
      · exact h_interior t ⟨h0, ht.2⟩ x v w
  exact h_construct


end DifferentialGeometry.PDE.RicciFlow
