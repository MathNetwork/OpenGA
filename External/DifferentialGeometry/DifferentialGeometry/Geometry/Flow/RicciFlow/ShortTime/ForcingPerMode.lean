import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold







namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedVariables false in































omit [BoundarylessManifold I M] in
theorem forcing_continuous_interior
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (u₁ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) (R : ℝ)
    (hu₁ : ∀ s, u₁ s = tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (hN_cont : Continuous N_cont)
    (repr : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2)
    (Nsec : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
          (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g_bg (repr u) x v w)
    (hrepr_small : ∀ u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      ∃ δ' : ℝ, δ' < 1 ∧
        metricCauchySchwarzBound (I := I) (M := M) g_bg
          (ccTensorBilinSymm (I := I) g_bg (repr u)) δ')
    (hcont : ∀ ε : ℝ, 0 < ε → ContinuousOn u₁ (Set.Icc ε T))
    (hball : ∀ ε : ℝ, 0 < ε → ∀ s ∈ Set.Icc ε T,
      u₁ s ∈ Metric.closedBall
        (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) u₀) R) :
    ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun s => (N_cont (u₁ s) :
        tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))) (Set.Icc ε T) := by
  intro ε hε
  exact hN_cont.comp_continuousOn (hcont ε hε)

open MeasureTheory in
set_option linter.unusedVariables false in
theorem permode_sum_hasderivat
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (u₁ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce)
    (hu₂sol : ∀ s, u₂ s =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce s)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckGeometricN (I := I) g_bg a
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce t)))
    (hu₂ : ∀ s, tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) = timeH1.toFun u s)
    (hu₁ : ∀ s, u₁ s = tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
    (hderiv_ae : (u.deriv : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a (u₁ s)))
    (hRHS_cont : ContinuousOn
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a (u₁ s)) (Set.Ioo (0 : ℝ) T)) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun r => (timeH1.toFun u r : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          deTurckGeometricN (I := I) g_bg a (u₁ s)) s := by
  classical
  set RHS : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
      deTurckGeometricN (I := I) g_bg a (u₁ s) with hRHS_def
  intro s hs
  obtain ⟨hs0, hsT⟩ := hs
  have hsmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  have hTpos : (0 : ℝ) ≤ T := hs0.le.trans hsT.le
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hTpos⟩
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs0.le, hsT.le⟩
  have hderiv_int : IntervalIntegrable (fun r => u.deriv r) volume 0 s :=
    u.intervalIntegrable_deriv h0mem hsIcc
  have hRHS_int : IntervalIntegrable RHS volume 0 s := by
    have hsub : Set.uIoc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (Set.uIcc_subset_Icc h0mem hsIcc)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_ae
    exact hderiv_int.congr_ae hae
  have hRHS_at : ContinuousAt RHS s :=
    hRHS_cont.continuousAt (isOpen_Ioo.mem_nhds hsmem)
  have hRHS_meas : StronglyMeasurableAtFilter RHS (𝓝 s) volume :=
    hRHS_cont.stronglyMeasurableAtFilter isOpen_Ioo s hsmem
  have hftc_RHS : HasDerivAt (fun r => ∫ x in (0 : ℝ)..r, RHS x) (RHS s) s :=
    intervalIntegral.integral_hasDerivAt_right hRHS_int hRHS_meas hRHS_at
  have heq : (fun r => ∫ x in (0 : ℝ)..r, u.deriv x)
      =ᶠ[nhds s] fun r => ∫ x in (0 : ℝ)..r, RHS x := by
    filter_upwards [Ioo_mem_nhds hs0 hsT] with r hr
    refine intervalIntegral.integral_congr_ae ?_
    have hrIcc : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    have hsub : Set.uIoc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (Set.uIcc_subset_Icc h0mem hrIcc)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_ae
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with x hx hxmem
    exact hx hxmem
  have hftc_u : HasDerivAt (fun r => ∫ x in (0 : ℝ)..r, u.deriv x) (RHS s) s :=
    hftc_RHS.congr_of_eventuallyEq heq
  have hconst : HasDerivAt
      (fun r => (timeH1.toFun u r : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
      (RHS s) s := by
    have h := hftc_u.const_add u.init
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with r
    rw [timeH1.toFun_apply]
  exact hconst

end DifferentialGeometry.PDE.RicciFlow
