import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.RealizeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.SolutionC2Continuous
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity








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






























theorem deturck_metric_pde_interior
    (g_bg : SmoothRiemannianMetric I M) {T : ℝ} (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (hreal : ∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s s) x v w)
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (repr : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g_bg 0 2)
    (Nsec : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g_bg 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
          (Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g_bg (repr u) x v w)
    (hrepr_small : ∀ u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      ∃ δ' : ℝ, δ' < 1 ∧
        metricCauchySchwarzBound (I := I) (M := M) g_bg
          (ccTensorBilinSymm (I := I) g_bg (repr u)) δ')
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s)
    (hsmall : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∃ δ' : ℝ, δ' < 1 ∧
      metricCauchySchwarzBound (I := I) (M := M) g_bg
        (ccTensorBilinSymm (I := I) g_bg (T_s s)) δ')
    (hsmoothrepr : ∀ (s : ℝ)
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (u₂ s).coeff i
        = tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hNsec_geom : ∀ (s : ℝ) (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g_bg
          (rawTensorConnLapSmooth (I := I) g_bg 0 2 (T_s s)) x' v' w'
        + ccTensorBilinSymm (I := I) g_bg
            (repr (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
        = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t := by
  intro t ht x v w
  set u_car : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) with hu_car_def
  set u_car' : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
      N_cont
        (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) with hu_car'_def
  obtain ⟨ℓ_a, hℓ⟩ := realize_eval_carrier_factorization (I := I) (M := M) g_bg a ha x v w
  have hfactor : ∀ s : ℝ,
      ccTensorBilinSymm (I := I) g_bg (T_s s) x v w = ℓ_a (u_car s) := by
    intro s
    refine (hℓ (T_s s) (u_car s) ?_).symm
    intro i
    rw [hu_car_def]
    simp only [tensorHsInclusion_coeff_apply]
    exact hsmoothrepr s i
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun r : ℝ => u_car r) (u_car' s) (Set.Ici 0) s := by
    intro s hs
    exact (hreg s hs).hasDerivWithinAt
  have hpush := pointwise_deriv_through_realize (I := I) (M := M) g_bg a
    g_DT T_s u_car u_car' x v w ℓ_a
    (fun s => hreal s x v w) hfactor hderiv t ht
  have hmatch := rhs_matches_deturck_at_solution (I := I) (M := M) g_bg a u₂ ℓ_a
    g_DT T_s x v w hreal N_cont repr Nsec hN_coeff hNsec_realize hrepr_small
    hsmoothrepr hℓ hNsec_geom t (Set.Ioo_subset_Ico_self ht)
  rw [hu_car'_def] at hpush
  rw [hmatch] at hpush
  exact hpush

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deturck_metric_pde_at_zero
    (g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x)
    (h_cont : ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T))
    (h_rhs_cont : ContinuousWithinAt
      (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w) (Set.Ioi 0) 0)
    (h_interior : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner x v w)
      (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) :
    HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
      (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w) (Set.Ici 0) 0 := by
  set f : ℝ → ℝ := fun s : ℝ => (g_DT s).inner x v w with hf_def
  set rhs : ℝ → ℝ := fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w with hrhs_def
  have hHasDerivAt : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt f (rhs t) t := by
    intro t ht
    exact (h_interior t ht).hasDerivAt (Ici_mem_nhds ht.1)
  have f_diff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) T) := by
    intro t ht
    exact ((hHasDerivAt t ht).differentiableAt).differentiableWithinAt
  have f_lim : ContinuousWithinAt f (Set.Ioo (0 : ℝ) T) 0 :=
    (h_cont.continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hT
  have hEqOn : Set.EqOn rhs (fun x => deriv f x) (Set.Ioo (0 : ℝ) T) := by
    intro t ht
    exact ((hHasDerivAt t ht).deriv).symm
  have f_lim' : Filter.Tendsto (fun x => deriv f x) (𝓝[>] (0 : ℝ))
      (𝓝 (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) := by
    have h_rhs_tendsto : Filter.Tendsto rhs (𝓝[>] (0 : ℝ))
        (𝓝 (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) := h_rhs_cont
    exact h_rhs_tendsto.congr' (hEqOn.eventuallyEq_of_mem hs)
  exact hasDerivWithinAt_Ici_of_tendsto_deriv f_diff f_lim hs f_lim'

end DifferentialGeometry.PDE.RicciFlow
