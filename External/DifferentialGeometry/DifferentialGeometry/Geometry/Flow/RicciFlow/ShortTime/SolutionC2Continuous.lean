import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.RealizeTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciContinuityInMetricTime
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
theorem deturck_solution_c2_continuous_icc0
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (hcont : ContinuousOn (fun s : ℝ => u s) (Set.Icc 0 T))
    (hreal : ∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s s) x v w)
    (hsmoothrepr : ∀ (s : ℝ)
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (u s).coeff i
        = tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hC2_chart : ∀ (α : M) (y : M), y ∈ chartLeviCivitaGoodSet (I := I) α →
      ∀ i j : Fin (Module.finrank ℝ E), ∀ k : ℕ, k ≤ 2 →
        ContinuousOn
          (fun s : ℝ => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j)
            (extChartAt I α y))
          (Set.Icc 0 T)) :
    (∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T))
    ∧ (∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w) (Set.Icc 0 T)) := by
  have hconj1 : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T) := by
    intro x v w
    obtain ⟨ℓ_a, hℓ_a⟩ :=
      realize_eval_carrier_factorization (I := I) (M := M) g_bg a ha x v w
    have hval : ∀ s : ℝ,
        (g_DT s).inner x v w = g_bg.inner x v w + ℓ_a (u s) := by
      intro s
      rw [hreal s x v w, hℓ_a (T_s s) (u s) (hsmoothrepr s)]
    have hfun : (fun s : ℝ => (g_DT s).inner x v w)
        = fun s : ℝ => g_bg.inner x v w + ℓ_a (u s) := by
      funext s; exact hval s
    rw [hfun]
    have hcomp : ContinuousOn (fun s : ℝ => ℓ_a (u s)) (Set.Icc 0 T) :=
      ℓ_a.continuous.comp_continuousOn hcont
    exact continuousOn_const.add hcomp
  refine ⟨hconj1, ?_⟩
  intro x v w
  exact ricci_continuous_in_metric_time (I := I) (M := M) g_DT T x v w hC2_chart

end DifferentialGeometry.PDE.RicciFlow
