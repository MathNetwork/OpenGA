import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.ForcingPerMode
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
theorem deturck_interior_time_regularity
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce)
    (hu₂sol : ∀ s, u₂ s =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce s)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckGeometricN (I := I) g_bg a
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce t)))
    (hu₂ : ∀ s, tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) = timeH1.toFun u s)
    (hderiv_ae : (u.deriv : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a
          (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))))
    (hRHS_cont : ContinuousOn
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a
          (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) (Set.Ioo (0 : ℝ) T)) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun r => (timeH1.toFun u r : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          deTurckGeometricN (I := I) g_bg a
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s := by
  exact permode_sum_hasderivat (I := I) (M := M) g_bg a u₀ gforce hT hT1 u u₂
    (fun s => tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
    hu hu₂sol hforce hu₂ (fun _ => rfl) hderiv_ae hRHS_cont

end DifferentialGeometry.PDE.RicciFlow
