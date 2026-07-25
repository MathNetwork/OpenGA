import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciTensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieMatrixChartBridge
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckVectorFieldContinuousInMetric
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile


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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
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

namespace RicciContInMetricAux

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramOnE_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) :=
    (chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
  exact (hcd.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma fderiv_chartGramOnE_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (fun z : E => fderiv ℝ (chartGramOnE (I := I) g α i j) z) y := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) :=
    (chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
  have hcdAt : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α i j) y :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  have hderiv := hcdAt.fderiv_right (m := ∞) le_rfl
  exact hderiv.differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma partialDeriv_partialDeriv_chartGramOnE_eq_iteratedFDeriv_two
    (g : SmoothRiemannianMetric I M) (α : M) (i j m l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y =
      iteratedFDeriv ℝ 2 (chartGramOnE (I := I) g α i j) y
        ![(chartModelBasis E) m, (chartModelBasis E) l] := by
  have hl : (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j))
      = fun z : E => fderiv ℝ (chartGramOnE (I := I) g α i j) z ((chartModelBasis E) l) := by
    funext z; rfl
  rw [show partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j)) y
      = fderiv ℝ (fun z : E => fderiv ℝ (chartGramOnE (I := I) g α i j) z
            ((chartModelBasis E) l)) y ((chartModelBasis E) m) from by rw [hl]; rfl]
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply (fderiv_chartGramOnE_diffAt_int (I := I) g α i j hy)
    (differentiableAt_const _)]
  simp [ContinuousLinearMap.flip_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartGramOnE_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (y : E) (s : Set ℝ)
    (h0 : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
      (chartGramOnE (I := I) (g_DT t) α i j) y) s) :
    ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ
    ![]).continuous
  have hcomp := hL.comp_continuousOn h0
  refine hcomp.congr ?_
  intro t _
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_zero_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma partialDeriv_chartGramOnE_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (l i j : Fin (Module.finrank ℝ E)) (y : E) (s : Set ℝ)
    (h1 : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
      (chartGramOnE (I := I) (g_DT t) α i j) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y) s := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E) ℝ
    ![(chartModelBasis E) l]).continuous
  have hcomp := hL.comp_continuousOn h1
  refine hcomp.congr ?_
  intro t _
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_one_apply, Matrix.cons_val_zero]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma partialDeriv_partialDeriv_chartGramOnE_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (m l i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (h2 : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
      (chartGramOnE (I := I) (g_DT t) α i j) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j)) y) s := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ
    ![(chartModelBasis E) m, (chartModelBasis E) l]).continuous
  have hcomp := hL.comp_continuousOn h2
  refine hcomp.congr ?_
  intro t _
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply]
  rw [← partialDeriv_partialDeriv_chartGramOnE_eq_iteratedFDeriv_two
    (I := I) (g_DT t) α i j m l hy]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma gramBracket_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : E) (s : Set ℝ)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ => gramBracket (I := I) (g_DT t) α i j l y) s := by
  have heq : (fun t : ℝ => gramBracket (I := I) (g_DT t) α i j l y)
      = fun t : ℝ =>
          partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT t) α l j) y +
            partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT t) α l i) y -
            partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y := by
    funext t; rfl
  rw [heq]
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · exact partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α i l j y s (h1 l j)
  · exact partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α j l i y s (h1 l i)
  · exact partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α l i j y s (h1 i j)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma gramBracketDeriv_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (m i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ => gramBracketDeriv (I := I) (g_DT t) α m i j l y) s := by
  have heq : (fun t : ℝ => gramBracketDeriv (I := I) (g_DT t) α m i j l y)
      = fun t : ℝ =>
          partialDeriv (E := E) m
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT t) α l j)) y +
            partialDeriv (E := E) m
              (partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT t) α l i)) y -
            partialDeriv (E := E) m
              (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j)) y := by
    funext t; rfl
  rw [heq]
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · exact partialDeriv_partialDeriv_chartGramOnE_continuous_of_hC2
      (I := I) g_DT α m i l j hy s (h2 l j)
  · exact partialDeriv_partialDeriv_chartGramOnE_continuous_of_hC2
      (I := I) g_DT α m j l i hy s (h2 l i)
  · exact partialDeriv_partialDeriv_chartGramOnE_continuous_of_hC2
      (I := I) g_DT α m l i j hy s (h2 i j)

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartInvGramOnE_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (m k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y) s := by
  classical
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s :=
    fun a b => chartGramOnE_continuous_of_hC2 (I := I) g_DT α a b y s (h0 a b)
  have heq : ∀ t ∈ s,
      partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y =
        -∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) (g_DT t) α k a y *
              chartInvGramOnE (I := I) (g_DT t) α b l y *
              partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT t) α a b) y := by
    intro t _
    exact partialDeriv_chartInvGramOnE_eq (I := I) (g_DT t) α y m k l hy
  refine ContinuousOn.congr ?_ heq
  refine ContinuousOn.neg ?_
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s hentry hx k a
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s hentry hx b l
  · exact partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α m a b y s (h1 a b)

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartChristoffel_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT t) α i j k) y) s := by
  classical
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s :=
    fun a b => chartGramOnE_continuous_of_hC2 (I := I) g_DT α a b y s (h0 a b)
  have heq : ∀ t ∈ s,
      partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT t) α i j k) y =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y *
              gramBracket (I := I) (g_DT t) α i j l y +
            chartInvGramOnE (I := I) (g_DT t) α k l y *
              gramBracketDeriv (I := I) (g_DT t) α m i j l y) := by
    intro t _
    exact partialDeriv_chartChristoffel_eq (I := I) (g_DT t) α m i j k hy
  refine ContinuousOn.congr ?_ heq
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_sum _ (fun l _ => ?_)
  refine ContinuousOn.add (ContinuousOn.mul ?_ ?_) (ContinuousOn.mul ?_ ?_)
  · exact partialDeriv_chartInvGramOnE_continuous_of_hC2
      (I := I) g_DT α m k l hy s hx h0 h1
  · exact gramBracket_continuous_of_hC2 (I := I) g_DT α i j l y s h1
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s hentry hx k l
  · exact gramBracketDeriv_continuous_of_hC2 (I := I) g_DT α m i j l hy s h2

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRiemannTensor_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (i j k r : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      chartRiemannTensor (I := I) (g_DT t) α i j k r y) s := by
  classical
  have heq : (fun t : ℝ => chartRiemannTensor (I := I) (g_DT t) α i j k r y)
      = fun t : ℝ =>
          partialDeriv (E := E) j (chartChristoffel (I := I) (g_DT t) α i k r) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) (g_DT t) α i j r) y +
            (∑ n : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) (g_DT t) α j n r y *
                  chartChristoffel (I := I) (g_DT t) α i k n y -
                chartChristoffel (I := I) (g_DT t) α k n r y *
                  chartChristoffel (I := I) (g_DT t) α i j n y)) := by
    funext t; rw [chartRiemannTensor_def]
  rw [heq]
  refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) ?_
  · exact partialDeriv_chartChristoffel_continuous_of_hC2
      (I := I) g_DT α j i k r hy s hx h0 h1 h2
  · exact partialDeriv_chartChristoffel_continuous_of_hC2
      (I := I) g_DT α k i j r hy s hx h0 h1 h2
  · refine continuousOn_finset_sum _ (fun n _ => ?_)
    have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
        ContinuousOn (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b c y) s := by
      intro a b c
      refine chartChristoffel_continuous_in_metric_at (I := I) g_DT α y s ?_ ?_ hx a b c
      · exact fun p q => chartGramOnE_continuous_of_hC2 (I := I) g_DT α p q y s (h0 p q)
      · exact fun p q r' =>
          partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α p q r' y s (h1 q r')
    exact ContinuousOn.sub (ContinuousOn.mul (hΓ j n r) (hΓ i k n))
      (ContinuousOn.mul (hΓ k n r) (hΓ i j n))

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRicciTensor_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      chartRicciTensor (I := I) (g_DT t) α i k y) s := by
  classical
  have heq : (fun t : ℝ => chartRicciTensor (I := I) (g_DT t) α i k y)
      = fun t : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) (g_DT t) α i j k j y := by
    funext t; rw [chartRicciTensor_def]
  rw [heq]
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  exact chartRiemannTensor_continuous_of_hC2 (I := I) g_DT α i j k j hy s hx h0 h1 h2

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartDeTurckVFComp_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) {y : E}
    (_hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg α k y) s := by
  classical
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s :=
    fun a b => chartGramOnE_continuous_of_hC2 (I := I) g_DT α a b y s (h0 a b)
  have h_partial : ∀ l a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ =>
        partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α a b) y) s :=
    fun l a b => partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α l a b y s (h1 a b)
  exact chartDeTurckVFComp_continuous_in_metric_at (I := I) g_bg α y s g_DT hentry h_partial hx k

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartDeTurckVFComp_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M) (α : M)
    (m k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      partialDeriv (E := E) m
        (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg α k) y) s := by
  classical
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s :=
    fun a b => chartGramOnE_continuous_of_hC2 (I := I) g_DT α a b y s (h0 a b)
  have h_partial : ∀ l a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ =>
        partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α a b) y) s :=
    fun l a b => partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α l a b y s (h1 a b)
  have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b c y) s :=
    fun a b c => chartChristoffel_continuous_in_metric_at (I := I) g_DT α y s hentry
      (fun l p q => h_partial l p q) hx a b c
  have heq : ∀ t ∈ s,
      partialDeriv (E := E) m
          (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg α k) y =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α a b) y *
              (chartChristoffel (I := I) (g_DT t) α a b k y -
                chartChristoffel (I := I) g_bg α a b k y)
            + chartInvGramOnE (I := I) (g_DT t) α a b y *
              (partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT t) α a b k) y -
                partialDeriv (E := E) m (chartChristoffel (I := I) g_bg α a b k) y)) := by
    intro t _
    exact partialDeriv_chartDeTurckVFComp_eq (I := I) (g_DT t) g_bg α m k hy
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  refine ContinuousOn.add (ContinuousOn.mul ?_ ?_) (ContinuousOn.mul ?_ ?_)
  · exact partialDeriv_chartInvGramOnE_continuous_of_hC2 (I := I) g_DT α m a b hy s hx h0 h1
  · exact (hΓ a b k).sub continuousOn_const
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s hentry hx a b
  · exact (partialDeriv_chartChristoffel_continuous_of_hC2
      (I := I) g_DT α m a b k hy s hx h0 h1 h2).sub continuousOn_const

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartLieDeTurckComp_continuous_of_hC2
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContinuousOn (fun t : ℝ =>
      chartLieDeTurckComp (I := I) (g_DT t) g_bg α i j y) s := by
  classical
  have hVF : ∀ k : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ =>
        DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg α k y) s :=
    fun k => chartDeTurckVFComp_continuous_of_hC2 (I := I) g_DT g_bg α k hy s hx h0 h1
  have hVFp : ∀ m k : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ =>
        partialDeriv (E := E) m
          (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg α k) y) s :=
    fun m k => partialDeriv_chartDeTurckVFComp_continuous_of_hC2
      (I := I) g_DT g_bg α m k hy s hx h0 h1 h2
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s :=
    fun a b => chartGramOnE_continuous_of_hC2 (I := I) g_DT α a b y s (h0 a b)
  have hgp : ∀ l a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ =>
        partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α a b) y) s :=
    fun l a b => partialDeriv_chartGramOnE_continuous_of_hC2 (I := I) g_DT α l a b y s (h1 a b)
  have heq : (fun t : ℝ => chartLieDeTurckComp (I := I) (g_DT t) g_bg α i j y)
      = fun t : ℝ =>
          (∑ k : Fin (Module.finrank ℝ E),
              DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg α k y *
                partialDeriv (E := E) k (chartGramOnE (I := I) (g_DT t) α i j) y)
          + (∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) (g_DT t) α k j y *
                partialDeriv (E := E) i
                  (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg α k) y)
          + (∑ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) (g_DT t) α i k y *
                partialDeriv (E := E) j
                  (DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g_bg α k) y) := by
    funext t; rw [chartLieDeTurckComp_def]
  rw [heq]
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · exact continuousOn_finset_sum _ (fun k _ => (hVF k).mul (hgp k i j))
  · exact continuousOn_finset_sum _ (fun k _ => (hgram k j).mul (hVFp i k))
  · exact continuousOn_finset_sum _ (fun k _ => (hgram i k).mul (hVFp j k))

end RicciContInMetricAux

namespace RicciContJointAux

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (Sp : Set (ℝ × M))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointGram_continuousOn
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (a b : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M => chartGramOnE (I := I) (g_DT q.1) α a b
      (extChartAt I α q.2)) Sp := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ ![]).continuous
  refine (hL.comp_continuousOn (h0 a b)).congr ?_
  intro q _
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_zero_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointGramPartial_continuousOn
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (l a b : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT q.1) α a b)
        (extChartAt I α q.2)) Sp := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E) ℝ
    ![(chartModelBasis E) l]).continuous
  refine (hL.comp_continuousOn (h1 a b)).congr ?_
  intro q _
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_one_apply, Matrix.cons_val_zero]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointGramPartialPartial_continuousOn
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (m l a b : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT q.1) α a b))
        (extChartAt I α q.2)) Sp := by
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ
    ![(chartModelBasis E) m, (chartModelBasis E) l]).continuous
  refine (hL.comp_continuousOn (h2 a b)).congr ?_
  intro q hq
  have hy : extChartAt I α q.2 ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) (hgood q hq)
  simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply]
  rw [← RicciContInMetricAux.partialDeriv_partialDeriv_chartGramOnE_eq_iteratedFDeriv_two
    (I := I) (g_DT q.1) α a b m l hy]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointDet_continuousOn
    (hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => chartGramOnE (I := I) (g_DT q.1) α a b
        (extChartAt I α q.2)) Sp) :
    ContinuousOn (fun q : ℝ × M =>
      (Matrix.of fun a b => chartGramOnE (I := I) (g_DT q.1) α a b
        (extChartAt I α q.2)).det) Sp := by
  classical
  have hrewrite : (fun q : ℝ × M =>
      (Matrix.of fun a b => chartGramOnE (I := I) (g_DT q.1) α a b (extChartAt I α q.2)).det)
        = fun q : ℝ × M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
            (Equiv.Perm.sign σ : ℝ) * ∏ k : Fin (Module.finrank ℝ E),
              chartGramOnE (I := I) (g_DT q.1) α (σ k) k (extChartAt I α q.2) := by
    funext q; rw [Matrix.det_apply]; simp [Units.smul_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun σ _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  exact continuousOn_finset_prod _ (fun k _ => hentry (σ k) k)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointAdjugate_continuousOn
    (hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => chartGramOnE (I := I) (g_DT q.1) α a b
        (extChartAt I α q.2)) Sp)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      (Matrix.of fun a b => chartGramOnE (I := I) (g_DT q.1) α a b
        (extChartAt I α q.2)).adjugate i j) Sp := by
  classical
  have hrewrite : (fun q : ℝ × M =>
      (Matrix.of fun a b => chartGramOnE (I := I) (g_DT q.1) α a b (extChartAt I α q.2)).adjugate i j)
        = fun q : ℝ × M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
            (Equiv.Perm.sign σ : ℝ) * ∏ k : Fin (Module.finrank ℝ E),
              ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT q.1) α a b
                (extChartAt I α q.2)).updateRow j (Pi.single i (1 : ℝ))) (σ k) k := by
    funext q; rw [Matrix.adjugate_apply, Matrix.det_apply]; simp [Units.smul_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun σ _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_prod _ (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun q : ℝ × M =>
        ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT q.1) α a b (extChartAt I α q.2)).updateRow j
          (Pi.single i (1 : ℝ))) (σ k) k)
          = fun _ : ℝ × M =>
              (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i (1 : ℝ)) k := by
      funext q; rw [hσk, Matrix.updateRow_self]
    rw [heq]; exact continuousOn_const
  · have heq : (fun q : ℝ × M =>
        ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT q.1) α a b (extChartAt I α q.2)).updateRow j
          (Pi.single i (1 : ℝ))) (σ k) k)
          = fun q : ℝ × M =>
              chartGramOnE (I := I) (g_DT q.1) α (σ k) k (extChartAt I α q.2) := by
      funext q; rw [Matrix.updateRow_ne hσk]; rfl
    rw [heq]; exact hentry (σ k) k

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointInvGram_continuousOn
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => chartGramOnE (I := I) (g_DT q.1) α a b
        (extChartAt I α q.2)) Sp)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      chartInvGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2)) Sp := by
  classical
  set Gmat : ℝ × M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun q => Matrix.of fun a b => chartGramOnE (I := I) (g_DT q.1) α a b (extChartAt I α q.2)
    with hGmat
  have hGmat_eq : ∀ q : ℝ × M, Gmat q = chartGramMatrix (I := I) (g_DT q.1) α
      ((extChartAt I α).symm (extChartAt I α q.2)) := by
    intro q; ext a b; rw [hGmat]; simp only [Matrix.of_apply]; rw [chartGramOnE_def]
  have hbase : ∀ q ∈ Sp, ((extChartAt I α).symm (extChartAt I α q.2)) ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro q hq
    rw [(extChartAt I α).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) (hgood q hq))]
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) (hgood q hq)
  have hcongr : ∀ q ∈ Sp,
      chartInvGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2) =
        ((Gmat q).det)⁻¹ * (Gmat q).adjugate i j := by
    intro q hq
    rw [chartInvGramOnE_def]
    unfold chartInvGramMatrix
    have hpos := chartGramMatrix_det_pos (I := I) (g_DT q.1) α (hbase q hq)
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (g_DT q.1) α
            ((extChartAt I α).symm (extChartAt I α q.2))).det •
          (chartGramMatrix (I := I) (g_DT q.1) α
            ((extChartAt I α).symm (extChartAt I α q.2))).adjugate) i j =
      ((Gmat q).det)⁻¹ * (Gmat q).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul, hGmat_eq q]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContinuousOn.congr ?_ hcongr
  refine ContinuousOn.mul ?_ (jointAdjugate_continuousOn g_DT α Sp hentry i j)
  refine (jointDet_continuousOn g_DT α Sp hentry).inv₀ ?_
  intro q hq
  have hpos := chartGramMatrix_det_pos (I := I) (g_DT q.1) α (hbase q hq)
  have : (Gmat q).det = (chartGramMatrix (I := I) (g_DT q.1) α
      ((extChartAt I α).symm (extChartAt I α q.2))).det := by rw [hGmat_eq q]
  rw [this]; exact ne_of_gt hpos

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointGramBracket_continuousOn
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M => gramBracket (I := I) (g_DT q.1) α i j l
      (extChartAt I α q.2)) Sp := by
  have heq : (fun q : ℝ × M => gramBracket (I := I) (g_DT q.1) α i j l (extChartAt I α q.2))
      = fun q : ℝ × M =>
          partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT q.1) α l j) (extChartAt I α q.2) +
            partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT q.1) α l i) (extChartAt I α q.2) -
            partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT q.1) α i j) (extChartAt I α q.2) := by
    funext q; rfl
  rw [heq]
  exact ((jointGramPartial_continuousOn g_DT α Sp h1 i l j).add
    (jointGramPartial_continuousOn g_DT α Sp h1 j l i)).sub
    (jointGramPartial_continuousOn g_DT α Sp h1 l i j)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointGramBracketDeriv_continuousOn
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (m i j l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M => gramBracketDeriv (I := I) (g_DT q.1) α m i j l
      (extChartAt I α q.2)) Sp := by
  have heq : (fun q : ℝ × M => gramBracketDeriv (I := I) (g_DT q.1) α m i j l (extChartAt I α q.2))
      = fun q : ℝ × M =>
          partialDeriv (E := E) m
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT q.1) α l j)) (extChartAt I α q.2) +
            partialDeriv (E := E) m
              (partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT q.1) α l i)) (extChartAt I α q.2) -
            partialDeriv (E := E) m
              (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT q.1) α i j)) (extChartAt I α q.2) := by
    funext q; rfl
  rw [heq]
  exact ((jointGramPartialPartial_continuousOn g_DT α Sp hgood h2 m i l j).add
    (jointGramPartialPartial_continuousOn g_DT α Sp hgood h2 m j l i)).sub
    (jointGramPartialPartial_continuousOn g_DT α Sp hgood h2 m l i j)

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jointInvGramPartial_continuousOn
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (m k l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT q.1) α k l)
        (extChartAt I α q.2)) Sp := by
  classical
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => chartGramOnE (I := I) (g_DT q.1) α a b
        (extChartAt I α q.2)) Sp :=
    fun a b => jointGram_continuousOn g_DT α Sp h0 a b
  have heq : ∀ q ∈ Sp,
      partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT q.1) α k l) (extChartAt I α q.2) =
        -∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) (g_DT q.1) α k a (extChartAt I α q.2) *
              chartInvGramOnE (I := I) (g_DT q.1) α b l (extChartAt I α q.2) *
              partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT q.1) α a b)
                (extChartAt I α q.2) := by
    intro q hq
    exact partialDeriv_chartInvGramOnE_eq (I := I) (g_DT q.1) α (extChartAt I α q.2) m k l
      (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) (hgood q hq))
  refine ContinuousOn.congr ?_ heq
  refine ContinuousOn.neg ?_
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  exact ((jointInvGram_continuousOn g_DT α Sp hgood hentry k a).mul
    (jointInvGram_continuousOn g_DT α Sp hgood hentry b l)).mul
    (jointGramPartial_continuousOn g_DT α Sp h1 m a b)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma jointChristoffel_continuousOn
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      chartChristoffel (I := I) (g_DT q.1) α i j k (extChartAt I α q.2)) Sp := by
  classical
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => chartGramOnE (I := I) (g_DT q.1) α a b
        (extChartAt I α q.2)) Sp :=
    fun a b => jointGram_continuousOn g_DT α Sp h0 a b
  have heq : (fun q : ℝ × M => chartChristoffel (I := I) (g_DT q.1) α i j k (extChartAt I α q.2))
      = fun q : ℝ × M =>
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (g_DT q.1) α
              ((extChartAt I α).symm (extChartAt I α q.2)) k l *
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT q.1) α l j)
                  (extChartAt I α q.2) +
               partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT q.1) α l i)
                  (extChartAt I α q.2) -
               partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT q.1) α i j)
                  (extChartAt I α q.2)) := by
    funext q; rw [chartChristoffel_def]
  rw [heq]
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_sum _ (fun l _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · have hcongr : (fun q : ℝ × M => chartInvGramMatrix (I := I) (g_DT q.1) α
          ((extChartAt I α).symm (extChartAt I α q.2)) k l)
        = fun q : ℝ × M => chartInvGramOnE (I := I) (g_DT q.1) α k l (extChartAt I α q.2) := by
      funext q; rfl
    rw [hcongr]
    exact jointInvGram_continuousOn g_DT α Sp hgood hentry k l
  · exact ((jointGramPartial_continuousOn g_DT α Sp h1 i l j).add
      (jointGramPartial_continuousOn g_DT α Sp h1 j l i)).sub
      (jointGramPartial_continuousOn g_DT α Sp h1 l i j)

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jointChristoffelPartial_continuousOn
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (m i j k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT q.1) α i j k)
        (extChartAt I α q.2)) Sp := by
  classical
  have heq : ∀ q ∈ Sp,
      partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT q.1) α i j k) (extChartAt I α q.2) =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT q.1) α k l)
              (extChartAt I α q.2) *
            gramBracket (I := I) (g_DT q.1) α i j l (extChartAt I α q.2) +
          chartInvGramOnE (I := I) (g_DT q.1) α k l (extChartAt I α q.2) *
            gramBracketDeriv (I := I) (g_DT q.1) α m i j l (extChartAt I α q.2)) := by
    intro q hq
    exact partialDeriv_chartChristoffel_eq (I := I) (g_DT q.1) α m i j k
      (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) (hgood q hq))
  refine ContinuousOn.congr ?_ heq
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_sum _ (fun l _ => ?_)
  have hentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => chartGramOnE (I := I) (g_DT q.1) α a b
        (extChartAt I α q.2)) Sp :=
    fun a b => jointGram_continuousOn g_DT α Sp h0 a b
  refine ContinuousOn.add (ContinuousOn.mul ?_ ?_) (ContinuousOn.mul ?_ ?_)
  · exact jointInvGramPartial_continuousOn g_DT α Sp hgood h0 h1 m k l
  · exact jointGramBracket_continuousOn g_DT α Sp h1 i j l
  · exact jointInvGram_continuousOn g_DT α Sp hgood hentry k l
  · exact jointGramBracketDeriv_continuousOn g_DT α Sp hgood h2 m i j l

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jointRiemann_continuousOn
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (i j k r : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      chartRiemannTensor (I := I) (g_DT q.1) α i j k r (extChartAt I α q.2)) Sp := by
  classical
  have heq : (fun q : ℝ × M => chartRiemannTensor (I := I) (g_DT q.1) α i j k r (extChartAt I α q.2))
      = fun q : ℝ × M =>
          partialDeriv (E := E) j (chartChristoffel (I := I) (g_DT q.1) α i k r)
              (extChartAt I α q.2) -
            partialDeriv (E := E) k (chartChristoffel (I := I) (g_DT q.1) α i j r)
              (extChartAt I α q.2) +
            (∑ n : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) (g_DT q.1) α j n r (extChartAt I α q.2) *
                  chartChristoffel (I := I) (g_DT q.1) α i k n (extChartAt I α q.2) -
                chartChristoffel (I := I) (g_DT q.1) α k n r (extChartAt I α q.2) *
                  chartChristoffel (I := I) (g_DT q.1) α i j n (extChartAt I α q.2))) := by
    funext q; rw [chartRiemannTensor_def]
  rw [heq]
  refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) ?_
  · exact jointChristoffelPartial_continuousOn g_DT α Sp hgood h0 h1 h2 j i k r
  · exact jointChristoffelPartial_continuousOn g_DT α Sp hgood h0 h1 h2 k i j r
  · refine continuousOn_finset_sum _ (fun n _ => ?_)
    have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
        ContinuousOn (fun q : ℝ × M => chartChristoffel (I := I) (g_DT q.1) α a b c
          (extChartAt I α q.2)) Sp :=
      fun a b c => jointChristoffel_continuousOn g_DT α Sp hgood h0 h1 a b c
    exact ((hΓ j n r).mul (hΓ i k n)).sub ((hΓ k n r).mul (hΓ i j n))

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma jointRicci_continuousOn
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (i k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      chartRicciTensor (I := I) (g_DT q.1) α i k (extChartAt I α q.2)) Sp := by
  classical
  have heq : (fun q : ℝ × M => chartRicciTensor (I := I) (g_DT q.1) α i k (extChartAt I α q.2))
      = fun q : ℝ × M => ∑ j : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) (g_DT q.1) α i j k j (extChartAt I α q.2) := by
    funext q; rw [chartRicciTensor_def]
  rw [heq]
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  exact jointRiemann_continuousOn g_DT α Sp hgood h0 h1 h2 i j k j

end RicciContJointAux

namespace MovingPushforwardAux

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma moving_chartCoord_continuousWithinAt
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (x : M) (u : TangentSpace I x)
    (α : M) (S : Set ℝ) (s₀ : ℝ)
    (hbase0 : (Φ_fam s₀ : M → M) x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (horbit : ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) S s₀)
    (htotal : ContinuousWithinAt
      (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x u) : TangentBundle I M)) S s₀) :
    ContinuousWithinAt
      (fun s : ℝ => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
        ((Φ_fam s : M → M) x) (mfderiv I I (Φ_fam s : M → M) x u)) S s₀ := by
  classical
  set e := trivializationAt E (TangentSpace I) α with he
  set F : ℝ → TangentBundle I M := fun s : ℝ =>
    (TotalSpace.mk' E ((Φ_fam s : M → M) x)
      (mfderiv I I (Φ_fam s : M → M) x u) : TangentBundle I M) with hF
  have hsrc0 : F s₀ ∈ e.source := by
    rw [he, Bundle.Trivialization.mem_source]; exact hbase0
  have hcontTriv : ContinuousWithinAt (fun p : TangentBundle I M => (e p).2) e.source (F s₀) :=
    (e.continuousOn.continuousWithinAt hsrc0).snd
  have hpre : F ⁻¹' e.source ∈ nhdsWithin s₀ S :=
    htotal.preimage_mem_nhdsWithin (e.open_source.mem_nhds hsrc0)
  have hcomp : ContinuousWithinAt (fun s : ℝ => (e (F s)).2) S s₀ :=
    hcontTriv.comp_of_preimage_mem_nhdsWithin htotal hpre
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbnhds : e.baseSet ∈ nhds ((Φ_fam s₀ : M → M) x) := e.open_baseSet.mem_nhds hbase0
    have hpb : (fun s : ℝ => (Φ_fam s : M → M) x) ⁻¹' e.baseSet ∈ nhdsWithin s₀ S :=
      horbit.preimage_mem_nhdsWithin hbnhds
    filter_upwards [hpb] with s hs
    change e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam s : M → M) x u) = (e (F s)).2
    rw [hF, e.apply_eq_prod_continuousLinearEquivAt ℝ _ hs,
      e.coe_continuousLinearEquivAt_eq (R := ℝ) hs]
  · change e.continuousLinearMapAt ℝ ((Φ_fam s₀ : M → M) x)
        (mfderiv I I (Φ_fam s₀ : M → M) x u) = (e (F s₀)).2
    rw [hF, e.apply_eq_prod_continuousLinearEquivAt ℝ _ hbase0,
      e.coe_continuousLinearEquivAt_eq (R := ℝ) hbase0]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem moving_chartCoord_jointContinuousWithinAt
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (x₀ : M) (i : Fin (Module.finrank ℝ E)) (α : M)
    (S : Set (ℝ × M)) (p₀ : ℝ × M)
    (hbase0 : (Φ_fam p₀.1 : M → M) p₀.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (horbit : ContinuousWithinAt (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) S p₀)
    (htotal : ContinuousWithinAt
      (fun p : ℝ × M => (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
          : TangentBundle I M)) S p₀) :
    ContinuousWithinAt
      (fun p : ℝ × M => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
        ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))) S p₀ := by
  classical
  set e := trivializationAt E (TangentSpace I) α with he
  set F : ℝ × M → TangentBundle I M := fun p : ℝ × M =>
    (TotalSpace.mk' E ((Φ_fam p.1 : M → M) p.2)
      (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
        : TangentBundle I M) with hF
  have hsrc0 : F p₀ ∈ e.source := by
    rw [he, Bundle.Trivialization.mem_source]; exact hbase0
  have hcontTriv : ContinuousWithinAt (fun b : TangentBundle I M => (e b).2) e.source (F p₀) :=
    (e.continuousOn.continuousWithinAt hsrc0).snd
  have hpre : F ⁻¹' e.source ∈ nhdsWithin p₀ S :=
    htotal.preimage_mem_nhdsWithin (e.open_source.mem_nhds hsrc0)
  have hcomp : ContinuousWithinAt (fun p : ℝ × M => (e (F p)).2) S p₀ :=
    hcontTriv.comp_of_preimage_mem_nhdsWithin htotal hpre
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbnhds : e.baseSet ∈ nhds ((Φ_fam p₀.1 : M → M) p₀.2) := e.open_baseSet.mem_nhds hbase0
    have hpb : (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2) ⁻¹' e.baseSet ∈ nhdsWithin p₀ S :=
      horbit.preimage_mem_nhdsWithin hbnhds
    filter_upwards [hpb] with p hs
    change e.continuousLinearMapAt ℝ ((Φ_fam p.1 : M → M) p.2)
        (mfderiv I I (Φ_fam p.1 : M → M) p.2 (chartBasisVecFiber (I := I) x₀ i p.2))
          = (e (F p)).2
    rw [hF, e.apply_eq_prod_continuousLinearEquivAt ℝ _ hs,
      e.coe_continuousLinearEquivAt_eq (R := ℝ) hs]
  · change e.continuousLinearMapAt ℝ ((Φ_fam p₀.1 : M → M) p₀.2)
        (mfderiv I I (Φ_fam p₀.1 : M → M) p₀.2 (chartBasisVecFiber (I := I) x₀ i p₀.2))
          = (e (F p₀)).2
    rw [hF, e.apply_eq_prod_continuousLinearEquivAt ℝ _ hbase0,
      e.coe_continuousLinearEquivAt_eq (R := ℝ) hbase0]

private lemma cwa_finset_sum {ι : Type*} {N : Type*} [AddCommMonoid N] [TopologicalSpace N]
    [ContinuousAdd N] {f : ι → ℝ → N} (s : Finset ι) {t : Set ℝ} {x : ℝ}
    (h : ∀ i ∈ s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a : ℝ => ∑ i ∈ s, f i a) t x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuousWithinAt_const
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [NeZero (Module.finrank ℝ E)] in
private lemma repr_continuousWithinAt {S : Set ℝ} {s₀ : ℝ} {f : ℝ → E}
    (hf : ContinuousWithinAt f S s₀) (p : Fin (Module.finrank ℝ E)) :
    ContinuousWithinAt (fun s : ℝ => ((chartModelBasis E).repr (f s)) p) S s₀ := by
  have hlin : Continuous (fun y : E => ((chartModelBasis E).repr y) p) :=
    ((Finsupp.lapply (R := ℝ) (M := ℝ) (α := Fin (Module.finrank ℝ E)) p).comp
      (chartModelBasis E).repr.toLinearMap).continuous_of_finiteDimensional
  exact hlin.continuousWithinAt.comp hf (Set.mapsTo_univ _ _)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma ricci_moving_chart_sum
    (g : SmoothRiemannianMetric I M) (α : M) {y : M}
    (hy : y ∈ chartLeviCivitaGoodSet (I := I) α)
    (vy wy : TangentSpace I y) :
    ricciTensor (I := I) g y vy wy =
      ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ y vy)) p *
        ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ y wy)) q *
        chartRicciTensor (I := I) g α p q (extChartAt I α y) := by
  classical
  have hbase : y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hy
  set bv : Fin (Module.finrank ℝ E) → ℝ := fun p => ((chartModelBasis E).repr
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ y vy)) p with hbv
  set bw : Fin (Module.finrank ℝ E) → ℝ := fun q => ((chartModelBasis E).repr
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ y wy)) q with hbw
  have hvy : vy = ∑ p : Fin (Module.finrank ℝ E), bv p • chartBasisVecFiber (I := I) α p y :=
    chartBasisVecFiber_recompose (I := I) α hbase vy
  have hwy : wy = ∑ q : Fin (Module.finrank ℝ E), bw q • chartBasisVecFiber (I := I) α q y :=
    chartBasisVecFiber_recompose (I := I) α hbase wy
  conv_lhs => rw [hvy, hwy]
  rw [map_sum (ricciTensor (I := I) g y), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum (ricciTensor (I := I) g y (chartBasisVecFiber (I := I) α p y)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, smul_eq_mul]
  rw [ricciTensor_chartBasisVec_alpha_eq (I := I) g α p q hy]
  ring

end MovingPushforwardAux

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem gfam_inner_continuous_on
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (_hT : 0 < T)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (x : M) (v w : TangentSpace I x)
    (hg_joint : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
            (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ (chartAt H α).source))
    (hΦ_orbit : ∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T))
    (hΦ_total : ∀ (y : M) (u : TangentSpace I y),
      ContinuousOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
          (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ico 0 T)) :
    ContinuousOn
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
      (Set.Ico 0 T) := by
  classical
  open MovingPushforwardAux in
  rw [pullbackMetric_inner_funext g_DT Φ_fam x v w]
  intro s₀ hs₀
  set α : M := (Φ_fam s₀ : M → M) x with hα
  set e := trivializationAt E (TangentSpace I) α with he
  have hbase0 : (Φ_fam s₀ : M → M) x ∈ e.baseSet := by
    rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hsrc0 : (Φ_fam s₀ : M → M) x ∈ (extChartAt I α).source := by
    rw [hα]; exact mem_extChartAt_source (I := I) α
  have horbit : ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ico 0 T) s₀ :=
    (hΦ_orbit x).continuousWithinAt hs₀
  have hcoordV : ∀ i : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun s : ℝ => ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
            (mfderiv I I (Φ_fam s : M → M) x v))) i) (Set.Ico 0 T) s₀ :=
    fun i => repr_continuousWithinAt
      (moving_chartCoord_continuousWithinAt Φ_fam x v α (Set.Ico 0 T) s₀
        hbase0 horbit ((hΦ_total x v).continuousWithinAt hs₀)) i
  have hcoordW : ∀ j : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun s : ℝ => ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
            (mfderiv I I (Φ_fam s : M → M) x w))) j) (Set.Ico 0 T) s₀ :=
    fun j => repr_continuousWithinAt
      (moving_chartCoord_continuousWithinAt Φ_fam x w α (Set.Ico 0 T) s₀
        hbase0 horbit ((hΦ_total x w).continuousWithinAt hs₀)) j
  have hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun s : ℝ => Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j
          (extChartAt I α ((Φ_fam s : M → M) x))) (Set.Ico 0 T) s₀ := by
    intro i j
    set Sp : Set (ℝ × M) := Set.Icc 0 T ×ˢ (chartAt H α).source with hSp
    have hsrc0' : (Φ_fam s₀ : M → M) x ∈ (chartAt H α).source := by
      rw [hα]; exact mem_chart_source H α
    have hpair : ContinuousWithinAt (fun s : ℝ => (s, (Φ_fam s : M → M) x))
        (Set.Ico 0 T) s₀ :=
      continuousWithinAt_id.prodMk horbit
    have hpre : (fun s : ℝ => (s, (Φ_fam s : M → M) x)) ⁻¹' Sp
        ∈ nhdsWithin s₀ (Set.Ico 0 T) := by
      have hsnhds : (chartAt H α).source ∈ nhds ((Φ_fam s₀ : M → M) x) :=
        (chartAt H α).open_source.mem_nhds hsrc0'
      have hs : (fun s : ℝ => (Φ_fam s : M → M) x) ⁻¹' (chartAt H α).source
          ∈ nhdsWithin s₀ (Set.Ico 0 T) :=
        horbit.preimage_mem_nhdsWithin hsnhds
      have hself : (Set.Ico 0 T : Set ℝ) ∈ nhdsWithin s₀ (Set.Ico 0 T) := self_mem_nhdsWithin
      filter_upwards [hs, hself] with s hssrc hsico
      exact ⟨⟨hsico.1, le_of_lt hsico.2⟩, hssrc⟩
    have hpt0 : ((s₀, (Φ_fam s₀ : M → M) x) : ℝ × M) ∈ Sp :=
      ⟨⟨hs₀.1, le_of_lt hs₀.2⟩, hsrc0'⟩
    have hcomp := ((hg_joint α i j).continuousWithinAt hpt0).comp_of_preimage_mem_nhdsWithin_of_eq
      hpair hpre rfl
    simpa only [Function.comp_def] using hcomp
  have hsum : ∀ s, (Φ_fam s : M → M) x ∈ e.baseSet →
      (Φ_fam s : M → M) x ∈ (extChartAt I α).source →
      (g_DT s).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w)
        = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
                (mfderiv I I (Φ_fam s : M → M) x v))) i *
            ((chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
                (mfderiv I I (Φ_fam s : M → M) x w))) j *
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j
              (extChartAt I α ((Φ_fam s : M → M) x)) := by
    intro s hb hsr
    exact g_inner_eq_chart_sum (I := I) (g_DT s) α hb hsr
      (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w)
  have hsumcont : ContinuousWithinAt
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
            (mfderiv I I (Φ_fam s : M → M) x v))) i *
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
            (mfderiv I I (Φ_fam s : M → M) x w))) j *
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j
          (extChartAt I α ((Φ_fam s : M → M) x))) (Set.Ico 0 T) s₀ := by
    refine cwa_finset_sum _ (fun i _ => ?_)
    refine cwa_finset_sum _ (fun j _ => ?_)
    exact ((hcoordV i).mul (hcoordW j)).mul (hgram i j)
  refine hsumcont.congr_of_eventuallyEq ?_ ?_
  · have hbnhds : e.baseSet ∈ nhds ((Φ_fam s₀ : M → M) x) := e.open_baseSet.mem_nhds hbase0
    have hsrcnhds : (extChartAt I α).source ∈ nhds ((Φ_fam s₀ : M → M) x) :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hsrc0
    have hpb : (fun s : ℝ => (Φ_fam s : M → M) x) ⁻¹' e.baseSet ∈ nhdsWithin s₀ (Set.Ico 0 T) :=
      horbit.preimage_mem_nhdsWithin hbnhds
    have hps : (fun s : ℝ => (Φ_fam s : M → M) x) ⁻¹' (extChartAt I α).source
        ∈ nhdsWithin s₀ (Set.Ico 0 T) :=
      horbit.preimage_mem_nhdsWithin hsrcnhds
    filter_upwards [hpb, hps] with s hb hsr
    exact hsum s hb hsr
  · exact hsum s₀ hbase0 hsrc0

omit [CompactSpace M] in
theorem ricci_gfam_continuous_on
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (_hT : 0 < T)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (x : M) (v w : TangentSpace I x)
    (hC2 : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α))
    (hΦ0 : ∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T))
    (hΦ_total : ∀ (y : M) (u : TangentSpace I y),
      ContinuousOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
          (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ico 0 T)) :
    ContinuousOn
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w)
      (Set.Ico 0 T) := by
  classical
  open MovingPushforwardAux RicciContJointAux in
  have hnat : (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w)
      = fun s : ℝ => ricciTensor (I := I) (g_DT s) (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w) := by
    funext s
    exact ricci_tensor_pullback_natural_under_diffeomorphism (I := I) (g_DT s) (Φ_fam s) x v w
  rw [hnat]
  intro s₀ hs₀
  set α : M := (Φ_fam s₀ : M → M) x with hα
  set e := trivializationAt E (TangentSpace I) α with he
  have hgood0 : (Φ_fam s₀ : M → M) x ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [hα]; exact self_mem_chartLeviCivitaGoodSet (I := I) (α := α)
  have hbase0 : (Φ_fam s₀ : M → M) x ∈ e.baseSet := by
    rw [he, hα]; exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have horbit : ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ico 0 T) s₀ :=
    (hΦ0 x).continuousWithinAt hs₀
  have hcoordV : ∀ p : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun s : ℝ => ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
            (mfderiv I I (Φ_fam s : M → M) x v))) p) (Set.Ico 0 T) s₀ :=
    fun p => repr_continuousWithinAt
      (moving_chartCoord_continuousWithinAt Φ_fam x v α (Set.Ico 0 T) s₀
        hbase0 horbit ((hΦ_total x v).continuousWithinAt hs₀)) p
  have hcoordW : ∀ q : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun s : ℝ => ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
            (mfderiv I I (Φ_fam s : M → M) x w))) q) (Set.Ico 0 T) s₀ :=
    fun q => repr_continuousWithinAt
      (moving_chartCoord_continuousWithinAt Φ_fam x w α (Set.Ico 0 T) s₀
        hbase0 horbit ((hΦ_total x w).continuousWithinAt hs₀)) q
  set Sp : Set (ℝ × M) := Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α with hSp
  have hgoodSp : ∀ qp ∈ Sp, qp.2 ∈ chartLeviCivitaGoodSet (I := I) α := fun qp hqp => hqp.2
  have hjet : ∀ (k : ℕ), k ≤ 2 → ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun qp : ℝ × M => iteratedFDeriv ℝ k
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT qp.1) α a b)
        (extChartAt I α qp.2)) Sp :=
    fun k hk a b => hC2 α a b k hk
  have hric : ∀ p q : Fin (Module.finrank ℝ E),
      ContinuousWithinAt
        (fun s : ℝ => chartRicciTensor (I := I) (g_DT s) α p q
          (extChartAt I α ((Φ_fam s : M → M) x))) (Set.Ico 0 T) s₀ := by
    intro p q
    have hjoint := jointRicci_continuousOn g_DT α Sp hgoodSp
      (hjet 0 (by norm_num)) (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) p q
    have hpair : ContinuousWithinAt (fun s : ℝ => (s, (Φ_fam s : M → M) x))
        (Set.Ico 0 T) s₀ :=
      continuousWithinAt_id.prodMk horbit
    have hpre : (fun s : ℝ => (s, (Φ_fam s : M → M) x)) ⁻¹' Sp ∈ nhdsWithin s₀ (Set.Ico 0 T) := by
      have hgnhds : chartLeviCivitaGoodSet (I := I) α ∈ nhds ((Φ_fam s₀ : M → M) x) :=
        (chartLeviCivitaGoodSet_isOpen (I := I) α).mem_nhds hgood0
      have hg := horbit.preimage_mem_nhdsWithin hgnhds
      have hicc : (Set.Ico 0 T : Set ℝ) ⊆ Set.Icc 0 T := Set.Ico_subset_Icc_self
      have hself : (Set.Ico 0 T : Set ℝ) ∈ nhdsWithin s₀ (Set.Ico 0 T) := self_mem_nhdsWithin
      filter_upwards [hg, hself] with s hsg hsicc
      exact ⟨hicc hsicc, hsg⟩
    have hpt0 : ((s₀, (Φ_fam s₀ : M → M) x) : ℝ × M) ∈ Sp :=
      ⟨Set.Ico_subset_Icc_self hs₀, hgood0⟩
    have hcomp := (hjoint.continuousWithinAt hpt0).comp_of_preimage_mem_nhdsWithin_of_eq
      hpair hpre rfl
    simpa only [Function.comp_def] using hcomp
  have hsum : ∀ s, (Φ_fam s : M → M) x ∈ chartLeviCivitaGoodSet (I := I) α →
      ricciTensor (I := I) (g_DT s) ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w)
        = ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
                (mfderiv I I (Φ_fam s : M → M) x v))) p *
            ((chartModelBasis E).repr
              (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
                (mfderiv I I (Φ_fam s : M → M) x w))) q *
            chartRicciTensor (I := I) (g_DT s) α p q (extChartAt I α ((Φ_fam s : M → M) x)) := by
    intro s hg
    exact ricci_moving_chart_sum (I := I) (g_DT s) α hg
      (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w)
  have hsumcont : ContinuousWithinAt
      (fun s : ℝ => ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
            (mfderiv I I (Φ_fam s : M → M) x v))) p *
        ((chartModelBasis E).repr
          (e.continuousLinearMapAt ℝ ((Φ_fam s : M → M) x)
            (mfderiv I I (Φ_fam s : M → M) x w))) q *
        chartRicciTensor (I := I) (g_DT s) α p q
          (extChartAt I α ((Φ_fam s : M → M) x))) (Set.Ico 0 T) s₀ := by
    refine cwa_finset_sum _ (fun p _ => ?_)
    refine cwa_finset_sum _ (fun q _ => ?_)
    exact ((hcoordV p).mul (hcoordW q)).mul (hric p q)
  refine hsumcont.congr_of_eventuallyEq ?_ ?_
  · have hgnhds : chartLeviCivitaGoodSet (I := I) α ∈ nhds ((Φ_fam s₀ : M → M) x) :=
      (chartLeviCivitaGoodSet_isOpen (I := I) α).mem_nhds hgood0
    have hpg : (fun s : ℝ => (Φ_fam s : M → M) x) ⁻¹' chartLeviCivitaGoodSet (I := I) α
        ∈ nhdsWithin s₀ (Set.Ico 0 T) :=
      horbit.preimage_mem_nhdsWithin hgnhds
    filter_upwards [hpg] with s hg
    exact hsum s hg
  · exact hsum s₀ hgood0

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricci_continuous_in_metric_time
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ) (x : M) (v w : TangentSpace I x)
    (hC2 : ∀ (α : M) (y : M), y ∈ chartLeviCivitaGoodSet (I := I) α →
      ∀ i j : Fin (Module.finrank ℝ E), ∀ k : ℕ, k ≤ 2 →
        ContinuousOn
          (fun s : ℝ => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j)
            (extChartAt I α y))
          (Set.Icc 0 T)) :
    ContinuousOn (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w) (Set.Icc 0 T) := by
  classical
  open RicciContInMetricAux in
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hxgood
  have hx_base : ((extChartAt I x).symm (extChartAt I x x)) ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [(extChartAt I x).left_inv (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hxgood)]
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hxgood
  have h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 0 (by norm_num)
  have h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 1 (by norm_num)
  have h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 2 (by norm_num)
  have hbridge : ∀ t : ℝ,
      ricciTensor (I := I) (g_DT t) x v w =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) k *
              ((chartModelBasis E).repr w) i *
              chartRicciTensor (I := I) (g_DT t) x i k (extChartAt I x x) := by
    intro t
    exact ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I) (g_DT t) x
      (chartRiemannBasisIdentity_holds (I := I) (g_DT t) x) v w
  rw [show (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w)
        = fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr v) k *
                ((chartModelBasis E).repr w) i *
                chartRicciTensor (I := I) (g_DT s) x i k (extChartAt I x x) from by
    funext s; exact hbridge s]
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  exact chartRicciTensor_continuous_of_hC2 (I := I) g_DT x i k hx_int (Set.Icc 0 T)
    hx_base h0 h1 h2

open RicciContInMetricAux DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients in

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicci_jointContinuousOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (Sp : Set (ℝ × M))
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (i k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      chartRicciTensor (I := I) (g_DT q.1) α i k (extChartAt I α q.2)) Sp :=
  RicciContJointAux.jointRicci_continuousOn g_DT α Sp hgood h0 h1 h2 i k


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemann_jointContinuousOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (Sp : Set (ℝ × M))
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (i j k r : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      chartRiemannTensor (I := I) (g_DT q.1) α i j k r (extChartAt I α q.2)) Sp :=
  RicciContJointAux.jointRiemann_continuousOn g_DT α Sp hgood h0 h1 h2 i j k r


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciChartFrameComp_jointContinuousOn [I.Boundaryless]
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (Sp : Set (ℝ × M))
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun q : ℝ × M =>
      ricciTensor (I := I) (g_DT q.1) q.2
        (chartBasisVecFiber (I := I) α i q.2)
        (chartBasisVecFiber (I := I) α j q.2)) Sp :=
  (chartRicci_jointContinuousOn g_DT α Sp hgood h0 h1 h2 i j).congr
    (fun q hq => ricciTensor_chartBasisVec_alpha_eq (I := I) (g_DT q.1) α i j (hgood q hq))

omit [CompactSpace M] in


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricScalar_chartTrace_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    metricScalarAt (I := I) g x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α i j (extChartAt I α x) *
          ricciTensor (I := I) g x
            (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x) := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hxsrc : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hgram : ∀ k l : Fin (Module.finrank ℝ E),
      g.inner x (chartBasisFamily (I := I) α hbase k) (chartBasisFamily (I := I) α hbase l)
        = chartGramMatrix (I := I) g α x k l := by
    intro k l
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    exact (chartGramMatrix_apply (I := I) g α x k l).symm
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x
      (chartBasisFamily (I := I) α hbase)
      (fun k l => chartInvGramMatrix (I := I) g α x k l) := by
    intro i j
    refine ⟨?_, ?_⟩
    · simp only [hgram]
      rw [← Matrix.mul_apply, chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hbase,
        Matrix.one_apply]
    · simp only [hgram]
      rw [← Matrix.mul_apply, chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hbase,
        Matrix.one_apply]
  have htrace := DifferentialGeometry.Integral.Connection.metricTracePair0SAt_eq_sum_basis
    (I := I) g (chartBasisFamily (I := I) α hbase)
    (fun k l => chartInvGramMatrix (I := I) g α x k l) hinv (metricRicciAt (I := I) g x)
  unfold metricScalarAt
  rw [htrace]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc, chartBasisFamily_apply,
    chartBasisFamily_apply]
  congr 1
  exact metricRicciAt_apply_eq_ricciTensor (I := I) g x
    (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)


omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartScalar_jointContinuousOn [I.Boundaryless]
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (Sp : Set (ℝ × M))
    (hgood : ∀ q ∈ Sp, q.2 ∈ chartLeviCivitaGoodSet (I := I) α)
    (h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 0
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 1
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp)
    (h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × M => iteratedFDeriv ℝ 2
        (chartGramOnE (I := I) (g_DT q.1) α a b) (extChartAt I α q.2)) Sp) :
    ContinuousOn (fun q : ℝ × M => metricScalarAt (I := I) (g_DT q.1) q.2) Sp := by
  refine (?_ : ContinuousOn (fun q : ℝ × M =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (g_DT q.1) α i j (extChartAt I α q.2) *
          ricciTensor (I := I) (g_DT q.1) q.2
            (chartBasisVecFiber (I := I) α i q.2)
            (chartBasisVecFiber (I := I) α j q.2)) Sp).congr
    (fun q hq => metricScalar_chartTrace_eq (I := I) (g_DT q.1) α (hgood q hq))
  refine continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ => ?_))
  exact (RicciContJointAux.jointInvGram_continuousOn g_DT α Sp hgood
      (fun a b => RicciContJointAux.jointGram_continuousOn g_DT α Sp h0 a b) i j).mul
    (ricciChartFrameComp_jointContinuousOn (I := I) g_DT α Sp hgood h0 h1 h2 i j)

open RicciContInMetricAux
  DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieDeriv_deTurckVF_continuous_in_metric_time
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (x : M) (v w : TangentSpace I x)
    (hC2 : ∀ (α : M) (y : M), y ∈ chartLeviCivitaGoodSet (I := I) α →
      ∀ i j : Fin (Module.finrank ℝ E), ∀ k : ℕ, k ≤ 2 →
        ContinuousOn
          (fun s : ℝ => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j)
            (extChartAt I α y))
          (Set.Icc 0 T)) :
    ContinuousOn (fun s : ℝ =>
      lieDerivMetric (I := I) (g_DT s)
        (deTurckVF (I := I) (g_DT s) g_bg) x v w) (Set.Icc 0 T) := by
  classical
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hxgood
  have hx_base : ((extChartAt I x).symm (extChartAt I x x)) ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [(extChartAt I x).left_inv (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hxgood)]
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hxgood
  have h0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 0
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 0 (by norm_num)
  have h1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 1
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 1 (by norm_num)
  have h2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ 2
        (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT t) x a b)
        (extChartAt I x x)) (Set.Icc 0 T) :=
    fun a b => hC2 x x hxgood a b 2 (by norm_num)
  have hbridge : ∀ t : ℝ,
      lieDerivMetric (I := I) (g_DT t)
          (deTurckVF (I := I) (g_DT t) g_bg) x v w =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) i *
              ((chartModelBasis E).repr w) j *
              chartLieDeTurckComp (I := I) (g_DT t) g_bg x i j (extChartAt I x x) := by
    intro t
    rw [lieDerivMetric_apply]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [lieDerivMetricMatrix_def_chart,
      chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp (I := I) (g_DT t) g_bg x i j hxgood]
  rw [show (fun s : ℝ =>
        lieDerivMetric (I := I) (g_DT s)
          (deTurckVF (I := I) (g_DT s) g_bg) x v w)
        = fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr v) i *
                ((chartModelBasis E).repr w) j *
                chartLieDeTurckComp (I := I) (g_DT s) g_bg x i j (extChartAt I x x) from by
    funext s; exact hbridge s]
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  exact chartLieDeTurckComp_continuous_of_hC2 (I := I) g_DT g_bg x i j hx_int (Set.Icc 0 T)
    hx_base h0 h1 h2

end DifferentialGeometry.PDE.RicciFlow
