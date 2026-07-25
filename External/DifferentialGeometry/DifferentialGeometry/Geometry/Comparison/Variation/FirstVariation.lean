import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport
import DifferentialGeometry.Geometry.Comparison.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Compactness.Compact
import DifferentialGeometry.Geometry.Comparison.Variation.ArcLength
import DifferentialGeometry.Geometry.Comparison.Variation.SpeedDerivative



noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

omit [T2Space M] [SigmaCompactSpace M] in
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [NeZero (Module.finrank ℝ E)] in
lemma metric_compat_hasDerivAt_inner_of_chartCurveDeriv
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t₀ : ℝ)
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_chartDeriv :
      DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀)
    (hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀)
    (hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t₀) t₀) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (W s))
      (g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀)) t₀ := by
  classical
  set α : M := γ t₀ with hα_def
  set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
  set Wrep : ℝ → E := chartRepAt (I := I) γ W t₀ with hWrep_def
  have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H (γ t₀)
  have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
    hγ_cont (hbaseSet_open.mem_nhds hbase_t₀)
  have hVround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
      (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s) = V s := by
    intro s hs
    simpa [hVrep_def, chartRepAt_apply] using
      (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hs (V s)
  have hWround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
      (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Wrep s) = W s := by
    intro s hs
    simpa [hWrep_def, chartRepAt_apply] using
      (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hs (W s)
  set f : ℝ → ℝ := fun s => g.inner (γ s) (V s) (W s) with hf_def
  have hf_eq : f =ᶠ[𝓝 t₀]
      fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep Wrep s := by
    filter_upwards [hsrc_mem] with s hs
    have hVs := hVround s hs
    have hWs := hWround s hs
    have hfs : f s = g.inner (γ s)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Wrep s)) := by
      rw [hf_def]; rw [hVs, hWs]
    rw [hfs, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (Vrep s) (Wrep s)]
    rw [AlongCurve.chartGramAlongCurve_def]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ s) = γ s := by
      rw [chartCurve_def]
      refine (extChartAt I α).left_inv ?_
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      rw [TangentBundle.trivializationAt_baseSet] at hs
      exact hs
    rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hinv]
  have hu_hasDerivAt : HasDerivAt (chartCurve (I := I) α γ)
      (deriv (chartCurve (I := I) α γ) t₀) t₀ :=
    hγ_chartDeriv.hasDerivAt
  have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
    have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α ((extChartAt I α).map_source hxsrc)
  have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ := hVdiff.hasDerivAt
  have hWrep_hasDerivAt : HasDerivAt Wrep (deriv Wrep t₀) t₀ := hWdiff.hasDerivAt
  have hgram := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep Wrep
    (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
    (Vprime := fun _ => deriv Vrep t₀)
    (Wprime := fun _ => deriv Wrep t₀)
    hu_hasDerivAt hmem_int hVrep_hasDerivAt hWrep_hasDerivAt
  have hbase_set0 : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  have hDVchart :
      deriv Vrep t₀ +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
          (chartCurve (I := I) α γ t₀)
        = chartCovDerivAlong (I := I) g α γ Vrep t₀ := by
    rw [chartCovDerivAlong_def]
  have hDWchart :
      deriv Wrep t₀ +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t₀) (Wrep t₀)
          (chartCurve (I := I) α γ t₀)
        = chartCovDerivAlong (I := I) g α γ Wrep t₀ := by
    rw [chartCovDerivAlong_def]
  have hDV_eq : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
        (covDerivAlong (I := I) g γ V t₀)
      = chartCovDerivAlong (I := I) g α γ Vrep t₀ := by
    have := covDerivAlong_chartCoord (I := I) g γ V t₀
    rw [hα_def, hVrep_def]; exact this
  have hDW_eq : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
        (covDerivAlong (I := I) g γ W t₀)
      = chartCovDerivAlong (I := I) g α γ Wrep t₀ := by
    have := covDerivAlong_chartCoord (I := I) g γ W t₀
    rw [hα_def, hWrep_def]; exact this
  have hVt₀_coord : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (V t₀) = Vrep t₀ := by
    rw [hVrep_def, chartRepAt_apply, hα_def]
  have hWt₀_coord : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (W t₀) = Wrep t₀ := by
    rw [hWrep_def, chartRepAt_apply, hα_def]
  have hrtV : (trivializationAt E (TangentSpace I) α).symmL ℝ α (Vrep t₀) = V t₀ := by
    rw [← hVt₀_coord]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtW : (trivializationAt E (TangentSpace I) α).symmL ℝ α (Wrep t₀) = W t₀ := by
    rw [← hWt₀_coord]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtDV : (trivializationAt E (TangentSpace I) α).symmL ℝ α
        (chartCovDerivAlong (I := I) g α γ Vrep t₀)
      = covDerivAlong (I := I) g γ V t₀ := by
    rw [← hDV_eq]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtDW : (trivializationAt E (TangentSpace I) α).symmL ℝ α
        (chartCovDerivAlong (I := I) g α γ Wrep t₀)
      = covDerivAlong (I := I) g γ W t₀ := by
    rw [← hDW_eq]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  set u0 : E := chartCurve (I := I) α γ t₀ with hu0_def
  have hu0_eq : u0 = extChartAt I α α := by
    rw [hu0_def, chartCurve_def, hα_def]
  have hGram_eq : ∀ l j : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
        = chartGramMatrix (I := I) g α α l j := by
    intro l j
    rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hu0_eq,
      (extChartAt I α).left_inv (mem_extChartAt_source α)]
  have hinnerDV :
      g.inner α (covDerivAlong (I := I) g γ V t₀) (W t₀)
        = ∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
              * chartCoord (E := E) l (chartCovDerivAlong (I := I) g α γ Vrep t₀)
              * chartCoord (E := E) j (Wrep t₀) := by
    rw [← hrtDV, ← hrtW, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α _ _]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hGram_eq l j]
  have hinnerDW :
      g.inner α (V t₀) (covDerivAlong (I := I) g γ W t₀)
        = ∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α i l u0
              * chartCoord (E := E) i (Vrep t₀)
              * chartCoord (E := E) l (chartCovDerivAlong (I := I) g α γ Wrep t₀) := by
    rw [← hrtV, ← hrtDW, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α _ _]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [hGram_eq i l]
  refine (hgram.congr_of_eventuallyEq hf_eq).congr_deriv ?_
  rw [hinnerDV, hinnerDW]
  simp only [← hDVchart, ← hDWchart]

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inner_deriv_at
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t₀ : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t₀)
    (hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀)
    (hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t₀) t₀) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (W s))
      (g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀)) t₀ := by
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hn; exact absurd hn (by simp)
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀ := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n ((extChartAt I (γ t₀)) ∘ γ) t₀ := by
      have hφ : ContMDiffAt I 𝓘(ℝ, E) n (extChartAt I (γ t₀)) (γ t₀) :=
        (contMDiffAt_extChartAt (I := I) (x := γ t₀)).of_le (by exact_mod_cast le_top)
      exact hφ.comp t₀ hγ
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt hn0
  exact metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I) g γ V W t₀
    hγ.continuousAt hchartDeriv hVdiff hWdiff

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma metric_compat_hasDerivAt_inner
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t₀ : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀)
    (hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t₀) t₀) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (W s))
      (g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀)) t₀ := by
  exact inner_deriv_at (I := I) hn g γ V W t₀ hγ.contMDiffAt hVdiff hWdiff

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma commute_ds_dt_intrinsic
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t := by
  classical
  set α : M := f 0 t with hα
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f s u) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun u : ℝ => (s, u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f u v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun u : ℝ => (u, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun s : ℝ => f s t) := hslice_v t
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := hslice_u 0
  rw [covDerivAlong_def, covDerivAlong_def]
  have hfootL : (fun s : ℝ => f s t) 0 = α := by rw [hα]
  have hfootR : (fun v : ℝ => f 0 v) t = α := by rw [hα]
  set repL : ℝ → E := chartRepAt (I := I) (fun s : ℝ => f s t)
    (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 with hrepL
  set repR : ℝ → E := chartRepAt (I := I) (fun v : ℝ => f 0 v)
    (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t with hrepR
  set secL : ℝ → E :=
    fun s : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ) with hsecL
  set secR : ℝ → E :=
    fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ) with hsecR
  have hopenL : IsOpen {s : ℝ | f s t ∈ (chartAt H α).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0L : (0 : ℝ) ∈ {s : ℝ | f s t ∈ (chartAt H α).source} := by
    change f 0 t ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t)
  have hrepL_eq : repL =ᶠ[𝓝 (0 : ℝ)] secL := by
    filter_upwards [hopenL.mem_nhds h0L] with s hs
    have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := hs
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f s u) ((hslice_u s).mdifferentiableAt (by norm_num)) α hsrc
    change (trivializationAt E (TangentSpace I) ((fun s : ℝ => f s t) 0)).continuousLinearMapAt ℝ
        ((fun s : ℝ => f s t) s) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
      = fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ)
    rw [hfootL]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun v : ℝ => extChartAt I α (f s v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  have hopenR : IsOpen {v : ℝ | f 0 v ∈ (chartAt H α).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0R : t ∈ {v : ℝ | f 0 v ∈ (chartAt H α).source} := by
    change f 0 t ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t)
  have hrepR_eq : repR =ᶠ[𝓝 t] secR := by
    filter_upwards [hopenR.mem_nhds h0R] with v hv
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f u v) ((hslice_v v).mdifferentiableAt (by norm_num)) α hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ))
      = fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    rw [hfootR]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  have hchartL : chartCovDerivAlong (I := I) g ((fun s : ℝ => f s t) 0) (fun s : ℝ => f s t) repL 0
      = chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0 := by
    rw [hfootL, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepL_eq.deriv_eq,
      hrepL_eq.eq_of_nhds]
  have hchartR : chartCovDerivAlong (I := I) g ((fun v : ℝ => f 0 v) t) (fun v : ℝ => f 0 v) repR t
      = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t := by
    rw [hfootR, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepR_eq.deriv_eq,
      hrepR_eq.eq_of_nhds]
  have hcommute := commute_ds_dt_fixed_chart (I := I) g f hf 0 t
  rw [show f (0 : ℝ) t = α from hα] at hcommute
  have hcommute' :
      chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0
        = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t :=
    hcommute
  rw [hchartL, hchartR]
  rw [hcommute']

omit [T2Space M] [SigmaCompactSpace M] in
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_commute_transverse_longitudinal_of_variation
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ)
    (hF2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => extChartAt I (f 0 t) (f p.1 p.2)) (0, t))
    (hslice_u : ∀ᶠ s in 𝓝 (0 : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => f s u) t)
    (hslice_v : ∀ᶠ v in 𝓝 t, ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => f u v) 0)
    (htransverse_cont : ContinuousAt (fun s : ℝ => f s t) 0)
    (hcentral_cont : ContinuousAt (fun v : ℝ => f 0 v) t) :
    covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t := by
  classical
  set α : M := f 0 t with hα
  rw [covDerivAlong_def, covDerivAlong_def]
  have hfootL : (fun s : ℝ => f s t) 0 = α := by rw [hα]
  have hfootR : (fun v : ℝ => f 0 v) t = α := by rw [hα]
  set repL : ℝ → E := chartRepAt (I := I) (fun s : ℝ => f s t)
    (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 with hrepL
  set repR : ℝ → E := chartRepAt (I := I) (fun v : ℝ => f 0 v)
    (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t with hrepR
  set secL : ℝ → E :=
    fun s : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ) with hsecL
  set secR : ℝ → E :=
    fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ) with hsecR
  have hsrcL_nhds : {s : ℝ | f s t ∈ (chartAt H α).source} ∈ 𝓝 (0 : ℝ) := by
    refine htransverse_cont.preimage_mem_nhds ?_
    rw [hα]; exact (chartAt H α).open_source.mem_nhds (mem_chart_source H (f 0 t))
  have hrepL_eq : repL =ᶠ[𝓝 (0 : ℝ)] secL := by
    filter_upwards [hsrcL_nhds, hslice_u] with s hs hslice_u_s
    have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := hs
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t :=
      hslice_u_s.mdifferentiableAt (by decide)
    have hbridge :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (γ := fun u : ℝ => f s u) hmdiff α (t := t) hsrc
    change (trivializationAt E (TangentSpace I) ((fun s : ℝ => f s t) 0)).continuousLinearMapAt ℝ
        ((fun s : ℝ => f s t) s) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
      = fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ)
    rw [hfootL]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun v : ℝ => extChartAt I α (f s v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  have hsrcR_nhds : {v : ℝ | f 0 v ∈ (chartAt H α).source} ∈ 𝓝 t := by
    refine hcentral_cont.preimage_mem_nhds ?_
    rw [hα]; exact (chartAt H α).open_source.mem_nhds (mem_chart_source H (f 0 t))
  have hrepR_eq : repR =ᶠ[𝓝 t] secR := by
    filter_upwards [hsrcR_nhds, hslice_v] with v hv hslice_v_v
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0 :=
      hslice_v_v.mdifferentiableAt (by decide)
    have hbridge :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (γ := fun u : ℝ => f u v) hmdiff α (t := 0) hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ))
      = fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    rw [hfootR]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  have hchartL : chartCovDerivAlong (I := I) g ((fun s : ℝ => f s t) 0) (fun s : ℝ => f s t) repL 0
      = chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0 := by
    rw [hfootL, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepL_eq.deriv_eq,
      hrepL_eq.eq_of_nhds]
  have hchartR : chartCovDerivAlong (I := I) g ((fun v : ℝ => f 0 v) t) (fun v : ℝ => f 0 v) repR t
      = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t := by
    rw [hfootR, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepR_eq.deriv_eq,
      hrepR_eq.eq_of_nhds]
  have hcommute := commute_ds_dt_fixed_chart_C2 (I := I) g f 0 t (by rw [← hα]; exact hF2)
  rw [show f (0 : ℝ) t = α from hα] at hcommute
  have hcommute' :
      chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0
        = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t :=
    hcommute
  rw [hchartL, hchartR]
  rw [hcommute']

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartPulled_contDiffAt_infty
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (α : M) (s₀ t₀ : ℝ)
    (hsrc : f s₀ t₀ ∈ (chartAt H α).source) :
    ContDiffAt ℝ (8 : ℕ) (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s₀, t₀) := by
  have hext : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I α) (f s₀ t₀) :=
    contMDiffAt_extChartAt' (I := I) (n := (8 : ℕ)) (x := α) hsrc
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ)
      (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s₀, t₀) :=
    hext.comp (s₀, t₀) hf.contMDiffAt
  rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma variationField_chartRep_differentiableAt
    (_g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t₀ : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t₀) t₀ := by
  classical
  set α : M := f 0 t₀ with hα
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f u v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun u : ℝ => (u, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set sec : ℝ → E := fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    with hsec
  have hsec_cdiff : ContDiffAt ℝ (7 : ℕ) sec t₀ := by
    have hsrc0 : f 0 t₀ ∈ (chartAt H α).source := by rw [hα]; exact mem_chart_source H (f 0 t₀)
    have hjoint : ContDiffAt ℝ (8 : ℕ)
        (Function.uncurry (fun v u : ℝ => extChartAt I α (f u v))) (t₀, (0 : ℝ)) := by
      have h := chartPulled_contDiffAt_infty (I := I) f hf α 0 t₀ hsrc0
      have hswap : ContDiffAt ℝ (8 : ℕ)
          ((fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) ∘ (fun q : ℝ × ℝ => (q.2, q.1)))
          (t₀, (0 : ℝ)) :=
        h.comp (t₀, (0 : ℝ)) ((contDiffAt_snd).prodMk (contDiffAt_fst))
      exact hswap
    have hg0 : ContDiffAt ℝ (7 : ℕ) (fun _ : ℝ => (0 : ℝ)) t₀ := contDiffAt_const
    have hpartial : ContDiffAt ℝ (7 : ℕ)
        (fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) ((fun _ : ℝ => (0:ℝ)) v)) t₀ :=
      ContDiffAt.fderiv (𝕜 := ℝ)
        (f := fun v u : ℝ => extChartAt I α (f u v)) (g := fun _ : ℝ => (0 : ℝ))
        hjoint hg0 (by exact_mod_cast (by norm_num : (7 : ℕ) + 1 ≤ 8))
    have heval : ContDiffAt ℝ (7 : ℕ)
        (fun v : ℝ => (ContinuousLinearMap.apply ℝ E (1 : ℝ))
          (fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0)) t₀ :=
      (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀ hpartial
    exact heval
  have hopen : IsOpen {v : ℝ | f 0 v ∈ (chartAt H α).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0 : t₀ ∈ {v : ℝ | f 0 v ∈ (chartAt H α).source} := by
    change f 0 t₀ ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t₀)
  have heq : (chartRepAt (I := I) (fun v : ℝ => f 0 v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t₀)
        =ᶠ[𝓝 t₀] sec := by
    filter_upwards [hopen.mem_nhds h0] with v hv
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun u : ℝ => f u v) ((hslice_v v).mdifferentiableAt (by norm_num)) α hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t₀)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) = sec v
    rw [hsec, show (fun v : ℝ => f 0 v) t₀ = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_cdiff.differentiableAt (by simp))

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma velocityField_chartRep_differentiableAt
    (_g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t₀ : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) v (1 : ℝ)) t₀) t₀ := by
  classical
  set α : M := f 0 t₀ with hα
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  set sec : ℝ → E := fun v : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f 0 w)) v (1 : ℝ)
    with hsec
  have hchartcurve_cdiff : ContDiffAt ℝ (8 : ℕ) (fun w : ℝ => extChartAt I α (f 0 w)) t₀ := by
    have hext : ContMDiffAt I 𝓘(ℝ, E) (8 : ℕ) (extChartAt I α) (f 0 t₀) :=
      (contMDiffAt_extChartAt (I := I) (x := α)).of_le (by exact_mod_cast le_top)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ) (fun w : ℝ => extChartAt I α (f 0 w)) t₀ :=
      hext.comp t₀ hcentral.contMDiffAt
    exact contMDiffAt_iff_contDiffAt.mp hcomp
  have hsec_cdiff : ContDiffAt ℝ (7 : ℕ) sec t₀ := by
    have hfd : ContDiffAt ℝ (7 : ℕ) (fderiv ℝ (fun w : ℝ => extChartAt I α (f 0 w))) t₀ :=
      hchartcurve_cdiff.fderiv_right (by exact_mod_cast (by norm_num : (7 : ℕ) + 1 ≤ 8))
    have heval : ContDiffAt ℝ (7 : ℕ)
        (fun v : ℝ => (ContinuousLinearMap.apply ℝ E (1 : ℝ))
          (fderiv ℝ (fun w : ℝ => extChartAt I α (f 0 w)) v)) t₀ :=
      (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀ hfd
    exact heval
  have hopen : IsOpen {v : ℝ | f 0 v ∈ (chartAt H α).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0 : t₀ ∈ {v : ℝ | f 0 v ∈ (chartAt H α).source} := by
    change f 0 t₀ ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t₀)
  have heq : (chartRepAt (I := I) (fun v : ℝ => f 0 v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) v (1 : ℝ)) t₀)
        =ᶠ[𝓝 t₀] sec := by
    filter_upwards [hopen.mem_nhds h0] with v hv
    have hsrc : (fun w : ℝ => f 0 w) v ∈ (chartAt H α).source := hv
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := fun w : ℝ => f 0 w) (hcentral.mdifferentiableAt (by norm_num)) α hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t₀)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) v (1 : ℝ)) = sec v
    rw [hsec, show (fun v : ℝ => f 0 v) t₀ = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun w : ℝ => f 0 w))
        = (fun w : ℝ => extChartAt I α (f 0 w)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_cdiff.differentiableAt (by simp))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma g_inner_along_curve_contMDiff
    {n : WithTop ℕ∞} [ENat.LEInfty n] (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {v w : ∀ t : ℝ, TangentSpace I (γ t)}
    (hv : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) n (fun t : ℝ => (TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t) (v t) : TangentBundle I M)))
    (hw : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) n (fun t : ℝ => (TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t) (w t) : TangentBundle I M))) :
    ContDiff ℝ n (fun t : ℝ => g.inner (γ t) (v t) (w t)) := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hinner := ContMDiff.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _)) (b := γ) (v := v) (w := w) hv hw
  have hcm : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) n (fun t : ℝ => g.inner (γ t) (v t) (w t)) := by
    refine hinner.congr (fun t => ?_); rfl
  rw [← contMDiff_iff_contDiff]; exact hcm

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem first_variation_of_arcLength_fixed_endpoints
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hfix0 : ∀ s : ℝ, f s 0 = f 0 0) (hfixL : ∀ s : ℝ, f s L = f 0 L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) = 1) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      (- ∫ t in (0 : ℝ)..L,
        g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g (fun v : ℝ => f 0 v)
            (fun v : ℝ =>
              mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  set γ : ℝ → M := fun v : ℝ => f 0 v with hγ_def
  set V : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) with hV_def
  set γ' : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) with hγ'_def
  have hUnit' : ∀ t ∈ Set.Icc (0 : ℝ) L, speedSq (I := I) g f 0 t = 1 := by
    intro t ht; exact hUnit t ht
  have harc : (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      = (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t)) := by
    funext s; exact arcLength_slice_eq_integral_sqrt_speedSq (I := I) g f s L
  rw [harc]
  have hS2 := speedIntegral_hasDerivAt (I := I) g f L hf hL hUnit'
  have hsqrt1 : ∀ t ∈ Set.Icc (0 : ℝ) L, Real.sqrt (speedSq (I := I) g f 0 t) = 1 := by
    intro t ht; rw [hUnit' t ht, Real.sqrt_one]
  have hintegrand_eq : Set.EqOn
      (fun t : ℝ =>
        (2 * g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
          / (2 * Real.sqrt (speedSq (I := I) g f 0 t)))
      (fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t))
      (Set.uIcc 0 L) := by
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hL)] at ht
    simp only []
    rw [hsqrt1 t ht, mul_one]
    have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
    rw [show covDerivAlong (I := I) g (fun s : ℝ => f s t)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
        = covDerivAlong (I := I) g γ V t from by
      rw [hcomm, hγ_def, hV_def]]
    rw [hγ'_def, hγ_def]
    ring
  rw [intervalIntegral.integral_congr hintegrand_eq] at hS2
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hVdiff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀ := by
    intro t₀; rw [hγ_def, hV_def]
    exact variationField_chartRep_differentiableAt (I := I) g f hf t₀
  have hγ'diff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ γ' t₀) t₀ := by
    intro t₀; rw [hγ_def, hγ'_def]
    exact velocityField_chartRep_differentiableAt (I := I) g f hf t₀
  have hbdry : ∀ t ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (γ' s))
        (g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
          + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t)) t := by
    intro t _ht
    exact metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
  have hV0 : V 0 = 0 := by
    change mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ) = 0
    have hconst : (fun u : ℝ => f u 0) = (fun _ : ℝ => f 0 0) := by funext u; exact hfix0 u
    rw [hconst, mfderiv_const]; rfl
  have hVL : V L = 0 := by
    change mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u L) 0 (1 : ℝ) = 0
    have hconst : (fun u : ℝ => f u L) = (fun _ : ℝ => f 0 L) := by funext u; exact hfixL u
    rw [hconst, mfderiv_const]; rfl
  set hbd : ℝ → ℝ := fun s : ℝ => g.inner (γ s) (V s) (γ' s) with hbd_def
  set hbd' : ℝ → ℝ := fun t : ℝ =>
    g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
      + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t) with hbd'_def
  have hfswap : IsSmoothVariation (I := I) (fun a b : ℝ => f b a) := by
    have hswapmap : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun q : ℝ × ℝ => (q.2, q.1)) := contMDiff_snd.prodMk contMDiff_fst
    exact (hf : ContMDiff _ _ _ _).comp hswapmap
  have hVtotal : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) (7 : ℕ) (fun t : ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) (fun a b : ℝ => f b a) hfswap
    have hcomp := hbase.comp
      (contMDiff_id.prodMk contMDiff_const : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (7 : ℕ)
        (fun t : ℝ => (t, (0 : ℝ))))
    refine hcomp.congr (fun t => ?_)
    rfl
  have hγ'total : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) (7 : ℕ) (fun t : ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (γ' t) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
    have hcomp := hbase.comp
      (contMDiff_const.prodMk contMDiff_id : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (7 : ℕ)
        (fun t : ℝ => ((0 : ℝ), t)))
    refine hcomp.congr (fun t => ?_)
    rfl
  have hbd_contdiff : ContDiff ℝ (7 : ℕ) hbd :=
    g_inner_along_curve_contMDiff (I := I) (M := M) g hVtotal hγ'total
  have hderiv_cont : Continuous (deriv hbd) := hbd_contdiff.continuous_deriv (by norm_num)
  have hbd'_eq_deriv : ∀ t : ℝ, hbd' t = deriv hbd t := by
    intro t
    have hd : HasDerivAt hbd (hbd' t) t := by
      have := metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
      exact this
    exact (hd.deriv).symm
  have hbd'_cont : Continuous hbd' := by
    refine hderiv_cont.congr (fun t => (hbd'_eq_deriv t).symm)
  have hbd'_int : IntervalIntegrable hbd' MeasureTheory.volume 0 L :=
    hbd'_cont.continuousOn.intervalIntegrable
  have hFTC : (∫ t in (0 : ℝ)..L, hbd' t) = hbd L - hbd 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) hbd'_int
    exact metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
  have hbdL0 : hbd L = 0 := by
    change g.inner (γ L) (V L) (γ' L) = 0
    rw [hVL, map_zero, ContinuousLinearMap.zero_apply]
  have hbd00 : hbd 0 = 0 := by
    change g.inner (γ 0) (V 0) (γ' 0) = 0
    rw [hV0, map_zero, ContinuousLinearMap.zero_apply]
  rw [hbdL0, hbd00, sub_zero] at hFTC
  set A : ℝ → ℝ := fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
    with hA_def
  set D2num : ℝ → ℝ := fun t : ℝ =>
    2 * g.inner (f 0 t)
      (covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) with hD2num_def
  have hG : ContDiff ℝ (7 : ℕ) (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_contDiff (I := I) (M := M) g f hf
  have hD2num_eq : ∀ t : ℝ,
      D2num t = fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) (1, 0) := by
    intro t
    have hS1 := speedSq_hasDerivAt (I := I) g f t hf
    have hslice : HasDerivAt
        (fun u : ℝ => (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (u, t))
        (fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) (1, 0)) 0 := by
      have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) :=
        (hG.differentiable (by simp)).differentiableAt
      have := Aux2.hasDerivAt_slice_fst
        (fun u v : ℝ => speedSq (I := I) g f u v) 0 t hdiff
      simpa using this
    have hS1' : HasDerivAt
        (fun u : ℝ => (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (u, t)) (D2num t) 0 := by
      simpa [hD2num_def] using hS1
    exact hS1'.unique hslice
  have hD2num_cont : Continuous D2num := by
    have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ =>
        speedSq (I := I) g f q.1 q.2) p) := hG.continuous_fderiv (by simp)
    have hcapp : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ =>
        speedSq (I := I) g f q.1 q.2) p (1, 0)) := hc.clm_apply continuous_const
    have : Continuous (fun t : ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => speedSq (I := I) g f q.1 q.2) (0, t) (1, 0)) :=
      hcapp.comp (continuous_const.prodMk continuous_id)
    exact this.congr (fun t => (hD2num_eq t).symm)
  have hA_eq_half : ∀ t : ℝ, A t = D2num t / 2 := by
    intro t
    change g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
      = (2 * g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))) / 2
    have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
    rw [show covDerivAlong (I := I) g γ V t
        = covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 from by
      rw [hγ_def, hV_def]; rw [hcomm]]
    rw [hγ'_def, hγ_def]; ring
  have hA_cont : Continuous A := by
    have : A = (fun t : ℝ => D2num t / 2) := by funext t; exact hA_eq_half t
    rw [this]; exact hD2num_cont.div_const 2
  have hA_int : IntervalIntegrable A MeasureTheory.volume 0 L :=
    hA_cont.continuousOn.intervalIntegrable
  set B : ℝ → ℝ := fun t : ℝ => g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t)
    with hB_def
  have hB_eq : ∀ t : ℝ, B t = hbd' t - A t := by
    intro t; rw [hB_def, hbd'_def, hA_def]; ring
  have hB_cont : Continuous B := by
    have : B = (fun t : ℝ => hbd' t - A t) := by funext t; exact hB_eq t
    rw [this]; exact hbd'_cont.sub hA_cont
  have hB_int : IntervalIntegrable B MeasureTheory.volume 0 L :=
    hB_cont.continuousOn.intervalIntegrable
  have hsplit : (∫ t in (0 : ℝ)..L, hbd' t)
      = (∫ t in (0 : ℝ)..L, A t) + (∫ t in (0 : ℝ)..L, B t) := by
    rw [← intervalIntegral.integral_add hA_int hB_int]
  rw [hsplit] at hFTC
  have hAB : (∫ t in (0 : ℝ)..L, A t) = - (∫ t in (0 : ℝ)..L, B t) := by linarith [hFTC]
  have hS2A : HasDerivAt
      (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t))
      (∫ t in (0 : ℝ)..L, A t) 0 := hS2
  rw [hAB] at hS2A
  exact hS2A

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem first_variation_of_arcLength_free_endpoints
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) = 1) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      ( (g.inner (f 0 L)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u L) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) L (1 : ℝ))
         - g.inner (f 0 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) 0 (1 : ℝ)))
        - ∫ t in (0 : ℝ)..L,
          g.inner (f 0 t)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
            (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
              (I := I) g (fun v : ℝ => f 0 v)
              (fun v : ℝ =>
                mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  set γ : ℝ → M := fun v : ℝ => f 0 v with hγ_def
  set V : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) with hV_def
  set γ' : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) with hγ'_def
  have hUnit' : ∀ t ∈ Set.Icc (0 : ℝ) L, speedSq (I := I) g f 0 t = 1 := by
    intro t ht; exact hUnit t ht
  have harc : (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      = (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t)) := by
    funext s; exact arcLength_slice_eq_integral_sqrt_speedSq (I := I) g f s L
  rw [harc]
  have hS2 := speedIntegral_hasDerivAt (I := I) g f L hf hL hUnit'
  have hsqrt1 : ∀ t ∈ Set.Icc (0 : ℝ) L, Real.sqrt (speedSq (I := I) g f 0 t) = 1 := by
    intro t ht; rw [hUnit' t ht, Real.sqrt_one]
  have hintegrand_eq : Set.EqOn
      (fun t : ℝ =>
        (2 * g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
          / (2 * Real.sqrt (speedSq (I := I) g f 0 t)))
      (fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t))
      (Set.uIcc 0 L) := by
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hL)] at ht
    simp only []
    rw [hsqrt1 t ht, mul_one]
    have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
    rw [show covDerivAlong (I := I) g (fun s : ℝ => f s t)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
        = covDerivAlong (I := I) g γ V t from by
      rw [hcomm, hγ_def, hV_def]]
    rw [hγ'_def, hγ_def]
    ring
  rw [intervalIntegral.integral_congr hintegrand_eq] at hS2
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hVdiff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀ := by
    intro t₀; rw [hγ_def, hV_def]
    exact variationField_chartRep_differentiableAt (I := I) g f hf t₀
  have hγ'diff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ γ' t₀) t₀ := by
    intro t₀; rw [hγ_def, hγ'_def]
    exact velocityField_chartRep_differentiableAt (I := I) g f hf t₀
  have hbdry : ∀ t ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (γ' s))
        (g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
          + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t)) t := by
    intro t _ht
    exact metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
  set hbd : ℝ → ℝ := fun s : ℝ => g.inner (γ s) (V s) (γ' s) with hbd_def
  set hbd' : ℝ → ℝ := fun t : ℝ =>
    g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
      + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t) with hbd'_def
  have hfswap : IsSmoothVariation (I := I) (fun a b : ℝ => f b a) := by
    have hswapmap : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun q : ℝ × ℝ => (q.2, q.1)) := contMDiff_snd.prodMk contMDiff_fst
    exact (hf : ContMDiff _ _ _ _).comp hswapmap
  have hVtotal : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) (7 : ℕ) (fun t : ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) (fun a b : ℝ => f b a) hfswap
    have hcomp := hbase.comp
      (contMDiff_id.prodMk contMDiff_const : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (7 : ℕ)
        (fun t : ℝ => (t, (0 : ℝ))))
    refine hcomp.congr (fun t => ?_)
    rfl
  have hγ'total : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) (7 : ℕ) (fun t : ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (γ' t) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
    have hcomp := hbase.comp
      (contMDiff_const.prodMk contMDiff_id : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (7 : ℕ)
        (fun t : ℝ => ((0 : ℝ), t)))
    refine hcomp.congr (fun t => ?_)
    rfl
  have hbd_contdiff : ContDiff ℝ (7 : ℕ) hbd :=
    g_inner_along_curve_contMDiff (I := I) (M := M) g hVtotal hγ'total
  have hderiv_cont : Continuous (deriv hbd) := hbd_contdiff.continuous_deriv (by norm_num)
  have hbd'_eq_deriv : ∀ t : ℝ, hbd' t = deriv hbd t := by
    intro t
    have hd : HasDerivAt hbd (hbd' t) t := by
      have := metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
      exact this
    exact (hd.deriv).symm
  have hbd'_cont : Continuous hbd' := by
    refine hderiv_cont.congr (fun t => (hbd'_eq_deriv t).symm)
  have hbd'_int : IntervalIntegrable hbd' MeasureTheory.volume 0 L :=
    hbd'_cont.continuousOn.intervalIntegrable
  have hFTC : (∫ t in (0 : ℝ)..L, hbd' t) = hbd L - hbd 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) hbd'_int
    exact metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
  set A : ℝ → ℝ := fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
    with hA_def
  set D2num : ℝ → ℝ := fun t : ℝ =>
    2 * g.inner (f 0 t)
      (covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) with hD2num_def
  have hG : ContDiff ℝ (7 : ℕ) (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_contDiff (I := I) (M := M) g f hf
  have hD2num_eq : ∀ t : ℝ,
      D2num t = fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) (1, 0) := by
    intro t
    have hS1 := speedSq_hasDerivAt (I := I) g f t hf
    have hslice : HasDerivAt
        (fun u : ℝ => (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (u, t))
        (fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) (1, 0)) 0 := by
      have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) :=
        (hG.differentiable (by simp)).differentiableAt
      have := Aux2.hasDerivAt_slice_fst
        (fun u v : ℝ => speedSq (I := I) g f u v) 0 t hdiff
      simpa using this
    have hS1' : HasDerivAt
        (fun u : ℝ => (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (u, t)) (D2num t) 0 := by
      simpa [hD2num_def] using hS1
    exact hS1'.unique hslice
  have hD2num_cont : Continuous D2num := by
    have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ =>
        speedSq (I := I) g f q.1 q.2) p) := hG.continuous_fderiv (by simp)
    have hcapp : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ =>
        speedSq (I := I) g f q.1 q.2) p (1, 0)) := hc.clm_apply continuous_const
    have : Continuous (fun t : ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => speedSq (I := I) g f q.1 q.2) (0, t) (1, 0)) :=
      hcapp.comp (continuous_const.prodMk continuous_id)
    exact this.congr (fun t => (hD2num_eq t).symm)
  have hA_eq_half : ∀ t : ℝ, A t = D2num t / 2 := by
    intro t
    change g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
      = (2 * g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))) / 2
    have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
    rw [show covDerivAlong (I := I) g γ V t
        = covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 from by
      rw [hγ_def, hV_def]; rw [hcomm]]
    rw [hγ'_def, hγ_def]; ring
  have hA_cont : Continuous A := by
    have : A = (fun t : ℝ => D2num t / 2) := by funext t; exact hA_eq_half t
    rw [this]; exact hD2num_cont.div_const 2
  have hA_int : IntervalIntegrable A MeasureTheory.volume 0 L :=
    hA_cont.continuousOn.intervalIntegrable
  set B : ℝ → ℝ := fun t : ℝ => g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t)
    with hB_def
  have hB_eq : ∀ t : ℝ, B t = hbd' t - A t := by
    intro t; rw [hB_def, hbd'_def, hA_def]; ring
  have hB_cont : Continuous B := by
    have : B = (fun t : ℝ => hbd' t - A t) := by funext t; exact hB_eq t
    rw [this]; exact hbd'_cont.sub hA_cont
  have hB_int : IntervalIntegrable B MeasureTheory.volume 0 L :=
    hB_cont.continuousOn.intervalIntegrable
  have hsplit : (∫ t in (0 : ℝ)..L, hbd' t)
      = (∫ t in (0 : ℝ)..L, A t) + (∫ t in (0 : ℝ)..L, B t) := by
    rw [← intervalIntegral.integral_add hA_int hB_int]
  rw [hsplit] at hFTC
  have hAB : (∫ t in (0 : ℝ)..L, A t) = (hbd L - hbd 0) - (∫ t in (0 : ℝ)..L, B t) := by
    linarith [hFTC]
  have hS2A : HasDerivAt
      (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t))
      (∫ t in (0 : ℝ)..L, A t) 0 := hS2
  rw [hAB] at hS2A
  exact hS2A

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem first_variation_geodesic_fixed_end
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (hfc : ∀ t : ℝ, f 0 t = γ t)
    (hfixL : ∀ s : ℝ, f s L = γ L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      (- g.inner (γ 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ))) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  have hfγ : (fun v : ℝ => f 0 v) = γ := by
    funext v; exact hfc v
  have hfv := first_variation_of_arcLength_free_endpoints (I := I) g f L hf hL
    (by
      intro t ht
      rw [hfc t, hfγ]
      exact hUnit t ht)
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact hfγ ▸ (hf : ContMDiff _ _ _ _).comp hincl
  have haccel0 : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t = 0 := by
    intro t ht
    have hgeo : HasGeodesicEquationAt (I := I) g γ t := hγ t ht
    have hzero : covDerivAlong (I := I) g γ
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t = 0 :=
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t
        (hγ_smooth.contMDiffAt.of_le
          (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8))) hgeo
    rw [hfγ]
    exact hzero
  have hVL : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u L) 0 (1 : ℝ) = 0 := by
    have hconst : (fun u : ℝ => f u L) = (fun _ : ℝ => γ L) := by
      funext u; exact hfixL u
    rw [hconst, mfderiv_const]
    rfl
  have hint0 : (∫ t in (0 : ℝ)..L,
      g.inner (f 0 t)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
        (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) = 0 := by
    have hcongr : (∫ t in (0 : ℝ)..L,
        g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
            (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t))
        = ∫ _t in (0 : ℝ)..L, (0 : ℝ) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le (le_of_lt hL)] at ht
      rw [haccel0 t ht, ContinuousLinearMap.map_zero]
    rw [hcongr, intervalIntegral.integral_zero]
  rw [hint0] at hfv
  rw [hVL, ContinuousLinearMap.map_zero, ContinuousLinearMap.zero_apply] at hfv
  have hcentral0 :
      mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) 0 (1 : ℝ) =
        mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ) := by
    rw [hfγ]
    rfl
  rw [hcentral0] at hfv
  rw [hfc 0] at hfv
  simpa using hfv

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dist_deriv_of_length [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (hfc : ∀ t : ℝ, f 0 t = γ t)
    (hfixL : ∀ s : ℝ, f s L = γ L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (hdist : (fun s : ℝ => dist (f s 0) (γ L)) =ᶠ[nhds (0 : ℝ)]
        (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)) :
    HasDerivAt (fun s : ℝ => dist (f s 0) (γ L))
      (- g.inner (γ 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ))) 0 := by
  exact (first_variation_geodesic_fixed_end (I := I) g γ f L hf hL hγ hfc hfixL hUnit)
    |>.congr_of_eventuallyEq hdist

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem halfSq_deriv_length [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (hfc : ∀ t : ℝ, f 0 t = γ t)
    (hfixL : ∀ s : ℝ, f s L = γ L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (hdist : (fun s : ℝ => dist (f s 0) (γ L)) =ᶠ[nhds (0 : ℝ)]
        (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L))
    (hdist0 : dist (f 0 0) (γ L) = L) :
    HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * dist (f s 0) (γ L) ^ 2)
      (L * (- g.inner (γ 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ)))) 0 := by
  have hd := dist_deriv_of_length (I := I) g γ f L hf hL hγ hfc hfixL hUnit hdist
  have hsq := (hd.pow 2).const_mul (1 / 2 : ℝ)
  simpa [hdist0, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem first_variation_vanishes_for_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (hfc : ∀ t : ℝ, f 0 t = γ t)
    (hfix0 : ∀ s : ℝ, f s 0 = γ 0) (hfixL : ∀ s : ℝ, f s L = γ L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      0 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  have hfγ : (fun v : ℝ => f 0 v) = γ := by funext v; exact hfc v
  have hfv := first_variation_of_arcLength_fixed_endpoints (I := I) g f L hf hL
    (fun s => by rw [hfix0 s, ← hfc 0]) (fun s => by rw [hfixL s, ← hfc L])
    (by
      intro t ht
      rw [hfc t, hfγ]; exact hUnit t ht)
  have hsmooth_central : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) γ := hfγ ▸ hsmooth_central
  have haccel0 : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t = 0 := by
    intro t ht
    have hgeo : HasGeodesicEquationAt (I := I) g γ t := hγ t ht
    have hzero : covDerivAlong (I := I) g γ
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t = 0 :=
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t
        (hγ_smooth.contMDiffAt.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8))) hgeo
    rw [hfγ]; exact hzero
  have hint0 : (∫ t in (0 : ℝ)..L,
      g.inner (f 0 t)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
        (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) = 0 := by
    have hcongr : (∫ t in (0 : ℝ)..L,
        g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
            (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t))
        = ∫ _t in (0 : ℝ)..L, (0 : ℝ) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le (le_of_lt hL)] at ht
      rw [haccel0 t ht, map_zero]
    rw [hcongr, intervalIntegral.integral_zero]
  rw [hint0, neg_zero] at hfv
  exact hfv

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
