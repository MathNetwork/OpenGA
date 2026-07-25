import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ChartTransition
import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelLocalODE
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.Basic
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.OneForm
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.TwoTensor
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue


noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic


omit [NeZero (Module.finrank ℝ E)] in
theorem parallel_ode_chart_local
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y : ℝ → E) (s : Set ℝ) :
    IsParallelChart (I := I) g α γ uPrime Y s ↔
      (∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) ∧
        (∀ t ∈ s, HasDerivAt Y
          (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t)) t) := by
  unfold IsParallelChart IsCovDerivAlongChart
  refine Iff.and Iff.rfl ?_
  refine forall_congr' (fun t => ?_)
  refine imp_congr_right (fun _ => ?_)
  simp [zero_sub]


omit [NeZero (Module.finrank ℝ E)] in
theorem parallel_local_existence_uniqueness [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (huCont : ContinuousOn uPrime (Set.Icc a b))
    (huCurveCont : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (v₀ : E) :
    ∃ Y : ℝ → E,
      ((∀ t ∈ Set.Icc a b, HasDerivWithinAt Y
          (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t)) (Set.Icc a b) t) ∧
        Y t₀ = v₀) ∧
      (∀ Y' : ℝ → E,
        ((∀ t ∈ Set.Icc a b, HasDerivWithinAt Y'
            (- chartChristoffelContraction (I := I) g α (uPrime t) (Y' t)
                (chartCurve (I := I) α γ t)) (Set.Icc a b) t) ∧
          Y' t₀ = v₀) →
        Set.EqOn Y Y' (Set.Icc a b)) := by
  obtain ⟨Y, hY_deriv, hY_init⟩ :=
    parallel_local_existence_on_Icc (I := I) g α γ uPrime hab ht₀ huCont
      huCurveCont hsource v₀
  refine ⟨Y, ⟨hY_deriv, hY_init⟩, ?_⟩
  rintro Y' ⟨hY'_deriv, hY'_init⟩
  exact parallel_local_uniqueness_on_Icc (I := I) g α γ uPrime hab ht₀ huCont
    huCurveCont hsource hY_deriv hY'_deriv (hY_init.trans hY'_init.symm)


theorem parallel_chart_overlap_consistency [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (γ : ℝ → M) (hγ : Continuous γ)
    (uPrimeα Yα : ℝ → E) (s : Set ℝ)
    (hαβ : ∀ t ∈ s, γ t ∈ (chartAt H α).source ∩ (chartAt H β).source)
    (hpar : IsParallelChart (I := I) g α γ uPrimeα Yα s) :
    IsParallelChart (I := I) g β γ
      (fun t => Geodesic.chartTransitionAt (I := I) α β
                  (chartCurve (I := I) α γ t) (uPrimeα t))
      (fun t => Geodesic.chartTransitionAt (I := I) α β
                  (chartCurve (I := I) α γ t) (Yα t))
      s := by
  classical
  set uPrimeβ : ℝ → E := fun t =>
    chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (uPrimeα t) with huPrimeβ
  set Yβ : ℝ → E := fun t =>
    chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (Yα t) with hYβ
  refine ⟨?_, ?_⟩
  · intro t ht
    set U : Set ℝ := γ ⁻¹' ((chartAt H α).source ∩ (chartAt H β).source) with hU_def
    have hU_open : IsOpen U :=
      ((chartAt H α).open_source.inter (chartAt H β).open_source).preimage hγ
    have htU : t ∈ U := hαβ t ht
    have hU_nhds : U ∈ 𝓝 t := hU_open.mem_nhds htU
    have hcurve_eq : (chartCurve (I := I) β γ) =ᶠ[𝓝 t]
        (fun s => chartTransitionMap (I := I) α β (chartCurve (I := I) α γ s)) := by
      filter_upwards [hU_nhds] with σ hσ
      obtain ⟨hσα, _hσβ⟩ := hσ
      rw [chartCurve_def, chartCurve_def]
      exact (chartTransitionMap_apply_extChartAt (I := I) α β hσα).symm
    have huα : HasDerivAt (chartCurve (I := I) α γ) (uPrimeα t) t :=
      IsParallelChart.chartCurve_hasDerivAt hpar ht
    have hsrc_t : chartCurve (I := I) α γ t ∈ chartTransitionSource (I := I) α β :=
      extChartAt_mem_chartTransitionSource (I := I) α β (hαβ t ht).1 (hαβ t ht).2
    have hTdiff : DifferentiableAt ℝ (chartTransitionMap (I := I) α β)
        (chartCurve (I := I) α γ t) :=
      chartTransitionMap_differentiableAt (I := I) α β hsrc_t
    have hcomp : HasDerivAt
        (fun s => chartTransitionMap (I := I) α β (chartCurve (I := I) α γ s))
        (chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (uPrimeα t)) t := by
      have := hTdiff.hasFDerivAt.comp_hasDerivAt t huα
      simpa [chartTransitionAt_def] using this
    exact (hcomp.congr_of_eventuallyEq hcurve_eq)
  · intro t ht
    obtain ⟨htα, htβ⟩ := hαβ t ht
    set x : E := chartCurve (I := I) α γ t with hx_def
    have hsrc_t : x ∈ chartTransitionSource (I := I) α β :=
      extChartAt_mem_chartTransitionSource (I := I) α β htα htβ
    have huα : HasDerivAt (chartCurve (I := I) α γ) (uPrimeα t) t :=
      IsParallelChart.chartCurve_hasDerivAt hpar ht
    have hYαd : HasDerivAt Yα
        (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x) t :=
      IsParallelChart.hasDerivAt hpar ht
    have hAdiff : DifferentiableAt ℝ
        (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E)) x := by
      have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
        chartTransitionSource_isOpen (I := I) α β
      exact ((chartTransitionAt_smooth (I := I) α β).contDiffAt
        (h_open.mem_nhds hsrc_t)).differentiableAt (by simp)
    have hcA : HasDerivAt
        (fun s => (chartTransitionAt (I := I) α β (chartCurve (I := I) α γ s) : E →L[ℝ] E))
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) t :=
      hAdiff.hasFDerivAt.comp_hasDerivAt t huα
    have hYβd : HasDerivAt Yβ
        (((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t)
          + chartTransitionAt (I := I) α β x
              (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x)) t := by
      have := hcA.clm_apply hYαd
      simpa [hYβ, hx_def] using this
    have hfoot :
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t) =
          chartTransitionAt (I := I) α β x
            (chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x) :=
      fderiv_chartTransitionAt_apply_eq_pushCorrection (I := I) α β hsrc_t
        (uPrimeα t) (Yα t)
    have hxeq : x = extChartAt I α (γ t) := by rw [hx_def, chartCurve_def]
    have htransform :
        chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x =
          chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β x)
              (chartChristoffelContraction (I := I) g β
                (chartTransitionAt (I := I) α β x (uPrimeα t))
                (chartTransitionAt (I := I) α β x (Yα t))
                (chartTransitionMap (I := I) α β x))
            + chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x := by
      rw [hxeq]
      exact chartChristoffelContraction_transform (I := I) g α β htα htβ
        (uPrimeα t) (Yα t)
    have huβ_eq : chartCurve (I := I) β γ t = chartTransitionMap (I := I) α β x := by
      rw [hx_def, chartCurve_def, chartCurve_def,
        chartTransitionMap_apply_extChartAt (I := I) α β htα]
    have hDcollapse :
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t)
          + chartTransitionAt (I := I) α β x
              (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x)
          = - chartChristoffelContraction (I := I) g β
              (uPrimeβ t) (Yβ t) (chartCurve (I := I) β γ t) := by
      rw [hfoot, map_neg, ← sub_eq_add_neg, ← map_sub]
      have hsub :
          chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x -
              chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x =
            - chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β x)
                (chartChristoffelContraction (I := I) g β
                  (chartTransitionAt (I := I) α β x (uPrimeα t))
                  (chartTransitionAt (I := I) α β x (Yα t))
                  (chartTransitionMap (I := I) α β x)) := by
        rw [htransform]; abel
      rw [hsub, map_neg]
      have hinv := chartTransitionAt_comp_chartTransitionAt' (I := I) α β hsrc_t
      have hid := congrArg (fun L : E →L[ℝ] E => L
          (chartChristoffelContraction (I := I) g β
            (chartTransitionAt (I := I) α β x (uPrimeα t))
            (chartTransitionAt (I := I) α β x (Yα t))
            (chartTransitionMap (I := I) α β x))) hinv
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hid
      rw [hid, huβ_eq]
    have hgoal : HasDerivAt Yβ
        ((fun _ : ℝ => (0 : E)) t -
          chartChristoffelContraction (I := I) g β (uPrimeβ t) (Yβ t)
            (chartCurve (I := I) β γ t)) t := by
      rw [hDcollapse] at hYβd
      simpa using hYβd
    exact hgoal


omit [NeZero (Module.finrank ℝ E)] in
theorem parallel_global_extension [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (huCont : ContinuousOn (fun t => deriv (chartCurve (I := I) α γ) t) (Set.Icc a b))
    (huCurveCont : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b))
    (huDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (chartCurve (I := I) α γ) (deriv (chartCurve (I := I) α γ) t) t)
    (hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (v₀ : E) :
    ∃ V : ℝ → E,
      (V t₀ = v₀ ∧
        IsParallelChart (I := I) g α γ
          (fun t => deriv (chartCurve (I := I) α γ) t) V (Set.Ioo a b)) ∧
      (∀ V' : ℝ → E,
        (V' t₀ = v₀ ∧
          IsParallelChart (I := I) g α γ
            (fun t => deriv (chartCurve (I := I) α γ) t) V' (Set.Ioo a b)) →
        Set.EqOn V V' (Set.Ioo a b)) := by
  obtain ⟨Y, ⟨hY_deriv, hY_init⟩, -⟩ :=
    parallel_local_existence_uniqueness (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t) hab (Set.mem_Icc_of_Ioo ht₀)
      huCont huCurveCont hsource v₀
  have hIccNhds : ∀ t ∈ Set.Ioo a b, Set.Icc a b ∈ 𝓝 t := by
    intro t ht
    exact Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
  have hY_par : IsParallelChart (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t) Y (Set.Ioo a b) := by
    refine ⟨fun t ht => huDeriv t ht, ?_⟩
    intro t ht
    have hin : t ∈ Set.Icc a b := Set.mem_Icc_of_Ioo ht
    have hd := (hY_deriv t hin).hasDerivAt (hIccNhds t ht)
    simpa using hd
  refine ⟨Y, ⟨hY_init, hY_par⟩, ?_⟩
  obtain ⟨K, hK_Icc⟩ :=
    parallel_lipschitz_bound_on_compact (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t) hab huCont huCurveCont hsource
  have hK_Ioo : ParallelTransportLipschitzBound (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t) K (Set.Ioo a b) :=
    fun t ht => hK_Icc t (Set.mem_Icc_of_Ioo ht)
  intro V' ⟨hV'_init, hV'_par⟩
  exact IsParallelChart.unique_of_initial hY_par hV'_par hK_Ioo ht₀
    (hY_init.trans hV'_init.symm)


structure ParallelSegmentData [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (a b t₀ : ℝ) : Prop where

  hab : a ≤ b

  ht₀ : t₀ ∈ Set.Ioo a b

  huCont : ContinuousOn (fun t => deriv (chartCurve (I := I) α γ) t) (Set.Icc a b)

  huCurveCont : ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b)

  huDeriv : ∀ t ∈ Set.Ioo a b,
    HasDerivAt (chartCurve (I := I) α γ) (deriv (chartCurve (I := I) α γ) t) t

  hsource : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source


noncomputable def parallelTransport [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ : E) :
    SectionAlongCurve I M γ :=
  ⟨(parallel_global_extension (I := I) g α γ hd.hab hd.ht₀ hd.huCont
      hd.huCurveCont hd.huDeriv hd.hsource v₀).choose⟩


omit [NeZero (Module.finrank ℝ E)] in
lemma parallelTransport_spec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ : E) :
    (parallelTransport (I := I) g α γ hd v₀).toFun t₀ = v₀ ∧
      IsParallelChart (I := I) g α γ
        (fun t => deriv (chartCurve (I := I) α γ) t)
        (parallelTransport (I := I) g α γ hd v₀).toFun (Set.Ioo a b) :=
  (parallel_global_extension (I := I) g α γ hd.hab hd.ht₀ hd.huCont
    hd.huCurveCont hd.huDeriv hd.hsource v₀).choose_spec.1


omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem parallelTransport_initial [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ : E) :
    (parallelTransport (I := I) g α γ hd v₀).toFun t₀ = v₀ :=
  (parallelTransport_spec (I := I) g α γ hd v₀).1


omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransport_isParallel [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ : E) :
    IsParallelChart (I := I) g α γ
      (fun t => deriv (chartCurve (I := I) α γ) t)
      (parallelTransport (I := I) g α γ hd v₀).toFun (Set.Ioo a b) :=
  (parallelTransport_spec (I := I) g α γ hd v₀).2


omit [NeZero (Module.finrank ℝ E)] in
theorem chartGramAlongCurve_hasDerivAt_zero_of_parallel [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    {V W : ℝ → E} {s : Set ℝ}
    (hV : IsParallelChart (I := I) g α γ
      (fun t => deriv (AlongCurve.chartCurve (I := I) α γ) t) V s)
    (hW : IsParallelChart (I := I) g α γ
      (fun t => deriv (AlongCurve.chartCurve (I := I) α γ) t) W s)
    (hsrc : ∀ τ ∈ s, γ τ ∈ (chartAt H α).source)
    {t : ℝ} (ht : s ∈ 𝓝 t) :
    HasDerivAt (fun τ => AlongCurve.chartGramAlongCurve (I := I) g α γ V W τ)
      0 t := by
  have hts : t ∈ s := mem_of_mem_nhds ht
  have huPrime : HasDerivAt (AlongCurve.chartCurve (I := I) α γ)
      (deriv (AlongCurve.chartCurve (I := I) α γ) t) t :=
    (AlongCurve.IsParallelChart.chartCurve_hasDerivAt hV hts)
  have hVd : HasDerivAt V
      (- chartChristoffelContraction (I := I) g α
          (deriv (AlongCurve.chartCurve (I := I) α γ) t) (V t)
          (AlongCurve.chartCurve (I := I) α γ t)) t :=
    AlongCurve.IsParallelChart.hasDerivAt hV hts
  have hWd : HasDerivAt W
      (- chartChristoffelContraction (I := I) g α
          (deriv (AlongCurve.chartCurve (I := I) α γ) t) (W t)
          (AlongCurve.chartCurve (I := I) α γ t)) t :=
    AlongCurve.IsParallelChart.hasDerivAt hW hts
  have hmem : AlongCurve.chartCurve (I := I) α γ t ∈
      interior (extChartAt I α).target := by
    have hxsrc : γ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hsrc t hts
    have hxtarget : AlongCurve.chartCurve (I := I) α γ t ∈
        (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hxtarget
  have hbase := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant
    (I := I) g α γ V W
    (uPrime := fun τ => deriv (AlongCurve.chartCurve (I := I) α γ) τ)
    (Vprime := fun _ => - chartChristoffelContraction (I := I) g α
      (deriv (AlongCurve.chartCurve (I := I) α γ) t) (V t)
      (AlongCurve.chartCurve (I := I) α γ t))
    (Wprime := fun _ => - chartChristoffelContraction (I := I) g α
      (deriv (AlongCurve.chartCurve (I := I) α γ) t) (W t)
      (AlongCurve.chartCurve (I := I) α γ t))
    huPrime hmem hVd hWd
  have hVzero :
      (- chartChristoffelContraction (I := I) g α
          (deriv (AlongCurve.chartCurve (I := I) α γ) t) (V t)
          (AlongCurve.chartCurve (I := I) α γ t))
        + chartChristoffelContraction (I := I) g α
            (deriv (AlongCurve.chartCurve (I := I) α γ) t) (V t)
            (AlongCurve.chartCurve (I := I) α γ t) = 0 := by
    rw [neg_add_cancel]
  have hWzero :
      (- chartChristoffelContraction (I := I) g α
          (deriv (AlongCurve.chartCurve (I := I) α γ) t) (W t)
          (AlongCurve.chartCurve (I := I) α γ t))
        + chartChristoffelContraction (I := I) g α
            (deriv (AlongCurve.chartCurve (I := I) α γ) t) (W t)
            (AlongCurve.chartCurve (I := I) α γ t) = 0 := by
    rw [neg_add_cancel]
  rw [hVzero, hWzero] at hbase
  simpa using hbase


omit [NeZero (Module.finrank ℝ E)] in
theorem parallelTransport_preserves_inner_product [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) {a b t₀ : ℝ}
    (hd : ParallelSegmentData (I := I) g α γ a b t₀) (v₀ w₀ : E)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    AlongCurve.chartGramAlongCurve (I := I) g α γ
        (parallelTransport (I := I) g α γ hd v₀).toFun
        (parallelTransport (I := I) g α γ hd w₀).toFun t =
      AlongCurve.chartGramAlongCurve (I := I) g α γ
        (parallelTransport (I := I) g α γ hd v₀).toFun
        (parallelTransport (I := I) g α γ hd w₀).toFun t₀ := by
  classical
  set V : ℝ → E := (parallelTransport (I := I) g α γ hd v₀).toFun with hV_def
  set W : ℝ → E := (parallelTransport (I := I) g α γ hd w₀).toFun with hW_def
  set f : ℝ → ℝ := fun τ =>
    AlongCurve.chartGramAlongCurve (I := I) g α γ V W τ with hf_def
  set o : Set ℝ := Set.Ioo a b with ho_def
  have ho_open : IsOpen o := isOpen_Ioo
  have hsrc_o : ∀ τ ∈ o, γ τ ∈ (chartAt H α).source :=
    fun τ hτ => hd.hsource τ (Set.mem_Icc_of_Ioo hτ)
  have hVparo : IsParallelChart (I := I) g α γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) α γ) τ) V o :=
    parallelTransport_isParallel (I := I) g α γ hd v₀
  have hWparo : IsParallelChart (I := I) g α γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) α γ) τ) W o :=
    parallelTransport_isParallel (I := I) g α γ hd w₀
  have hderiv : ∀ τ ∈ o, HasDerivAt f 0 τ := by
    intro τ hτ
    exact chartGramAlongCurve_hasDerivAt_zero_of_parallel (I := I) g α γ
      hVparo hWparo hsrc_o (ho_open.mem_nhds hτ)
  have hconst : ∀ x ∈ o, f x = f t₀ :=
    fun x hx => ho_open.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun τ hτ => (hderiv τ hτ).differentiableAt.differentiableWithinAt)
      (fun τ hτ => (hderiv τ hτ).deriv) hx hd.ht₀
  exact hconst t ht


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem trivialization_coordinateChange_eq_chartTransitionAt [I.Boundaryless]
    (α β : M) {b : M}
    (hα : b ∈ (chartAt H α).source) (hβ : b ∈ (chartAt H β).source) (v : E) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) =
      Geodesic.chartTransitionAt (I := I) α β (extChartAt I α b) v := by
  have hαsrc : b ∈ (chartAt H α).source := hα
  have hβsrc : b ∈ (chartAt H β).source := hβ
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hβsrc,
    TangentBundle.symmL_trivializationAt_eq_core (I := I) hαsrc]
  have hb_self : b ∈ (chartAt H b).source := mem_chart_source H b
  have hmem : b ∈ (tangentBundleCore I M).baseSet (achart H α)
      ∩ (tangentBundleCore I M).baseSet (achart H b)
      ∩ (tangentBundleCore I M).baseSet (achart H β) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [tangentBundleCore_baseSet]; exact hαsrc
    · rw [tangentBundleCore_baseSet]; exact hb_self
    · rw [tangentBundleCore_baseSet]; exact hβsrc
  have hcomp := (tangentBundleCore I M).coordChange_comp
    (achart H α) (achart H b) (achart H β) b hmem v
  have hcc : ((tangentBundleCore I M).coordChange (achart H α) (achart H β) b) v =
      Geodesic.chartTransitionAt (I := I) α β (extChartAt I α b) v := by
    change tangentCoordChange I α β b v = _
    rw [tangentCoordChange_def]
    rw [Geodesic.chartTransitionAt_def, Geodesic.chartTransitionMap_def]
    have hrange : (Set.range I : Set E) = Set.univ :=
      ModelWithCorners.Boundaryless.range_eq_univ (I := I)
    rw [hrange, fderivWithin_univ]
  rw [← hcc]
  exact hcomp


theorem exists_uniform_chart_partition
    (γ : ℝ → M) (hγ : Continuous γ) {L : ℝ} (hL : 0 < L) :
    ∃ (N : ℕ) (bp : ℕ → M), 0 < N ∧
      ∀ k : ℕ, k < N → ∀ t ∈ Set.Icc (k * L / N) ((k + 1) * L / N),
        γ t ∈ (chartAt H (bp k)).source := by
  classical
  set c : ℝ → Set ℝ := fun τ => γ ⁻¹' (chartAt H (γ τ)).source with hc_def
  have hc_open : ∀ τ, IsOpen (c τ) := fun τ =>
    (chartAt H (γ τ)).open_source.preimage hγ
  have hcover : Set.Icc (0 : ℝ) L ⊆ ⋃ τ, c τ := by
    intro x _hx
    exact Set.mem_iUnion.2 ⟨x, by simp only [hc_def, Set.mem_preimage]; exact mem_chart_source H (γ x)⟩
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_Icc (a := (0 : ℝ)) (b := L)) hc_open hcover
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (L / δ)
  set N : ℕ := N₀ + 1 with hN_def
  have hN_pos : 0 < N := Nat.succ_pos _
  have hN_pos_real : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hmesh : L / N < δ := by
    have hN_gt : L / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast Nat.le_succ N₀)
    rw [div_lt_iff₀ hN_pos_real]
    rw [div_lt_iff₀ hδ_pos] at hN_gt
    linarith
  have hmid_mem : ∀ k : ℕ, k < N →
      ((k * L / N + (k + 1) * L / N) / 2) ∈ Set.Icc (0 : ℝ) L := by
    intro k hk
    constructor
    · have h1 : 0 ≤ (k : ℝ) * L / N := by positivity
      have h2 : 0 ≤ ((k : ℝ) + 1) * L / N := by positivity
      linarith
    · have hk1 : (k : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hk
      have hub1 : ((k : ℝ) + 1) * L / N ≤ L := by
        rw [div_le_iff₀ hN_pos_real]
        nlinarith [hL.le, hk1]
      have hub0 : (k : ℝ) * L / N ≤ ((k : ℝ) + 1) * L / N := by
        apply div_le_div_of_nonneg_right ?_ hN_pos_real.le
        nlinarith [hL.le]
      linarith
  have hchoose : ∀ k : ℕ, k < N → ∃ τ : ℝ,
      ∀ t ∈ Set.Icc ((k : ℝ) * L / N) (((k : ℝ) + 1) * L / N),
        γ t ∈ (chartAt H (γ τ)).source := by
    intro k hk
    obtain ⟨τ, hτ⟩ := hδ _ (hmid_mem k hk)
    refine ⟨τ, fun t ht => ?_⟩
    have htball : t ∈ Metric.ball ((k * L / N + (k + 1) * L / N) / 2) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      obtain ⟨htl, htr⟩ := ht
      have hwidth : ((k : ℝ) + 1) * L / N - (k : ℝ) * L / N = L / N := by
        field_simp; ring
      have hmid_lo : (k * L / N + (k + 1) * L / N) / 2 - t ≤ L / N := by
        have : (k * L / N + (k + 1) * L / N) / 2 ≤ ((k : ℝ) + 1) * L / N := by linarith
        nlinarith [htl, this, hwidth]
      have hmid_hi : t - (k * L / N + (k + 1) * L / N) / 2 ≤ L / N := by
        have : (k : ℝ) * L / N ≤ (k * L / N + (k + 1) * L / N) / 2 := by linarith
        nlinarith [htr, this, hwidth]
      have habs : |t - (k * L / N + (k + 1) * L / N) / 2| ≤ L / N := by
        rw [abs_le]; constructor <;> linarith
      exact lt_of_le_of_lt habs hmesh
    have := hτ htball
    simp only [hc_def, Set.mem_preimage] at this
    exact this
  choose! tp htp using hchoose
  exact ⟨N, fun k => γ (tp k), hN_pos, fun k hk t ht => htp k hk t ht⟩


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem chartCurve_continuousOn_of_mapsTo
    (α : M) (γ : ℝ → M) (hγ : Continuous γ) {a b : ℝ}
    (hsrc : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source) :
    ContinuousOn (chartCurve (I := I) α γ) (Set.Icc a b) := by
  have hφ : ContinuousOn (extChartAt I α) (extChartAt I α).source :=
    continuousOn_extChartAt (I := I) α
  have hmaps : Set.MapsTo γ (Set.Icc a b) (extChartAt I α).source := by
    intro t ht
    rw [extChartAt_source (I := I) α]
    exact hsrc t ht
  exact hφ.comp hγ.continuousOn hmaps


theorem exists_piece_parallel_section [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (N : ℕ∞) γ)
    {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Set.Icc a b)
    (hsrc : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (v₀ : TangentSpace I (γ t₀)) :
    ∃ V : ∀ t, TangentSpace I (γ t),
      V t₀ = v₀ ∧
      (∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Ioo a b, covDerivAlong (I := I) g γ V t = 0) := by
  classical
  set uPrime : ℝ → E := fun t => deriv (AlongCurve.chartCurve (I := I) α γ) t with huPrime_def
  have hcurveCont : ContinuousOn (AlongCurve.chartCurve (I := I) α γ) (Set.Icc a b) :=
    chartCurve_continuousOn_of_mapsTo (I := I) α γ hγ.continuous hsrc
  set U : Set ℝ := γ ⁻¹' (chartAt H α).source with hU_def
  have hU_open : IsOpen U := (chartAt H α).open_source.preimage hγ.continuous
  have hUcd : ContDiffOn ℝ (N : ℕ∞) (AlongCurve.chartCurve (I := I) α γ) U := by
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (N : ℕ∞) ((extChartAt I α) ∘ γ) U := by
      have hφ : ContMDiffOn I 𝓘(ℝ, E) (N : ℕ∞) (extChartAt I α) (chartAt H α).source :=
        (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).of_le (by exact_mod_cast le_top)
      exact hφ.comp hγ.contMDiffOn (fun s hs => hs)
    have hfun : (AlongCurve.chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
    rw [hfun]; exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  have hIcc_sub_U : Set.Icc a b ⊆ U := fun t ht => hsrc t ht
  have huPrimeCont : ContinuousOn uPrime (Set.Icc a b) := by
    have hderiv_cd : ContDiffOn ℝ (0 : ℕ∞) (deriv (AlongCurve.chartCurve (I := I) α γ)) U :=
      hUcd.deriv_of_isOpen hU_open (by
        have : (1 : ℕ) ≤ N := le_trans one_le_two hN
        exact_mod_cast this)
    exact (hderiv_cd.continuousOn).mono hIcc_sub_U
  have hγa_src : γ t₀ ∈ (chartAt H α).source := hsrc t₀ ht₀
  set y₀ : E := (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t₀) v₀ with hy₀_def
  obtain ⟨Y, hY_deriv, hY_init⟩ :=
    parallel_local_existence_on_Icc (I := I) g α γ uPrime hab.le ht₀
      huPrimeCont hcurveCont hsrc y₀
  set V : ∀ t, TangentSpace I (γ t) := fun s =>
    (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Y s) with hV_def
  have hIccNhds : ∀ t ∈ Set.Ioo a b, Set.Icc a b ∈ 𝓝 t := fun t ht =>
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
  have hcurveDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (AlongCurve.chartCurve (I := I) α γ) (uPrime t) t := by
    intro t ht
    have ht_U : t ∈ U := hIcc_sub_U (Set.mem_Icc_of_Ioo ht)
    have : DifferentiableAt ℝ (AlongCurve.chartCurve (I := I) α γ) t :=
      (hUcd.differentiableOn (by exact_mod_cast (show N ≠ 0 by omega)) t ht_U).differentiableAt
        (hU_open.mem_nhds ht_U)
    exact this.hasDerivAt
  have hY_par_Ioo : IsParallelChart (I := I) g α γ uPrime Y (Set.Ioo a b) := by
    refine ⟨fun t ht => hcurveDeriv t ht, ?_⟩
    intro t ht
    have hd := (hY_deriv t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (hIccNhds t ht)
    simpa using hd
  have hrep_eq : ∀ t ∈ Set.Ioo a b,
      chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
        (fun s => Geodesic.chartTransitionAt (I := I) α (γ t)
          (AlongCurve.chartCurve (I := I) α γ s) (Y s)) := by
    intro t ht
    set W : Set ℝ := γ ⁻¹' ((chartAt H α).source ∩ (chartAt H (γ t)).source) with hW_def
    have hW_open : IsOpen W :=
      ((chartAt H α).open_source.inter (chartAt H (γ t)).open_source).preimage hγ.continuous
    have htW : t ∈ W := ⟨hsrc t (Set.mem_Icc_of_Ioo ht), mem_chart_source H (γ t)⟩
    filter_upwards [hW_open.mem_nhds htW] with s hs
    obtain ⟨hsα, hsβ⟩ := hs
    rw [chartRepAt_apply, hV_def]
    simp only
    rw [trivialization_coordinateChange_eq_chartTransitionAt (I := I) α (γ t) hsα hsβ (Y s)]
    rw [AlongCurve.chartCurve_def]
  refine ⟨V, ?_, ?_, ?_⟩
  · rw [hV_def]
    simp only
    rw [hY_init, hy₀_def]
    have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hγa_src
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase v₀
  · intro t ht
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ (hrep_eq t ht))
    set Tαβ : E → (E →L[ℝ] E) := fun x => Geodesic.chartTransitionAt (I := I) α (γ t) x
      with hTαβ_def
    have hsrc_t : AlongCurve.chartCurve (I := I) α γ t ∈
        Geodesic.chartTransitionSource (I := I) α (γ t) :=
      Geodesic.extChartAt_mem_chartTransitionSource (I := I) α (γ t)
        (hsrc t (Set.mem_Icc_of_Ioo ht)) (mem_chart_source H (γ t))
    have hTopen : IsOpen (Geodesic.chartTransitionSource (I := I) α (γ t)) :=
      Geodesic.chartTransitionSource_isOpen (I := I) α (γ t)
    have hTdiff : DifferentiableAt ℝ Tαβ (AlongCurve.chartCurve (I := I) α γ t) :=
      ((Geodesic.chartTransitionAt_smooth (I := I) α (γ t)).contDiffAt
        (hTopen.mem_nhds hsrc_t)).differentiableAt (by simp)
    have hcurve_diff : DifferentiableAt ℝ (AlongCurve.chartCurve (I := I) α γ) t :=
      (hcurveDeriv t ht).differentiableAt
    have hY_diff : DifferentiableAt ℝ Y t :=
      ((hY_deriv t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (hIccNhds t ht)).differentiableAt
    have hTcomp_diff : DifferentiableAt ℝ
        (fun s => (Tαβ (AlongCurve.chartCurve (I := I) α γ s) : E →L[ℝ] E)) t :=
      hTdiff.comp t hcurve_diff
    exact hTcomp_diff.clm_apply hY_diff
  · intro t ht
    rw [covDerivAlong_eq_zero_iff (I := I) g γ V t]
    set o : Set ℝ := Set.Ioo a b ∩ γ ⁻¹' (chartAt H (γ t)).source with ho_def
    have ho_open : IsOpen o :=
      isOpen_Ioo.inter ((chartAt H (γ t)).open_source.preimage hγ.continuous)
    have hto : t ∈ o := ⟨ht, mem_chart_source H (γ t)⟩
    have ho_sub : o ⊆ Set.Ioo a b := fun s hs => hs.1
    have hoverlap : ∀ s ∈ o, γ s ∈ (chartAt H α).source ∩ (chartAt H (γ t)).source :=
      fun s hs => ⟨hsrc s (Set.mem_Icc_of_Ioo (ho_sub hs)), hs.2⟩
    have hY_par_o : IsParallelChart (I := I) g α γ uPrime Y o :=
      ⟨fun s hs => hY_par_Ioo.1 s (ho_sub hs), fun s hs => hY_par_Ioo.2 s (ho_sub hs)⟩
    have hpush_par := parallel_chart_overlap_consistency (I := I) g α (γ t) γ hγ.continuous
      uPrime Y o hoverlap hY_par_o
    set Yβ : ℝ → E := fun s => Geodesic.chartTransitionAt (I := I) α (γ t)
      (AlongCurve.chartCurve (I := I) α γ s) (Y s) with hYβ_def
    have hvel_eq : ∀ s ∈ o,
        deriv (AlongCurve.chartCurve (I := I) (γ t) γ) s =
          Geodesic.chartTransitionAt (I := I) α (γ t)
            (AlongCurve.chartCurve (I := I) α γ s) (uPrime s) := by
      intro s hs
      exact (hpush_par.1 s hs).deriv
    have hpush_par' : IsParallelChart (I := I) g (γ t) γ
        (fun s => deriv (AlongCurve.chartCurve (I := I) (γ t) γ) s) Yβ o := by
      refine ⟨fun s hs => ?_, fun s hs => ?_⟩
      · have h1 := hpush_par.1 s hs
        simp only []
        rw [hvel_eq s hs]; exact h1
      · have h2 := hpush_par.2 s hs
        simp only [hvel_eq s hs]
        exact h2
    have hYβ_zero : chartCovDerivAlong (I := I) g (γ t) γ Yβ t = 0 := by
      have hd := hpush_par'.hasDerivAt hto
      rw [chartCovDerivAlong_def, hd.deriv]
      abel
    have hrep_eqβ : chartRepAt (I := I) γ V t =ᶠ[𝓝 t] Yβ := hrep_eq t ht
    have hgoal : chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t =
        chartCovDerivAlong (I := I) g (γ t) γ Yβ t := by
      rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
      rw [hrep_eqβ.deriv_eq, hrep_eqβ.eq_of_nhds]
    rw [hgoal, hYβ_zero]


omit [NeZero (Module.finrank ℝ E)] in
theorem parallel_transport_preserves_inner_product [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (N : ℕ∞) γ)
    {lo hi : ℝ} (hlohi : lo ≤ hi)
    (V W : ∀ t, TangentSpace I (γ t))
    (hVdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hWdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t)
    (hVpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ V t = 0)
    (hWpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ W t = 0) :
    ∀ t ∈ Set.Icc lo hi,
      g.inner (γ t) (V t) (W t) = g.inner (γ lo) (V lo) (W lo) := by
  classical
  set f : ℝ → ℝ := fun t => g.inner (γ t) (V t) (W t) with hf_def
  have hlocal : ∀ t₀ ∈ Set.Icc lo hi, HasDerivAt f 0 t₀ := by
    intro t₀ ht₀
    set α : M := γ t₀ with hα_def
    set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
    set Wrep : ℝ → E := chartRepAt (I := I) γ W t₀ with hWrep_def
    have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H (γ t₀)
    have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    have hsrc_open : IsOpen {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} :=
      hbaseSet_open.preimage hγ.continuous
    have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
      hsrc_open.mem_nhds hbase_t₀
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
        (deriv (chartCurve (I := I) α γ) t₀) t₀ := by
      have hcd : ContDiffAt ℝ (N : ℕ∞) (chartCurve (I := I) α γ) t₀ := by
        have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (N : ℕ∞) ((extChartAt I α) ∘ γ) t₀ := by
          have hφ : ContMDiffAt I 𝓘(ℝ, E) (N : ℕ∞) (extChartAt I α) (γ t₀) :=
            (contMDiffAt_extChartAt (I := I) (x := α) (n := ∞)).of_le (by exact_mod_cast le_top)
          exact hφ.comp t₀ (hγ.contMDiffAt)
        exact contMDiffAt_iff_contDiffAt.mp hmdiff
      exact (hcd.differentiableAt (by exact_mod_cast (show N ≠ 0 by omega))).hasDerivAt
    have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
      have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
      exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) α ((extChartAt I α).map_source hxsrc)
    have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ := (hVdiff t₀ ht₀).hasDerivAt
    have hWrep_hasDerivAt : HasDerivAt Wrep (deriv Wrep t₀) t₀ := (hWdiff t₀ ht₀).hasDerivAt
    have hgram := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep Wrep
      (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
      (Vprime := fun _ => deriv Vrep t₀)
      (Wprime := fun _ => deriv Wrep t₀)
      hu_hasDerivAt hmem_int hVrep_hasDerivAt hWrep_hasDerivAt
    have hcorrV :
        deriv Vrep t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have : chartCovDerivAlong (I := I) g α γ Vrep t₀ = 0 := by
        rw [hα_def, hVrep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ V t₀).mp (hVpar t₀ ht₀)
      rw [chartCovDerivAlong_def] at this; exact this
    have hcorrW :
        deriv Wrep t₀ +
          chartChristoffelContraction (I := I) g α
            (deriv (chartCurve (I := I) α γ) t₀) (Wrep t₀)
            (chartCurve (I := I) α γ t₀) = 0 := by
      have : chartCovDerivAlong (I := I) g α γ Wrep t₀ = 0 := by
        rw [hα_def, hWrep_def]
        exact (covDerivAlong_eq_zero_iff (I := I) g γ W t₀).mp (hWpar t₀ ht₀)
      rw [chartCovDerivAlong_def] at this; exact this
    have hderiv0 : HasDerivAt
        (fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep Wrep s) 0 t₀ := by
      convert hgram using 1
      simp only [hcorrV, hcorrW]
      simp
    exact hderiv0.congr_of_eventuallyEq hf_eq
  have hcont : ContinuousOn f (Set.Icc lo hi) :=
    fun t ht => ((hlocal t ht).continuousAt).continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico lo hi, HasDerivWithinAt f 0 (Set.Ici x) x :=
    fun x hx => (hlocal x (Set.mem_Icc_of_Ico hx)).hasDerivWithinAt
  have hconst : ∀ x ∈ Set.Icc lo hi, f x = f lo :=
    constant_of_has_deriv_right_zero hcont hderivWithin
  intro t ht
  exact hconst t ht


omit [NeZero (Module.finrank ℝ E)] in
theorem parallel_transport_unique_of_eq_at_point [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (N : ℕ∞) γ)
    {lo hi : ℝ} (hlohi : lo ≤ hi)
    (V W : ∀ t, TangentSpace I (γ t))
    (hVdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t)
    (hWdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ W t) t)
    (hVpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ V t = 0)
    (hWpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ W t = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc lo hi) (hagree : V t₀ = W t₀) :
    ∀ t ∈ Set.Icc lo hi, V t = W t := by
  classical
  set D : ∀ t, TangentSpace I (γ t) := fun s => V s - W s with hD_def
  have hDdiff : ∀ t ∈ Set.Icc lo hi,
      DifferentiableAt ℝ (chartRepAt (I := I) γ D t) t := by
    intro t ht
    have heq : chartRepAt (I := I) γ D t =
        fun s => chartRepAt (I := I) γ V t s - chartRepAt (I := I) γ W t s := by
      funext s; rw [hD_def]; simp only [chartRepAt_apply, map_sub]
    rw [heq]
    exact (hVdiff t ht).sub (hWdiff t ht)
  have hDpar : ∀ t ∈ Set.Icc lo hi, covDerivAlong (I := I) g γ D t = 0 := by
    intro t ht
    have hDfun : D = fun s => V s + ((-1 : ℝ) • W s) := by
      funext s; rw [hD_def]; simp [sub_eq_add_neg]
    rw [hDfun]
    have hWsmul_diff : DifferentiableAt ℝ
        (chartRepAt (I := I) γ (fun s => (-1 : ℝ) • W s) t) t := by
      have heq : chartRepAt (I := I) γ (fun s => (-1 : ℝ) • W s) t =
          fun s => (-1 : ℝ) • chartRepAt (I := I) γ W t s := by
        funext s; simp only [chartRepAt_apply, map_smul]
      rw [heq]; exact (hWdiff t ht).const_smul (-1 : ℝ)
    rw [covDerivAlong_add (I := I) g γ V (fun s => (-1 : ℝ) • W s) t (hVdiff t ht) hWsmul_diff]
    rw [covDerivAlong_smul (I := I) g γ (-1 : ℝ) W t]
    rw [hVpar t ht, hWpar t ht]
    simp
  have hDt₀ : D t₀ = 0 := by rw [hD_def]; simp only; rw [hagree]; abel
  have hconst := parallel_transport_preserves_inner_product (I := I) g γ hN hγ hlohi D D
    hDdiff hDdiff hDpar hDpar
  intro t ht
  have hzero_t₀ : g.inner (γ t₀) (D t₀) (D t₀) = 0 := by
    rw [hDt₀]; simp
  have hval_t : g.inner (γ t) (D t) (D t) = g.inner (γ lo) (D lo) (D lo) := hconst t ht
  have hval_t₀ : g.inner (γ t₀) (D t₀) (D t₀) = g.inner (γ lo) (D lo) (D lo) := hconst t₀ ht₀
  have hDt_sq : g.inner (γ t) (D t) (D t) = 0 := by
    rw [hval_t, ← hval_t₀, hzero_t₀]
  have hDt : D t = 0 := by
    by_contra hne
    exact absurd hDt_sq (ne_of_gt (g.pos (γ t) (D t) hne))
  have : V t - W t = 0 := hDt
  rw [sub_eq_zero] at this
  exact this


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartRepAt_eventuallyEq_of_eventuallyEq (γ : ℝ → M)
    {V W : ∀ t, TangentSpace I (γ t)} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, V s = W s) :
    chartRepAt (I := I) γ V t =ᶠ[𝓝 t] chartRepAt (I := I) γ W t := by
  filter_upwards [h] with s hs
  rw [chartRepAt_apply, chartRepAt_apply, hs]


omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_congr_of_eventuallyEq (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {V W : ∀ t, TangentSpace I (γ t)} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, V s = W s) :
    covDerivAlong (I := I) g γ V t = covDerivAlong (I := I) g γ W t := by
  have hrep := chartRepAt_eventuallyEq_of_eventuallyEq (I := I) γ h
  rw [covDerivAlong_def, covDerivAlong_def, chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [hrep.deriv_eq, hrep.eq_of_nhds]


theorem exists_uniform_chart_radius
    (γ : ℝ → M) (hγ : Continuous γ) (L : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (0 : ℝ) L, ∃ α : M,
      ∀ s ∈ Set.Icc (t - r) (t + r), γ s ∈ (chartAt H α).source := by
  classical
  set c : ℝ → Set ℝ := fun τ => γ ⁻¹' (chartAt H (γ τ)).source with hc_def
  have hc_open : ∀ τ, IsOpen (c τ) := fun τ => (chartAt H (γ τ)).open_source.preimage hγ
  have hcover : Set.Icc (-1 : ℝ) (L + 1) ⊆ ⋃ τ, c τ := by
    intro x _hx
    exact Set.mem_iUnion.2 ⟨x, by simp only [hc_def, Set.mem_preimage]; exact mem_chart_source H (γ x)⟩
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_Icc (a := (-1 : ℝ)) (b := L + 1)) hc_open hcover
  refine ⟨min (δ / 2) 1, lt_min (by positivity) one_pos, ?_⟩
  intro t ht
  have ht_in : t ∈ Set.Icc (-1 : ℝ) (L + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨τ, hτ⟩ := hδ t ht_in
  refine ⟨γ τ, fun s hs => ?_⟩
  have hsball : s ∈ Metric.ball t δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    obtain ⟨hsl, hsr⟩ := hs
    have hr_le : min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
    have habs : |s - t| ≤ min (δ / 2) 1 := by
      rw [abs_le]; constructor <;> linarith
    have : |s - t| ≤ δ / 2 := le_trans habs hr_le
    linarith [this]
  have := hτ hsball
  simp only [hc_def, Set.mem_preimage] at this
  exact this


theorem exists_global_parallel_transport_on_Ioo [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ,ℝ) I (N : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    ∃ (δ : ℝ) (_ : 0 < δ) (V : ∀ t, TangentSpace I (γ t)),
      V 0 = v₀ ∧
      (∀ t ∈ Set.Ioo (-δ) (L + δ), DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Ioo (-δ) (L + δ), covDerivAlong (I := I) g γ V t = 0) := by
  classical
  obtain ⟨r, hr_pos, hr⟩ := exists_uniform_chart_radius (H := H) γ hγ.continuous L
  set step : ℝ := r / 4 with hstep_def
  have hstep_pos : 0 < step := by rw [hstep_def]; positivity
  set c : ℕ → ℝ := fun n => min L (n * step) with hc_def
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n => le_min hL.le (by positivity)
  have hc_le : ∀ n, c n ≤ L := fun n => min_le_left _ _
  have hc_mono : ∀ n, c n ≤ c (n + 1) := by
    intro n
    have hstep : c n = min L ((n : ℝ) * step) := rfl
    have hstep1 : c (n + 1) = min L (((n : ℝ) + 1) * step) := by
      rw [hc_def]; push_cast; ring_nf
    rw [hstep, hstep1]
    refine le_min (min_le_left _ _) (le_trans (min_le_right _ _) ?_)
    have : (n : ℝ) * step ≤ ((n : ℝ) + 1) * step := by nlinarith [hstep_pos]
    exact this
  have hc_stuck : ∀ n, c n = L → c (n + 1) = L := fun n hn =>
    le_antisymm (hc_le (n + 1)) (hn ▸ hc_mono n)
  set Q : ℕ → Prop := fun n => ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = v₀ ∧
      (∀ t ∈ Set.Ioo (-step) (c n + step),
        DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Ioo (-step) (c n + step), covDerivAlong (I := I) g γ V t = 0)
    with hQ_def
  have hpiece : ∀ p ∈ Set.Icc (0 : ℝ) L, ∀ w : TangentSpace I (γ p),
      ∃ Vp : ∀ t, TangentSpace I (γ t), Vp p = w ∧
        (∀ t ∈ Set.Ioo (p - step) (p + 2 * step),
          DifferentiableAt ℝ (chartRepAt (I := I) γ Vp t) t) ∧
        (∀ t ∈ Set.Ioo (p - step) (p + 2 * step),
          covDerivAlong (I := I) g γ Vp t = 0) := by
    intro p hp w
    obtain ⟨α, hα⟩ := hr p hp
    have hsub : Set.Icc (p - step) (p + 2 * step) ⊆ Set.Icc (p - r) (p + r) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · have : p - r ≤ p - step := by rw [hstep_def]; linarith [hr_pos]
        linarith [hs.1]
      · have : p + 2 * step ≤ p + r := by rw [hstep_def]; linarith [hr_pos]
        linarith [hs.2]
    have hsrc' : ∀ t ∈ Set.Icc (p - step) (p + 2 * step), γ t ∈ (chartAt H α).source :=
      fun t ht => hα t (hsub ht)
    have hlt : p - step < p + 2 * step := by linarith [hstep_pos]
    have hp_mem : p ∈ Set.Icc (p - step) (p + 2 * step) := ⟨by linarith [hstep_pos], by linarith [hstep_pos]⟩
    obtain ⟨Vp, hVp_init, hVp_diff, hVp_par⟩ :=
      exists_piece_parallel_section (I := I) g α γ hN hγ hlt hp_mem hsrc' w
    exact ⟨Vp, hVp_init, hVp_diff, hVp_par⟩
  have hc0 : c 0 = 0 := by
    change min L ((0 : ℕ) * step) = 0
    rw [Nat.cast_zero, zero_mul]; exact min_eq_right hL.le
  have hQ0 : Q 0 := by
    have h0L : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl _, hL.le⟩
    obtain ⟨V0, hV0_init, hV0_diff, hV0_par⟩ := hpiece 0 h0L v₀
    refine ⟨V0, hV0_init, ?_, ?_⟩
    · intro t ht
      rw [hc0] at ht
      refine hV0_diff t ⟨by linarith [ht.1], by linarith [ht.2, hstep_pos]⟩
    · intro t ht
      rw [hc0] at ht
      refine hV0_par t ⟨by linarith [ht.1], by linarith [ht.2, hstep_pos]⟩
  have hQstep : ∀ n, Q n → Q (n + 1) := by
    intro n hn
    obtain ⟨Vn, hVn_init, hVn_diff, hVn_par⟩ := hn
    by_cases hcL : c n = L
    · have hcn1L : c (n + 1) = L := hc_stuck n hcL
      refine ⟨Vn, hVn_init, ?_, ?_⟩
      · intro t ht
        refine hVn_diff t ⟨ht.1, ?_⟩
        rw [hcn1L] at ht; rw [hcL]; exact ht.2
      · intro t ht
        refine hVn_par t ⟨ht.1, ?_⟩
        rw [hcn1L] at ht; rw [hcL]; exact ht.2
    · have hcn_lt : c n < L := lt_of_le_of_ne (hc_le n) hcL
      have hcn_def : c n = min L ((n : ℝ) * step) := rfl
      have hns_lt : (n : ℝ) * step < L := by
        have : min L ((n : ℝ) * step) < L := by rw [← hcn_def]; exact hcn_lt
        rcases min_lt_iff.mp this with h | h
        · exact absurd h (lt_irrefl _)
        · exact h
      have hcn_eq : c n = (n : ℝ) * step := by
        rw [hcn_def]; exact min_eq_right (le_of_lt hns_lt)
      have hcn_mem : c n ∈ Set.Icc (0 : ℝ) L := ⟨hc_nonneg n, hc_le n⟩
      obtain ⟨Vp, hVp_init, hVp_diff, hVp_par⟩ := hpiece (c n) hcn_mem (Vn (c n))
      set ov_lo : ℝ := c n - step / 2 with hov_lo
      have hov_lo_lt : ov_lo ≤ c n := by rw [hov_lo]; linarith [hstep_pos]
      have hVn_dom : Set.Icc ov_lo (c n) ⊆ Set.Ioo (-step) (c n + step) := by
        intro s hs
        rw [hov_lo] at hs
        refine ⟨by linarith [hs.1, hstep_pos, hc_nonneg n], by linarith [hs.2, hstep_pos]⟩
      have hVp_dom : Set.Icc ov_lo (c n) ⊆ Set.Ioo (c n - step) (c n + 2 * step) := by
        intro s hs
        rw [hov_lo] at hs
        refine ⟨by linarith [hs.1, hstep_pos], by linarith [hs.2, hstep_pos]⟩
      have hagree : ∀ s ∈ Set.Icc ov_lo (c n), Vn s = Vp s := by
        refine parallel_transport_unique_of_eq_at_point (I := I) g γ hN hγ hov_lo_lt Vn Vp
          (fun s hs => hVn_diff s (hVn_dom hs)) (fun s hs => hVp_diff s (hVp_dom hs))
          (fun s hs => hVn_par s (hVn_dom hs)) (fun s hs => hVp_par s (hVp_dom hs))
          ⟨hov_lo_lt, le_refl _⟩ ?_
        rw [hVp_init]
      set Vc : ∀ t, TangentSpace I (γ t) := fun s => if s ≤ c n then Vn s else Vp s with hVc_def
      have hVc0 : Vc 0 = v₀ := by
        rw [hVc_def]; simp only
        rw [if_pos (by linarith [hc_nonneg n] : (0 : ℝ) ≤ c n)]
        exact hVn_init
      have hcast : ((n + 1 : ℕ) : ℝ) * step = (n : ℝ) * step + step := by
        push_cast; ring
      have hcn1_eq : c (n + 1) = min L ((n : ℝ) * step + step) := by
        change min L (((n + 1 : ℕ) : ℝ) * step) = min L ((n : ℝ) * step + step)
        rw [hcast]
      have hcn1_le : c (n + 1) ≤ c n + step := by
        rw [hcn1_eq, hcn_eq]; exact min_le_right _ _
      refine ⟨Vc, hVc0, ?_, ?_⟩
      · intro t ht
        by_cases htc : t < c n
        · have heq : ∀ᶠ s in 𝓝 t, Vc s = Vn s := by
            filter_upwards [eventually_lt_nhds htc] with s hs
            rw [hVc_def]; simp only; rw [if_pos (le_of_lt hs)]
          rw [(chartRepAt_eventuallyEq_of_eventuallyEq (I := I) γ heq).differentiableAt_iff]
          exact hVn_diff t ⟨ht.1, by linarith [htc, hstep_pos]⟩
        · replace htc := not_lt.mp htc
          have ht_gt : ov_lo < t := by rw [hov_lo]; linarith [htc, hstep_pos]
          have heq : ∀ᶠ s in 𝓝 t, Vc s = Vp s := by
            filter_upwards [eventually_gt_nhds ht_gt] with s hs
            rw [hVc_def]; simp only
            by_cases hsc : s ≤ c n
            · rw [if_pos hsc]; exact hagree s ⟨le_of_lt hs, hsc⟩
            · rw [if_neg hsc]
          rw [(chartRepAt_eventuallyEq_of_eventuallyEq (I := I) γ heq).differentiableAt_iff]
          refine hVp_diff t ⟨by linarith [htc, hstep_pos], ?_⟩
          have : c (n + 1) + step ≤ c n + 2 * step := by linarith [hcn1_le, hstep_pos]
          linarith [ht.2, this]
      · intro t ht
        by_cases htc : t < c n
        · have heq : ∀ᶠ s in 𝓝 t, Vc s = Vn s := by
            filter_upwards [eventually_lt_nhds htc] with s hs
            rw [hVc_def]; simp only; rw [if_pos (le_of_lt hs)]
          rw [covDerivAlong_congr_of_eventuallyEq (I := I) g γ heq]
          exact hVn_par t ⟨ht.1, by linarith [htc, hstep_pos]⟩
        · replace htc := not_lt.mp htc
          have ht_gt : ov_lo < t := by rw [hov_lo]; linarith [htc, hstep_pos]
          have heq : ∀ᶠ s in 𝓝 t, Vc s = Vp s := by
            filter_upwards [eventually_gt_nhds ht_gt] with s hs
            rw [hVc_def]; simp only
            by_cases hsc : s ≤ c n
            · rw [if_pos hsc]; exact hagree s ⟨le_of_lt hs, hsc⟩
            · rw [if_neg hsc]
          rw [covDerivAlong_congr_of_eventuallyEq (I := I) g γ heq]
          refine hVp_par t ⟨by linarith [htc, hstep_pos], ?_⟩
          have : c (n + 1) + step ≤ c n + 2 * step := by linarith [hcn1_le, hstep_pos]
          linarith [ht.2, this]
  have hQall : ∀ n, Q n := fun n => Nat.rec hQ0 hQstep n
  obtain ⟨N, hN⟩ := exists_nat_gt (L / step)
  have hN_ge : (N : ℝ) * step ≥ L := by
    rw [ge_iff_le, ← div_le_iff₀ hstep_pos]; exact le_of_lt hN
  have hcN : c N = L := by
    rw [hc_def]; exact min_eq_left hN_ge
  obtain ⟨V, hV_init, hV_diff, hV_par⟩ := hQall N
  rw [hcN] at hV_diff hV_par
  refine ⟨step, hstep_pos, V, hV_init, ?_, ?_⟩
  · intro t ht
    exact hV_diff t ⟨ht.1, ht.2⟩
  · intro t ht
    exact hV_par t ⟨ht.1, ht.2⟩


theorem exists_parallel_transport_on_Icc [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ,ℝ) I (N : ℕ∞) γ)
    {L : ℝ} (hL : 0 < L) (v₀ : TangentSpace I (γ 0)) :
    ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = v₀ ∧
      (∀ t ∈ Set.Icc (0:ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Icc (0:ℝ) L, covDerivAlong (I := I) g γ V t = 0) := by
  obtain ⟨δ, hδ_pos, V, hV0, hVdiff, hVpar⟩ :=
    exists_global_parallel_transport_on_Ioo (I := I) g γ hN hγ hL v₀
  have hsub : Set.Icc (0 : ℝ) L ⊆ Set.Ioo (-δ) (L + δ) := by
    intro t ht
    exact ⟨by linarith [ht.1, hδ_pos], by linarith [ht.2, hδ_pos]⟩
  exact ⟨V, hV0, fun t ht => hVdiff t (hsub ht), fun t ht => hVpar t (hsub ht)⟩

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
