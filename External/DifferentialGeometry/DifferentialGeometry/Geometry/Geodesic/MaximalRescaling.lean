import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.UniformChartFlowBridge
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformUniqueness
import DifferentialGeometry.Geometry.Geodesic.GeodesicEquationFromIntegralCurve
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval



noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential

section ChartFiberCoordSelfApply

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartFiberCoord_mk_self (α : M) (v : E) :
    chartFiberCoord (I := I) α (⟨α, v⟩ : TangentBundle I M) = v := by
  classical
  change (trivializationAt E (TangentSpace I) α
      (⟨α, v⟩ : TangentBundle I M)).2 = v
  have hα_mem : α ∈ (chartAt H α).source := mem_chart_source H α
  have hα_src : α ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα_mem
  have hbase : α ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hα_mem
  have hcore :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α =
      (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ)
      (b₀ := α) (b := α) hα_mem
  have hself : ∀ w : E, tangentCoordChange I α α α w = w :=
    fun w => tangentCoordChange_self (I := I) (x := α) (z := α) (v := w) hα_src
  have hcore_at :
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α) v = v := by
    rw [hcore]
    exact hself v
  have happly :
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α) v =
      (trivializationAt E (TangentSpace I) α
        (⟨α, v⟩ : TangentBundle I M)).2 := by
    change ((trivializationAt E (TangentSpace I) α).linearMapAt ℝ α) v = _
    have hcoe :=
      (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
        (R := ℝ) hbase
    exact congrFun hcoe v
  rw [← happly, hcore_at]

end ChartFiberCoordSelfApply

section ChartPushLiftAtZero

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPushLift_zero_of_init
    {f : ℝ → TangentBundle I M} {p : M} {v : E}
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M)) :
    chartPushLift (I := I) f 0 0 = (extChartAt I p p, v) := by
  classical
  rw [chartPushLift_self_pair (I := I) f 0]
  have hproj : (f 0).proj = p := by rw [hf0]
  have hfiber : chartFiberCoord (I := I) p (f 0) = v := by
    rw [hf0]; exact chartFiberCoord_mk_self (I := I) p v
  rw [hproj, hfiber]

end ChartPushLiftAtZero

section RescaledChartOrbit

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushLift_rescaled_eventually_hasDerivAt_chartPhaseVF
    {g : SmoothRiemannianMetric I M} {p : M}
    {f_v : ℝ → TangentBundle I M}
    (hf_v0_proj : (f_v 0).proj = p)
    (hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0)
    (a : ℝ) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun s' : ℝ =>
          rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s')))
        (chartPhaseVF (I := I) g p
          (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))) s := by
  classical
  have hcv_phase := chartPushLift_eventually_hasDerivAt_chartPhaseVF (I := I)
    (g := g) (α := p) (f := f_v) hf_v0_proj hf_v_int
  have hmul_cont : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
  have hpull : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f_v 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f_v 0 (a * s))) (a * s) := by
    have hnhds : (fun s : ℝ => a * s) ⁻¹' {t : ℝ | HasDerivAt (chartPushLift (I := I) f_v 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f_v 0 t)) t} ∈ 𝓝 (0 : ℝ) := by
      apply hmul_cont.continuousAt.preimage_mem_nhds
      simp only [mul_zero]
      exact hcv_phase
    exact hnhds
  filter_upwards [hpull] with s hs
  exact hasDerivAt_rescaled_orbit (I := I) (g := g) (α := p)
    (c := chartPushLift (I := I) f_v 0) (s₀ := s) (a := a) hs

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma rescaled_chartPushLift_at_zero
    {f_v : ℝ → TangentBundle I M} {p : M} {v : E}
    (hf_v0 : f_v 0 = (⟨p, v⟩ : TangentBundle I M)) (a : ℝ) :
    rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * 0)) =
      (extChartAt I p p, a • v) := by
  classical
  rw [mul_zero]
  rw [chartPushLift_zero_of_init (I := I) (f := f_v) (p := p) (v := v) hf_v0]
  rfl

end RescaledChartOrbit

section ChartCoordUniqueness

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushLift_av_phaseVF_and_target_interior
    {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ} {v : E}
    {f_av : ℝ → TangentBundle I M}
    (hf_av0 : f_av 0 = (⟨p, a • v⟩ : TangentBundle I M))
    (hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f_av 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f_av 0 t)) t ∧
      chartPushLift (I := I) f_av 0 t ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
  have hproj : (f_av 0).proj = p := by rw [hf_av0]
  exact chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior
    (I := I) (g := g) (α := p) (f := f_av) hproj hf_av_int

omit [NeZero (Module.finrank ℝ E)] in
lemma rescaled_chartPushLift_phaseVF_and_target_interior
    {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ} {v : E}
    {f_v : ℝ → TangentBundle I M}
    (hf_v0 : f_v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun s' : ℝ =>
          rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s')))
        (chartPhaseVF (I := I) g p
          (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))) s ∧
      rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
  classical
  have hf_v0_proj : (f_v 0).proj = p := by rw [hf_v0]
  have hphase := chartPushLift_rescaled_eventually_hasDerivAt_chartPhaseVF
    (I := I) (g := g) (p := p) (f_v := f_v) hf_v0_proj hf_v_int a
  have hf_v_cont : ContinuousAt f_v 0 := hf_v_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp_v : ContinuousAt (fun t => (f_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_v_cont
  have hmul_cont : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
  have hmul_cont_at0 : ContinuousAt (fun s : ℝ => a * s) 0 := hmul_cont.continuousAt
  have hcomp : ContinuousAt (fun s : ℝ => (f_v (a * s)).proj) 0 := by
    have hcomp_v' : ContinuousAt (fun t => (f_v t).proj) ((fun s : ℝ => a * s) 0) := by
      simp only [mul_zero]; exact hcomp_v
    exact hcomp_v'.comp hmul_cont_at0
  have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
  have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
  have hp_nhds : (chartAt H p).source ∈ 𝓝 p := hp_open.mem_nhds hp_mem
  have hf_v_proj_at_0 : (f_v 0).proj = p := hf_v0_proj
  have hsrc_nhds : (fun s : ℝ => (f_v (a * s)).proj) ⁻¹' (chartAt H p).source ∈
      𝓝 (0 : ℝ) := by
    apply hcomp.preimage_mem_nhds
    have h_at_zero : (f_v (a * (0 : ℝ))).proj = p := by
      rw [mul_zero]; exact hf_v_proj_at_0
    rw [h_at_zero]
    exact hp_nhds
  filter_upwards [hphase, hsrc_nhds] with s hsphase hssrc
  refine ⟨hsphase, ?_⟩
  have hpair : chartPushLift (I := I) f_v 0 (a * s) =
      (extChartAt I p (f_v (a * s)).proj,
        chartFiberCoord (I := I) p (f_v (a * s))) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f_v) (t₀ := 0) (t := a * s) ?_
    · rw [h_eq, hf_v_proj_at_0]
    · rw [hf_v_proj_at_0]; exact hssrc
  rw [hpair]
  refine ⟨?_, Set.mem_univ _⟩
  have h_target : extChartAt I p (f_v (a * s)).proj ∈ (extChartAt I p).target := by
    have h_src : (f_v (a * s)).proj ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hssrc
    exact (extChartAt I p).map_source h_src
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushLift_rescaled_eq_chartPushLift_av_eventually
    {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ} {v : E}
    {f_v f_av : ℝ → TangentBundle I M}
    (hf_v0 : f_v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0)
    (hf_av0 : f_av 0 = (⟨p, a • v⟩ : TangentBundle I M))
    (hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0) :
    (fun s : ℝ =>
        rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))
      =ᶠ[𝓝 (0 : ℝ)] chartPushLift (I := I) f_av 0 := by
  classical
  have hc_R0 : rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * 0)) =
      (extChartAt I p p, a • v) := rescaled_chartPushLift_at_zero (I := I) hf_v0 a
  have hc_av0 : chartPushLift (I := I) f_av 0 0 = (extChartAt I p p, a • v) :=
    chartPushLift_zero_of_init (I := I) hf_av0
  have hz₀_target : (extChartAt I p p, a • v) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hp_src : p ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact mem_chart_source H p
    have h_target : extChartAt I p p ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hp_src
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target
  have hd_R := rescaled_chartPushLift_phaseVF_and_target_interior (I := I)
    (g := g) (p := p) (a := a) (v := v) (f_v := f_v) hf_v0 hf_v_int
  have hd_av := chartPushLift_av_phaseVF_and_target_interior (I := I)
    (g := g) (p := p) (a := a) (v := v) (f_av := f_av) hf_av0 hf_av_int
  exact chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
    (c₁ := fun s : ℝ =>
        rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s)))
    (c₂ := chartPushLift (I := I) f_av 0) (z₀ := (extChartAt I p p, a • v))
    hz₀_target hc_R0 hc_av0 hd_R hd_av

end ChartCoordUniqueness

section ManifoldProjection

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma rescaled_chartPushLift_fst
    {f_v : ℝ → TangentBundle I M} {p : M} {a : ℝ} {s : ℝ}
    (hf_v0_proj : (f_v 0).proj = p)
    (hs_src : (f_v (a * s)).proj ∈ (chartAt H p).source) :
    (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s))).1 =
      extChartAt I p (projectCurve (I := I) f_v (a * s)) := by
  classical
  have hfst : (chartPushLift (I := I) f_v 0 (a * s)).1 =
      extChartAt I p (f_v (a * s)).proj := by
    have h := chartPushLift_fst (I := I) (f := f_v) 0 (a * s) ?_
    · rw [show (f_v 0).proj = p from hf_v0_proj] at h
      exact h
    · rw [hf_v0_proj]; exact hs_src
  change ((chartPushLift (I := I) f_v 0 (a * s)).1, _).1 = _
  rw [hfst]; rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem projectCurve_rescale_eventually
    {g : SmoothRiemannianMetric I M} {p : M} {a : ℝ} {v : E}
    {f_v f_av : ℝ → TangentBundle I M}
    (hf_v0 : f_v 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0)
    (hf_av0 : f_av 0 = (⟨p, a • v⟩ : TangentBundle I M))
    (hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0) :
    (fun s : ℝ => projectCurve (I := I) f_v (a * s))
      =ᶠ[𝓝 (0 : ℝ)] projectCurve (I := I) f_av := by
  classical
  have heq := chartPushLift_rescaled_eq_chartPushLift_av_eventually
    (I := I) (g := g) (p := p) (a := a) (v := v)
    (f_v := f_v) (f_av := f_av) hf_v0 hf_v_int hf_av0 hf_av_int
  have hf_v_cont : ContinuousAt f_v 0 := hf_v_int.continuousAt
  have hf_av_cont : ContinuousAt f_av 0 := hf_av_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hcomp_v : ContinuousAt (fun t => (f_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_v_cont
  have hcomp_av : ContinuousAt (fun s => (f_av s).proj) 0 :=
    hπ_cont.continuousAt.comp hf_av_cont
  have hmul_cont : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
  have hmul_cont_at0 : ContinuousAt (fun s : ℝ => a * s) 0 := hmul_cont.continuousAt
  have hcomp_v_mul : ContinuousAt (fun s : ℝ => (f_v (a * s)).proj) 0 := by
    have hcomp_v' : ContinuousAt (fun t => (f_v t).proj) ((fun s : ℝ => a * s) 0) := by
      simp only [mul_zero]; exact hcomp_v
    exact hcomp_v'.comp hmul_cont_at0
  have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
  have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
  have hp_nhds : (chartAt H p).source ∈ 𝓝 p := hp_open.mem_nhds hp_mem
  have hf_v0_proj : (f_v 0).proj = p := by rw [hf_v0]
  have hf_av0_proj : (f_av 0).proj = p := by rw [hf_av0]
  have hsrc_v : (fun s : ℝ => (f_v (a * s)).proj) ⁻¹' (chartAt H p).source ∈
      𝓝 (0 : ℝ) := by
    apply hcomp_v_mul.preimage_mem_nhds
    have h_at_zero : (f_v (a * (0 : ℝ))).proj = p := by
      rw [mul_zero]; exact hf_v0_proj
    rw [h_at_zero]
    exact hp_nhds
  have hsrc_av : (fun s : ℝ => (f_av s).proj) ⁻¹' (chartAt H p).source ∈
      𝓝 (0 : ℝ) := by
    apply hcomp_av.preimage_mem_nhds
    rw [hf_av0_proj]
    exact hp_nhds
  filter_upwards [heq, hsrc_v, hsrc_av] with s hs_eq hs_v hs_av
  have h_fst_eq : (rescaleChartOrbit (E := E) a (chartPushLift (I := I) f_v 0 (a * s))).1 =
      (chartPushLift (I := I) f_av 0 s).1 := by
    have := congrArg Prod.fst hs_eq
    exact this
  have hlhs := rescaled_chartPushLift_fst (I := I) (f_v := f_v) (p := p)
    (a := a) (s := s) hf_v0_proj hs_v
  have hrhs : (chartPushLift (I := I) f_av 0 s).1 =
      extChartAt I p (f_av s).proj := by
    have h := chartPushLift_fst (I := I) (f := f_av) 0 s ?_
    · rw [show (f_av 0).proj = p from hf_av0_proj] at h
      exact h
    · rw [hf_av0_proj]; exact hs_av
  rw [hlhs] at h_fst_eq
  rw [hrhs] at h_fst_eq
  have hv_src : projectCurve (I := I) f_v (a * s) ∈ (extChartAt I p).source := by
    rw [extChartAt_source, projectCurve_apply]; exact hs_v
  have hav_src : (f_av s).proj ∈ (extChartAt I p).source := by
    rw [extChartAt_source]; exact hs_av
  have hlhs_inv : (extChartAt I p).symm (extChartAt I p
      (projectCurve (I := I) f_v (a * s))) =
      projectCurve (I := I) f_v (a * s) :=
    (extChartAt I p).left_inv hv_src
  have hrhs_inv : (extChartAt I p).symm (extChartAt I p
      (f_av s).proj) = (f_av s).proj :=
    (extChartAt I p).left_inv hav_src
  have h_inv := congrArg (extChartAt I p).symm h_fst_eq
  rw [hlhs_inv, hrhs_inv] at h_inv
  change projectCurve (I := I) f_v (a * s) = projectCurve (I := I) f_av s
  rw [projectCurve_apply]
  exact h_inv

end ManifoldProjection

section ChosenCurveRescaling

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicChosenCurve_rescale_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v)) :
    (fun s : ℝ =>
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s))
      =ᶠ[𝓝 (0 : ℝ)] maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom := by
  classical
  obtain ⟨J_v, _hJv_open, _hJv_conn, _h0_Jv, _ha_Jv, hwit_v⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v ha_dom
  obtain ⟨J_av, _hJav_open, _hJav_conn, _h0_Jav, _h1_Jav, hwit_av⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (a • v) h1_dom
  obtain ⟨f_v, hproj_v, hf_v0, hf_v_int_on⟩ := hwit_v
  obtain ⟨f_av, hproj_av, hf_av0, hf_av_int_on⟩ := hwit_av
  have hf_v_int : IsMIntegralCurveAt f_v
      (geodesicVectorFieldChart (I := I) g p) 0 :=
    hf_v_int_on.isMIntegralCurveAt (_hJv_open.mem_nhds _h0_Jv)
  have hf_av_int : IsMIntegralCurveAt f_av
      (geodesicVectorFieldChart (I := I) g p) 0 :=
    hf_av_int_on.isMIntegralCurveAt (_hJav_open.mem_nhds _h0_Jav)
  have hrescale := projectCurve_rescale_eventually (I := I)
    (g := g) (p := p) (a := a) (v := (v : E))
    (f_v := f_v) (f_av := f_av) hf_v0 hf_v_int hf_av0 hf_av_int
  filter_upwards [hrescale] with s hs
  rw [projectCurve_apply, projectCurve_apply] at hs
  rw [← hproj_v (a * s), ← hproj_av s]
  exact hs

end ChosenCurveRescaling

section RescaleAtOneSmallScale

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicChosenCurve_rescale_at_one
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v))
    (h1_in : (1 : ℝ) ∈ {s : ℝ |
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s) =
          maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom s}) :
    maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom 1 =
      maximalGeodesicChosenCurve (I := I) g p v ha_dom a := by
  have h := h1_in
  simp only [Set.mem_setOf_eq, mul_one] at h
  exact h.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesic_rescale_at_one_of_agreement
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v))
    (h1_in : (1 : ℝ) ∈ {s : ℝ |
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s) =
          maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom s}) :
    maximalGeodesic (I := I) g p (a • v) 1 =
      maximalGeodesic (I := I) g p v a := by
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := a • v) h1_dom]
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := v) ha_dom]
  exact maximalGeodesicChosenCurve_rescale_at_one (I := I)
    g p v a ha_dom h1_dom h1_in

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesic_rescale_at_one
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (a : ℝ)
    (_ha_pos : 0 < a)
    (ha_dom : a ∈ maximalGeodesicInterval (I := I) g p v)
    (h1_dom : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (a • v))
    (h1_in_agreement : (1 : ℝ) ∈ {s : ℝ |
        maximalGeodesicChosenCurve (I := I) g p v ha_dom (a * s) =
          maximalGeodesicChosenCurve (I := I) g p (a • v) h1_dom s}) :
    maximalGeodesic (I := I) g p (a • v) 1 =
      maximalGeodesic (I := I) g p v a :=
  maximalGeodesic_rescale_at_one_of_agreement (I := I) g p v a ha_dom h1_dom
    h1_in_agreement

end RescaleAtOneSmallScale

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
