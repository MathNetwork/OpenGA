import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import DifferentialGeometry.Geometry.Exponential.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Basic



noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

section ChartOfTM

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem extChartAt_tangent_apply_snd
    (q : TangentBundle I M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H q.proj).source) :
    (extChartAt I.tangent q p).2 =
      (trivializationAt E (TangentSpace I) q.proj).continuousLinearMapAt ℝ p.proj p.snd := by
  classical
  have hp_base : p.proj ∈ (trivializationAt E (TangentSpace I) q.proj).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp
  have hcoe :=
    (trivializationAt E (TangentSpace I) q.proj).coe_linearMapAt_of_mem
      (R := ℝ) hp_base
  have hcoe_at :
      (trivializationAt E (TangentSpace I) q.proj).linearMapAt ℝ p.proj p.snd =
      (trivializationAt E (TangentSpace I) q.proj p).2 := by
    have h := congrFun hcoe p.snd
    exact h
  have hext : extChartAt I.tangent q p =
      ((extChartAt I q.proj) (trivializationAt E (TangentSpace I) q.proj p).1,
        (trivializationAt E (TangentSpace I) q.proj p).2) := by
    rw [FiberBundle.extChartAt]
    rfl
  rw [hext]
  change (trivializationAt E (TangentSpace I) q.proj p).2 = _
  rw [← hcoe_at]
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem extChartAt_tangent_apply_fst
    (q : TangentBundle I M) {p : TangentBundle I M}
    (_hp : p.proj ∈ (chartAt H q.proj).source) :
    (extChartAt I.tangent q p).1 = extChartAt I q.proj p.proj := by
  classical
  have hext : extChartAt I.tangent q p =
      ((extChartAt I q.proj) (trivializationAt E (TangentSpace I) q.proj p).1,
        (trivializationAt E (TangentSpace I) q.proj p).2) := by
    rw [FiberBundle.extChartAt]
    rfl
  rw [hext]
  have hp1 : (trivializationAt E (TangentSpace I) q.proj p).1 = p.proj :=
    TangentBundle.trivializationAt_fst _ _
  rw [hp1]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem extChartAt_tangent_zero_apply
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p =
      (extChartAt I α p.proj,
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ p.proj p.snd) := by
  classical
  apply Prod.ext
  · have h := extChartAt_tangent_apply_fst (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := p) (by exact hp)
    exact h
  · have h := extChartAt_tangent_apply_snd (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := p) (by exact hp)
    exact h

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem extChartAt_tangent_zero_apply_chartFiber
    (α : M) {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p =
      (extChartAt I α p.proj, chartFiberCoord (I := I) α p) := by
  classical
  apply Prod.ext
  · exact extChartAt_tangent_apply_fst (I := I)
      (q := (⟨α, (0 : E)⟩ : TangentBundle I M)) (p := p) hp
  · have hext : extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p =
        ((extChartAt I α) (trivializationAt E (TangentSpace I) α p).1,
          (trivializationAt E (TangentSpace I) α p).2) := by
      rw [FiberBundle.extChartAt]
      rfl
    rw [hext]
    rfl

end ChartOfTM

section ChartPushLiftDecomposition

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem extChartAt_tangent_eq_at_proj
    (q : TangentBundle I M) :
    extChartAt I.tangent q =
      extChartAt I.tangent (⟨q.proj, (0 : E)⟩ : TangentBundle I M) := by
  classical
  rw [FiberBundle.extChartAt, FiberBundle.extChartAt]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushLift_eq_pair
    {f : ℝ → TangentBundle I M} (t₀ t : ℝ)
    (ht : (f t).proj ∈ (chartAt H (f t₀).proj).source) :
    chartPushLift (I := I) f t₀ t =
      (extChartAt I (f t₀).proj (f t).proj,
        chartFiberCoord (I := I) (f t₀).proj (f t)) := by
  classical
  unfold chartPushLift
  rw [extChartAt_tangent_eq_at_proj (I := I) (f t₀)]
  exact extChartAt_tangent_zero_apply_chartFiber (I := I) (f t₀).proj ht

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushLift_fst
    {f : ℝ → TangentBundle I M} (t₀ t : ℝ)
    (ht : (f t).proj ∈ (chartAt H (f t₀).proj).source) :
    (chartPushLift (I := I) f t₀ t).1 = extChartAt I (f t₀).proj (f t).proj := by
  rw [chartPushLift_eq_pair (I := I) t₀ t ht]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushLift_snd
    {f : ℝ → TangentBundle I M} (t₀ t : ℝ)
    (ht : (f t).proj ∈ (chartAt H (f t₀).proj).source) :
    (chartPushLift (I := I) f t₀ t).2 = chartFiberCoord (I := I) (f t₀).proj (f t) := by
  rw [chartPushLift_eq_pair (I := I) t₀ t ht]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushLift_self_pair
    (f : ℝ → TangentBundle I M) (t₀ : ℝ) :
    chartPushLift (I := I) f t₀ t₀ =
      (extChartAt I (f t₀).proj (f t₀).proj,
        chartFiberCoord (I := I) (f t₀).proj (f t₀)) := by
  classical
  apply chartPushLift_eq_pair
  exact mem_chart_source H (f t₀).proj

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushLift_self_apply_at_zero_section
    {f : ℝ → TangentBundle I M} {α : M} (t₀ : ℝ)
    (hf : f t₀ = (⟨α, (0 : E)⟩ : TangentBundle I M)) :
    chartPushLift (I := I) f t₀ t₀ = (extChartAt I α α, (0 : E)) := by
  classical
  rw [chartPushLift_self_pair (I := I) f t₀]
  have hproj : (f t₀).proj = α := by rw [hf]
  rw [hproj]
  have hfiber : chartFiberCoord (I := I) α (f t₀) = (0 : E) := by
    rw [hf]
    exact chartFiberCoord_self_zero (I := I) α
  rw [hfiber]

end ChartPushLiftDecomposition

section HeadlineBridge

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedFlow_eq_lift_proj_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v_chart : E)
    {f : ℝ → TangentBundle I M}
    (hf0_proj : (f 0).proj = p)
    (hf0_fiber : chartFiberCoord (I := I) p (f 0) = v_chart)
    (hf_chart_src_eventually : ∀ᶠ t in 𝓝 (0 : ℝ),
      (f t).proj ∈ (chartAt H p).source)
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f 0 t)) t ∧
      chartPushLift (I := I) f 0 t ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, v_chart) : E × E), 0) =
        (extChartAt I p p, v_chart) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        (f t).proj = chartFlowGeodesicCurve (I := I) Φ p v_chart t) := by
  classical
  set c : ℝ → E × E := chartPushLift (I := I) f 0 with hc_def
  have hc0 : c 0 = ((extChartAt I p p, v_chart) : E × E) := by
    have hf0_src : (f 0).proj ∈ (chartAt H p).source := by
      rw [hf0_proj]; exact mem_chart_source H p
    rw [hc_def, chartPushLift_eq_pair (I := I) 0 0]
    · have hproj : (f 0).proj = p := hf0_proj
      rw [hproj, hf0_fiber]
    · rw [hf0_proj]; exact mem_chart_source H p
  obtain ⟨Φ, hΦ_init, hc_eq_orbit⟩ :=
    exists_chartFlow_orbit_eq_chartPhase_solution_eventually
      (I := I) (g := g) (p := p) (v_chart := v_chart) (c := c) hc0 hd
  refine ⟨Φ, hΦ_init, ?_⟩
  filter_upwards [hc_eq_orbit, hf_chart_src_eventually] with t ht_eq ht_src
  have hc_fst : (c t).1 = extChartAt I p (f t).proj := by
    rw [hc_def]
    have h := chartPushLift_fst (I := I) (f := f) 0 t ?_
    · rw [show (f 0).proj = p from hf0_proj] at h
      exact h
    · rw [hf0_proj]; exact ht_src
  have h_orbit_fst :
      (Φ (((extChartAt I p p, v_chart) : E × E), t)).1 =
        extChartAt I p (f t).proj := by
    have := congrArg Prod.fst ht_eq
    rw [hc_fst] at this
    exact this.symm
  unfold chartFlowGeodesicCurve chartFlowOrbit
  rw [h_orbit_fst]
  have ht_src' : (f t).proj ∈ (extChartAt I p).source := by
    rw [extChartAt_source]; exact ht_src
  exact ((extChartAt I p).left_inv ht_src').symm

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedFlow_eq_witness_curve_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v_chart : E)
    {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf0 : f 0 = (⟨p, v_chart⟩ : TangentBundle I M))
    (hf_int_at0 : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) 0)
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f 0 t)) t ∧
      chartPushLift (I := I) f 0 t ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, v_chart) : E × E), 0) =
        (extChartAt I p p, v_chart) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        γ t = chartFlowGeodesicCurve (I := I) Φ p v_chart t) := by
  classical
  have hf0_proj : (f 0).proj = p := by rw [hf0]
  have hf0_fiber : chartFiberCoord (I := I) p (f 0) = v_chart := by
    rw [hf0]
    change (trivializationAt E (TangentSpace I) p
        (⟨p, v_chart⟩ : TangentBundle I M)).2 = v_chart
    have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
    have hp_src : p ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact hp_mem
    have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hp_mem
    have hcore :
        (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p =
        (tangentBundleCore I M).coordChange (achart H p) (achart H p) p :=
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ)
        (b₀ := p) (b := p) hp_mem
    have hself : ∀ v : E, tangentCoordChange I p p p v = v :=
      fun v => tangentCoordChange_self (I := I) (x := p) (z := p) (v := v) hp_src
    have hcore_at :
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v_chart =
        v_chart := by
      rw [hcore]
      exact hself v_chart
    have happly :
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v_chart =
        (trivializationAt E (TangentSpace I) p
          (⟨p, v_chart⟩ : TangentBundle I M)).2 := by
      change ((trivializationAt E (TangentSpace I) p).linearMapAt ℝ p) v_chart = _
      have hcoe :=
        (trivializationAt E (TangentSpace I) p).coe_linearMapAt_of_mem
          (R := ℝ) hbase
      exact congrFun hcoe v_chart
    rw [← happly, hcore_at]
  have hf_cont_at0 : ContinuousAt f 0 := hf_int_at0.continuousAt
  have hf_chart_src_eventually : ∀ᶠ t in 𝓝 (0 : ℝ),
      (f t).proj ∈ (chartAt H p).source := by
    have hπ_cont : Continuous
        (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    have hcomp : ContinuousAt (fun t => (f t).proj) 0 :=
      hπ_cont.continuousAt.comp hf_cont_at0
    have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
    have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
    have hp_nhds : (chartAt H p).source ∈ 𝓝 p := hp_open.mem_nhds hp_mem
    have hpf0 : (f 0).proj = p := hf0_proj
    have : (fun t => (f t).proj) ⁻¹' (chartAt H p).source ∈ 𝓝 (0 : ℝ) := by
      apply hcomp.preimage_mem_nhds
      rw [hpf0]
      exact hp_nhds
    exact this
  obtain ⟨Φ, hΦ_init, hev⟩ :=
    chartPushedFlow_eq_lift_proj_eventually
      (I := I) (g := g) (p := p) (v_chart := v_chart) (f := f)
      hf0_proj hf0_fiber hf_chart_src_eventually hd
  refine ⟨Φ, hΦ_init, ?_⟩
  filter_upwards [hev] with t ht
  rw [← hproj t]
  exact ht

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedFlow_eq_maximalGeodesicChosenCurve_eventually
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t₁ : ℝ} (ht₁ : t₁ ∈ maximalGeodesicInterval (I := I) g p v)
    {f : ℝ → TangentBundle I M}
    (hproj_chosen : ∀ t, (f t).proj =
      maximalGeodesicChosenCurve (I := I) g p v ht₁ t)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_int_at0 : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) 0)
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f 0)
        (chartPhaseVF (I := I) g p (chartPushLift (I := I) f 0 t)) t ∧
      chartPushLift (I := I) f 0 t ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, (v : E)) : E × E), 0) =
        (extChartAt I p p, (v : E)) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        maximalGeodesicChosenCurve (I := I) g p v ht₁ t =
          chartFlowGeodesicCurve (I := I) Φ p (v : E) t) :=
  chartPushedFlow_eq_witness_curve_eventually
    (I := I) (g := g) (p := p) (v_chart := (v : E))
    (γ := maximalGeodesicChosenCurve (I := I) g p v ht₁)
    (f := f) hproj_chosen hf0 hf_int_at0 hd

end HeadlineBridge

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
