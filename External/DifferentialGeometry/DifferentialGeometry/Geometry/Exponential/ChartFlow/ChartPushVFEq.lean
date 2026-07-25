import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Geodesic.Uniqueness



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
open DifferentialGeometry.Integral.DivergenceTheorem

section AchartEquality

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma achart_modelProd_eq_of_proj_eq {q₁ q₂ : TangentBundle I M}
    (h : q₁.proj = q₂.proj) :
    achart (ModelProd H E) q₁ = achart (ModelProd H E) q₂ := by
  refine Subtype.ext ?_
  change chartAt (ModelProd H E) q₁ = chartAt (ModelProd H E) q₂
  rw [TangentBundle.chartAt q₁, TangentBundle.chartAt q₂, h]

end AchartEquality

section TangentCoordChange

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma mem_chartAt_modelProd_zero_source_iff
    (α : M) (q : TangentBundle I M) :
    q ∈ (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source ↔
      q.proj ∈ (chartAt H α).source := by
  exact TangentBundle.mem_chart_source_iff (I := I) (M := M) q
    (⟨α, (0 : E)⟩ : TangentBundle I M)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma trivializationAt_tangent_continuousLinearMapAt_eq_core
    (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ q =
      (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
        (achart (ModelProd H E) q)
        (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) q := by
  have hq_src : q ∈
      (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) α q).mpr hq
  exact TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (b₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (b := q) hq_src

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tangentCoordChange_tangent_eq_triv
    (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) (V : E × E) :
    tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q V =
      (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ q V := by
  rw [trivializationAt_tangent_continuousLinearMapAt_eq_core (I := I) α q hq]
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tangentCoordChange_tangent_symm_apply
    (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) (v_fiber : E × E) :
    tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q
      ((trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).symm q v_fiber) = v_fiber := by
  classical
  have hq_base : q ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (mem_chartAt_modelProd_zero_source_iff (I := I) α q).mpr hq
  rw [tangentCoordChange_tangent_eq_triv (I := I) α q hq]
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hsymm : e.symm q v_fiber = e.symmL ℝ q v_fiber := by
    rfl
  rw [hsymm]
  exact e.continuousLinearMapAt_symmL hq_base v_fiber

omit [NeZero (Module.finrank ℝ E)] in
lemma tangentCoordChange_tangent_geodesicVF
    (g : SmoothRiemannianMetric I M) (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) :
    tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q
      (geodesicVectorFieldChart (I := I) g α q) =
        geodesicVectorFieldChartFiber (I := I) g α q := by
  unfold geodesicVectorFieldChart
  exact tangentCoordChange_tangent_symm_apply (I := I) α q hq
    (geodesicVectorFieldChartFiber (I := I) g α q)

end TangentCoordChange

section ChartPushVFEq

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma achart_modelProd_f0_eq
    {f : ℝ → TangentBundle I M} {α : M}
    (hf0_proj : (f 0).proj = α) :
    achart (ModelProd H E) (f 0) =
      achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M) := by
  apply achart_modelProd_eq_of_proj_eq (I := I)
  exact hf0_proj

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tangentCoordChange_tangent_f0_eq
    {f : ℝ → TangentBundle I M} {α : M}
    (hf0_proj : (f 0).proj = α) (q : TangentBundle I M) :
    tangentCoordChange I.tangent q (f 0) q =
      tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q := by
  change (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
      (achart (ModelProd H E) q) (achart (ModelProd H E) (f 0)) q =
    (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
      (achart (ModelProd H E) q)
      (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) q
  rw [achart_modelProd_f0_eq (I := I) (f := f) (α := α) hf0_proj]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushVF_eq_geodesicVectorFieldChartFiber
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} (hf0_proj : (f 0).proj = α)
    (t : ℝ) (ht : (f t).proj ∈ (chartAt H α).source) :
    chartPushVF (I := I) g α f 0 t =
      geodesicVectorFieldChartFiber (I := I) g α (f t) := by
  unfold chartPushVF
  rw [tangentCoordChange_tangent_f0_eq (I := I) hf0_proj (f t)]
  exact tangentCoordChange_tangent_geodesicVF (I := I) g α (f t) ht

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem geodesicVectorFieldChartFiber_eq_chartPhaseVF
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} (hf0_proj : (f 0).proj = α)
    (t : ℝ) (ht : (f t).proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChartFiber (I := I) g α (f t) =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t) := by
  classical
  have hpair : chartPushLift (I := I) f 0 t =
      (extChartAt I α (f t).proj, chartFiberCoord (I := I) α (f t)) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f) (t₀ := 0) (t := t) ?_
    · rw [h_eq]
      rw [hf0_proj]
    · rw [hf0_proj]; exact ht
  rw [hpair]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushVF_eq_chartPhaseVF
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} (hf0_proj : (f 0).proj = α)
    (t : ℝ) (ht : (f t).proj ∈ (chartAt H α).source) :
    chartPushVF (I := I) g α f 0 t =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t) := by
  rw [chartPushVF_eq_geodesicVectorFieldChartFiber (I := I) g α
        hf0_proj t ht]
  exact geodesicVectorFieldChartFiber_eq_chartPhaseVF (I := I) g α
    hf0_proj t ht

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma achart_modelProd_ft₀_eq
    {f : ℝ → TangentBundle I M} {α : M} {t₀ : ℝ}
    (hft₀_proj : (f t₀).proj = α) :
    achart (ModelProd H E) (f t₀) =
      achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M) := by
  apply achart_modelProd_eq_of_proj_eq (I := I)
  exact hft₀_proj

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tangentCoordChange_tangent_ft₀_eq
    {f : ℝ → TangentBundle I M} {α : M} {t₀ : ℝ}
    (hft₀_proj : (f t₀).proj = α) (q : TangentBundle I M) :
    tangentCoordChange I.tangent q (f t₀) q =
      tangentCoordChange I.tangent q (⟨α, (0 : E)⟩ : TangentBundle I M) q := by
  change (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
      (achart (ModelProd H E) q) (achart (ModelProd H E) (f t₀)) q =
    (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
      (achart (ModelProd H E) q)
      (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) q
  rw [achart_modelProd_ft₀_eq (I := I) (f := f) (α := α) (t₀ := t₀) hft₀_proj]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushVF_eq_geodesicVectorFieldChartFiber_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ} (hft₀_proj : (f t₀).proj = α)
    (s : ℝ) (hs : (f s).proj ∈ (chartAt H α).source) :
    chartPushVF (I := I) g α f t₀ s =
      geodesicVectorFieldChartFiber (I := I) g α (f s) := by
  unfold chartPushVF
  rw [tangentCoordChange_tangent_ft₀_eq (I := I) (t₀ := t₀) hft₀_proj (f s)]
  exact tangentCoordChange_tangent_geodesicVF (I := I) g α (f s) hs

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem geodesicVectorFieldChartFiber_eq_chartPhaseVF_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ} (hft₀_proj : (f t₀).proj = α)
    (s : ℝ) (hs : (f s).proj ∈ (chartAt H α).source) :
    geodesicVectorFieldChartFiber (I := I) g α (f s) =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f t₀ s) := by
  classical
  have hpair : chartPushLift (I := I) f t₀ s =
      (extChartAt I α (f s).proj, chartFiberCoord (I := I) α (f s)) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f) (t₀ := t₀) (t := s) ?_
    · rw [h_eq]
      rw [hft₀_proj]
    · rw [hft₀_proj]; exact hs
  rw [hpair]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushVF_eq_chartPhaseVF_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ} (hft₀_proj : (f t₀).proj = α)
    (s : ℝ) (hs : (f s).proj ∈ (chartAt H α).source) :
    chartPushVF (I := I) g α f t₀ s =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f t₀ s) := by
  rw [chartPushVF_eq_geodesicVectorFieldChartFiber_at (I := I) g α
        hft₀_proj s hs]
  exact geodesicVectorFieldChartFiber_eq_chartPhaseVF_at (I := I) g α
    hft₀_proj s hs

end ChartPushVFEq

section EventualChartPhase

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushLift_eventually_hasDerivAt_chartPhaseVF
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M}
    (hf0_proj : (f 0).proj = α)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f 0)
        (chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t)) t := by
  have hd := chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := α)
    (t₀ := 0) (f := f) hf
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_cont0 : ContinuousAt f 0 := hf.continuousAt
  have hcomp0 : ContinuousAt (fun t => (f t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_cont0
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hα_mem : α ∈ (chartAt H α).source := mem_chart_source H α
  have hf0_α : (f 0).proj = α := hf0_proj
  have hα_nhds : (chartAt H α).source ∈ 𝓝 α := hα_open.mem_nhds hα_mem
  have hsrc_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 (0 : ℝ) := by
    apply hcomp0.preimage_mem_nhds
    rw [hf0_α]
    exact hα_nhds
  filter_upwards [hd, hsrc_nhds] with t htD ht_src
  have hreplace : chartPushVF (I := I) g α f 0 t =
      chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t) :=
    chartPushVF_eq_chartPhaseVF (I := I) g α hf0_proj t ht_src
  rw [hreplace] at htD
  exact htD

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior
    {g : SmoothRiemannianMetric I M} {α : M}
    {f : ℝ → TangentBundle I M}
    (hf0_proj : (f 0).proj = α)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartPushLift (I := I) f 0)
        (chartPhaseVF (I := I) g α (chartPushLift (I := I) f 0 t)) t ∧
      chartPushLift (I := I) f 0 t ∈
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_cont0 : ContinuousAt f 0 := hf.continuousAt
  have hcomp0 : ContinuousAt (fun t => (f t).proj) 0 :=
    hπ_cont.continuousAt.comp hf_cont0
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hα_mem : α ∈ (chartAt H α).source := mem_chart_source H α
  have hf0_α : (f 0).proj = α := hf0_proj
  have hα_nhds : (chartAt H α).source ∈ 𝓝 α := hα_open.mem_nhds hα_mem
  have hsrc_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 (0 : ℝ) := by
    apply hcomp0.preimage_mem_nhds
    rw [hf0_α]
    exact hα_nhds
  have hd_phase :=
    chartPushLift_eventually_hasDerivAt_chartPhaseVF (I := I) (g := g) (α := α)
      (f := f) hf0_proj hf
  filter_upwards [hd_phase, hsrc_nhds] with t htD ht_src
  refine ⟨htD, ?_⟩
  have hpair : chartPushLift (I := I) f 0 t =
      (extChartAt I α (f t).proj, chartFiberCoord (I := I) α (f t)) := by
    have h_eq := chartPushLift_eq_pair (I := I) (f := f) (t₀ := 0) (t := t) ?_
    · rw [h_eq]; rw [hf0_α]
    · rw [hf0_α]; exact ht_src
  rw [hpair]
  refine ⟨?_, Set.mem_univ _⟩
  have h_target : extChartAt I α (f t).proj ∈ (extChartAt I α).target := by
    have h_src : (f t).proj ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact ht_src
    exact (extChartAt I α).map_source h_src
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) α h_target

end EventualChartPhase

section UnconditionalBridge

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedFlow_eq_witness_curve_eventually_unconditional
    (g : SmoothRiemannianMetric I M) (p : M) (v_chart : E)
    {γ : ℝ → M}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf0 : f 0 = (⟨p, v_chart⟩ : TangentBundle I M))
    (hf_int_at0 : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, v_chart) : E × E), 0) =
        (extChartAt I p p, v_chart) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        γ t = chartFlowGeodesicCurve (I := I) Φ p v_chart t) := by
  have hf0_proj : (f 0).proj = p := by rw [hf0]
  have hd := chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior
    (I := I) (g := g) (α := p) (f := f) hf0_proj hf_int_at0
  exact chartPushedFlow_eq_witness_curve_eventually
    (I := I) (g := g) (p := p) (v_chart := v_chart)
    (γ := γ) (f := f) hproj hf0 hf_int_at0 hd

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedFlow_eq_maximalGeodesicChosenCurve_eventually_unconditional
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t₁ : ℝ} (ht₁ : t₁ ∈ maximalGeodesicInterval (I := I) g p v)
    {f : ℝ → TangentBundle I M}
    (hproj_chosen : ∀ t, (f t).proj =
      maximalGeodesicChosenCurve (I := I) g p v ht₁ t)
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hf_int_at0 : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g p) 0) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      Φ (((extChartAt I p p, (v : E)) : E × E), 0) =
        (extChartAt I p p, (v : E)) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        maximalGeodesicChosenCurve (I := I) g p v ht₁ t =
          chartFlowGeodesicCurve (I := I) Φ p (v : E) t) :=
  chartPushedFlow_eq_witness_curve_eventually_unconditional
    (I := I) (g := g) (p := p) (v_chart := (v : E))
    (γ := maximalGeodesicChosenCurve (I := I) g p v ht₁)
    (f := f) hproj_chosen hf0 hf_int_at0

end UnconditionalBridge

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
