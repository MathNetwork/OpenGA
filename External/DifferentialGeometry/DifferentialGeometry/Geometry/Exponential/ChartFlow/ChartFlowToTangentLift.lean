import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformExistence
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Geodesic.Uniqueness



noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

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

section Definition

def chartFlowOrbitLift (Φ : (E × E) × ℝ → E × E) (p : M) (v : E) :
    ℝ → TangentBundle I M :=
  fun s => (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
    (Φ (((extChartAt I p p, v) : E × E), s))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartFlowOrbitLift_apply
    (Φ : (E × E) × ℝ → E × E) (p : M) (v : E) (s : ℝ) :
    chartFlowOrbitLift (I := I) Φ p v s =
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (Φ (((extChartAt I p p, v) : E × E), s)) := rfl

end Definition

section InverseChart

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma mem_extChartAt_tangent_zero_target
    (p : M) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    z ∈ (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
  classical
  have htarget := FiberBundle.extChartAt_target
    (IB := I) (F := E) (E := TangentSpace I)
    (x := (⟨p, (0 : E)⟩ : TangentBundle I M))
  rw [htarget]
  rcases hz with ⟨hz1, hz2⟩
  refine ⟨⟨?_, ?_⟩, hz2⟩
  · exact interior_subset hz1
  · rw [Set.mem_preimage, TangentBundle.trivializationAt_baseSet]
    have hz1_target : z.1 ∈ (extChartAt I p).target := interior_subset hz1
    have hz1_src : (extChartAt I p).symm z.1 ∈ (extChartAt I p).source :=
      (extChartAt I p).map_target hz1_target
    rwa [extChartAt_source] at hz1_src

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma extChartAt_tangent_zero_symm_proj
    (p : M) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z).proj =
      (extChartAt I p).symm z.1 := by
  classical
  have htgt := mem_extChartAt_tangent_zero_target (I := I) (p := p) hz
  set q : TangentBundle I M :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z with hq_def
  have hq_extsrc : q ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).source :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).map_target htgt
  have hq_chsrc : q ∈
      (chartAt (ModelProd H E) (⟨p, (0 : E)⟩ : TangentBundle I M)).source := by
    rwa [extChartAt_source] at hq_extsrc
  have hq_proj_src : q.proj ∈ (chartAt H p).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) p q).mp hq_chsrc
  have hright :
      extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) q = z :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).right_inv htgt
  have hfst :=
    extChartAt_tangent_apply_fst (I := I)
      (q := (⟨p, (0 : E)⟩ : TangentBundle I M)) (p := q) hq_proj_src
  have h_z1 : z.1 = extChartAt I p q.proj := by
    have := congrArg Prod.fst hright
    rw [hfst] at this
    exact this.symm
  have hq_extsrc_base : q.proj ∈ (extChartAt I p).source := by
    rwa [extChartAt_source]
  have hinv : (extChartAt I p).symm (extChartAt I p q.proj) = q.proj :=
    (extChartAt I p).left_inv hq_extsrc_base
  rw [h_z1, hinv]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma extChartAt_tangent_zero_apply_symm
    (p : M) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
        ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z) = z :=
  (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).right_inv
    (mem_extChartAt_tangent_zero_target (I := I) (p := p) hz)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartAt_source_of_extChartAt_tangent_zero_symm
    (p : M) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z).proj ∈
      (chartAt H p).source := by
  classical
  set q : TangentBundle I M :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm z with hq_def
  have htgt := mem_extChartAt_tangent_zero_target (I := I) (p := p) hz
  have hq_extsrc : q ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).source :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).map_target htgt
  have hq_chsrc : q ∈
      (chartAt (ModelProd H E) (⟨p, (0 : E)⟩ : TangentBundle I M)).source := by
    rwa [extChartAt_source] at hq_extsrc
  exact (mem_chartAt_modelProd_zero_source_iff (I := I) p q).mp hq_chsrc

end InverseChart

section InitialValue

variable [I.Boundaryless]

omit [I.Boundaryless] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLift_zero
    (p : M) (v : E) {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E)) :
    chartFlowOrbitLift (I := I) Φ p v 0 = (⟨p, v⟩ : TangentBundle I M) := by
  classical
  unfold chartFlowOrbitLift
  rw [hΦ_init]
  set q : TangentBundle I M := (⟨p, v⟩ : TangentBundle I M) with hq_def
  have hp_src : p ∈ (chartAt H p).source := mem_chart_source H p
  have hq_proj_src : q.proj ∈ (chartAt H p).source := hp_src
  have hch :=
    extChartAt_tangent_zero_apply_chartFiber (I := I) p (p := q) hq_proj_src
  have hfiber : chartFiberCoord (I := I) p q = v := by
    rw [hq_def]
    change (trivializationAt E (TangentSpace I) p
        (⟨p, v⟩ : TangentBundle I M)).2 = v
    have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hp_src
    have hp_extsrc : p ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact hp_src
    have hcore :
        (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p =
        (tangentBundleCore I M).coordChange (achart H p) (achart H p) p :=
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ)
        (b₀ := p) (b := p) hp_src
    have hself : ∀ w : E, tangentCoordChange I p p p w = w :=
      fun w =>
        tangentCoordChange_self (I := I) (x := p) (z := p) (v := w) hp_extsrc
    have hcore_at :
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v = v := by
      rw [hcore]; exact hself v
    have happly :
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v =
        (trivializationAt E (TangentSpace I) p
          (⟨p, v⟩ : TangentBundle I M)).2 := by
      change ((trivializationAt E (TangentSpace I) p).linearMapAt ℝ p) v = _
      have hcoe :=
        (trivializationAt E (TangentSpace I) p).coe_linearMapAt_of_mem
          (R := ℝ) hbase
      exact congrFun hcoe v
    rw [← happly, hcore_at]
  have h_q_proj : q.proj = p := by rw [hq_def]
  rw [h_q_proj, hfiber] at hch
  have hq_chsrc : q ∈ (chartAt (ModelProd H E)
      (⟨p, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [mem_chartAt_modelProd_zero_source_iff (I := I) p q]
    exact hq_proj_src
  have hq_extsrc : q ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hq_chsrc
  have hleft :
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) q) = q :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv hq_extsrc
  rw [← hch] at *
  exact hleft

end InitialValue

section ProjectionIdentity

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartFlowOrbitLift_proj
    (p : M) (v : E) {Φ : (E × E) × ℝ → E × E} (s : ℝ)
    (hΦ_target : Φ (((extChartAt I p p, v) : E × E), s) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    (chartFlowOrbitLift (I := I) Φ p v s).proj =
      (extChartAt I p).symm (Φ (((extChartAt I p p, v) : E × E), s)).1 := by
  unfold chartFlowOrbitLift
  exact extChartAt_tangent_zero_symm_proj (I := I) p hΦ_target

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartFlowOrbitLift_proj_mem_chartAt_source
    (p : M) (v : E) {Φ : (E × E) × ℝ → E × E} (s : ℝ)
    (hΦ_target : Φ (((extChartAt I p p, v) : E × E), s) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    (chartFlowOrbitLift (I := I) Φ p v s).proj ∈ (chartAt H p).source := by
  unfold chartFlowOrbitLift
  exact chartAt_source_of_extChartAt_tangent_zero_symm (I := I) p hΦ_target

end ProjectionIdentity

section ChartPushLiftIdentification

variable [I.Boundaryless]

omit [I.Boundaryless] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLift_chartPushLift_eq
    (p : M) (v : E) {Φ : (E × E) × ℝ → E × E} (s : ℝ)
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E))
    (hΦ_target : Φ (((extChartAt I p p, v) : E × E), s) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    chartPushLift (I := I) (chartFlowOrbitLift (I := I) Φ p v) 0 s =
      Φ (((extChartAt I p p, v) : E × E), s) := by
  classical
  have hF0 : chartFlowOrbitLift (I := I) Φ p v 0 = (⟨p, v⟩ : TangentBundle I M) :=
    chartFlowOrbitLift_zero (I := I) p v hΦ_init
  have hchart_eq :
      extChartAt I.tangent (chartFlowOrbitLift (I := I) Φ p v 0) =
        extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) := by
    rw [extChartAt_tangent_eq_at_proj (I := I) (chartFlowOrbitLift (I := I) Φ p v 0)]
    rw [hF0]
  unfold chartPushLift
  rw [hchart_eq]
  unfold chartFlowOrbitLift
  exact extChartAt_tangent_zero_apply_symm (I := I) p hΦ_target

end ChartPushLiftIdentification

section Continuity

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartFlowOrbitLift_continuousOn
    (p : M) (v : E) {Φ : (E × E) × ℝ → E × E} {T : ℝ}
    (hΦ_cont : ContinuousOn (fun s : ℝ => Φ (((extChartAt I p p, v) : E × E), s))
      (Set.Ioo (-T) T))
    (hΦ_target : ∀ s ∈ Set.Ioo (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ContinuousOn (chartFlowOrbitLift (I := I) Φ p v) (Set.Ioo (-T) T) := by
  classical
  have h_extsrc : ∀ s ∈ Set.Ioo (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
    intro s hs
    exact mem_extChartAt_tangent_zero_target (I := I) p (hΦ_target s hs)
  have hsymm_cont :=
    continuousOn_extChartAt_symm (I := I.tangent)
      (⟨p, (0 : E)⟩ : TangentBundle I M)
  unfold chartFlowOrbitLift
  refine hsymm_cont.comp hΦ_cont ?_
  intro s hs
  exact h_extsrc s hs

end Continuity

section IntegralCurveAtZero

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlowOrbitLift_eventuallyEq_isMIntegralCurveAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E))
    (hΦ_chart_phase : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s ∧
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    ∃ (g_v : ℝ → TangentBundle I M),
      g_v 0 = (⟨p, v⟩ : TangentBundle I M) ∧
      IsMIntegralCurveAt g_v (geodesicVectorFieldChart (I := I) g p) 0 ∧
      g_v =ᶠ[𝓝 (0 : ℝ)] chartFlowOrbitLift (I := I) Φ p v := by
  classical
  obtain ⟨g_v, hg0, hg_int⟩ :=
    Geodesic.exists_isMIntegralCurveAt_geodesicVectorFieldChart
      (I := I) (g := g) (p := p) (v := v)
  refine ⟨g_v, hg0, hg_int, ?_⟩
  have hF0 : chartFlowOrbitLift (I := I) Φ p v 0 = (⟨p, v⟩ : TangentBundle I M) :=
    chartFlowOrbitLift_zero (I := I) p v hΦ_init
  have hg_proj0 : (g_v 0).proj = p := by rw [hg0]
  have hd_g_phase :=
    chartPushLift_eventually_hasDerivAt_chartPhaseVF_and_target_interior
      (I := I) (g := g) (α := p) (f := g_v) hg_proj0 hg_int
  have hc_g0 : chartPushLift (I := I) g_v 0 0 = ((extChartAt I p p, v) : E × E) := by
    have h := chartPushLift_self_pair (I := I) g_v 0
    rw [h]
    have hproj0 : (g_v 0).proj = p := hg_proj0
    rw [hproj0]
    have hfiber0 : chartFiberCoord (I := I) p (g_v 0) = v := by
      rw [hg0]
      change (trivializationAt E (TangentSpace I) p
          (⟨p, v⟩ : TangentBundle I M)).2 = v
      have hp_src : p ∈ (chartAt H p).source := mem_chart_source H p
      have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]; exact hp_src
      have hp_extsrc : p ∈ (extChartAt I p).source := by
        rw [extChartAt_source]; exact hp_src
      have hcore :
          (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p =
          (tangentBundleCore I M).coordChange (achart H p) (achart H p) p :=
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ)
          (b₀ := p) (b := p) hp_src
      have hself : ∀ w : E, tangentCoordChange I p p p w = w :=
        fun w => tangentCoordChange_self (I := I) (x := p) (z := p) (v := w) hp_extsrc
      have hcore_at :
          ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v = v := by
        rw [hcore]; exact hself v
      have happly :
          ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p) v =
          (trivializationAt E (TangentSpace I) p
            (⟨p, v⟩ : TangentBundle I M)).2 := by
        change ((trivializationAt E (TangentSpace I) p).linearMapAt ℝ p) v = _
        have hcoe :=
          (trivializationAt E (TangentSpace I) p).coe_linearMapAt_of_mem
            (R := ℝ) hbase
        exact congrFun hcoe v
      rw [← happly, hcore_at]
    rw [hfiber0]
  have hΦorbit_zero :
      (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s')) 0 =
        ((extChartAt I p p, v) : E × E) := hΦ_init
  have hbase_interior : ((extChartAt I p p, v) : E × E) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hp_extsrc : p ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact mem_chart_source H p
    have h_target : extChartAt I p p ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source hp_extsrc
    refine ⟨?_, Set.mem_univ _⟩
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target
  have hcd_eq := chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
    (c₁ := chartPushLift (I := I) g_v 0)
    (c₂ := fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
    (z₀ := ((extChartAt I p p, v) : E × E))
    hbase_interior hc_g0 hΦorbit_zero hd_g_phase hΦ_chart_phase
  have hchart_eq :
      extChartAt I.tangent (g_v 0) =
        extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) := by
    rw [extChartAt_tangent_eq_at_proj (I := I) (g_v 0), hg0]
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hg_cont0 : ContinuousAt g_v 0 := hg_int.continuousAt
  have hcomp0 : ContinuousAt (fun s => (g_v s).proj) 0 :=
    hπ_cont.continuousAt.comp hg_cont0
  have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
  have hp_mem : p ∈ (chartAt H p).source := mem_chart_source H p
  have hp_nhds : (chartAt H p).source ∈ 𝓝 p := hp_open.mem_nhds hp_mem
  have hsrc_nhds : (fun s : ℝ => (g_v s).proj) ⁻¹' (chartAt H p).source ∈
      𝓝 (0 : ℝ) := by
    apply hcomp0.preimage_mem_nhds
    rw [hg_proj0]; exact hp_nhds
  filter_upwards [hcd_eq, hsrc_nhds] with s hs_eq hs_src
  unfold chartPushLift at hs_eq
  rw [hchart_eq] at hs_eq
  have hg_src : g_v s ∈ (chartAt (ModelProd H E)
      (⟨p, (0 : E)⟩ : TangentBundle I M)).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) p (g_v s)).mpr hs_src
  have hg_extsrc : g_v s ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hg_src
  have hleft :
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_v s)) = g_v s :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv hg_extsrc
  unfold chartFlowOrbitLift
  rw [← hs_eq]
  exact hleft.symm

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLift_isMIntegralCurveAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E))
    (hΦ_chart_phase : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s ∧
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    IsMIntegralCurveAt (chartFlowOrbitLift (I := I) Φ p v)
      (geodesicVectorFieldChart (I := I) g p) 0 := by
  classical
  obtain ⟨g_v, _hg0, hg_int, hg_eq⟩ :=
    exists_chartFlowOrbitLift_eventuallyEq_isMIntegralCurveAt_zero
      (I := I) (g := g) (p := p) (v := v) (Φ := Φ) hΦ_init hΦ_chart_phase
  rw [IsMIntegralCurveAt] at hg_int ⊢
  filter_upwards [hg_int, hg_eq, hg_eq.eventually_nhds] with s hs_int hs_eq hs_eq_nhds
  rw [← hs_eq]
  refine hs_int.congr_of_eventuallyEq ?_
  filter_upwards [hs_eq_nhds] with x hx
  exact hx.symm

end IntegralCurveAtZero

section HeadlineUniform

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlowOrbitLift_data_uniform
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (ρ T : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        Φ (((extChartAt I p p, v) : E × E), 0) =
          ((extChartAt I p p, v) : E × E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        chartFlowOrbitLift (I := I) Φ p v 0 =
          (⟨p, v⟩ : TangentBundle I M)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        (chartFlowOrbitLift (I := I) Φ p v s).proj =
          (extChartAt I p).symm
            (Φ (((extChartAt I p p, v) : E × E), s)).1) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ, ∀ s ∈ Set.Icc (-T) T,
        chartPushLift (I := I) (chartFlowOrbitLift (I := I) Φ p v) 0 s =
          Φ (((extChartAt I p p, v) : E × E), s)) ∧
      (∀ v ∈ Metric.ball (0 : E) ρ,
        IsMIntegralCurveAt (chartFlowOrbitLift (I := I) Φ p v)
          (geodesicVectorFieldChart (I := I) g p) 0) := by
  classical
  obtain ⟨ρ, T, Φ, hρ_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, _hF_data⟩ :=
    exists_uniform_existence_interval (I := I) (g := g) (p := p)
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact chartFlowOrbitLift_zero (I := I) p v (hΦ_init v hv)
  · intro v hv s hs
    exact chartFlowOrbitLift_proj (I := I) p v s (hΦ_target v hv s hs)
  · intro v hv s hs
    exact chartFlowOrbitLift_chartPushLift_eq (I := I) p v s
      (hΦ_init v hv) (hΦ_target v hv s hs)
  · intro v hv
    have hΦ_phase_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
        HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
          (chartPhaseVF (I := I) g p
            (Φ (((extChartAt I p p, v) : E × E), s))) s ∧
        Φ (((extChartAt I p p, v) : E × E), s) ∈
          (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
      have hIoo_nhds : Set.Ioo (-T) T ∈ 𝓝 (0 : ℝ) :=
        isOpen_Ioo.mem_nhds ⟨by linarith, hT_pos⟩
      filter_upwards [hIoo_nhds] with s hs
      refine ⟨hΦ_phase v hv s hs, ?_⟩
      exact hΦ_target v hv s (Set.Ioo_subset_Icc_self hs)
    exact chartFlowOrbitLift_isMIntegralCurveAt_zero (I := I) (g := g) (p := p)
      (v := v) (Φ := Φ) (hΦ_init v hv) hΦ_phase_ev

end HeadlineUniform

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
