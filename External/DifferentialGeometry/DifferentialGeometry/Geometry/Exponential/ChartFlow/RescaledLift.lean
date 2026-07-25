import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowToTangentLift
import DifferentialGeometry.Geometry.Exponential.ChartFlow.InverseManifoldChain
import DifferentialGeometry.Geometry.Exponential.ChartFlow.PreconnectedPropagation
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowData
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.MaximalRescaling



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

def chartFlowOrbitLiftRescaled
    (Φ : (E × E) × ℝ → E × E) (p : M) (t' : ℝ) (v : E) :
    ℝ → TangentBundle I M :=
  fun s => (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
    (rescaleChartOrbit (E := E) t' (Φ (((extChartAt I p p, v) : E × E), t' * s)))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartFlowOrbitLiftRescaled_apply
    (Φ : (E × E) × ℝ → E × E) (p : M) (t' : ℝ) (v : E) (s : ℝ) :
    chartFlowOrbitLiftRescaled (I := I) Φ p t' v s =
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (rescaleChartOrbit (E := E) t' (Φ (((extChartAt I p p, v) : E × E), t' * s))) := rfl

end Definition

section ChartTargetInterior

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] in
lemma rescaleChartOrbit_mem_chartTargetInterior
    {p : M} (t' : ℝ) {z : E × E}
    (hz : z ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    rescaleChartOrbit (E := E) t' z ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
  refine ⟨?_, Set.mem_univ _⟩
  change z.1 ∈ _
  exact hz.1

end ChartTargetInterior

section InitialValue

variable [I.Boundaryless]

omit [I.Boundaryless] in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLiftRescaled_zero
    (p : M) (v : E) (t' : ℝ) {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E)) :
    chartFlowOrbitLiftRescaled (I := I) Φ p t' v 0 =
      (⟨p, t' • v⟩ : TangentBundle I M) := by
  classical
  have hzero : chartFlowOrbitLiftRescaled (I := I) Φ p t' v 0 =
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (rescaleChartOrbit (E := E) t' (Φ (((extChartAt I p p, v) : E × E), 0))) := by
    unfold chartFlowOrbitLiftRescaled
    rw [mul_zero]
  rw [hzero, hΦ_init]
  change (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
      ((extChartAt I p p, t' • v) : E × E) = (⟨p, t' • v⟩ : TangentBundle I M)
  exact chartFlowOrbitLift_zero (I := I) (Φ := fun _ => ((extChartAt I p p, t' • v) : E × E))
    p (t' • v) rfl

end InitialValue

section ProjectionIdentity

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartFlowOrbitLiftRescaled_proj
    (p : M) (v : E) (t' : ℝ) {Φ : (E × E) × ℝ → E × E} (s : ℝ)
    (hΦ_target : Φ (((extChartAt I p p, v) : E × E), t' * s) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s).proj =
      (extChartAt I p).symm (Φ (((extChartAt I p p, v) : E × E), t' * s)).1 := by
  classical
  unfold chartFlowOrbitLiftRescaled
  have hresc_target := rescaleChartOrbit_mem_chartTargetInterior (I := I) (p := p)
    t' hΦ_target
  have h := extChartAt_tangent_zero_symm_proj (I := I) (p := p)
    (z := rescaleChartOrbit (E := E) t' (Φ (((extChartAt I p p, v) : E × E), t' * s)))
    hresc_target
  rw [h]
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartFlowOrbitLiftRescaled_proj_mem_chartAt_source
    (p : M) (v : E) (t' : ℝ) {Φ : (E × E) × ℝ → E × E} (s : ℝ)
    (hΦ_target : Φ (((extChartAt I p p, v) : E × E), t' * s) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :
    (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s).proj ∈
      (chartAt H p).source := by
  classical
  unfold chartFlowOrbitLiftRescaled
  have hresc_target := rescaleChartOrbit_mem_chartTargetInterior (I := I) (p := p)
    t' hΦ_target
  exact chartAt_source_of_extChartAt_tangent_zero_symm (I := I) (p := p) hresc_target

end ProjectionIdentity

section RescaledChartPhase

variable [I.Boundaryless]

lemma mul_mem_Ioo_of_pos_of_lt
    {T t' : ℝ} (ht' : 0 < t') {s : ℝ}
    (hs : s ∈ Set.Ioo (-T / t') (T / t')) :
    t' * s ∈ Set.Ioo (-T) T := by
  obtain ⟨hlo, hhi⟩ := hs
  constructor
  · have h1 : t' * (-T / t') < t' * s := mul_lt_mul_of_pos_left hlo ht'
    have h2 : t' * (-T / t') = -T := by
      field_simp
    linarith
  · have h1 : t' * s < t' * (T / t') := mul_lt_mul_of_pos_left hhi ht'
    have h2 : t' * (T / t') = T := by
      field_simp
    linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma rescaled_orbit_hasDerivAt_chartPhaseVF
    {g : SmoothRiemannianMetric I M} {p : M} {Φ : (E × E) × ℝ → E × E}
    {T t' : ℝ} (ht'_pos : 0 < t') (v : E)
    (hΦ_phase : ∀ s' ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s'' : ℝ => Φ (((extChartAt I p p, v) : E × E), s''))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s'))) s')
    {s : ℝ} (hs : s ∈ Set.Ioo (-T / t') (T / t')) :
    HasDerivAt
      (fun s' : ℝ =>
        rescaleChartOrbit (E := E) t'
          (Φ (((extChartAt I p p, v) : E × E), t' * s')))
      (chartPhaseVF (I := I) g p
        (rescaleChartOrbit (E := E) t'
          (Φ (((extChartAt I p p, v) : E × E), t' * s)))) s := by
  classical
  have hts : t' * s ∈ Set.Ioo (-T) T :=
    mul_mem_Ioo_of_pos_of_lt ht'_pos hs
  have hd : HasDerivAt (fun s'' : ℝ => Φ (((extChartAt I p p, v) : E × E), s''))
      (chartPhaseVF (I := I) g p
        (Φ (((extChartAt I p p, v) : E × E), t' * s))) (t' * s) :=
    hΦ_phase (t' * s) hts
  exact hasDerivAt_rescaled_orbit (I := I) (g := g) (α := p)
    (c := fun s'' : ℝ => Φ (((extChartAt I p p, v) : E × E), s''))
    (s₀ := s) (a := t') hd

end RescaledChartPhase

section LocalLiftAtsZero

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma local_lift_eventuallyEq_chartFlowOrbitLiftRescaled
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) (t' : ℝ)
    {Φ : (E × E) × ℝ → E × E} {s₀ : ℝ}
    (hΦ_target_s₀ : Φ (((extChartAt I p p, v) : E × E), t' * s₀) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hd_phase : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt
        (fun s' : ℝ => rescaleChartOrbit (E := E) t'
          (Φ (((extChartAt I p p, v) : E × E), t' * s')))
        (chartPhaseVF (I := I) g p
          (rescaleChartOrbit (E := E) t'
            (Φ (((extChartAt I p p, v) : E × E), t' * s)))) s ∧
      Φ (((extChartAt I p p, v) : E × E), t' * s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    {g_loc : ℝ → TangentBundle I M}
    (hg_loc_s₀ : g_loc s₀ = chartFlowOrbitLiftRescaled (I := I) Φ p t' v s₀)
    (hg_loc_int : IsMIntegralCurveAt g_loc
      (geodesicVectorFieldChart (I := I) g p) s₀) :
    g_loc =ᶠ[𝓝 s₀] chartFlowOrbitLiftRescaled (I := I) Φ p t' v := by
  classical
  have hresc_target_s₀ :=
    rescaleChartOrbit_mem_chartTargetInterior (I := I) (p := p) t' hΦ_target_s₀
  have hF_s₀_src : (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s₀).proj ∈
      (chartAt H p).source :=
    chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p v t' s₀ hΦ_target_s₀
  have hg_loc_s₀_src : (g_loc s₀).proj ∈ (chartAt H p).source := by
    rw [hg_loc_s₀]; exact hF_s₀_src
  have hd_gloc :=
    eventually_hasDerivAt_chartPhaseVF_at_zero_section (I := I)
      (g := g) (α := p) (s₀ := s₀) (f := g_loc) hg_loc_s₀_src hg_loc_int
  set c₁ : ℝ → E × E := fun τ : ℝ =>
    extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + τ)) with hc₁_def
  set c₂ : ℝ → E × E := fun τ : ℝ =>
    rescaleChartOrbit (E := E) t' (Φ (((extChartAt I p p, v) : E × E), t' * (s₀ + τ)))
    with hc₂_def
  set z₀ : E × E := rescaleChartOrbit (E := E) t'
      (Φ (((extChartAt I p p, v) : E × E), t' * s₀)) with hz₀_def
  have hz₀_interior : z₀ ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := hresc_target_s₀
  have hc₂_zero : c₂ 0 = z₀ := by
    change rescaleChartOrbit (E := E) t'
        (Φ (((extChartAt I p p, v) : E × E), t' * (s₀ + 0))) =
      rescaleChartOrbit (E := E) t'
        (Φ (((extChartAt I p p, v) : E × E), t' * s₀))
    rw [add_zero]
  have hc₁_zero : c₁ 0 = z₀ := by
    change extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)
        (g_loc (s₀ + 0)) = z₀
    rw [add_zero, hg_loc_s₀]
    unfold chartFlowOrbitLiftRescaled
    exact extChartAt_tangent_zero_apply_symm (I := I) p hresc_target_s₀
  have htranslate : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
    have h1 : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
      (continuous_const.add continuous_id).continuousAt
    have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) := h1
    simpa using this
  have hd_c₂ : ∀ᶠ τ in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (chartPhaseVF (I := I) g p (c₂ τ)) τ ∧
      c₂ τ ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hev := htranslate.eventually hd_phase
    filter_upwards [hev] with τ hτ
    obtain ⟨hτD, hτT⟩ := hτ
    refine ⟨?_, ?_⟩
    · have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
        simpa using (hasDerivAt_id τ).const_add s₀
      have hcomp := hτD.scomp τ h_shift
      simp only [one_smul] at hcomp
      convert hcomp using 1
    · exact rescaleChartOrbit_mem_chartTargetInterior (I := I) (p := p) t' hτT
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hc₁_target_int : ∀ᶠ τ in 𝓝 (0 : ℝ),
      c₁ τ ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hcomp : ContinuousAt (fun τ : ℝ => (g_loc (s₀ + τ)).proj) 0 := by
      have h_shift : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have h_gloc_at : ContinuousAt g_loc (s₀ + 0) := by
        rw [add_zero]; exact hg_loc_int.continuousAt
      exact hπ_cont.continuousAt.comp (h_gloc_at.comp h_shift)
    have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
    have hp_nhds : (chartAt H p).source ∈ 𝓝 ((g_loc s₀).proj) := by
      apply hp_open.mem_nhds
      rw [hg_loc_s₀]; exact hF_s₀_src
    have hval0 : (g_loc (s₀ + 0)).proj = (g_loc s₀).proj := by rw [add_zero]
    have hpre : (fun τ : ℝ => (g_loc (s₀ + τ)).proj) ⁻¹'
        (chartAt H p).source ∈ 𝓝 (0 : ℝ) := by
      apply hcomp.preimage_mem_nhds
      rw [hval0]; exact hp_nhds
    filter_upwards [hpre] with τ hτ
    have hpair :
        extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + τ)) =
          (extChartAt I p (g_loc (s₀ + τ)).proj,
            chartFiberCoord (I := I) p (g_loc (s₀ + τ))) :=
      extChartAt_tangent_zero_apply_chartFiber (I := I) p hτ
    refine ⟨?_, Set.mem_univ _⟩
    show (c₁ τ).1 ∈ _
    have h_c₁_val : c₁ τ =
        (extChartAt I p (g_loc (s₀ + τ)).proj,
          chartFiberCoord (I := I) p (g_loc (s₀ + τ))) := hpair
    rw [h_c₁_val]
    change extChartAt I p (g_loc (s₀ + τ)).proj ∈ _
    have h_extsrc : (g_loc (s₀ + τ)).proj ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact hτ
    have h_target : extChartAt I p (g_loc (s₀ + τ)).proj ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source h_extsrc
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p h_target
  have hd_c₁ : ∀ᶠ τ in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (chartPhaseVF (I := I) g p (c₁ τ)) τ ∧
      c₁ τ ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hd_gloc_shift := htranslate.eventually hd_gloc
    filter_upwards [hd_gloc_shift, hc₁_target_int] with τ hτD hτT
    refine ⟨?_, hτT⟩
    have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add s₀
    have hcomp := hτD.scomp τ h_shift
    simp only [one_smul] at hcomp
    convert hcomp using 1
  have hc_eq : c₁ =ᶠ[𝓝 (0 : ℝ)] c₂ :=
    chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := p)
      (c₁ := c₁) (c₂ := c₂) (z₀ := z₀) hz₀_interior hc₁_zero hc₂_zero hd_c₁ hd_c₂
  have htranslate_inv : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 0) := by
    have h1 : ContinuousAt (fun s : ℝ => s - s₀) s₀ :=
      (continuous_id.sub continuous_const).continuousAt
    have : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) := h1
    simpa using this
  have hc_eq_in_s : ∀ᶠ s in 𝓝 s₀, c₁ (s - s₀) = c₂ (s - s₀) :=
    htranslate_inv.eventually hc_eq
  have hgloc_proj_src : ∀ᶠ s in 𝓝 s₀, (g_loc s).proj ∈ (chartAt H p).source := by
    have hcomp : ContinuousAt (fun s : ℝ => (g_loc s).proj) s₀ :=
      hπ_cont.continuousAt.comp hg_loc_int.continuousAt
    have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
    apply hcomp.preimage_mem_nhds
    rw [show (g_loc s₀).proj = (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s₀).proj
      from by rw [hg_loc_s₀]]
    exact hp_open.mem_nhds hF_s₀_src
  filter_upwards [hc_eq_in_s, hgloc_proj_src] with s hs_c_eq hs_gloc_src
  have hs_ext_eq :
      extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc s) =
        rescaleChartOrbit (E := E) t'
          (Φ (((extChartAt I p p, v) : E × E), t' * s)) := by
    have h₁ : c₁ (s - s₀) =
        extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc s) := by
      simp [hc₁_def, add_sub_cancel]
    have h₂ : c₂ (s - s₀) =
        rescaleChartOrbit (E := E) t'
          (Φ (((extChartAt I p p, v) : E × E), t' * s)) := by
      simp [hc₂_def, add_sub_cancel]
    rw [← h₁, hs_c_eq, h₂]
  have hgloc_chsrc : g_loc s ∈
      (chartAt (ModelProd H E) (⟨p, (0 : E)⟩ : TangentBundle I M)).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) p (g_loc s)).mpr hs_gloc_src
  have hgloc_extsrc : g_loc s ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hgloc_chsrc
  have hleft :
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc s)) = g_loc s :=
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).left_inv hgloc_extsrc
  unfold chartFlowOrbitLiftRescaled
  rw [← hleft, hs_ext_eq]

end LocalLiftAtsZero

section IntegralCurveOnIoo

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLiftRescaled_isMIntegralCurveAt_of_mem_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {T t' : ℝ} (ht'_pos : 0 < t')
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (-T / t') (T / t')) :
    IsMIntegralCurveAt (chartFlowOrbitLiftRescaled (I := I) Φ p t' v)
      (geodesicVectorFieldChart (I := I) g p) s₀ := by
  classical
  have hts₀ : t' * s₀ ∈ Set.Ioo (-T) T :=
    mul_mem_Ioo_of_pos_of_lt ht'_pos hs₀
  have hts₀_Icc : t' * s₀ ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self hts₀
  have hΦ_target_s₀ := hΦ_target_Icc (t' * s₀) hts₀_Icc
  have hF_s₀_src : (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s₀).proj ∈
      (chartAt H p).source :=
    chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p v t' s₀ hΦ_target_s₀
  have hsmooth : ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun w : TangentBundle I M =>
        (⟨w, geodesicVectorFieldChart (I := I) g p w⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s₀) :=
    geodesicVectorFieldChart_contMDiffAt (I := I) g p
      (p₀ := chartFlowOrbitLiftRescaled (I := I) Φ p t' v s₀) hF_s₀_src
  have hsmooth1 : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun w : TangentBundle I M =>
        (⟨w, geodesicVectorFieldChart (I := I) g p w⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s₀) :=
    hsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  obtain ⟨g_loc, hg_loc_s₀, hg_loc_int⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g p)
      (t₀ := s₀) (x₀ := chartFlowOrbitLiftRescaled (I := I) Φ p t' v s₀) hsmooth1
  have hd_phase_ev : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt
        (fun s' : ℝ => rescaleChartOrbit (E := E) t'
          (Φ (((extChartAt I p p, v) : E × E), t' * s')))
        (chartPhaseVF (I := I) g p
          (rescaleChartOrbit (E := E) t'
            (Φ (((extChartAt I p p, v) : E × E), t' * s)))) s ∧
      Φ (((extChartAt I p p, v) : E × E), t' * s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hIoo_nhds : Set.Ioo (-T / t') (T / t') ∈ 𝓝 s₀ := isOpen_Ioo.mem_nhds hs₀
    filter_upwards [hIoo_nhds] with s hs
    refine ⟨?_, ?_⟩
    · exact rescaled_orbit_hasDerivAt_chartPhaseVF (I := I) (g := g) (p := p)
        (Φ := Φ) (T := T) (t' := t') ht'_pos v hΦ_phase_Ioo hs
    · exact hΦ_target_Icc (t' * s)
        (Set.Ioo_subset_Icc_self (mul_mem_Ioo_of_pos_of_lt ht'_pos hs))
  have h_eq : g_loc =ᶠ[𝓝 s₀] chartFlowOrbitLiftRescaled (I := I) Φ p t' v :=
    local_lift_eventuallyEq_chartFlowOrbitLiftRescaled (I := I) (g := g) (p := p)
      (v := v) (t' := t') (Φ := Φ) (s₀ := s₀)
      hΦ_target_s₀ hd_phase_ev hg_loc_s₀ hg_loc_int
  rw [IsMIntegralCurveAt] at hg_loc_int ⊢
  filter_upwards [hg_loc_int, h_eq, h_eq.eventually_nhds] with s hs_int hs_eq hs_eq_nhds
  rw [← hs_eq]
  refine hs_int.congr_of_eventuallyEq ?_
  filter_upwards [hs_eq_nhds] with x hx
  exact hx.symm

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {T t' : ℝ} (ht'_pos : 0 < t')
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s) :
    IsMIntegralCurveOn (chartFlowOrbitLiftRescaled (I := I) Φ p t' v)
      (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T / t') (T / t')) := by
  apply IsMIntegralCurveAt.isMIntegralCurveOn
  intro s₀ hs₀
  exact chartFlowOrbitLiftRescaled_isMIntegralCurveAt_of_mem_Ioo (I := I) g p v
    ht'_pos hΦ_target_Icc hΦ_phase_Ioo hs₀

end IntegralCurveOnIoo

section ProjectionAtOne

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

private lemma isPreconnected_Ioo_real (a b : ℝ) :
    IsPreconnected (Set.Ioo a b) :=
  (convex_Ioo a b).isPreconnected

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rescaled_lift_witness_data
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {T t' : ℝ} (ht'_pos : 0 < t')
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E))
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s) :
    chartFlowOrbitLiftRescaled (I := I) Φ p t' v 0 =
      (⟨p, t' • v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn (chartFlowOrbitLiftRescaled (I := I) Φ p t' v)
      (geodesicVectorFieldChart (I := I) g p)
      (Set.Ioo (-T / t') (T / t')) := by
  refine ⟨?_, ?_⟩
  · exact chartFlowOrbitLiftRescaled_zero (I := I) p v t' hΦ_init
  · exact chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo (I := I) g p v
      ht'_pos hΦ_target_Icc hΦ_phase_Ioo

omit [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {T t' : ℝ} (ht'_pos : 0 < t')
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E))
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s)
    {s : ℝ} (hs : s ∈ Set.Ioo (-T / t') (T / t')) :
    (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s).proj =
      maximalGeodesic (I := I) g p (t' • v) s := by
  classical
  obtain ⟨hF0, hF_int⟩ :=
    rescaled_lift_witness_data (I := I) (g := g) (p := p) (v := v)
      (T := T) (t' := t') ht'_pos (Φ := Φ) hΦ_init hΦ_target_Icc hΦ_phase_Ioo
  set J : Set ℝ := Set.Ioo (-T / t') (T / t') with hJ_def
  have hJ_open : IsOpen J := isOpen_Ioo
  have hJ_conn : IsPreconnected J := isPreconnected_Ioo_real _ _
  have hT_div : 0 < T / t' := by
    have hineq : -T / t' < T / t' := lt_trans hs.1 hs.2
    have : -T < T := by
      have := mul_lt_mul_of_pos_right hineq ht'_pos
      field_simp at this
      linarith
    have hT_pos : 0 < T := by linarith
    exact div_pos hT_pos ht'_pos
  have hT_div_neg : -T / t' < 0 := by
    rw [neg_div]; exact neg_lt_zero.mpr hT_div
  have h0_J : (0 : ℝ) ∈ J := ⟨hT_div_neg, hT_div⟩
  obtain ⟨g_v, hg0, hg_int⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) (g := g)
      (p := p) (v := t' • v)
  obtain ⟨ε, hε, hg_on, hgeo, hg_src⟩ :=
    exists_picardLift_witness_interval (I := I) (g := g) (p := p)
      (v := t' • v) hg0 hg_int
  have hgeo_F : IsGeodesicOnWithInitial (I := I) g
      (fun s => (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s).proj) J p (t' • v) := by
    refine ⟨chartFlowOrbitLiftRescaled (I := I) Φ p t' v, ?_, hF0, hF_int⟩
    intro _; rfl
  have hs_witness : MaximalGeodesicWitness (I := I) g p (t' • v) s :=
    ⟨fun s => (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s).proj,
      J, hJ_open, hJ_conn, h0_J, hs, hgeo_F⟩
  have hs_mem : s ∈ maximalGeodesicInterval (I := I) g p (t' • v) := hs_witness
  rw [maximalGeodesic_of_mem (I := I) hs_mem]
  obtain ⟨J', hJ'_open, hJ'_conn, h0_J', hs_J', hgeo'⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (t' • v) hs_mem
  obtain ⟨f', hproj', hf'_0, hf'_on⟩ := hgeo'
  set K : Set ℝ := J ∩ J' with hK_def
  have hK_open : IsOpen K := hJ_open.inter hJ'_open
  have hK_conn : IsPreconnected K := by
    have hJ_ord : OrdConnected J := hJ_conn.ordConnected
    have hJ'_ord : OrdConnected J' := hJ'_conn.ordConnected
    have hK_ord : OrdConnected K := hJ_ord.inter hJ'_ord
    exact hK_ord.isPreconnected
  have h0_K : (0 : ℝ) ∈ K := ⟨h0_J, h0_J'⟩
  have hs_K : s ∈ K := ⟨hs, hs_J'⟩
  have hF_on_K : IsMIntegralCurveOn (chartFlowOrbitLiftRescaled (I := I) Φ p t' v)
      (geodesicVectorFieldChart (I := I) g p) K :=
    hF_int.mono Set.inter_subset_left
  have hf'_on_K : IsMIntegralCurveOn f'
      (geodesicVectorFieldChart (I := I) g p) K :=
    hf'_on.mono Set.inter_subset_right
  have hF_src_K : ∀ s' ∈ K,
      (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s').proj ∈
        (chartAt H p).source := by
    intro s' hs'_K
    have hs'_J : s' ∈ J := hs'_K.1
    have hts' : t' * s' ∈ Set.Ioo (-T) T :=
      mul_mem_Ioo_of_pos_of_lt ht'_pos hs'_J
    have hΦ_target_s' := hΦ_target_Icc (t' * s') (Set.Ioo_subset_Icc_self hts')
    exact chartFlowOrbitLiftRescaled_proj_mem_chartAt_source (I := I) p v t' s'
      hΦ_target_s'
  have h0_eq : chartFlowOrbitLiftRescaled (I := I) Φ p t' v 0 = f' 0 := by
    rw [hF0, hf'_0]
  have heqOn := isMIntegralCurveOn_eq_of_isPreconnected (I := I) (g := g) (p := p)
    (f₁ := chartFlowOrbitLiftRescaled (I := I) Φ p t' v) (f₂ := f')
    hK_open hK_conn h0_K hF_on_K hf'_on_K hF_src_K h0_eq
  have hF_s_eq : chartFlowOrbitLiftRescaled (I := I) Φ p t' v s = f' s := heqOn hs_K
  have : (chartFlowOrbitLiftRescaled (I := I) Φ p t' v s).proj = (f' s).proj := by
    rw [hF_s_eq]
  rw [this]
  exact hproj' s

omit [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLiftRescaled_proj_at_one
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {T t' : ℝ} (ht'_pos : 0 < t') (ht'_lt : t' < T)
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_init : Φ (((extChartAt I p p, v) : E × E), 0) =
      ((extChartAt I p p, v) : E × E))
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s) :
    (chartFlowOrbitLiftRescaled (I := I) Φ p t' v 1).proj =
      expMap (I := I) g p (show TangentSpace I p from t' • v) := by
  classical
  have h1_in : (1 : ℝ) ∈ Set.Ioo (-T / t') (T / t') := by
    refine ⟨?_, ?_⟩
    · have hT_pos : 0 < T := lt_trans ht'_pos ht'_lt
      have : -T / t' < 0 := by
        rw [neg_div]
        exact neg_lt_zero.mpr (div_pos hT_pos ht'_pos)
      linarith
    · rw [lt_div_iff₀ ht'_pos]
      linarith
  have hproj1 := chartFlowOrbitLiftRescaled_proj_eq_maximalGeodesic_on_Ioo
    (I := I) (g := g) (p := p) (v := v) (T := T) (t' := t') ht'_pos
    (Φ := Φ) hΦ_init hΦ_target_Icc hΦ_phase_Ioo (s := 1) h1_in
  rw [hproj1]
  rfl

end ProjectionAtOne

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
