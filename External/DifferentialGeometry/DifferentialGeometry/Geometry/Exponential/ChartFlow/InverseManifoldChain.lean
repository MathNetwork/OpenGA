import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowToTangentLift
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique



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

section ChartPhaseAtZeroSection

variable [I.Boundaryless]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem eventually_hasDerivAt_chartPhaseVF_at_zero_section
    {g : SmoothRiemannianMetric I M} {α : M} {s₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hα_src : (f s₀).proj ∈ (chartAt H α).source)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) s₀) :
    ∀ᶠ s in 𝓝 s₀,
      HasDerivAt
        (fun s' : ℝ => extChartAt I.tangent
          (⟨α, (0 : E)⟩ : TangentBundle I M) (f s'))
        (chartPhaseVF (I := I) g α
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s))) s := by
  classical
  set q₀ : TangentBundle I M := (⟨α, (0 : E)⟩ : TangentBundle I M) with hq₀_def
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_cont0 : ContinuousAt f s₀ := hf.continuousAt
  have hcomp0 : ContinuousAt (fun s => (f s).proj) s₀ :=
    hπ_cont.continuousAt.comp hf_cont0
  have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hα_nhds : (chartAt H α).source ∈ 𝓝 ((f s₀).proj) :=
    hα_open.mem_nhds hα_src
  have hsrc_nhds : (fun s : ℝ => (f s).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 s₀ :=
    hcomp0.preimage_mem_nhds hα_nhds
  filter_upwards [hf, hsrc_nhds] with s hHas hs_src
  have hf_chsrc : f s ∈ (chartAt (ModelProd H E) q₀).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) α (f s)).mpr hs_src
  have hf_extsrc : f s ∈ (extChartAt I.tangent q₀).source := by
    rw [extChartAt_source]; exact hf_chsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp s (hasMFDerivAt_extChartAt (I := I.tangent) hf_chsrc)
    hHas).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hf_chsrc]
  rw [hq₀_def]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
  congr 1
  trans (geodesicVectorFieldChartFiber (I := I) g α (f s))
  · exact tangentCoordChange_tangent_geodesicVF (I := I) g α (f s) hs_src
  · symm
    rw [extChartAt_tangent_zero_apply_chartFiber (I := I) α hs_src]
    rfl

end ChartPhaseAtZeroSection

section LocalLiftAtsZero

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_local_lift_at
    (g : SmoothRiemannianMetric I M) (α : M)
    {q : TangentBundle I M}
    (hq : q.proj ∈ (chartAt H α).source) (s₀ : ℝ) :
    ∃ g_loc : ℝ → TangentBundle I M,
      g_loc s₀ = q ∧
      IsMIntegralCurveAt g_loc (geodesicVectorFieldChart (I := I) g α) s₀ := by
  classical
  have hsmooth : ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun w : TangentBundle I M =>
        (⟨w, geodesicVectorFieldChart (I := I) g α w⟩ :
          TangentBundle I.tangent (TangentBundle I M))) q :=
    geodesicVectorFieldChart_contMDiffAt (I := I) g α (p₀ := q) hq
  have hsmooth1 : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun w : TangentBundle I M =>
        (⟨w, geodesicVectorFieldChart (I := I) g α w⟩ :
          TangentBundle I.tangent (TangentBundle I M))) q :=
    hsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g α)
      (t₀ := s₀) (x₀ := q) hsmooth1

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma local_lift_eventuallyEq_chartFlowOrbitLift
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    {Φ : (E × E) × ℝ → E × E} {s₀ : ℝ}
    (hΦ_target_s₀ : Φ (((extChartAt I p p, v) : E × E), s₀) ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_chart_phase : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s ∧
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    {g_loc : ℝ → TangentBundle I M}
    (hg_loc_s₀ : g_loc s₀ = chartFlowOrbitLift (I := I) Φ p v s₀)
    (hg_loc_int : IsMIntegralCurveAt g_loc
      (geodesicVectorFieldChart (I := I) g p) s₀) :
    g_loc =ᶠ[𝓝 s₀] chartFlowOrbitLift (I := I) Φ p v := by
  classical
  have hF_s₀_src : (chartFlowOrbitLift (I := I) Φ p v s₀).proj ∈
      (chartAt H p).source :=
    chartFlowOrbitLift_proj_mem_chartAt_source (I := I) p v s₀ hΦ_target_s₀
  have hg_loc_s₀_src : (g_loc s₀).proj ∈ (chartAt H p).source := by
    rw [hg_loc_s₀]; exact hF_s₀_src
  have hd_gloc :=
    eventually_hasDerivAt_chartPhaseVF_at_zero_section (I := I)
      (g := g) (α := p) (s₀ := s₀) (f := g_loc) hg_loc_s₀_src hg_loc_int
  set c₁ : ℝ → E × E := fun τ : ℝ =>
    extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + τ)) with hc₁_def
  set c₂ : ℝ → E × E := fun τ : ℝ =>
    Φ (((extChartAt I p p, v) : E × E), s₀ + τ) with hc₂_def
  set z₀ : E × E := Φ (((extChartAt I p p, v) : E × E), s₀) with hz₀_def
  have hz₀_interior : z₀ ∈
      (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := hΦ_target_s₀
  have hc₂_zero : c₂ 0 = z₀ := by
    change Φ (((extChartAt I p p, v) : E × E), s₀ + 0) =
      Φ (((extChartAt I p p, v) : E × E), s₀)
    rw [add_zero]
  have hc₁_zero : c₁ 0 = z₀ := by
    change extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + 0)) =
      Φ (((extChartAt I p p, v) : E × E), s₀)
    rw [add_zero, hg_loc_s₀]
    unfold chartFlowOrbitLift
    exact extChartAt_tangent_zero_apply_symm (I := I) p hΦ_target_s₀
  have hd_c₂ : ∀ᶠ τ in 𝓝 (0 : ℝ),
      HasDerivAt c₂ (chartPhaseVF (I := I) g p (c₂ τ)) τ ∧
      c₂ τ ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have htranslate : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
      have h1 : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) := h1
      simpa using this
    have hev := htranslate.eventually hΦ_chart_phase
    filter_upwards [hev] with τ hτ
    obtain ⟨hτD, hτT⟩ := hτ
    refine ⟨?_, hτT⟩
    have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add s₀
    have hcomp := hτD.scomp τ h_shift
    simp only [one_smul] at hcomp
    convert hcomp using 1
  have hd_c₁ : ∀ᶠ τ in 𝓝 (0 : ℝ),
      HasDerivAt c₁ (chartPhaseVF (I := I) g p (c₁ τ)) τ ∧
      c₁ τ ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
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
      have hval0 : (g_loc (s₀ + 0)).proj = (g_loc s₀).proj := by
        rw [add_zero]
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
    have htranslate : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
      have h1 : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) := h1
      simpa using this
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
  have hc_eq_in_s : ∀ᶠ s in 𝓝 s₀, c₁ (s - s₀) = c₂ (s - s₀) := htranslate_inv.eventually hc_eq
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hgloc_proj_src : ∀ᶠ s in 𝓝 s₀, (g_loc s).proj ∈ (chartAt H p).source := by
    have hcomp : ContinuousAt (fun s : ℝ => (g_loc s).proj) s₀ :=
      hπ_cont.continuousAt.comp hg_loc_int.continuousAt
    have hp_open : IsOpen (chartAt H p).source := (chartAt H p).open_source
    apply hcomp.preimage_mem_nhds
    rw [show (g_loc s₀).proj = (chartFlowOrbitLift (I := I) Φ p v s₀).proj
      from by rw [hg_loc_s₀]]
    exact hp_open.mem_nhds hF_s₀_src
  have hΦ_target_ev : ∀ᶠ s in 𝓝 s₀,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hΦ_chart_phase] with s hs
    exact hs.2
  filter_upwards [hc_eq_in_s, hgloc_proj_src, hΦ_target_ev] with s hs_c_eq hs_gloc_src hs_orbit_t
  have hs_ext_eq :
      extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc s) =
        Φ (((extChartAt I p p, v) : E × E), s) := by
    have h₁ : c₁ (s - s₀) =
        extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) (g_loc s) := by
      simp [hc₁_def, add_sub_cancel]
    have h₂ : c₂ (s - s₀) = Φ (((extChartAt I p p, v) : E × E), s) := by
      simp [hc₂_def, add_sub_cancel]
    rw [← h₁, hs_c_eq, h₂]
  have h_F_v_eq :
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (Φ (((extChartAt I p p, v) : E × E), s)) =
      chartFlowOrbitLift (I := I) Φ p v s := rfl
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
  rw [← hleft, hs_ext_eq]
  rfl

end LocalLiftAtsZero

section IntegralCurveOnIoo

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLift_isMIntegralCurveAt_of_mem_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) {T : ℝ}
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (-T) T) :
    IsMIntegralCurveAt (chartFlowOrbitLift (I := I) Φ p v)
      (geodesicVectorFieldChart (I := I) g p) s₀ := by
  classical
  have hF_s₀_src : (chartFlowOrbitLift (I := I) Φ p v s₀).proj ∈
      (chartAt H p).source :=
    chartFlowOrbitLift_proj_mem_chartAt_source (I := I) p v s₀
      (hΦ_target_Icc s₀ (Set.Ioo_subset_Icc_self hs₀))
  obtain ⟨g_loc, hg_loc_s₀, hg_loc_int⟩ :=
    exists_local_lift_at (I := I) (g := g) (α := p) (q := chartFlowOrbitLift (I := I) Φ p v s₀)
      hF_s₀_src s₀
  have hΦ_chart_phase : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s ∧
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) := by
    have hIoo_nhds : Set.Ioo (-T) T ∈ 𝓝 s₀ := isOpen_Ioo.mem_nhds hs₀
    filter_upwards [hIoo_nhds] with s hs
    refine ⟨hΦ_phase_Ioo s hs, ?_⟩
    exact hΦ_target_Icc s (Set.Ioo_subset_Icc_self hs)
  have h_eq : g_loc =ᶠ[𝓝 s₀] chartFlowOrbitLift (I := I) Φ p v :=
    local_lift_eventuallyEq_chartFlowOrbitLift (I := I) (g := g) (p := p) (v := v)
      (Φ := Φ) (s₀ := s₀)
      (hΦ_target_Icc s₀ (Set.Ioo_subset_Icc_self hs₀)) hΦ_chart_phase
      hg_loc_s₀ hg_loc_int
  rw [IsMIntegralCurveAt] at hg_loc_int ⊢
  filter_upwards [hg_loc_int, h_eq, h_eq.eventually_nhds] with s hs_int hs_eq hs_eq_nhds
  rw [← hs_eq]
  refine hs_int.congr_of_eventuallyEq ?_
  filter_upwards [hs_eq_nhds] with x hx
  exact hx.symm

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartFlowOrbitLift_isMIntegralCurveOn_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (v : E) {T : ℝ}
    {Φ : (E × E) × ℝ → E × E}
    (hΦ_target_Icc : ∀ s ∈ Set.Icc (-T) T,
      Φ (((extChartAt I p p, v) : E × E), s) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E))
    (hΦ_phase_Ioo : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ (((extChartAt I p p, v) : E × E), s'))
        (chartPhaseVF (I := I) g p
          (Φ (((extChartAt I p p, v) : E × E), s))) s) :
    IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
      (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T) := by
  apply IsMIntegralCurveAt.isMIntegralCurveOn
  intro s₀ hs₀
  exact chartFlowOrbitLift_isMIntegralCurveAt_of_mem_Ioo (I := I) g p v
    hΦ_target_Icc hΦ_phase_Ioo hs₀

end IntegralCurveOnIoo

section HeadlineRD3a

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chartFlowOrbitLift_isMIntegralCurveOn_Ioo_data
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
      (∀ v ∈ Metric.ball (0 : E) ρ,
        IsMIntegralCurveOn (chartFlowOrbitLift (I := I) Φ p v)
          (geodesicVectorFieldChart (I := I) g p) (Set.Ioo (-T) T)) := by
  classical
  obtain ⟨ρ, T, Φ, hρ_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, hF_0,
    _hF_proj, _hF_chartPush, _hF_int⟩ :=
    exists_chartFlowOrbitLift_data_uniform (I := I) (g := g) (p := p)
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, hΦ_init, hΦ_target, hΦ_phase, hF_0, ?_⟩
  intro v hv
  exact chartFlowOrbitLift_isMIntegralCurveOn_Ioo (I := I) g p v
    (hΦ_target v hv) (hΦ_phase v hv)

end HeadlineRD3a

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
