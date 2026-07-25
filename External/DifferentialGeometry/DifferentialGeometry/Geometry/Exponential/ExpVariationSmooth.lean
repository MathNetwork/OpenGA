import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero
import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Geodesic.AffineReparam



noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section DiagExp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





def diagExp
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    TangentBundle I M → M × M :=
  fun u => (u.proj, expMapIntrinsic (I := I) g hEnorm u.proj u.snd)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] in
@[simp] theorem diagExp_apply
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (u : TangentBundle I M) :
    diagExp (I := I) g hEnorm u =
      (u.proj, expMapIntrinsic (I := I) g hEnorm u.proj u.snd) := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] in
@[simp] theorem diagExp_fst
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (u : TangentBundle I M) :
    (diagExp (I := I) g hEnorm u).1 = u.proj := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] in
@[simp] theorem diagExp_snd
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (u : TangentBundle I M) :
    (diagExp (I := I) g hEnorm u).2 =
      expMapIntrinsic (I := I) g hEnorm u.proj u.snd := rfl

end DiagExp

section JointVariationSmooth

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

private def chartVelocityLift (α : M) (Γ : ℝ → M) : ℝ → TangentBundle I M :=
  fun s => (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
    (chartCurve (I := I) α Γ s, deriv (chartCurve (I := I) α Γ) s)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem chartVelocityLift_isMIntegralCurveOn
    [CompleteSpace E] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (α : M) {Γ : ℝ → M} {O : Set ℝ}
    (hO_open : IsOpen O)
    (hΓ_cont : ContinuousOn Γ O)
    (hsrc : ∀ s ∈ O, Γ s ∈ (chartAt H α).source)
    (hgeo : ∀ s ∈ O, HasGeodesicEquationAt (I := I) g Γ s) :
    IsMIntegralCurveOn (chartVelocityLift (I := I) α Γ)
      (geodesicVectorFieldChart (I := I) g α) O := by
  classical
  apply IsMIntegralCurveAt.isMIntegralCurveOn
  intro s₀ hs₀
  set cphase : ℝ → E × E :=
    fun s => (chartCurve (I := I) α Γ s, deriv (chartCurve (I := I) α Γ) s) with hcphase_def
  have hΓ_s₀_src : Γ s₀ ∈ (chartAt H α).source := hsrc s₀ hs₀
  have hev := chartPhase_eventually_of_geodesicOn (I := I) g α hO_open hs₀ hΓ_cont hsrc hgeo
  have hcphase_s₀_interior : cphase s₀ ∈
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) :=
    (hev.self_of_nhds).2
  have hL_s₀_src : (chartVelocityLift (I := I) α Γ s₀).proj ∈ (chartAt H α).source := by
    change ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
      (cphase s₀)).proj ∈ _
    exact chartAt_source_of_extChartAt_tangent_zero_symm (I := I) α hcphase_s₀_interior
  have hsmoothVF : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun u : TangentBundle I M =>
        (⟨u, geodesicVectorFieldChart (I := I) g α u⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (chartVelocityLift (I := I) α Γ s₀) :=
    (geodesicVectorFieldChart_contMDiffAt (I := I) g α
        (p₀ := chartVelocityLift (I := I) α Γ s₀) hL_s₀_src).of_le
      (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  obtain ⟨g_loc, hg_loc_s₀, hg_loc_int⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g α)
      (t₀ := s₀) (x₀ := chartVelocityLift (I := I) α Γ s₀) hsmoothVF
  have hg_loc_s₀_src : (g_loc s₀).proj ∈ (chartAt H α).source := by
    rw [hg_loc_s₀]; exact hL_s₀_src
  have hd_gloc :=
    eventually_hasDerivAt_chartPhaseVF_at_zero_section (I := I)
      (g := g) (α := α) (s₀ := s₀) (f := g_loc) hg_loc_s₀_src hg_loc_int
  set c₁ : ℝ → E × E := fun s =>
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s) with hc₁_def
  set c₂ : ℝ → E × E := cphase with hc₂_def
  set w₀ : E × E := cphase s₀ with hw₀_def
  have hw₀_interior : w₀ ∈
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := hcphase_s₀_interior
  have hc₂_zero : c₂ s₀ = w₀ := rfl
  have hc₁_zero : c₁ s₀ = w₀ := by
    have : c₁ s₀ = extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s₀) := rfl
    rw [this, hg_loc_s₀]
    change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
      ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm (cphase s₀)) = w₀
    rw [extChartAt_tangent_zero_apply_symm (I := I) α hcphase_s₀_interior]
  have hd_c₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ s)) s ∧
      c₂ s ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := hev
  have hd_c₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ s)) s ∧
      c₁ s ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
    have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    have hgloc_proj_src : ∀ᶠ s in 𝓝 s₀, (g_loc s).proj ∈ (chartAt H α).source := by
      have hcomp : ContinuousAt (fun s : ℝ => (g_loc s).proj) s₀ :=
        hπ_cont.continuousAt.comp hg_loc_int.continuousAt
      exact hcomp.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hg_loc_s₀_src)
    filter_upwards [hd_gloc, hgloc_proj_src] with s hder hs_src
    have hpair := extChartAt_tangent_zero_apply_chartFiber (I := I) α (p := g_loc s) hs_src
    refine ⟨hder, ?_, Set.mem_univ _⟩
    change (c₁ s).1 ∈ _
    rw [hc₁_def]; simp only
    rw [hpair]
    change extChartAt I α (g_loc s).proj ∈ _
    have h_extsrc : (g_loc s).proj ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hs_src
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α ((extChartAt I α).map_source h_extsrc)
  have hc_eq : c₁ =ᶠ[𝓝 s₀] c₂ :=
    chartPhaseVF_orbit_uniqueness_at (I := I) (g := g) (q := α)
      (c₁ := c₁) (c₂ := c₂) (z₀ := w₀) (t := s₀) hw₀_interior hc₁_zero hc₂_zero hd_c₁ hd_c₂
  have hgloc_proj_src_nhds : ∀ᶠ s in 𝓝 s₀, (g_loc s).proj ∈ (chartAt H α).source := by
    have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    have hcomp : ContinuousAt (fun s : ℝ => (g_loc s).proj) s₀ :=
      hπ_cont.continuousAt.comp hg_loc_int.continuousAt
    exact hcomp.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hg_loc_s₀_src)
  have hgloc_eq_L : g_loc =ᶠ[𝓝 s₀] chartVelocityLift (I := I) α Γ := by
    filter_upwards [hc_eq, hgloc_proj_src_nhds] with s hs_c hs_src
    have hgloc_chsrc : g_loc s ∈
        (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source :=
      (mem_chartAt_modelProd_zero_source_iff (I := I) α (g_loc s)).mpr hs_src
    have hgloc_extsrc : g_loc s ∈
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
      rw [extChartAt_source]; exact hgloc_chsrc
    have hleft :
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s)) = g_loc s :=
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).left_inv hgloc_extsrc
    change g_loc s = (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm (c₂ s)
    rw [← hs_c]
    change g_loc s = (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s))
    exact hleft.symm
  rw [IsMIntegralCurveAt] at hg_loc_int ⊢
  filter_upwards [hg_loc_int, hgloc_eq_L, hgloc_eq_L.eventually_nhds]
    with s hs_int hs_eq hs_eq_nhds
  rw [← hs_eq]
  refine hs_int.congr_of_eventuallyEq ?_
  filter_upwards [hs_eq_nhds] with x hx
  exact hx.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
private theorem chartVelocityLift_proj
    (α : M) {Γ : ℝ → M} {s : ℝ} (hs : Γ s ∈ (chartAt H α).source) :
    (chartVelocityLift (I := I) α Γ s).proj = Γ s := by
  classical
  have hext_src : Γ s ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hs
  have hmem : (chartCurve (I := I) α Γ s, deriv (chartCurve (I := I) α Γ) s) ∈
      (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hΓ_target : extChartAt I α (Γ s) ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hext_src
    change chartCurve (I := I) α Γ s ∈ _
    rw [chartCurve_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hΓ_target
  change ((extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
    (chartCurve (I := I) α Γ s, deriv (chartCurve (I := I) α Γ) s)).proj = Γ s
  rw [extChartAt_tangent_zero_symm_proj (I := I) α hmem]
  change (extChartAt I α).symm (chartCurve (I := I) α Γ s) = Γ s
  rw [chartCurve_def, (extChartAt I α).left_inv hext_src]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem expMapIntrinsic_eq_chartFlow_proj_residual
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (α : M) (n : ℕ) (_hn : 1 ≤ n)
    (Φ : (E × E) × ℝ → E × E) (ρ T t' : ℝ)
    (hΦ : 0 < ρ ∧ 0 < T ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < t' ∧
      ContDiffOn ℝ (n : ℕ∞)
        (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1)
        (Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        Φ ((z, (0 : ℝ)) : (E × E) × ℝ) = z) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
          (chartPhaseVF (I := I) g α (Φ ((z, s) : (E × E) × ℝ))) s) ∧
      (∀ z ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Icc (-T) T,
        Φ ((z, s) : (E × E) × ℝ) ∈
          (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)))
    (q : M) (hq : q ∈ (chartAt H α).source) (w : TangentSpace I q)
    (hphase : ((extChartAt I α q,
        chartFiberCoord (I := I) α
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q (t'⁻¹ • w))) : E × E)
      ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ) :
    expMapIntrinsic (I := I) g hEnorm q w =
      (extChartAt I α).symm
        (Φ (((extChartAt I α q,
            chartFiberCoord (I := I) α
              (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q (t'⁻¹ • w))) : E × E),
          t') : E × E).1 := by
  classical
  obtain ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, _hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩ := hΦ
  set vq : TangentSpace I q := t'⁻¹ • w with hvq_def
  set vα : E := chartFiberCoord (I := I) α
    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq) with hvα_def
  set z₀ : E × E := ((extChartAt I α q, vα) : E × E) with hz₀_def
  have hz₀_ball : z₀ ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ := hphase
  have hz₀_init : Φ ((z₀, (0 : ℝ)) : (E × E) × ℝ) = z₀ := hΦ_init z₀ hz₀_ball
  have hz₀_ode : ∀ s ∈ Set.Ioo (-T) T,
      HasDerivAt (fun s' : ℝ => Φ ((z₀, s') : (E × E) × ℝ))
        (chartPhaseVF (I := I) g α (Φ ((z₀, s) : (E × E) × ℝ))) s := hΦ_ode z₀ hz₀_ball
  have hz₀_target : ∀ s ∈ Set.Icc (-T) T,
      Φ ((z₀, s) : (E × E) × ℝ) ∈
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := hΦ_target z₀ hz₀_ball
  set F : ℝ → TangentBundle I M := fun s =>
    (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
      (Φ ((z₀, s) : (E × E) × ℝ)) with hF_def
  have hq_extsrc : q ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hq
  have hQq_proj : (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq).proj ∈
      (chartAt H α).source := hq
  have hz₀_eq_chart :
      z₀ = extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq) := by
    rw [extChartAt_tangent_zero_apply_chartFiber (I := I) α hQq_proj]
  have hQq_chsrc : (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq) ∈
      (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) α _).mpr hQq_proj
  have hQq_extsrc : (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) q vq) ∈
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [extChartAt_source]; exact hQq_chsrc
  have hF0 : F 0 = (⟨q, vq⟩ : TangentBundle I M) := by
    rw [hF_def]
    simp only
    rw [hz₀_init, hz₀_eq_chart]
    exact (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).left_inv hQq_extsrc
  have hF_proj_src : ∀ s ∈ Set.Icc (-T) T, (F s).proj ∈ (chartAt H α).source := by
    intro s hs
    rw [hF_def]; simp only
    exact chartAt_source_of_extChartAt_tangent_zero_symm (I := I) α (hz₀_target s hs)
  have hF_proj_eq : ∀ s ∈ Set.Icc (-T) T,
      (F s).proj = (extChartAt I α).symm (Φ ((z₀, s) : (E × E) × ℝ)).1 := by
    intro s hs
    rw [hF_def]; simp only
    exact extChartAt_tangent_zero_symm_proj (I := I) α (hz₀_target s hs)
  have hF_intAt : ∀ s₀ ∈ Set.Ioo (-T) T,
      IsMIntegralCurveAt F (geodesicVectorFieldChart (I := I) g α) s₀ := by
    intro s₀ hs₀
    have hs₀_Icc : s₀ ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self hs₀
    have hFs₀_src : (F s₀).proj ∈ (chartAt H α).source := hF_proj_src s₀ hs₀_Icc
    have hsmoothVF : ContMDiffAt I.tangent I.tangent.tangent 1
        (fun u : TangentBundle I M =>
          (⟨u, geodesicVectorFieldChart (I := I) g α u⟩ :
            TangentBundle I.tangent (TangentBundle I M))) (F s₀) :=
      (geodesicVectorFieldChart_contMDiffAt (I := I) g α (p₀ := F s₀) hFs₀_src).of_le
        (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    obtain ⟨g_loc, hg_loc_s₀, hg_loc_int⟩ :=
      exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
        (I := I.tangent) (M := TangentBundle I M)
        (v := geodesicVectorFieldChart (I := I) g α)
        (t₀ := s₀) (x₀ := F s₀) hsmoothVF
    have hg_loc_s₀_src : (g_loc s₀).proj ∈ (chartAt H α).source := by
      rw [hg_loc_s₀]; exact hFs₀_src
    have hd_gloc :=
      eventually_hasDerivAt_chartPhaseVF_at_zero_section (I := I)
        (g := g) (α := α) (s₀ := s₀) (f := g_loc) hg_loc_s₀_src hg_loc_int
    set c₁ : ℝ → E × E := fun τ : ℝ =>
      extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + τ)) with hc₁_def
    set c₂ : ℝ → E × E := fun τ : ℝ => Φ ((z₀, s₀ + τ) : (E × E) × ℝ) with hc₂_def
    set w₀ : E × E := Φ ((z₀, s₀) : (E × E) × ℝ) with hw₀_def
    have hw₀_interior : w₀ ∈
        (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := hz₀_target s₀ hs₀_Icc
    have hc₂_zero : c₂ 0 = w₀ := by
      change Φ ((z₀, s₀ + 0) : (E × E) × ℝ) = Φ ((z₀, s₀) : (E × E) × ℝ); rw [add_zero]
    have hc₁_zero : c₁ 0 = w₀ := by
      change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc (s₀ + 0)) =
        Φ ((z₀, s₀) : (E × E) × ℝ)
      rw [add_zero, hg_loc_s₀, hF_def]
      simp only
      exact extChartAt_tangent_zero_apply_symm (I := I) α hw₀_interior
    have hd_c₂ : ∀ᶠ τ in 𝓝 (0 : ℝ),
        HasDerivAt c₂ (chartPhaseVF (I := I) g α (c₂ τ)) τ ∧
        c₂ τ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      have hshift_tendsto : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
        have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) :=
          (continuous_const.add continuous_id).continuousAt
        simpa using this
      have hIoo_nhds : Set.Ioo (-T) T ∈ 𝓝 s₀ := isOpen_Ioo.mem_nhds hs₀
      have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), s₀ + τ ∈ Set.Ioo (-T) T :=
        hshift_tendsto hIoo_nhds
      filter_upwards [hev] with τ hτ
      have hτD := hz₀_ode (s₀ + τ) hτ
      have hτT := hz₀_target (s₀ + τ) (Set.Ioo_subset_Icc_self hτ)
      refine ⟨?_, hτT⟩
      have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
        simpa using (hasDerivAt_id τ).const_add s₀
      have hcomp := hτD.scomp τ h_shift
      simpa only [one_smul] using hcomp
    have hd_c₁ : ∀ᶠ τ in 𝓝 (0 : ℝ),
        HasDerivAt c₁ (chartPhaseVF (I := I) g α (c₁ τ)) τ ∧
        c₁ τ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
      have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
        FiberBundle.continuous_proj E (TangentSpace I)
      have hc₁_target : ∀ᶠ τ in 𝓝 (0 : ℝ),
          c₁ τ ∈ (interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) := by
        have hcompcont : ContinuousAt (fun τ : ℝ => (g_loc (s₀ + τ)).proj) 0 := by
          have h_shift : ContinuousAt (fun τ : ℝ => s₀ + τ) 0 :=
            (continuous_const.add continuous_id).continuousAt
          have h_gloc_at : ContinuousAt g_loc (s₀ + 0) := by
            rw [add_zero]; exact hg_loc_int.continuousAt
          exact hπ_cont.continuousAt.comp (h_gloc_at.comp h_shift)
        have hα_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
        have hpre : (fun τ : ℝ => (g_loc (s₀ + τ)).proj) ⁻¹' (chartAt H α).source ∈
            𝓝 (0 : ℝ) := by
          apply hcompcont.preimage_mem_nhds
          rw [show (g_loc (s₀ + 0)).proj = (g_loc s₀).proj from by rw [add_zero]]
          exact hα_open.mem_nhds hg_loc_s₀_src
        filter_upwards [hpre] with τ hτ
        have hpair := extChartAt_tangent_zero_apply_chartFiber (I := I) α (p := g_loc (s₀ + τ)) hτ
        refine ⟨?_, Set.mem_univ _⟩
        show (c₁ τ).1 ∈ _
        rw [hc₁_def]; simp only
        rw [hpair]
        change extChartAt I α (g_loc (s₀ + τ)).proj ∈ _
        have h_extsrc : (g_loc (s₀ + τ)).proj ∈ (extChartAt I α).source := by
          rw [extChartAt_source]; exact hτ
        exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
          (I := I) α ((extChartAt I α).map_source h_extsrc)
      have hshift_tendsto : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 s₀) := by
        have : Tendsto (fun τ : ℝ => s₀ + τ) (𝓝 0) (𝓝 (s₀ + 0)) :=
          (continuous_const.add continuous_id).continuousAt
        simpa using this
      have hd_gloc_shift := hshift_tendsto.eventually hd_gloc
      filter_upwards [hd_gloc_shift, hc₁_target] with τ hτD hτT
      refine ⟨?_, hτT⟩
      have h_shift : HasDerivAt (fun τ : ℝ => s₀ + τ) 1 τ := by
        simpa using (hasDerivAt_id τ).const_add s₀
      have hcomp := hτD.scomp τ h_shift
      simpa only [one_smul] using hcomp
    have hc_eq : c₁ =ᶠ[𝓝 (0 : ℝ)] c₂ :=
      chartPhaseVF_orbit_uniqueness (I := I) (g := g) (α := α)
        (c₁ := c₁) (c₂ := c₂) (z₀ := w₀) hw₀_interior hc₁_zero hc₂_zero hd_c₁ hd_c₂
    have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    have htranslate_inv : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
        (continuous_id.sub continuous_const).continuousAt
      simpa using this
    have hc_eq_in_s : ∀ᶠ s in 𝓝 s₀, c₁ (s - s₀) = c₂ (s - s₀) := htranslate_inv.eventually hc_eq
    have hgloc_proj_src : ∀ᶠ s in 𝓝 s₀, (g_loc s).proj ∈ (chartAt H α).source := by
      have hcomp : ContinuousAt (fun s : ℝ => (g_loc s).proj) s₀ :=
        hπ_cont.continuousAt.comp hg_loc_int.continuousAt
      apply hcomp.preimage_mem_nhds
      exact ((chartAt H α).open_source).mem_nhds hg_loc_s₀_src
    have hgloc_eq_F : g_loc =ᶠ[𝓝 s₀] F := by
      filter_upwards [hc_eq_in_s, hgloc_proj_src] with s hs_c hs_src
      have hext_eq :
          extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s) =
            Φ ((z₀, s) : (E × E) × ℝ) := by
        have h₁ : c₁ (s - s₀) =
            extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s) := by
          rw [hc₁_def]; simp [add_sub_cancel]
        have h₂ : c₂ (s - s₀) = Φ ((z₀, s) : (E × E) × ℝ) := by
          rw [hc₂_def]; simp [add_sub_cancel]
        rw [← h₁, hs_c, h₂]
      have hgloc_chsrc : g_loc s ∈
          (chartAt (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)).source :=
        (mem_chartAt_modelProd_zero_source_iff (I := I) α (g_loc s)).mpr hs_src
      have hgloc_extsrc : g_loc s ∈
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
        rw [extChartAt_source]; exact hgloc_chsrc
      have hleft :
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
            (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (g_loc s)) = g_loc s :=
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).left_inv hgloc_extsrc
      rw [hF_def]; simp only
      rw [← hext_eq, hleft]
    rw [IsMIntegralCurveAt] at hg_loc_int ⊢
    filter_upwards [hg_loc_int, hgloc_eq_F, hgloc_eq_F.eventually_nhds]
      with s hs_int hs_eq hs_eq_nhds
    rw [← hs_eq]
    refine hs_int.congr_of_eventuallyEq ?_
    filter_upwards [hs_eq_nhds] with x hx
    exact hx.symm
  have hF_int : IsMIntegralCurveOn F (geodesicVectorFieldChart (I := I) g α)
      (Set.Ioo (-T) T) :=
    IsMIntegralCurveAt.isMIntegralCurveOn (fun s hs => hF_intAt s hs)
  set γF : ℝ → M := fun s => (F s).proj with hγF_def
  have hγF_cont : ContinuousOn γF (Set.Ioo (-T) T) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hF_int.continuousOn
  have hγF_geo : ∀ s ∈ Set.Ioo (-T) T, HasGeodesicEquationAt (I := I) g γF s := by
    intro s hs
    have hs_Icc : s ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self hs
    have hF_at : IsMIntegralCurveAt F (geodesicVectorFieldChart (I := I) g α) s :=
      hF_int.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hs)
    have hGeoAt : IsGeodesicAt (I := I) g γF s :=
      ⟨α, F, fun _ => rfl, hF_proj_src s hs_Icc, hF_at⟩
    exact hGeoAt.hasGeodesicEquationAt (I := I) g
  set Γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q vq with hΓ_def
  have hΓ_geo : IsGeodesic (I := I) g Γ := intrinsicGeodesic_isGeodesic (I := I) g hEnorm q vq
  have hΓ_cont : Continuous Γ := intrinsicGeodesic_continuous (I := I) g hEnorm q vq
  have hΓ0 : Γ 0 = q := intrinsicGeodesic_zero (I := I) g hEnorm q vq
  set S_Γ : Set ℝ :=
    Set.Ioo (-T) T ∩ (Γ ⁻¹' (chartAt H α).source) with hS_def
  have hS_open : IsOpen S_Γ := by
    rw [hS_def]
    exact isOpen_Ioo.inter (hΓ_cont.isOpen_preimage _ (chartAt H α).open_source)
  have h0_Sopen : (0 : ℝ) ∈ S_Γ := by
    refine ⟨⟨by linarith [hT_pos], hT_pos⟩, ?_⟩
    rw [Set.mem_preimage, hΓ0]; exact hq
  set J₀ : Set ℝ := connectedComponentIn S_Γ 0 with hJ₀_def
  have hJ₀_open : IsOpen J₀ := hS_open.connectedComponentIn
  have hJ₀_conn : IsPreconnected J₀ := isPreconnected_connectedComponentIn
  have h0_J₀ : (0 : ℝ) ∈ J₀ := mem_connectedComponentIn h0_Sopen
  have hJ₀_sub_S : J₀ ⊆ S_Γ := connectedComponentIn_subset S_Γ 0
  have hJ₀_sub_Ioo : J₀ ⊆ Set.Ioo (-T) T := fun s hs => (hJ₀_sub_S hs).1
  have hJ₀_src : ∀ s ∈ J₀, Γ s ∈ (chartAt H α).source := fun s hs => (hJ₀_sub_S hs).2
  have hΓ_geo_S : ∀ s ∈ S_Γ, HasGeodesicEquationAt (I := I) g Γ s :=
    fun s _ => hΓ_geo s
  have hΓ_src_S : ∀ s ∈ S_Γ, Γ s ∈ (chartAt H α).source := fun s hs => hs.2
  have hL_int : IsMIntegralCurveOn (chartVelocityLift (I := I) α Γ)
      (geodesicVectorFieldChart (I := I) g α) S_Γ :=
    chartVelocityLift_isMIntegralCurveOn (I := I) g α hS_open hΓ_cont.continuousOn
      hΓ_src_S hΓ_geo_S
  have hΓ_mdiff0 : MDifferentiableAt 𝓘(ℝ, ℝ) I Γ 0 :=
    ((intrinsicGeodesic_contMDiffOn (I := I) g hEnorm q vq).contMDiffAt
      (Filter.univ_mem)).mdifferentiableAt (by norm_num)
  have hΓv : (mfderiv 𝓘(ℝ, ℝ) I Γ 0 (1 : ℝ) : E) = (vq : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q vq
  have hLΓ0 : chartVelocityLift (I := I) α Γ 0 = (⟨q, vq⟩ : TangentBundle I M) := by
    have hcc_comp : chartCurve (I := I) α Γ = (extChartAt I α) ∘ Γ := by
      funext s; rw [chartCurve_def]; rfl
    have hderiv_fderiv : deriv (chartCurve (I := I) α Γ) 0
        = (fderiv ℝ ((extChartAt I α) ∘ Γ) 0 : ℝ →L[ℝ] E) (1 : ℝ) := by
      rw [hcc_comp]
      exact (fderiv_apply_one_eq_deriv (f := (extChartAt I α) ∘ Γ) (x := (0 : ℝ))).symm
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (γ := Γ) (t := 0) hΓ_mdiff0 α (by rw [hΓ0]; exact hq)
    rw [hΓ0] at hbridge
    have hderiv0 : deriv (chartCurve (I := I) α Γ) 0 =
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ q) vq := by
      rw [hderiv_fderiv, ← hbridge]
      exact congrArg _ hΓv
    have hq_base : q ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hq
    have hfib : ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ q) vq =
        chartFiberCoord (I := I) α (⟨q, vq⟩ : TangentBundle I M) := by
      rw [chartFiberCoord]
      rw [Trivialization.continuousLinearMapAt_apply]
      rw [(trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem hq_base]
    have hcc0 : chartCurve (I := I) α Γ 0 = extChartAt I α q := by
      rw [chartCurve_def, hΓ0]
    have hQq_eq :
        extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
            (⟨q, vq⟩ : TangentBundle I M) =
          (chartCurve (I := I) α Γ 0, deriv (chartCurve (I := I) α Γ) 0) := by
      rw [extChartAt_tangent_zero_apply_chartFiber (I := I) α hq, hcc0, hderiv0, hfib]
    have hQq_extsrc : (⟨q, vq⟩ : TangentBundle I M) ∈
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
      rw [extChartAt_source]
      exact (mem_chartAt_modelProd_zero_source_iff (I := I) α _).mpr hq
    change (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).symm
      (chartCurve (I := I) α Γ 0, deriv (chartCurve (I := I) α Γ) 0) = _
    rw [← hQq_eq]
    exact (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).left_inv hQq_extsrc
  have hF_eq_L : Set.EqOn F (chartVelocityLift (I := I) α Γ) J₀ := by
    have hF_on_J₀ : IsMIntegralCurveOn F (geodesicVectorFieldChart (I := I) g α) J₀ :=
      hF_int.mono hJ₀_sub_Ioo
    have hL_on_J₀ : IsMIntegralCurveOn (chartVelocityLift (I := I) α Γ)
        (geodesicVectorFieldChart (I := I) g α) J₀ :=
      hL_int.mono hJ₀_sub_S
    have hF_src_J₀ : ∀ s ∈ J₀, (F s).proj ∈ (chartAt H α).source :=
      fun s hs => hF_proj_src s (Set.Ioo_subset_Icc_self (hJ₀_sub_Ioo hs))
    have h0_eq : F 0 = chartVelocityLift (I := I) α Γ 0 := by rw [hF0, hLΓ0]
    exact isMIntegralCurveOn_eq_of_isPreconnected (I := I) (g := g) (p := α)
      (f₁ := F) (f₂ := chartVelocityLift (I := I) α Γ)
      hJ₀_open hJ₀_conn h0_J₀ hF_on_J₀ hL_on_J₀ hF_src_J₀ h0_eq
  have hγF_eq_Γ : ∀ s ∈ J₀, γF s = Γ s := by
    intro s hs
    have h := hF_eq_L hs
    rw [hγF_def]; simp only
    rw [h]
    exact chartVelocityLift_proj (I := I) α (hJ₀_src s hs)
  have hIcc_sub_Ioo : Set.Icc (0 : ℝ) t' ⊆ Set.Ioo (-T) T := by
    intro s hs
    refine ⟨by linarith [hs.1, hT_pos], lt_of_le_of_lt hs.2 ht'_Ioo.2⟩
  have hJ₀_relclosed : closure J₀ ∩ S_Γ ⊆ J₀ := by
    rintro s ⟨hs_cl, hs_S⟩
    have hsub₁ : J₀ ⊆ insert s J₀ := Set.subset_insert s J₀
    have hsub₂ : insert s J₀ ⊆ closure J₀ := by
      rw [Set.insert_subset_iff]
      exact ⟨hs_cl, subset_closure⟩
    have hconn : IsPreconnected (insert s J₀) :=
      hJ₀_conn.subset_closure hsub₁ hsub₂
    have hins_sub_S : insert s J₀ ⊆ S_Γ := by
      rw [Set.insert_subset_iff]; exact ⟨hs_S, hJ₀_sub_S⟩
    have h0_ins : (0 : ℝ) ∈ insert s J₀ := Set.mem_insert_of_mem s h0_J₀
    have := hconn.subset_connectedComponentIn h0_ins hins_sub_S
    exact this (Set.mem_insert s J₀)
  have hIcc_sub_Ioo : Set.Icc (0 : ℝ) t' ⊆ Set.Ioo (-T) T := by
    intro s hs
    refine ⟨by linarith [hs.1, hT_pos], lt_of_le_of_lt hs.2 ht'_Ioo.2⟩
  set A : Set ℝ := Set.Icc (0 : ℝ) t' ∩ J₀ with hA_def
  have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t' := ⟨le_refl _, le_of_lt ht'_pos⟩
  have h0_A : (0 : ℝ) ∈ A := ⟨h0_Icc, h0_J₀⟩
  have hbound : Set.Icc (0 : ℝ) t' ∩ closure A ⊆ J₀ := by
    rintro s ⟨hs, hs_cl⟩
    have hs_Ioo : s ∈ Set.Ioo (-T) T := hIcc_sub_Ioo hs
    have hγF_contAt : ContinuousAt γF s :=
      (hγF_cont s hs_Ioo).continuousAt (isOpen_Ioo.mem_nhds hs_Ioo)
    have hΓ_contAt : ContinuousAt Γ s := hΓ_cont.continuousAt
    have hγF_eq_Γ_at_s : γF s = Γ s := by
      have hcont_eq : ContinuousWithinAt (fun r => (γF r, Γ r)) A s :=
        (hγF_contAt.continuousWithinAt.prodMk hΓ_contAt.continuousWithinAt)
      have hclosed_diag : IsClosed {x : M × M | x.1 = x.2} := isClosed_diagonal
      have hev : ∀ᶠ r in 𝓝[A] s, (γF r, Γ r) ∈ {x : M × M | x.1 = x.2} := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact hγF_eq_Γ r hr.2
      have hs_clA : s ∈ closure A := hs_cl
      have hne : (𝓝[A] s).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hs_clA
      exact hclosed_diag.mem_of_tendsto hcont_eq.tendsto hev
    have hγF_s_src : γF s ∈ (chartAt H α).source :=
      hF_proj_src s (Set.Ioo_subset_Icc_self hs_Ioo)
    have hΓ_s_src : Γ s ∈ (chartAt H α).source := by rw [← hγF_eq_Γ_at_s]; exact hγF_s_src
    have hs_S : s ∈ S_Γ := ⟨hs_Ioo, hΓ_s_src⟩
    exact hJ₀_relclosed ⟨closure_mono (hA_def ▸ Set.inter_subset_right) hs_cl, hs_S⟩
  have hcover : Set.Icc (0 : ℝ) t' ⊆ closure A ∪ J₀ᶜ := by
    intro s hs
    by_cases hsJ : s ∈ J₀
    · exact Or.inl (subset_closure ⟨hs, hsJ⟩)
    · exact Or.inr hsJ
  have hdisj : Set.Icc (0 : ℝ) t' ∩ (closure A ∩ J₀ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro s ⟨hs, hs_cl, hs_nJ⟩
    exact hs_nJ (hbound ⟨hs, hs_cl⟩)
  have hsub_u : Set.Icc (0 : ℝ) t' ⊆ closure A := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_Icc)
        (closure A) J₀ᶜ isClosed_closure (hJ₀_open.isClosed_compl) hcover hdisj with hu | hv
    · exact hu
    · exact absurd (hv h0_Icc) (by simp [h0_J₀])
  have hIcc_sub_J₀ : Set.Icc (0 : ℝ) t' ⊆ J₀ :=
    fun s hs => hbound ⟨hs, hsub_u hs⟩
  have ht'_J₀ : t' ∈ J₀ := hIcc_sub_J₀ ⟨le_of_lt ht'_pos, le_refl _⟩
  have ht'_Icc : t' ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self ht'_Ioo
  have hFt'_orbit : (F t').proj = (extChartAt I α).symm (Φ ((z₀, t') : (E × E) × ℝ)).1 :=
    hF_proj_eq t' ht'_Icc
  have hFt'_Γ : (F t').proj = Γ t' := hγF_eq_Γ t' ht'_J₀
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  have hw_eq : w = t' • vq := by
    rw [hvq_def, smul_smul, mul_inv_cancel₀ ht'_ne, one_smul]
  have hΓt'_chain : Γ t' = expMapIntrinsic (I := I) g hEnorm q w := by
    rw [hΓ_def]
    rw [show expMapIntrinsic (I := I) g hEnorm q w =
      intrinsicGeodesic (I := I) g hEnorm q w 1 from rfl]
    rw [hw_eq, intrinsicGeodesic_smul (I := I) g hEnorm q vq t']
  rw [← hΓt'_chain, ← hFt'_Γ, hFt'_orbit, hz₀_def]

end JointVariationSmooth

section CoordMap

def chartFlowVelCoordMap
    (α : M) (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M) (c : ℝ) :
    ℝ × ℝ → E × E :=
  fun p =>
    (extChartAt I α (γ p.2),
      chartFiberCoord (I := I) α
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
          ((p.1 / c) • (V₀ p.2).snd)))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
@[simp] lemma chartFlowVelCoordMap_apply
    (α : M) (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M) (c : ℝ) (p : ℝ × ℝ) :
    chartFlowVelCoordMap (I := I) α γ V₀ c p =
      (extChartAt I α (γ p.2),
        chartFiberCoord (I := I) α
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            ((p.1 / c) • (V₀ p.2).snd))) := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
private lemma rescaledSection_fiberCoord_contMDiffAt
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M) (c : ℝ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (p₀ : ℝ × ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (γ p₀.2)
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            ((p.1 / c) • (V₀ p.2).snd) : TangentBundle I M)).2) p₀ := by
  classical
  set e := trivializationAt E (TangentSpace I) (γ p₀.2) with he_def
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun p : ℝ × ℝ => V₀ p.2) p₀ := (hV₀ p₀.2).comp p₀ contMDiffAt_snd
  have hcoord0 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (V₀ p₀.2).proj (V₀ p.2)).2) p₀ :=
    (Bundle.contMDiffAt_totalSpace.mp hbase).2
  have hbp : (V₀ p₀.2).proj = γ p₀.2 := hproj p₀.2
  rw [hbp] at hcoord0
  have hcoeff : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × ℝ => p.1 / c) p₀ := contMDiffAt_fst.div_const c
  have hsmul : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ =>
        (p.1 / c) •
          (trivializationAt E (TangentSpace I) (γ p₀.2) (V₀ p.2)).2) p₀ :=
    hcoeff.smul hcoord0
  refine hsmul.congr_of_eventuallyEq ?_
  have hbaseSet0 : γ p₀.2 ∈ e.baseSet := by
    rw [he_def, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H (γ p₀.2)
  have hγ_cont : ContinuousAt (fun p : ℝ × ℝ => γ p.2) p₀ :=
    (hγ.continuous.comp continuous_snd).continuousAt
  have hev : ∀ᶠ p in 𝓝 p₀, γ p.2 ∈ e.baseSet :=
    hγ_cont.preimage_mem_nhds (e.open_baseSet.mem_nhds hbaseSet0)
  filter_upwards [hev] with p hp
  have hlin := (e.linear ℝ hp).2 (p.1 / c) ((V₀ p.2).snd)
  have hV₀eq : (V₀ p.2 : TangentBundle I M) =
      TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2) ((V₀ p.2).snd) :=
    TotalSpace.ext (hproj p.2) (by rw [hproj p.2])
  rw [hV₀eq]
  exact hlin

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
private lemma chartFlowVelCoordMap_contMDiffAt
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M) (c : ℝ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (s₀ t₀ : ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × E) ∞
      (chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ c) (s₀, t₀) := by
  classical
  have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ => extChartAt I (γ t₀) (γ p.2)) (s₀, t₀) := by
    have hγcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun p : ℝ × ℝ => γ p.2) (s₀, t₀) := (hγ t₀).comp (s₀, t₀) contMDiffAt_snd
    have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (γ t₀)) (γ t₀) :=
      contMDiffAt_extChartAt (I := I) (x := γ t₀)
    exact hchart.comp (s₀, t₀) hγcomp
  have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ =>
        chartFiberCoord (I := I) (γ t₀)
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            ((p.1 / c) • (V₀ p.2).snd))) (s₀, t₀) := by
    have hfib := rescaledSection_fiberCoord_contMDiffAt (I := I)
      (γ := γ) (V₀ := V₀) (c := c) hV₀ hproj hγ (p₀ := (s₀, t₀))
    simpa [chartFiberCoord] using hfib
  exact hfst.prodMk_space hsnd

end CoordMap

section Headline

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem expMapIntrinsic_variation_contMDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (n : ℕ) (hn : 1 ≤ n) (s₀ t₀ : ℝ)
    (Φ : (E × E) × ℝ → E × E) (ρ T t' : ℝ)
    (hΦ : 0 < ρ ∧ 0 < T ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < t' ∧
      ContDiffOn ℝ (n : ℕ∞)
        (fun z : E × E => (Φ ((z, t') : (E × E) × ℝ)).1)
        (Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        Φ ((z, (0 : ℝ)) : (E × E) × ℝ) = z) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Ioo (-T) T,
        HasDerivAt (fun s' : ℝ => Φ ((z, s') : (E × E) × ℝ))
          (chartPhaseVF (I := I) g (γ t₀) (Φ ((z, s) : (E × E) × ℝ))) s) ∧
      (∀ z ∈ Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ,
        ∀ s ∈ Set.Icc (-T) T,
        Φ ((z, s) : (E × E) × ℝ) ∈
          (interior (extChartAt I (γ t₀)).target) ×ˢ (Set.univ : Set E)))
    (hsmall : ∀ᶠ p in 𝓝 (s₀, t₀),
      γ p.2 ∈ (chartAt H (γ t₀)).source ∧
        chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ t' p ∈
          Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
      (fun p : ℝ × ℝ =>
        expMapIntrinsic (I := I) g hEnorm (γ p.2)
          ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) (s₀, t₀) := by
  classical
  set α : M := γ t₀ with hα_def
  obtain ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩ := hΦ
  set G : E × E → E := fun z => (Φ ((z, t') : (E × E) × ℝ)).1 with hG_def
  set Ψ : ℝ × ℝ → E × E := chartFlowVelCoordMap (I := I) α γ V₀ t' with hΨ_def
  have hΨ_cd : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × E) (∞ : WithTop ℕ∞) Ψ (s₀, t₀) := by
    rw [hΨ_def]
    exact chartFlowVelCoordMap_contMDiffAt (I := I) γ V₀ t' hV₀ hproj hγ s₀ t₀
  have hΨ_cdn : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × E) (n : ℕ∞) Ψ (s₀, t₀) :=
    hΨ_cd.of_le (by exact_mod_cast le_top)
  have hΨ0_mem : Ψ (s₀, t₀) ∈
      Metric.ball ((extChartAt I α (γ t₀), (0 : E)) : E × E) ρ := by
    have := hsmall.self_of_nhds
    rw [hα_def]; exact this.2
  have hG_cdAt : ContDiffAt ℝ (n : ℕ∞) G (Ψ (s₀, t₀)) :=
    hG_cd.contDiffAt (Metric.isOpen_ball.mem_nhds hΨ0_mem)
  have hGΨ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (n : ℕ∞)
      (fun p : ℝ × ℝ => G (Ψ p)) (s₀, t₀) :=
    hG_cdAt.comp_contMDiffAt hΨ_cdn
  have hGΨ0_target : G (Ψ (s₀, t₀)) ∈ (extChartAt I α).target := by
    have ht'_Icc : t' ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self ht'_Ioo
    have hmem := hΦ_target (Ψ (s₀, t₀)) hΨ0_mem t' ht'_Icc
    exact interior_subset hmem.1
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞) (extChartAt I α).symm (G (Ψ (s₀, t₀))) := by
    have hwithin : ContMDiffWithinAt 𝓘(ℝ, E) I (n : ℕ∞) (extChartAt I α).symm
        (extChartAt I α).target (G (Ψ (s₀, t₀))) :=
      contMDiffWithinAt_extChartAt_symm_target (I := I) α hGΨ0_target
    refine hwithin.contMDiffAt ?_
    exact extChartAt_target_mem_nhds' (I := I) hGΨ0_target
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
      (fun p : ℝ × ℝ => (extChartAt I α).symm (G (Ψ p))) (s₀, t₀) :=
    hsymm.comp (s₀, t₀) hGΨ
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hsmall] with p hp
  obtain ⟨hq_src0, hball⟩ := hp
  have hq_src : γ p.2 ∈ (chartAt H α).source := hq_src0
  have hsmul_eq : (t'⁻¹ • (p.1 • (V₀ p.2).snd) : E) = (p.1 / t') • (V₀ p.2).snd := by
    rw [smul_smul, div_eq_mul_inv, mul_comm]
  have hphase_mem :
      ((extChartAt I α (γ p.2),
        chartFiberCoord (I := I) α
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            (t'⁻¹ • (p.1 • (V₀ p.2).snd : E)))) : E × E)
      ∈ Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ := by
    rw [hsmul_eq, hα_def]
    exact hball
  have hbridge := expMapIntrinsic_eq_chartFlow_proj_residual (I := I) g hEnorm α n hn
    Φ ρ T t' ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩
    (γ p.2) hq_src ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))
    hphase_mem
  rw [hbridge]
  change (extChartAt I α).symm
      (Φ (((extChartAt I α (γ p.2),
        chartFiberCoord (I := I) α
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
            (t'⁻¹ • (p.1 • (V₀ p.2).snd : E)))) : E × E), t')).1
    = (extChartAt I α).symm (G (Ψ p))
  rw [hG_def, hΨ_def, chartFlowVelCoordMap_apply, hsmul_eq]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem expMapIntrinsic_variation_contMDiffAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (n : ℕ) (hn : 1 ≤ n) (s₀ t₀ : ℝ) :
    ∃ (ρ t' : ℝ), 0 < ρ ∧ 0 < t' ∧
      ((∀ᶠ p in 𝓝 (s₀, t₀),
        γ p.2 ∈ (chartAt H (γ t₀)).source ∧
          chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ t' p ∈
            Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
        (fun p : ℝ × ℝ =>
          expMapIntrinsic (I := I) g hEnorm (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) (s₀, t₀)) := by
  classical
  obtain ⟨Φ, ρ, T, t', hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode,
    hΦ_target, _hΦ_cd⟩ :=
    exists_chartExp_jointContDiffOn_nat (I := I) g (γ t₀) n hn
  refine ⟨ρ, t', hρ_pos, ht'_pos, fun hsmall => ?_⟩
  exact expMapIntrinsic_variation_contMDiff (I := I) g hEnorm γ V₀ hγ hV₀ hproj n hn
    s₀ t₀ Φ ρ T t'
    ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩ hsmall

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem expMapIntrinsic_variation_smallField_phaseBall
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (t₀ t' ρ : ℝ) (hρ_pos : 0 < ρ) :
    ∃ δ > 0, ∀ s₀ ∈ Metric.ball (0 : ℝ) δ,
      ∀ᶠ p in 𝓝 (s₀, t₀),
        γ p.2 ∈ (chartAt H (γ t₀)).source ∧
          chartFlowVelCoordMap (I := I) (γ t₀) γ V₀ t' p ∈
            Metric.ball ((extChartAt I (γ t₀) (γ t₀), (0 : E)) : E × E) ρ := by
  classical
  set α : M := γ t₀ with hα_def
  have hΨ_cont : ContinuousAt (chartFlowVelCoordMap (I := I) α γ V₀ t') (0, t₀) :=
    (chartFlowVelCoordMap_contMDiffAt (I := I) γ V₀ t' hV₀ hproj hγ 0 t₀).continuousAt
  have hΨ0_eq : chartFlowVelCoordMap (I := I) α γ V₀ t' (0, t₀) =
      ((extChartAt I α α, (0 : E)) : E × E) := by
    rw [chartFlowVelCoordMap_apply]
    refine Prod.ext ?_ ?_
    · simp only
      rw [hα_def]
    · simp only
      have hmk : (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ (0, t₀).2)
            (((0, t₀).1 / t') • (V₀ (0, t₀).2).snd)) =
            (⟨α, (0 : E)⟩ : TangentBundle I M) := by
        refine TotalSpace.ext ?_ ?_
        · simp only [hα_def]
        · simp only [TotalSpace.mk', zero_div, zero_smul]
          rfl
      rw [hmk]
      exact chartFiberCoord_self_zero (I := I) α
  have hcenter_mem : ((extChartAt I α α, (0 : E)) : E × E) ∈
      Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ :=
    Metric.mem_ball_self hρ_pos
  have hsrc0 : γ (0, t₀).2 ∈ (chartAt H α).source := by
    simp only
    rw [hα_def]; exact mem_chart_source H (γ t₀)
  have hU : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀),
      γ p.2 ∈ (chartAt H α).source ∧
        chartFlowVelCoordMap (I := I) α γ V₀ t' p ∈
          Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ := by
    have hball_ev : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀),
        chartFlowVelCoordMap (I := I) α γ V₀ t' p ∈
          Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ := by
      have hmem : Metric.ball ((extChartAt I α α, (0 : E)) : E × E) ρ ∈
          𝓝 (chartFlowVelCoordMap (I := I) α γ V₀ t' (0, t₀)) := by
        rw [hΨ0_eq]; exact Metric.isOpen_ball.mem_nhds hcenter_mem
      exact hΨ_cont.preimage_mem_nhds hmem
    have hsrc_ev : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀),
        γ p.2 ∈ (chartAt H α).source := by
      have hγ_cont : ContinuousAt (fun p : ℝ × ℝ => γ p.2) (0, t₀) :=
        (hγ.continuous.comp continuous_snd).continuousAt
      exact hγ_cont.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hsrc0)
    filter_upwards [hball_ev, hsrc_ev] with p hp_ball hp_src
    exact ⟨hp_src, hp_ball⟩
  obtain ⟨O, hO_sub, hO_open, hO_mem⟩ := eventually_nhds_iff.mp hU
  have hslice_open : IsOpen {s : ℝ | (s, t₀) ∈ O} :=
    hO_open.preimage (by fun_prop : Continuous (fun s : ℝ => (s, t₀)))
  have hslice_mem : (0 : ℝ) ∈ {s : ℝ | (s, t₀) ∈ O} := hO_mem
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hslice_open 0 hslice_mem
  refine ⟨δ, hδ_pos, fun s₀ hs₀ => ?_⟩
  have hs₀O : (s₀, t₀) ∈ O := hδ_sub hs₀
  have hO_nhds : O ∈ 𝓝 (s₀, t₀) := hO_open.mem_nhds hs₀O
  filter_upwards [hO_nhds] with p hp
  exact hO_sub p hp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem expMapIntrinsic_variation_contMDiffAt_of_smallField
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (n : ℕ) (hn : 1 ≤ n) (t₀ : ℝ) :
    ∃ δ > 0, ∀ s₀ ∈ Metric.ball (0 : ℝ) δ,
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
        (fun p : ℝ × ℝ =>
          expMapIntrinsic (I := I) g hEnorm (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))) (s₀, t₀) := by
  classical
  obtain ⟨Φ, ρ, T, t', hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode,
    hΦ_target, _hΦ_cd⟩ :=
    exists_chartExp_jointContDiffOn_nat (I := I) g (γ t₀) n hn
  obtain ⟨δ, hδ_pos, hphase⟩ :=
    expMapIntrinsic_variation_smallField_phaseBall (I := I) γ V₀ hγ hV₀ hproj
      t₀ t' ρ hρ_pos
  refine ⟨δ, hδ_pos, fun s₀ hs₀ => ?_⟩
  exact expMapIntrinsic_variation_contMDiff (I := I) g hEnorm γ V₀ hγ hV₀ hproj n hn
    s₀ t₀ Φ ρ T t'
    ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩
    (hphase s₀ hs₀)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







omit [ConnectedSpace M] in
theorem diagExp_variation_contMDiffAt_of_smallField
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V₀ : ℝ → TangentBundle I M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV₀ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ V₀)
    (hproj : ∀ t, (V₀ t).proj = γ t)
    (n : ℕ) (hn : 1 ≤ n) (t₀ : ℝ) :
    ∃ δ > 0, ∀ s₀ ∈ Metric.ball (0 : ℝ) δ,
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (I.prod I) (n : ℕ∞)
        (fun p : ℝ × ℝ =>
          diagExp (I := I) g hEnorm
            (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ p.2)
              ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2))))
        (s₀, t₀) := by
  classical
  obtain ⟨δ, hδ_pos, hsmooth⟩ :=
    expMapIntrinsic_variation_contMDiffAt_of_smallField (I := I) g hEnorm γ V₀ hγ
      hV₀ hproj n hn t₀
  refine ⟨δ, hδ_pos, fun s₀ hs₀ => ?_⟩
  have hγn : ContMDiff 𝓘(ℝ, ℝ) I (n : ℕ∞) γ :=
    hγ.of_le (by exact_mod_cast le_top)
  have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (n : ℕ∞)
      (fun p : ℝ × ℝ => γ p.2) (s₀, t₀) :=
    (hγn t₀).comp (s₀, t₀) contMDiffAt_snd
  have hsnd := hsmooth s₀ hs₀
  have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (I.prod I) (n : ℕ∞)
      (fun p : ℝ × ℝ =>
        (γ p.2,
          expMapIntrinsic (I := I) g hEnorm (γ p.2)
            ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)))) (s₀, t₀) :=
    hfst.prodMk hsnd
  simpa [diagExp, TotalSpace.mk'] using hpair

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
















omit [ConnectedSpace M] in
theorem diagExp_contMDiffAt_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ContMDiffAt I.tangent (I.prod I) (n : ℕ∞) (diagExp (I := I) g hEnorm)
      (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  classical
  obtain ⟨Φ, ρ, T, t', hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode,
    hΦ_target, _hΦ_cd⟩ :=
    exists_chartExp_jointContDiffOn_nat (I := I) g p n hn
  set u₀ : TangentBundle I M := (⟨p, (0 : E)⟩ : TangentBundle I M) with hu₀_def
  set ctr : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hctr_def
  set Ξ : TangentBundle I M → E × E := fun u => extChartAt I.tangent u₀ u with hΞ_def
  set R : E × E → E × E := fun z => (z.1, t'⁻¹ • z.2) with hR_def
  set G : E × E → E := fun z => (Φ ((z, t') : (E × E) × ℝ)).1 with hG_def
  have hp_src : p ∈ (chartAt H p).source := mem_chart_source H p
  have hΞ0 : Ξ u₀ = ctr := by
    rw [hΞ_def]; simp only
    rw [extChartAt_tangent_zero_apply_chartFiber (I := I) p (p := u₀) (by rw [hu₀_def]; exact hp_src)]
    rw [hu₀_def, chartFiberCoord_self_zero (I := I) p]
  have hRctr : R ctr = ctr := by rw [hR_def, hctr_def]; simp
  have hctr_ball : ctr ∈ Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ := by
    rw [hctr_def]; exact Metric.mem_ball_self hρ_pos

  have hΞ_cd : ContMDiffAt I.tangent 𝓘(ℝ, E × E) (n : ℕ∞) Ξ u₀ := by
    rw [hΞ_def]
    exact (contMDiffAt_extChartAt (I := I.tangent) (x := u₀)).of_le (by exact_mod_cast le_top)

  have hR_cd : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) (n : ℕ∞) R (Ξ u₀) := by
    have hReq : R = ⇑((ContinuousLinearMap.fst ℝ E E).prod
        (t'⁻¹ • ContinuousLinearMap.snd ℝ E E)) := by
      funext z; rw [hR_def]; simp
    have hRcd : ContDiff ℝ (n : ℕ∞) R := by
      rw [hReq]; exact ContinuousLinearMap.contDiff _
    exact hRcd.contMDiff.contMDiffAt
  have hRΞ_cd : ContMDiffAt I.tangent 𝓘(ℝ, E × E) (n : ℕ∞) (fun u => R (Ξ u)) u₀ :=
    hR_cd.comp u₀ hΞ_cd

  have hG_at : ContDiffAt ℝ (n : ℕ∞) G (R (Ξ u₀)) := by
    rw [hΞ0, hRctr]
    exact hG_cd.contDiffAt (Metric.isOpen_ball.mem_nhds hctr_ball)
  have hGRΞ := (hG_at.contMDiffAt).comp u₀ hRΞ_cd

  have hGRu₀_target : G (R (Ξ u₀)) ∈ (extChartAt I p).target := by
    rw [hΞ0, hRctr]
    have ht'_Icc : t' ∈ Set.Icc (-T) T := Set.Ioo_subset_Icc_self ht'_Ioo
    have hmem := hΦ_target ctr hctr_ball t' ht'_Icc
    rw [hG_def]; exact interior_subset hmem.1
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞) (extChartAt I p).symm (G (R (Ξ u₀))) := by
    have hwithin : ContMDiffWithinAt 𝓘(ℝ, E) I (n : ℕ∞) (extChartAt I p).symm
        (extChartAt I p).target (G (R (Ξ u₀))) :=
      contMDiffWithinAt_extChartAt_symm_target (I := I) p hGRu₀_target
    exact hwithin.contMDiffAt (extChartAt_target_mem_nhds' (I := I) hGRu₀_target)
  have hcomp := hsymm.comp u₀ hGRΞ

  have h2 : ContMDiffAt I.tangent I (n : ℕ∞)
      (fun u : TangentBundle I M =>
        expMapIntrinsic (I := I) g hEnorm u.proj u.snd) u₀ := by
    refine hcomp.congr_of_eventuallyEq ?_
    have hsrc_ev : ∀ᶠ u in 𝓝 u₀, u.proj ∈ (chartAt H p).source := by
      have hproj_cont : ContinuousAt (fun u : TangentBundle I M => u.proj) u₀ :=
        (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt
      exact hproj_cont.preimage_mem_nhds
        (by rw [show u₀.proj = p from rfl]; exact (chartAt H p).open_source.mem_nhds hp_src)
    have hball_ev : ∀ᶠ u in 𝓝 u₀,
        R (Ξ u) ∈ Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ := by
      have hcont : ContinuousAt (fun u => R (Ξ u)) u₀ := hRΞ_cd.continuousAt
      have hmem : Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ ∈ 𝓝 (R (Ξ u₀)) := by
        rw [hΞ0, hRctr]; exact Metric.isOpen_ball.mem_nhds hctr_ball
      exact hcont.preimage_mem_nhds hmem
    filter_upwards [hsrc_ev, hball_ev] with u hu_src hu_ball
    change expMapIntrinsic (I := I) g hEnorm u.proj u.snd
        = (extChartAt I p).symm (G (R (Ξ u)))
    have hRΞ : R (Ξ u) =
        ((extChartAt I p u.proj, t'⁻¹ • chartFiberCoord (I := I) p u) : E × E) := by
      rw [hR_def, hΞ_def]; simp only
      rw [extChartAt_tangent_zero_apply_chartFiber (I := I) p (p := u) hu_src]
    have hfs : chartFiberCoord (I := I) p
          (⟨u.proj, t'⁻¹ • u.snd⟩ : TangentBundle I M) = t'⁻¹ • chartFiberCoord (I := I) p u :=
      chartFiberCoord_fiberScale (I := I) p (t'⁻¹) (q := u) hu_src
    have harg : ((extChartAt I p u.proj,
          chartFiberCoord (I := I) p (⟨u.proj, t'⁻¹ • u.snd⟩ : TangentBundle I M)) : E × E)
        = R (Ξ u) := by rw [hRΞ, hfs]
    have hphase : ((extChartAt I p u.proj,
          chartFiberCoord (I := I) p (⟨u.proj, t'⁻¹ • u.snd⟩ : TangentBundle I M)) : E × E)
        ∈ Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ := by
      rw [harg]; exact hu_ball
    have hbridge := expMapIntrinsic_eq_chartFlow_proj_residual (I := I) g hEnorm p n hn
      Φ ρ T t' ⟨hρ_pos, hT_pos, ht'_Ioo, ht'_pos, hG_cd, hΦ_init, hΦ_ode, hΦ_target⟩
      u.proj hu_src u.snd hphase
    rw [hbridge, harg, hG_def]

  have h1 : ContMDiffAt I.tangent I (n : ℕ∞)
      (fun u : TangentBundle I M => u.proj) u₀ := contMDiffAt_proj (TangentSpace I)
  have hpair := h1.prodMk h2
  simpa [diagExp, TotalSpace.mk'] using hpair

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
