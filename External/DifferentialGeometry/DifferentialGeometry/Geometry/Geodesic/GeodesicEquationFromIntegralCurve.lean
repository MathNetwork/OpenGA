import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
import DifferentialGeometry.Geometry.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Geodesic.Uniqueness



noncomputable section

open Bundle Manifold Set Filter Function
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

section ChartPushedDecomp

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartPushLift_fst_eq
    (f : ℝ → TangentBundle I M) (t₀ t : ℝ) :
    (chartPushLift (I := I) f t₀ t).1 =
      extChartAt I (f t₀).proj ((f t).proj) := by
  classical
  unfold chartPushLift
  rw [FiberBundle.extChartAt (E := TangentSpace I) (F := E)
        (HB := H) (IB := I) (f t₀)]
  simp only [PartialEquiv.trans_apply, PartialEquiv.prod_coe]
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartPushLift_fst_eq_chartLocalCurve
    {f : ℝ → TangentBundle I M} {γ : ℝ → M}
    (hproj : ∀ t, (f t).proj = γ t) (t₀ t : ℝ) :
    (chartPushLift (I := I) f t₀ t).1 =
      extChartAt I (γ t₀) (γ t) := by
  rw [chartPushLift_fst_eq (I := I) f t₀ t, hproj t₀, hproj t]

end ChartPushedDecomp

section ChartPushVFSelf

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushVF_self
    (g : SmoothRiemannianMetric I M) (α : M)
    (f : ℝ → TangentBundle I M) (t₀ : ℝ) :
    chartPushVF (I := I) g α f t₀ t₀ =
      geodesicVectorFieldChart (I := I) g α (f t₀) := by
  classical
  unfold chartPushVF
  have hsrc : f t₀ ∈ (extChartAt I.tangent (f t₀)).source :=
    mem_extChartAt_source (I := I.tangent) (f t₀)
  exact tangentCoordChange_self (I := I.tangent) (x := f t₀) (z := f t₀)
    (v := geodesicVectorFieldChart (I := I) g α (f t₀)) hsrc

end ChartPushVFSelf

section ChartCenteredLift

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_chartCenteredLift_at
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (t₀ : ℝ) :
    ∃ f : ℝ → TangentBundle I M,
      f t₀ = (⟨p, v⟩ : TangentBundle I M) ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) t₀ := by
  obtain ⟨f₀, hf₀_init, hf₀⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  refine ⟨f₀ ∘ (· - t₀), ?_, ?_⟩
  · change f₀ (t₀ - t₀) = (⟨p, v⟩ : TangentBundle I M)
    rw [sub_self]; exact hf₀_init
  · have hshift := hf₀.comp_add (-t₀)
    have hfn : (fun s : ℝ => s + -t₀) = (fun s : ℝ => s - t₀) := by
      funext s; ring
    have ht : (0 : ℝ) - -t₀ = t₀ := by ring
    rw [hfn, ht] at hshift
    exact hshift

end ChartCenteredLift

section FirstDerivative

variable [I.Boundaryless] [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasDerivAt_chartLocalCurve_of_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    HasDerivAt (chartLocalCurve (I := I) γ t₀)
      ((geodesicVectorFieldChart (I := I) g (γ t₀) (f t₀) : E × E).1) t₀ := by
  classical
  have hpush := chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := γ t₀) (t₀ := t₀) (f := f) hf
  have hpush_t₀ : HasDerivAt (chartPushLift (I := I) f t₀)
      (chartPushVF (I := I) g (γ t₀) f t₀ t₀) t₀ := hpush.self_of_nhds
  have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ t₀) :=
    hasFDerivAt_fst
  have hfst : HasDerivAt (fun t => (chartPushLift (I := I) f t₀ t).1)
      ((chartPushVF (I := I) g (γ t₀) f t₀ t₀).1) t₀ :=
    hfst_clm.comp_hasDerivAt t₀ hpush_t₀
  rw [chartPushVF_self (I := I) g (γ t₀) f t₀] at hfst
  have hfst_eq : (fun t : ℝ => (chartPushLift (I := I) f t₀ t).1) =
      chartLocalCurve (I := I) γ t₀ := by
    funext t
    rw [chartPushLift_fst_eq_chartLocalCurve (I := I) hproj t₀ t,
      chartLocalCurve_def]
  rw [hfst_eq] at hfst
  exact hfst

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem eventually_hasDerivAt_chartLocalCurve_of_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    ∀ᶠ s in nhds t₀, HasDerivAt (chartLocalCurve (I := I) γ t₀)
      (deriv (chartLocalCurve (I := I) γ t₀) s) s := by
  classical
  have hpush := chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := γ t₀) (t₀ := t₀) (f := f) hf
  filter_upwards [hpush] with s hs
  have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ s) :=
    hasFDerivAt_fst
  have hfst : HasDerivAt (fun t => (chartPushLift (I := I) f t₀ t).1)
      ((chartPushVF (I := I) g (γ t₀) f t₀ s).1) s :=
    hfst_clm.comp_hasDerivAt s hs
  have hfst_eq : (fun t : ℝ => (chartPushLift (I := I) f t₀ t).1) =
      chartLocalCurve (I := I) γ t₀ := by
    funext t
    rw [chartPushLift_fst_eq_chartLocalCurve (I := I) hproj t₀ t,
      chartLocalCurve_def]
  rw [hfst_eq] at hfst
  have hderiv : deriv (chartLocalCurve (I := I) γ t₀) s =
      (chartPushVF (I := I) g (γ t₀) f t₀ s).1 := hfst.deriv
  rw [hderiv]
  exact hfst

end FirstDerivative

section ConditionalHeadline

variable [I.Boundaryless] [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasGeodesicEquationAt_of_chartCentered_of_phase_identity
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀)
    (hphase : ∀ᶠ s in nhds t₀,
      chartPushVF (I := I) g (γ t₀) f t₀ s =
        chartPhaseVF (I := I) g (γ t₀) (chartPushLift (I := I) f t₀ s)) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  classical
  set β : M := γ t₀ with hβ_def
  have hpush := chartPushLift_eventually_hasDerivAt (I := I)
    (g := g) (α := β) (t₀ := t₀) (f := f) hf
  have hphase_push : ∀ᶠ s in nhds t₀, HasDerivAt (chartPushLift (I := I) f t₀)
      (chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ s)) s := by
    filter_upwards [hpush, hphase] with s hs hs_eq
    rw [← hs_eq]; exact hs
  set u : ℝ → E := fun s => (chartPushLift (I := I) f t₀ s).1 with hu_def
  set w : ℝ → E := fun s => (chartPushLift (I := I) f t₀ s).2 with hw_def
  have hu_eq : u = chartLocalCurve (I := I) γ t₀ := by
    funext s
    change (chartPushLift (I := I) f t₀ s).1 = chartLocalCurve (I := I) γ t₀ s
    rw [chartPushLift_fst_eq_chartLocalCurve (I := I) hproj t₀ s,
      chartLocalCurve_def]
  set v : E := w t₀ with hv_def
  set a : E := - chartChristoffelContraction (I := I) g β v v (u t₀) with ha_def
  have hu_t₀ : u t₀ = extChartAt I β (γ t₀) := by
    rw [hu_eq, chartLocalCurve_def]
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · have hphase_t₀ : HasDerivAt (chartPushLift (I := I) f t₀)
        (chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ t₀)) t₀ :=
      hphase_push.self_of_nhds
    have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
        (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ t₀) :=
      hasFDerivAt_fst
    have hu_deriv : HasDerivAt u
        ((chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ t₀)).1) t₀ :=
      hfst_clm.comp_hasDerivAt t₀ hphase_t₀
    have hPhVF : (chartPhaseVF (I := I) g β
        (chartPushLift (I := I) f t₀ t₀)).1 = w t₀ := by
      change (chartPushLift (I := I) f t₀ t₀).2 = w t₀
      rfl
    rw [hPhVF, ← hv_def, hu_eq] at hu_deriv
    exact hu_deriv
  · filter_upwards [hphase_push] with s hs
    have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
        (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ s) :=
      hasFDerivAt_fst
    have hu_deriv : HasDerivAt u
        ((chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ s)).1) s :=
      hfst_clm.comp_hasDerivAt s hs
    have hPhVF : (chartPhaseVF (I := I) g β
        (chartPushLift (I := I) f t₀ s)).1 = w s := by
      change (chartPushLift (I := I) f t₀ s).2 = w s
      rfl
    rw [hPhVF] at hu_deriv
    rw [hu_eq] at hu_deriv
    have : deriv (chartLocalCurve (I := I) γ t₀) s = w s := hu_deriv.deriv
    rw [this]
    exact hu_deriv
  · have heventually_eq : (fun s => deriv (chartLocalCurve (I := I) γ t₀) s) =ᶠ[𝓝 t₀] w := by
      filter_upwards [hphase_push] with s hs
      have hfst_clm : HasFDerivAt (Prod.fst : E × E → E)
          (ContinuousLinearMap.fst ℝ E E) (chartPushLift (I := I) f t₀ s) :=
        hasFDerivAt_fst
      have hu_deriv : HasDerivAt u
          ((chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ s)).1) s :=
        hfst_clm.comp_hasDerivAt s hs
      have hPhVF : (chartPhaseVF (I := I) g β
          (chartPushLift (I := I) f t₀ s)).1 = w s := by
        change (chartPushLift (I := I) f t₀ s).2 = w s
        rfl
      rw [hPhVF] at hu_deriv
      rw [hu_eq] at hu_deriv
      exact hu_deriv.deriv
    have hphase_t₀ : HasDerivAt (chartPushLift (I := I) f t₀)
        (chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ t₀)) t₀ :=
      hphase_push.self_of_nhds
    have hsnd_clm : HasFDerivAt (Prod.snd : E × E → E)
        (ContinuousLinearMap.snd ℝ E E) (chartPushLift (I := I) f t₀ t₀) :=
      hasFDerivAt_snd
    have hw_deriv : HasDerivAt w
        ((chartPhaseVF (I := I) g β (chartPushLift (I := I) f t₀ t₀)).2) t₀ :=
      hsnd_clm.comp_hasDerivAt t₀ hphase_t₀
    have hPhVF_snd : (chartPhaseVF (I := I) g β
        (chartPushLift (I := I) f t₀ t₀)).2 = a := by
      change -chartChristoffelContraction (I := I) g β
          (chartPushLift (I := I) f t₀ t₀).2
          (chartPushLift (I := I) f t₀ t₀).2
          (chartPushLift (I := I) f t₀ t₀).1 = a
      rw [ha_def, hv_def, hw_def, hu_def]
    rw [hPhVF_snd] at hw_deriv
    exact hw_deriv.congr_of_eventuallyEq heventually_eq
  · rw [hu_t₀] at ha_def
    rw [ha_def]
    change -chartChristoffelContraction (I := I) g β v v (extChartAt I β β) +
      chartChristoffelContraction (I := I) g (γ t₀) v v
        (extChartAt I (γ t₀) (γ t₀)) = 0
    rw [← hβ_def]; abel

end ConditionalHeadline

section UnconditionalChartCentered

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable [I.Boundaryless] [CompleteSpace E]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPushVF_eventually_eq_chartPhaseVF_of_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    ∀ᶠ s in nhds t₀,
      chartPushVF (I := I) g (γ t₀) f t₀ s =
        chartPhaseVF (I := I) g (γ t₀) (chartPushLift (I := I) f t₀ s) := by
  classical
  have hft₀_proj : (f t₀).proj = γ t₀ := hproj t₀
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_contAt : ContinuousAt f t₀ := hf.continuousAt
  have hcomp : ContinuousAt (fun s => (f s).proj) t₀ :=
    hπ_cont.continuousAt.comp hf_contAt
  have hα_open : IsOpen (chartAt H (γ t₀)).source :=
    (chartAt H (γ t₀)).open_source
  have hα_mem : γ t₀ ∈ (chartAt H (γ t₀)).source :=
    mem_chart_source H (γ t₀)
  have hα_nhds : (chartAt H (γ t₀)).source ∈ nhds (γ t₀) :=
    hα_open.mem_nhds hα_mem
  have hsrc_nhds : (fun s => (f s).proj) ⁻¹' (chartAt H (γ t₀)).source ∈
      nhds t₀ := by
    apply hcomp.preimage_mem_nhds
    rw [hft₀_proj]
    exact hα_nhds
  filter_upwards [hsrc_nhds] with s hs
  exact chartPushVF_eq_chartPhaseVF_at (I := I) g (γ t₀)
    (f := f) (t₀ := t₀) hft₀_proj s hs

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasGeodesicEquationAt_of_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj : ∀ t, (f t).proj = γ t)
    (hf : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ :=
  hasGeodesicEquationAt_of_chartCentered_of_phase_identity
    (g := g) (γ := γ) (t₀ := t₀) (f := f) hproj hf
    (chartPushVF_eventually_eq_chartPhaseVF_of_chartCentered
      (g := g) (γ := γ) (t₀ := t₀) (f := f) hproj hf)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasGeodesicEquationAt_of_exists_chartCentered_lift
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (h : ∃ f : ℝ → TangentBundle I M,
      (∀ t, (f t).proj = γ t) ∧
      IsMIntegralCurveAt f
        (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  obtain ⟨f, hproj, hf⟩ := h
  exact hasGeodesicEquationAt_of_chartCentered
    (g := g) (γ := γ) (t₀ := t₀) (f := f) hproj hf

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem IsGeodesicAt.hasGeodesicEquationAt_chartCentered
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀)
    (hα : (hγ.choose) = γ t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  obtain ⟨hproj, _hα_src, hf⟩ := hγ.choose_spec.choose_spec
  set f : ℝ → TangentBundle I M := hγ.choose_spec.choose with hf_def
  rw [hα] at hf
  exact hasGeodesicEquationAt_of_chartCentered
    (g := g) (γ := γ) (t₀ := t₀) (f := f) hproj hf

end UnconditionalChartCentered

section CrossVFReduction

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem HasGeodesicEquationAt.congr_of_eventuallyEq_at
    {g : SmoothRiemannianMetric I M} {γ γ' : ℝ → M} {t₀ : ℝ}
    (hγt₀ : γ t₀ = γ' t₀)
    (heq : γ =ᶠ[𝓝 t₀] γ')
    (h : HasGeodesicEquationAt (I := I) g γ' t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  classical
  have hcurve_eq : chartLocalCurve (I := I) γ t₀ =ᶠ[𝓝 t₀]
      chartLocalCurve (I := I) γ' t₀ := by
    filter_upwards [heq] with s hs
    change extChartAt I (γ t₀) (γ s) = extChartAt I (γ' t₀) (γ' s)
    rw [hγt₀, hs]
  obtain ⟨v, a, hv, hev, ha, halg⟩ := h
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · exact hv.congr_of_eventuallyEq hcurve_eq
  · have hev_eq_nhds : ∀ᶠ s in 𝓝 t₀,
        chartLocalCurve (I := I) γ t₀ =ᶠ[𝓝 s] chartLocalCurve (I := I) γ' t₀ :=
      hcurve_eq.eventually_nhds
    filter_upwards [hev, hev_eq_nhds] with s hs hs_nhds
    have hderiv_eq : deriv (chartLocalCurve (I := I) γ t₀) s =
        deriv (chartLocalCurve (I := I) γ' t₀) s :=
      Filter.EventuallyEq.deriv_eq hs_nhds
    rw [hderiv_eq]
    exact hs.congr_of_eventuallyEq hs_nhds
  · have hderiv_eventually : (fun s => deriv (chartLocalCurve (I := I) γ t₀) s) =ᶠ[𝓝 t₀]
        (fun s => deriv (chartLocalCurve (I := I) γ' t₀) s) := by
      filter_upwards [hcurve_eq.eventually_nhds] with s hs_nhds
      exact Filter.EventuallyEq.deriv_eq hs_nhds
    exact ha.congr_of_eventuallyEq hderiv_eventually
  · rw [hγt₀]
    exact halg

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_chartCenteredLift_at_lift_eq
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    {f : ℝ → TangentBundle I M}
    (hproj_t₀ : (f t₀).proj = γ t₀) :
    ∃ f₁ : ℝ → TangentBundle I M,
      f₁ t₀ = f t₀ ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ := by
  obtain ⟨f₁, hf₁_init, hf₁⟩ :=
    exists_chartCenteredLift_at (I := I) g (γ t₀) ((f t₀).snd : E) t₀
  refine ⟨f₁, ?_, hf₁⟩
  rw [hf₁_init, ← hproj_t₀]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem IsGeodesicAt.hasGeodesicEquationAt_of_chartCentered_lift_eventuallyEq
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}
    (_hγ : IsGeodesicAt (I := I) g γ t₀)
    {f₁ : ℝ → TangentBundle I M}
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀)
    (hf₁_proj_t₀ : (f₁ t₀).proj = γ t₀)
    (hcross : γ =ᶠ[𝓝 t₀] projectCurve (I := I) f₁) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  classical
  set γ_alt : ℝ → M := projectCurve (I := I) f₁ with hγ_alt_def
  have hγ_alt_t₀ : γ_alt t₀ = γ t₀ := hf₁_proj_t₀
  have hproj_alt : ∀ t, (f₁ t).proj = γ_alt t := fun t => rfl
  have hf₁_alt : IsMIntegralCurveAt f₁
      (geodesicVectorFieldChart (I := I) g (γ_alt t₀)) t₀ := by
    rw [hγ_alt_t₀]; exact hf₁
  have h_alt : HasGeodesicEquationAt (I := I) g γ_alt t₀ :=
    hasGeodesicEquationAt_of_chartCentered (I := I) (g := g) (γ := γ_alt)
      (t₀ := t₀) (f := f₁) hproj_alt hf₁_alt
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
    (γ := γ) (γ' := γ_alt) (t₀ := t₀) hγ_alt_t₀.symm hcross h_alt

end CrossVFReduction

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
