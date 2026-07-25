import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Homogeneity
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz



noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
theorem chartCoord_mfderiv_eq_fderiv_at
    {γ : ℝ → M} {α : M} {s : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s)
    (hs : γ s ∈ (chartAt H α).source) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s))
        ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) =
      (fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I)
        (x₀ := α) (x := γ s) hs]
  have hφ_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (γ s) :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hs
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) s =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ s)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ s) :=
    mfderiv_comp s hφ_mdiff hγ
  have hmf_eq_f :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I α) ∘ γ) s =
        fderiv ℝ ((extChartAt I α) ∘ γ) s :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (f := (extChartAt I α) ∘ γ) (x := s)
  have hRHS :
      (fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ) =
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ s)).comp
            (mfderiv 𝓘(ℝ, ℝ) I γ s)) (1 : ℝ) := by
    rw [← hmf_eq_f, hchain]; rfl
  rw [hRHS]; rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
theorem raw_mfderiv_eq_symmL_fderiv_at
    {γ : ℝ → M} {α : M} {s : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s)
    (hs : γ s ∈ (chartAt H α).source) :
    ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ) : E) =
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s))
        ((fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ)) := by
  have hCC := chartCoord_mfderiv_eq_fderiv_at (I := I) (γ := γ) (α := α)
    (s := s) hγ hs
  have hbaseSet : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hs
  have hround :
      ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s))
            ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ))) =
        ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) :=
    (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
      (R := ℝ) hbaseSet _
  calc ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ) : E)
      = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s))
          (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ s))
            ((mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ))) := hround.symm
    _ = ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s))
          ((fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ)) := by rw [hCC]

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem geodesic_speed_constant
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (hγ_C1 : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    ∀ s t : ℝ,
      (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1) =
        (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hγ_mdiff : MDifferentiable 𝓘(ℝ, ℝ) I γ := hγ_C1.mdifferentiable (by norm_num)
  set F : ℝ → ℝ := fun t =>
      (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) with hF_def
  have hF_deriv : ∀ t : ℝ, HasDerivAt F 0 t := by
    intro t
    have hγ_eq : HasGeodesicEquationAt (I := I) g γ t := hγ t
    set α : M := γ t with hα_def
    obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ_eq
    set u : ℝ → E := chartCurve (I := I) α γ with hu_def
    set V : ℝ → E := fun s => deriv u s with hV_def
    have hv' : HasDerivAt u v t := hv
    have hev' : ∀ᶠ s in nhds t, HasDerivAt u (deriv u s) s := hev
    have ha' : HasDerivAt V a t := ha
    have hVt : V t = v := by rw [hV_def]; exact hv'.deriv
    have hut_src : γ t ∈ (chartAt H α).source := by
      rw [hα_def]; exact mem_chart_source H (γ t)
    have hut_ext_src : γ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hut_src
    have hut_target : extChartAt I α (γ t) ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hut_ext_src
    have hmem : u t ∈ interior (extChartAt I α).target := by
      rw [hu_def, chartCurve_def]
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) α hut_target
    have hDV0 :
        a + chartChristoffelContraction (I := I) g α v v (u t) = 0 := by
      rw [hu_def, chartCurve_def]; exact hgeo
    have hcov := chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ V V
      (uPrime := fun _ => v) (Vprime := fun _ => a) (Wprime := fun _ => a)
      (t := t) hv' hmem ha' ha'
    have hval0 :
        (∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) g α l j (u t) *
              chartCoord (E := E) l
                (a + chartChristoffelContraction (I := I) g α v (V t) (u t)) *
              chartCoord (E := E) j (V t))
          + (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) g α i l (u t) *
              chartCoord (E := E) i (V t) *
              chartCoord (E := E) l
                (a + chartChristoffelContraction (I := I) g α v (V t) (u t)))
        = 0 := by
      have hcorr0 :
          a + chartChristoffelContraction (I := I) g α v (V t) (u t) = 0 := by
        rw [hVt]; exact hDV0
      simp only [hcorr0, chartCoord_zero, mul_zero, zero_mul,
        Finset.sum_const_zero, add_zero]
    have hcov0 : HasDerivAt (fun s => chartGramAlongCurve (I := I) g α γ V V s)
        0 t := by
      have := hcov
      rw [hval0] at this
      exact this
    have hF_eq : F =ᶠ[nhds t] (fun s => chartGramAlongCurve (I := I) g α γ V V s) := by
      have hsrc_nhds : {s : ℝ | γ s ∈ (chartAt H α).source} ∈ nhds t := by
        have hcont : Continuous γ := hγ_C1.continuous
        exact hcont.continuousAt.preimage_mem_nhds
          ((chartAt H α).open_source.mem_nhds hut_src)
      filter_upwards [hev', hsrc_nhds] with s hus hsrc
      have hγ_s : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s := hγ_mdiff s
      have hraw := raw_mfderiv_eq_symmL_fderiv_at (I := I) (γ := γ)
        (α := α) (s := s) hγ_s hsrc
      have hfderiv_eq :
          (fderiv ℝ ((extChartAt I α) ∘ γ) s : ℝ →L[ℝ] E) (1 : ℝ) = V s := rfl
      have hmf : (mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ) =
          ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)) (V s) := by
        rw [hraw, hfderiv_eq]
      change F s = chartGramAlongCurve (I := I) g α γ V V s
      have hFs : F s =
          (g.inner (γ s))
            (((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)) (V s))
            (((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s)) (V s)) := by
        rw [hF_def]
        change (g.inner (γ s)) ((mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ))
            ((mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ)) = _
        rw [hmf]
      rw [hFs, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (x := γ s)
        (V s) (V s)]
      rw [chartGramAlongCurve_def]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      have hinv : (extChartAt I α).symm (u s) = γ s := by
        rw [hu_def, chartCurve_def]
        exact (extChartAt I α).left_inv (by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc)
      rw [chartGramOnE_def, hinv]
    exact hcov0.congr_of_eventuallyEq hF_eq
  have hF_diff : Differentiable ℝ F :=
    fun t => (hF_deriv t).differentiableAt
  have hF_deriv_eq : ∀ t : ℝ, deriv F t = 0 :=
    fun t => (hF_deriv t).deriv
  have hF_const : ∀ s t : ℝ, F s = F t :=
    fun s t => is_const_of_deriv_eq_zero hF_diff hF_deriv_eq s t
  exact hF_const

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_speedSq_hasDerivAt_zero
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s)
    (hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) :
    HasDerivAt (fun r =>
      (g.inner (γ r)) (mfderiv 𝓘(ℝ, ℝ) I γ r 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ r 1)) 0 t := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hγ_mdiff_on : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s :=
    hγ_C1.mdifferentiableOn (by norm_num)
  have hγ_mdiffAt : ∀ r ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ r :=
    fun r hr => (hγ_mdiff_on r hr).mdifferentiableAt (hs.mem_nhds hr)
  set F : ℝ → ℝ := fun r =>
      (g.inner (γ r)) (mfderiv 𝓘(ℝ, ℝ) I γ r 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ r 1) with hF_def
  have hγ_eq : HasGeodesicEquationAt (I := I) g γ t := hγ t ht
  set α : M := γ t with hα_def
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ_eq
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  set V : ℝ → E := fun r => deriv u r with hV_def
  have hv' : HasDerivAt u v t := hv
  have ha' : HasDerivAt V a t := ha
  have hVt : V t = v := by rw [hV_def]; exact hv'.deriv
  have hut_src : γ t ∈ (chartAt H α).source := by
    rw [hα_def]; exact mem_chart_source H (γ t)
  have hut_ext_src : γ t ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hut_src
  have hut_target : extChartAt I α (γ t) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hut_ext_src
  have hmem : u t ∈ interior (extChartAt I α).target := by
    rw [hu_def, chartCurve_def]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α hut_target
  have hDV0 : a + chartChristoffelContraction (I := I) g α v v (u t) = 0 := by
    rw [hu_def, chartCurve_def]; exact hgeo
  have hcov := chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ V V
    (uPrime := fun _ => v) (Vprime := fun _ => a) (Wprime := fun _ => a)
    (t := t) hv' hmem ha' ha'
  have hval0 :
      (∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α l j (u t) *
            chartCoord (E := E) l
              (a + chartChristoffelContraction (I := I) g α v (V t) (u t)) *
            chartCoord (E := E) j (V t))
        + (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i l (u t) *
            chartCoord (E := E) i (V t) *
            chartCoord (E := E) l
              (a + chartChristoffelContraction (I := I) g α v (V t) (u t)))
      = 0 := by
    have hcorr0 :
        a + chartChristoffelContraction (I := I) g α v (V t) (u t) = 0 := by
      rw [hVt]; exact hDV0
    simp only [hcorr0, chartCoord_zero, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
  have hcov0 : HasDerivAt (fun r => chartGramAlongCurve (I := I) g α γ V V r)
      0 t := by
    have := hcov
    rw [hval0] at this
    exact this
  have hF_eq : F =ᶠ[nhds t] (fun r => chartGramAlongCurve (I := I) g α γ V V r) := by
    have hsrc_nhds : {r : ℝ | γ r ∈ (chartAt H α).source} ∈ nhds t := by
      have hcont : ContinuousAt γ t :=
        (hγ_C1.continuousOn.continuousAt (hs.mem_nhds ht))
      exact hcont.preimage_mem_nhds
        ((chartAt H α).open_source.mem_nhds hut_src)
    have hs_nhds : s ∈ nhds t := hs.mem_nhds ht
    filter_upwards [hev, hsrc_nhds, hs_nhds] with r hur hsrc hrs
    have hγ_r : MDifferentiableAt 𝓘(ℝ, ℝ) I γ r := hγ_mdiffAt r hrs
    have hraw := raw_mfderiv_eq_symmL_fderiv_at (I := I) (γ := γ)
      (α := α) (s := r) hγ_r hsrc
    have hfderiv_eq :
        (fderiv ℝ ((extChartAt I α) ∘ γ) r : ℝ →L[ℝ] E) (1 : ℝ) = V r := rfl
    have hmf : (mfderiv 𝓘(ℝ, ℝ) I γ r) (1 : ℝ) =
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ r)) (V r) := by
      rw [hraw, hfderiv_eq]
    change F r = chartGramAlongCurve (I := I) g α γ V V r
    have hFr : F r =
        (g.inner (γ r))
          (((trivializationAt E (TangentSpace I) α).symmL ℝ (γ r)) (V r))
          (((trivializationAt E (TangentSpace I) α).symmL ℝ (γ r)) (V r)) := by
      rw [hF_def]
      change (g.inner (γ r)) ((mfderiv 𝓘(ℝ, ℝ) I γ r) (1 : ℝ))
          ((mfderiv 𝓘(ℝ, ℝ) I γ r) (1 : ℝ)) = _
      rw [hmf]
    rw [hFr, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (x := γ r)
      (V r) (V r)]
    rw [chartGramAlongCurve_def]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hinv : (extChartAt I α).symm (u r) = γ r := by
      rw [hu_def, chartCurve_def]
      exact (extChartAt I α).left_inv (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc)
    rw [chartGramOnE_def, hinv]
  exact hcov0.congr_of_eventuallyEq hF_eq

omit [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_speedSq_const
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t₀ t₁ : ℝ}
    (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s)
    (hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s)
    (hIcc : Set.Icc (min t₀ t₁) (max t₀ t₁) ⊆ s) :
    (g.inner (γ t₀)) (mfderiv 𝓘(ℝ, ℝ) I γ t₀ 1) (mfderiv 𝓘(ℝ, ℝ) I γ t₀ 1) =
      (g.inner (γ t₁)) (mfderiv 𝓘(ℝ, ℝ) I γ t₁ 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t₁ 1) := by
  set F : ℝ → ℝ := fun r =>
      (g.inner (γ r)) (mfderiv 𝓘(ℝ, ℝ) I γ r 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ r 1) with hF_def
  rcases eq_or_ne t₀ t₁ with rfl | hne
  · rfl
  set K : Set ℝ := Set.Icc (min t₀ t₁) (max t₀ t₁) with hK_def
  have hmin_lt_max : min t₀ t₁ < max t₀ t₁ := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have hK_convex : Convex ℝ K := convex_Icc _ _
  have hK_uniqueDiff : UniqueDiffOn ℝ K := uniqueDiffOn_Icc hmin_lt_max
  have hF_deriv : ∀ r ∈ K, HasDerivAt F 0 r := fun r hr =>
    isGeodesicOn_speedSq_hasDerivAt_zero (I := I) g hs (hIcc hr) hγ hγ_C1
  have hF_diffOn : DifferentiableOn ℝ F K := fun r hr =>
    (hF_deriv r hr).differentiableAt.differentiableWithinAt
  have hF_fderivWithin : ∀ r ∈ K, fderivWithin ℝ F K r = 0 := by
    intro r hr
    rw [(hF_deriv r hr).hasFDerivAt.hasFDerivWithinAt.fderivWithin
      (hK_uniqueDiff r hr)]
    simp
  have ht₀_K : t₀ ∈ K := ⟨min_le_left _ _, le_max_left _ _⟩
  have ht₁_K : t₁ ∈ K := ⟨min_le_right _ _, le_max_right _ _⟩
  exact hK_convex.is_const_of_fderivWithin_eq_zero hF_diffOn hF_fderivWithin
    ht₀_K ht₁_K

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] in
theorem maximalGeodesic_edist_le_speed_mul_time
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {s t : ℝ}
    (_hs : s ∈ maximalGeodesicInterval (I := I) g p v)
    (_ht : t ∈ maximalGeodesicInterval (I := I) g p v)
    (hst : s ≤ t)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (maximalGeodesic (I := I) g p v) (Set.Icc s t))
    (hSpeedBound : ∀ τ : ℝ,
      ‖mfderiv 𝓘(ℝ, ℝ) I (maximalGeodesic (I := I) g p v) τ (1 : ℝ)‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt ((g.inner p) v v))) :
    riemannianEDist I
        (maximalGeodesic (I := I) g p v s)
        (maximalGeodesic (I := I) g p v t) ≤
      ENNReal.ofReal (Real.sqrt ((g.inner p) v v) * (t - s)) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set γ : ℝ → M := maximalGeodesic (I := I) g p v with hγ_def
  set c : ℝ := Real.sqrt ((g.inner p) v v) with hc_def
  have hc_nonneg : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have h_pathLen_le :
      pathELength I γ s t ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc s t,
            (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ _ => ?_)
      simpa [hγ_def, hc_def] using hSpeedBound τ
    have h_const :
        (∫⁻ _ in Set.Icc s t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) :=
      MeasureTheory.setLIntegral_const (Set.Icc s t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc s t) = ENNReal.ofReal (t - s) :=
      Real.volume_Icc
    have h_mul :
        ENNReal.ofReal c * ENNReal.ofReal (t - s)
          = ENNReal.ofReal (c * (t - s)) :=
      (ENNReal.ofReal_mul hc_nonneg).symm
    calc
      ∫⁻ τ in Set.Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - s) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - s)) := h_mul
  have h_dist_le :
      riemannianEDist I (γ s) (γ t) ≤ pathELength I γ s t :=
    riemannianEDist_le_pathELength (I := I) (γ := γ) (a := s) (b := t)
      hγ_smooth rfl rfl hst
  exact h_dist_le.trans h_pathLen_le

variable [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M] in
theorem maximalGeodesic_cauchySeq_of_tendsto_sup
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {T : ℝ} (_hT : IsLUB (maximalGeodesicInterval (I := I) g p v) T)
    {tₙ : ℕ → ℝ}
    (htₙ_mem : ∀ n, tₙ n ∈ maximalGeodesicInterval (I := I) g p v)
    (htₙ_lim : Tendsto tₙ atTop (𝓝 T))
    (hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I 1 (maximalGeodesic (I := I) g p v))
    (hSpeedBound : ∀ τ : ℝ,
      ‖mfderiv 𝓘(ℝ, ℝ) I (maximalGeodesic (I := I) g p v) τ (1 : ℝ)‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt ((g.inner p) v v))) :
    CauchySeq (fun n => maximalGeodesic (I := I) g p v (tₙ n)) := by
  set γ : ℝ → M := maximalGeodesic (I := I) g p v with hγ_def
  set c : ℝ := Real.sqrt ((g.inner p) v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have htₙ_cauchy : CauchySeq tₙ := htₙ_lim.cauchySeq
  rw [Metric.cauchySeq_iff] at htₙ_cauchy
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀_nn, hδ₀_ofReal_pos, hδ₀_ofReal_lt⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp hε
  have hδ₀_pos : 0 < δ₀ := ENNReal.ofReal_pos.mp hδ₀_ofReal_pos
  have hcc_pos : 0 < c + 1 := by linarith
  set δ : ℝ := δ₀ / (c + 1) with hδ_def
  have hδ_pos : 0 < δ := div_pos hδ₀_pos hcc_pos
  obtain ⟨N, hN⟩ := htₙ_cauchy δ hδ_pos
  refine ⟨N, fun m hm n hn => ?_⟩
  set s : ℝ := min (tₙ m) (tₙ n) with hs_def
  set t : ℝ := max (tₙ m) (tₙ n) with ht_def
  have hst : s ≤ t := min_le_max
  have hs_mem : s ∈ maximalGeodesicInterval (I := I) g p v := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [hs_def, min_eq_left h]; exact htₙ_mem m
    · rw [hs_def, min_eq_right h]; exact htₙ_mem n
  have ht_mem : t ∈ maximalGeodesicInterval (I := I) g p v := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [ht_def, max_eq_right h]; exact htₙ_mem n
    · rw [ht_def, max_eq_left h]; exact htₙ_mem m
  have h_bound :
      riemannianEDist I (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
    have :=
      maximalGeodesic_edist_le_speed_mul_time (I := I) g p v (s := s) (t := t)
        hs_mem ht_mem hst (hγ_smooth.contMDiffOn) hSpeedBound
    simpa [hγ_def, hc_def] using this
  have h_edist_bound :
      edist (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [IsRiemannianManifold.out (I := I) (γ s) (γ t)]
    exact h_bound
  have h_edist_eq :
      edist (γ (tₙ m)) (γ (tₙ n)) = edist (γ s) (γ t) := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · have hs_eq : s = tₙ m := by rw [hs_def, min_eq_left h]
      have ht_eq : t = tₙ n := by rw [ht_def, max_eq_right h]
      rw [hs_eq, ht_eq]
    · have hs_eq : s = tₙ n := by rw [hs_def, min_eq_right h]
      have ht_eq : t = tₙ m := by rw [ht_def, max_eq_left h]
      rw [hs_eq, ht_eq, edist_comm]
  have ht_sub_s : t - s = |tₙ m - tₙ n| := by
    rcases le_total (tₙ m) (tₙ n) with h | h
    · rw [hs_def, ht_def, min_eq_left h, max_eq_right h,
          abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [hs_def, ht_def, min_eq_right h, max_eq_left h,
          abs_of_nonneg (sub_nonneg.mpr h)]
  have h_dist_lt : |tₙ m - tₙ n| < δ := by
    have := hN m hm n hn
    rwa [Real.dist_eq] at this
  have ht_sub_s_nn : 0 ≤ t - s := sub_nonneg.mpr hst
  have h_ct_sub_s_le : c * (t - s) ≤ c * δ := by
    have h_abs_lt : t - s < δ := by rw [ht_sub_s]; exact h_dist_lt
    exact mul_le_mul_of_nonneg_left h_abs_lt.le hc_nn
  have h_cdelta_lt_real : c * δ < δ₀ := by
    rw [hδ_def]
    have hrw : c * (δ₀ / (c + 1)) = δ₀ * (c / (c + 1)) := by ring
    rw [hrw]
    have hfrac_lt_one : c / (c + 1) < 1 := by
      rw [div_lt_one hcc_pos]; linarith
    have := (mul_lt_mul_of_pos_left hfrac_lt_one hδ₀_pos)
    rwa [mul_one] at this
  calc edist (γ (tₙ m)) (γ (tₙ n))
      = edist (γ s) (γ t) := h_edist_eq
    _ ≤ ENNReal.ofReal (c * (t - s)) := h_edist_bound
    _ ≤ ENNReal.ofReal (c * δ) := ENNReal.ofReal_le_ofReal h_ct_sub_s_le
    _ < ENNReal.ofReal δ₀ := by
          rw [ENNReal.ofReal_lt_ofReal_iff hδ₀_pos]
          exact h_cdelta_lt_real
    _ < ε := hδ₀_ofReal_lt

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem maximalGeodesic_limit_exists_tangent_speed_eq
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {T : ℝ} (_hT : IsLUB (maximalGeodesicInterval (I := I) g p v) T)
    {tₙ : ℕ → ℝ}
    (_htₙ_mem : ∀ n, tₙ n ∈ maximalGeodesicInterval (I := I) g p v)
    (_htₙ_lim : Tendsto tₙ atTop (𝓝 T))
    {y : M}
    (_hy : Tendsto (fun n => maximalGeodesic (I := I) g p v (tₙ n))
      atTop (𝓝 y)) :
    ∃ w : TangentSpace I y,
      (g.inner y) w w = (g.inner p) v v := by
  have hfin_pos : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  haveI hNT : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
  obtain ⟨u, hu_ne⟩ : ∃ u : TangentSpace I y, u ≠ 0 :=
    ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
  set r : ℝ := (g.inner p) v v with hr_def
  have hr_nn : 0 ≤ r := by
    rcases eq_or_ne v 0 with hv | hv
    · simp [hr_def, hv]
    · exact (g.pos p v hv).le
  have hc_pos : 0 < (g.inner y) u u := g.pos y u hu_ne
  have hc_nn : 0 ≤ (g.inner y) u u := hc_pos.le
  have hc_ne : (g.inner y) u u ≠ 0 := ne_of_gt hc_pos
  have hratio_nn : 0 ≤ r / (g.inner y) u u := div_nonneg hr_nn hc_nn
  set s : ℝ := Real.sqrt (r / (g.inner y) u u) with hs_def
  refine ⟨s • u, ?_⟩
  have step1 :
      (g.inner y) (s • u) (s • u) = s * s * (g.inner y) u u := by
    rw [map_smul (g.inner y), ContinuousLinearMap.smul_apply,
        map_smul (g.inner y u), smul_eq_mul, smul_eq_mul]
    ring
  have hs_sq : s * s = r / (g.inner y) u u := by
    rw [hs_def]; exact Real.mul_self_sqrt hratio_nn
  rw [step1, hs_sq, div_mul_cancel₀ _ hc_ne]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem curve_edist_le_speed_mul_time
    {γ : ℝ → M} {s t c : ℝ}
    (hc_nonneg : 0 ≤ c) (hst : s ≤ t)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc s t))
    (hSpeedBound : ∀ τ ∈ Set.Icc s t,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c) :
    riemannianEDist I (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
  have h_pathLen_le :
      pathELength I γ s t ≤ ENNReal.ofReal (c * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc s t,
            (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ hτ => ?_)
      exact hSpeedBound τ hτ
    have h_const :
        (∫⁻ _ in Set.Icc s t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) :=
      MeasureTheory.setLIntegral_const (Set.Icc s t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc s t) = ENNReal.ofReal (t - s) :=
      Real.volume_Icc
    have h_mul :
        ENNReal.ofReal c * ENNReal.ofReal (t - s)
          = ENNReal.ofReal (c * (t - s)) :=
      (ENNReal.ofReal_mul hc_nonneg).symm
    calc
      ∫⁻ τ in Set.Icc s t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc s t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc s t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - s) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - s)) := h_mul
  exact (riemannianEDist_le_pathELength (I := I) (γ := γ) (a := s) (b := t)
    hγ_smooth rfl rfl hst).trans h_pathLen_le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem curve_exists_limit_of_bounded_speed
    {γ : ℝ → M} {a b c : ℝ} (hab : a < b) (hc_nonneg : 0 ≤ c)
    (hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Ioo a b))
    (hSpeedBound : ∀ τ ∈ Set.Ioo a b,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c) :
    ∃ y : M, Tendsto γ (nhdsWithin b (Set.Iio b))
      (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace y) := by
  haveI hNB : (nhdsWithin b (Set.Iio b)).NeBot := nhdsLT_neBot b
  suffices hcauchy : Cauchy (Filter.map γ (nhdsWithin b (Set.Iio b))) by
    exact cauchy_map_iff_exists_tendsto.mp hcauchy
  refine EMetric.cauchy_iff.mpr ⟨?_, ?_⟩
  · haveI : (Filter.map γ (nhdsWithin b (Set.Iio b))).NeBot := Filter.map_neBot
    exact Filter.NeBot.ne this
  · intro ε hε
    obtain ⟨δ₀, _hδ₀_nn, hδ₀_ofReal_pos, hδ₀_ofReal_lt⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp hε
    have hδ₀_pos : 0 < δ₀ := ENNReal.ofReal_pos.mp hδ₀_ofReal_pos
    have hcc_pos : 0 < c + 1 := by linarith
    set η : ℝ := min (δ₀ / (c + 1)) ((b - a) / 2) with hη_def
    have hη_le1 : η ≤ δ₀ / (c + 1) := min_le_left _ _
    have hη_le2 : η ≤ (b - a) / 2 := min_le_right _ _
    have hη_pos : 0 < η := lt_min (div_pos hδ₀_pos hcc_pos) (by linarith)
    have hba_gt : a < b - η := by linarith
    have hIoo_mem : Set.Ioo (b - η) b ∈ nhdsWithin b (Set.Iio b) := by
      have : Set.Ioo (b - η) b ∈ 𝓝[<] b :=
        Ioo_mem_nhdsLT (by linarith : b - η < b)
      simpa [nhdsWithin] using this
    refine ⟨γ '' Set.Ioo (b - η) b, Filter.image_mem_map hIoo_mem, ?_⟩
    rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩
    set s : ℝ := min sx sy with hs_def
    set t : ℝ := max sx sy with ht_def
    have hst : s ≤ t := min_le_max
    have hs_lo : b - η < s := lt_min hsx.1 hsy.1
    have ht_hi : t < b := max_lt hsx.2 hsy.2
    have ht_sub_s_lt : t - s < η := by
      have hs_hi : s ≤ t := hst
      have : t - s < b - (b - η) := by
        have hsx_lo : b - η < sx := hsx.1
        have hsy_lo : b - η < sy := hsy.1
        rcases le_total sx sy with h | h
        · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]; linarith [hsy.2]
        · rw [hs_def, ht_def, min_eq_right h, max_eq_left h]; linarith [hsx.2]
      linarith
    have ht_sub_s_nn : 0 ≤ t - s := sub_nonneg.mpr hst
    have hIcc_sub : Set.Icc s t ⊆ Set.Ioo a b := by
      intro τ hτ
      exact ⟨lt_of_lt_of_le (lt_trans hba_gt hs_lo) hτ.1, lt_of_le_of_lt hτ.2 ht_hi⟩
    have hγ_Icc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc s t) :=
      hγ_smooth.mono hIcc_sub
    have h_bound :
        riemannianEDist I (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) :=
      curve_edist_le_speed_mul_time (I := I) (γ := γ) (s := s) (t := t)
        (c := c) hc_nonneg hst hγ_Icc
        (fun τ hτ => hSpeedBound τ (hIcc_sub hτ))
    have h_edist_bound :
        edist (γ s) (γ t) ≤ ENNReal.ofReal (c * (t - s)) := by
      rw [IsRiemannianManifold.out (I := I) (γ s) (γ t)]; exact h_bound
    have h_edist_eq : edist (γ sx) (γ sy) = edist (γ s) (γ t) := by
      rcases le_total sx sy with h | h
      · rw [hs_def, ht_def, min_eq_left h, max_eq_right h]
      · rw [hs_def, ht_def, min_eq_right h, max_eq_left h, edist_comm]
    have h_cts_lt : c * (t - s) < δ₀ := by
      have h1 : c * (t - s) ≤ c * η :=
        mul_le_mul_of_nonneg_left ht_sub_s_lt.le hc_nonneg
      have h2 : c * η < δ₀ := by
        have h2a : c * η ≤ c * (δ₀ / (c + 1)) :=
          mul_le_mul_of_nonneg_left hη_le1 hc_nonneg
        have hrw : c * (δ₀ / (c + 1)) = δ₀ * (c / (c + 1)) := by ring
        have hfrac : c / (c + 1) < 1 := by rw [div_lt_one hcc_pos]; linarith
        have h2b : δ₀ * (c / (c + 1)) < δ₀ := by
          have := mul_lt_mul_of_pos_left hfrac hδ₀_pos
          rwa [mul_one] at this
        calc c * η ≤ c * (δ₀ / (c + 1)) := h2a
          _ = δ₀ * (c / (c + 1)) := hrw
          _ < δ₀ := h2b
      linarith
    rw [h_edist_eq]
    calc edist (γ s) (γ t)
        ≤ ENNReal.ofReal (c * (t - s)) := h_edist_bound
      _ < ENNReal.ofReal δ₀ := by
            rw [ENNReal.ofReal_lt_ofReal_iff hδ₀_pos]; exact h_cts_lt
      _ < ε := hδ₀_ofReal_lt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [CompleteSpace M] in
theorem eventually_mem_nhds_of_tendsto_riemannianEDist
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {α : Type*} {l : Filter α} {f : α → M} {p : M} {s : Set M} (hs : s ∈ 𝓝 p)
    (h : Tendsto (fun a => riemannianEDist I p (f a)) l (𝓝 (0 : ℝ≥0∞))) :
    ∀ᶠ a in l, f a ∈ s := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  obtain ⟨c, c_pos, hc⟩ := setOf_riemannianEDist_lt_subset_nhds' I hs
  have hIio : Set.Iio c ∈ 𝓝 (0 : ℝ≥0∞) := Iio_mem_nhds c_pos
  have hev : ∀ᶠ a in l, riemannianEDist I p (f a) < c := h hIio
  filter_upwards [hev] with a ha
  exact hc ha

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M] in
theorem tendsto_riemannianEDist_of_tendsto_metric_nhds
    {α : Type*} {l : Filter α} {f : α → M} {p : M}
    (h : Tendsto f l (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace p)) :
    Tendsto (fun a => riemannianEDist I p (f a)) l (𝓝 (0 : ℝ≥0∞)) := by
  rw [EMetric.tendsto_nhds] at h
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [h ε hε] with a ha
  rw [IsRiemannianManifold.out (I := I) (f a) p, riemannianEDist_comm] at ha
  exact ha.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [ConnectedSpace M] [CompleteSpace M] in
theorem eventually_mem_nhds_of_tendsto_metric_nhds
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {α : Type*} {l : Filter α} {f : α → M} {p : M} {s : Set M} (hs : s ∈ 𝓝 p)
    (h : Tendsto f l (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace p)) :
    ∀ᶠ a in l, f a ∈ s := by
  exact eventually_mem_nhds_of_tendsto_riemannianEDist (I := I) hs
    (tendsto_riemannianEDist_of_tendsto_metric_nhds (I := I) h)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [ConnectedSpace M] [CompleteSpace M] in
theorem tendsto_nhds_of_tendsto_metric_nhds
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {α : Type*} {l : Filter α} {f : α → M} {p : M}
    (h : Tendsto f l (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace p)) :
    Tendsto f l (𝓝 p) := by
  rw [tendsto_nhds]
  intro s hs hps
  exact eventually_mem_nhds_of_tendsto_metric_nhds (I := I) (hs.mem_nhds hps) h

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry
