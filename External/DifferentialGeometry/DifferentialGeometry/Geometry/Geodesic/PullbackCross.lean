import DifferentialGeometry.Geometry.Connection.ParallelTransport.PullbackCross

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  [NeZero (Module.finrank ℝ F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem velocity_rep_diffAt
    (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) gamma
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I gamma s :
          ℝ →L[ℝ] TangentSpace I (gamma s)) (1 : ℝ)) t) t := by
  let a : M := gamma t
  let u : ℝ → E := chartCurve (I := I) a gamma
  have hsrc : ∀ᶠ s in nhds t, gamma s ∈ (chartAt H a).source := by
    exact hgamma.continuousAt.preimage_mem_nhds
      ((chartAt H a).open_source.mem_nhds (by simp [a]))
  have hmdiff : ∀ᶠ s in nhds t,
      MDifferentiableAt 𝓘(ℝ, ℝ) I gamma s := by
    have hgamma2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma t :=
      hgamma.of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    have hsmooth : ∀ᶠ s in nhds t,
        ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma s :=
      (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hgamma2
    filter_upwards [hsmooth] with s hs
    exact hs.mdifferentiableAt (by decide)
  have hev :
      chartRepAt (I := I) gamma
          (fun s => (mfderiv 𝓘(ℝ, ℝ) I gamma s :
            ℝ →L[ℝ] TangentSpace I (gamma s)) (1 : ℝ)) t =ᶠ[nhds t]
        deriv u := by
    filter_upwards [hsrc, hmdiff] with s hs hms
    rw [chartRepAt_apply]
    rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := gamma) hms a (t := s) hs]
    rfl
  have hu : ContDiffAt ℝ ∞ u t := by
    have hchart : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s => extChartAt I a (gamma s)) t := by
      exact (contMDiffAt_extChartAt (I := I) (x := a)).comp t hgamma
    exact contMDiffAt_iff_contDiffAt.mp hchart
  have hu2 : ContDiffAt ℝ 2 u t :=
    hu.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hdu : DifferentiableAt ℝ (deriv u) t := by
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ u) t :=
      hu2.fderiv_right (m := 1) (by norm_num)
    have happ : DifferentiableAt ℝ (fun s => fderiv ℝ u s (1 : ℝ)) t :=
      (hfd.clm_apply contDiffAt_const).differentiableAt (by norm_num)
    have heq : (fun s => fderiv ℝ u s (1 : ℝ)) = deriv u := by
      funext s
      exact fderiv_apply_one_eq_deriv
    rw [← heq]
    exact happ
  exact hdu.congr_of_eventuallyEq (by simpa [a, u] using hev)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem geoEq_of_covVel_C2
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma t)
    (hzero :
      covDerivAlong (I := I) g gamma
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I gamma s :
          ℝ →L[ℝ] TangentSpace I (gamma s)) (1 : ℝ)) t = 0) :
    HasGeodesicEquationAt (I := I) g gamma t := by
  classical
  set u : ℝ → E := chartCurve (I := I) (gamma t) gamma with hu_def
  set rep : ℝ → E :=
    chartRepAt (I := I) gamma
      (fun s => (mfderiv 𝓘(ℝ, ℝ) I gamma s :
        ℝ →L[ℝ] TangentSpace I (gamma s)) (1 : ℝ)) t with hrep_def
  have hev_c2 : ∀ᶠ s in nhds t,
      ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma s :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hgamma
  have hev_src : ∀ᶠ s in nhds t,
      gamma s ∈ (chartAt H (gamma t)).source := by
    exact hgamma.continuousAt.preimage_mem_nhds
      ((chartAt H (gamma t)).open_source.mem_nhds
        (mem_chart_source H (gamma t)))
  obtain ⟨U, hU_sub, hU_open, ht_U⟩ :=
    eventually_nhds_iff.mp (hev_c2.and hev_src)
  have hUsub_c2 : ∀ s ∈ U,
      ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma s :=
    fun s hs => (hU_sub s hs).1
  have hUsub_src : ∀ s ∈ U,
      gamma s ∈ (chartAt H (gamma t)).source :=
    fun s hs => (hU_sub s hs).2
  have hU_nhds : U ∈ nhds t := hU_open.mem_nhds ht_U
  have hu_cdiffOn : ContDiffOn ℝ 2 u U := by
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2
        ((extChartAt I (gamma t)) ∘ gamma) U := by
      have hchart : ContMDiffOn I 𝓘(ℝ, E) 2
          (extChartAt I (gamma t)) (chartAt H (gamma t)).source :=
        contMDiffOn_extChartAt (I := I) (n := 2) (x := gamma t)
      have hgammaU : ContMDiffOn 𝓘(ℝ, ℝ) I 2 gamma U :=
        fun s hs => (hUsub_c2 s hs).contMDiffWithinAt
      exact hchart.comp hgammaU (fun s hs => hUsub_src s hs)
    change ContDiffOn ℝ 2 ((extChartAt I (gamma t)) ∘ gamma) U
    exact contMDiffOn_iff_contDiffOn.mp hcomp
  have hderiv_cdiffOn : ContDiffOn ℝ 1 (deriv u) U :=
    hu_cdiffOn.deriv_of_isOpen hU_open (by norm_num)
  have hu_diffAt : DifferentiableAt ℝ u t :=
    (hu_cdiffOn.differentiableOn (by norm_num) t ht_U).differentiableAt hU_nhds
  have hu_hasDerivAt : HasDerivAt u (deriv u t) t := hu_diffAt.hasDerivAt
  have hu_diffOn : DifferentiableOn ℝ u U :=
    hu_cdiffOn.differentiableOn (by norm_num)
  have hu_eventually_hasDerivAt :
      ∀ᶠ s in nhds t, HasDerivAt u (deriv u s) s := by
    filter_upwards [hU_nhds] with s hs
    exact ((hu_diffOn s hs).differentiableAt
      (hU_open.mem_nhds hs)).hasDerivAt
  have hderiv_diffAt : DifferentiableAt ℝ (deriv u) t :=
    (hderiv_cdiffOn.differentiableOn (by norm_num) t ht_U).differentiableAt hU_nhds
  have hderiv_hasDerivAt :
      HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    hderiv_diffAt.hasDerivAt
  have hrep_eqOn : EqOn rep (deriv u) U := by
    intro s hs
    have hs_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma s :=
      (hUsub_c2 s hs).mdifferentiableAt (by decide)
    rw [hrep_def, chartRepAt_apply]
    rw [MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (I := I) (M := M) (γ := gamma) hs_mdiff (gamma t)
      (t := s) (hUsub_src s hs)]
    rfl
  have hrep_eq : rep =ᶠ[nhds t] deriv u :=
    hrep_eqOn.eventuallyEq_of_mem hU_nhds
  have hchart :
      chartCovDerivAlong (I := I) g (gamma t) gamma rep t =
        deriv (deriv u) t +
          chartChristoffelContraction (I := I) g (gamma t)
            (deriv u t) (deriv u t) (extChartAt I (gamma t) (gamma t)) := by
    rw [chartCovDerivAlong_def, hrep_eq.deriv_eq, hrep_eq.eq_of_nhds]
    rfl
  rw [covDerivAlong_eq_zero_iff (I := I) g gamma
    (fun s => (mfderiv 𝓘(ℝ, ℝ) I gamma s :
      ℝ →L[ℝ] TangentSpace I (gamma s)) (1 : ℝ)) t] at hzero
  change chartCovDerivAlong (I := I) g (gamma t) gamma rep t = 0 at hzero
  rw [hchart] at hzero
  exact ⟨deriv u t, deriv (deriv u) t, hu_hasDerivAt,
    hu_eventually_hasDerivAt, hderiv_hasDerivAt, hzero⟩



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem geoEq_mapCrossAt
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t)
    (hgeo : HasGeodesicEquationAt (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) gamma t) :
    HasGeodesicEquationAt (I := J) g (fun s => Phi (gamma s)) t := by
  let delta : ℝ → N := fun s => Phi (gamma s)
  have hdelta : ContMDiffAt 𝓘(ℝ, ℝ) J ∞ delta t :=
    Phi.contMDiff.contMDiffAt.comp t hgamma
  let V : ∀ s, TangentSpace I (gamma s) :=
    fun s => (mfderiv 𝓘(ℝ, ℝ) I gamma s :
      ℝ →L[ℝ] TangentSpace I (gamma s)) (1 : ℝ)
  let W : ∀ s, TangentSpace J (delta s) :=
    fun s => mfderiv I J (Phi : M → N) (gamma s) (V s)
  have hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) gamma V t) t := by
    simpa [V] using velocity_rep_diffAt (I := I) gamma t hgamma
  have hsourceZero : covDerivAlong (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
      gamma V t = 0 := by
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
      gamma t
      (hgamma.of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hgeo
  have hnat := covAlong_natCrossAt
    (I := I) (J := J) g Phi gamma V t hgamma hVdiff
  have htargetZero : covDerivAlong (I := J) g delta W t = 0 := by
    rw [← hnat, hsourceZero, map_zero]
  have hgamma2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma t :=
    hgamma.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hgammaEv : ∀ᶠ s in nhds t,
      ContMDiffAt 𝓘(ℝ, ℝ) I 2 gamma s :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hgamma2
  have hWvel : W =ᶠ[nhds t] fun s =>
      (mfderiv 𝓘(ℝ, ℝ) J delta s : ℝ →L[ℝ] TangentSpace J (delta s)) (1 : ℝ) := by
    filter_upwards [hgammaEv] with s hs
    have hPhi : MDifferentiableAt I J (Phi : M → N) (gamma s) :=
      Phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
    have hgammaAt : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma s :=
      hs.mdifferentiableAt (by decide)
    have hcomp := mfderiv_comp_apply
      (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := J)
      (g := (Phi : M → N)) (f := gamma) (x := s)
      hPhi hgammaAt (1 : ℝ)
    simpa [W, V, delta, Function.comp_def] using hcomp.symm
  have hrep : chartRepAt (I := J) delta W t =ᶠ[nhds t]
      chartRepAt (I := J) delta
        (fun s => (mfderiv 𝓘(ℝ, ℝ) J delta s :
          ℝ →L[ℝ] TangentSpace J (delta s)) (1 : ℝ)) t := by
    filter_upwards [hWvel] with s hs
    rw [chartRepAt_apply, chartRepAt_apply, hs]
  have hcovEq : covDerivAlong (I := J) g delta W t =
      covDerivAlong (I := J) g delta
        (fun s => (mfderiv 𝓘(ℝ, ℝ) J delta s :
          ℝ →L[ℝ] TangentSpace J (delta s)) (1 : ℝ)) t := by
    rw [covDerivAlong_def, covDerivAlong_def,
      chartCovDerivAlong_def, chartCovDerivAlong_def,
      hrep.deriv_eq, hrep.eq_of_nhds]
  have htargetVelZero : covDerivAlong (I := J) g delta
      (fun s => (mfderiv 𝓘(ℝ, ℝ) J delta s :
        ℝ →L[ℝ] TangentSpace J (delta s)) (1 : ℝ)) t = 0 := by
    rw [← hcovEq]
    exact htargetZero
  exact geoEq_of_covVel_C2 (I := J) g delta t
    (hdelta.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) htargetVelZero



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem geoEq_mapCross
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M) (t : ℝ)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hgeo : HasGeodesicEquationAt (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) gamma t) :
    HasGeodesicEquationAt (I := J) g (fun s => Phi (gamma s)) t :=
  geoEq_mapCrossAt (I := I) (J := J) g Phi gamma t
    hgamma.contMDiffAt hgeo



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem geodesic_mapCross
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hgeo : IsGeodesic (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) gamma) :
    IsGeodesic (I := J) g (fun s => Phi (gamma s)) :=
  fun t => geoEq_mapCross (I := I) (J := J) g Phi gamma t hgamma (hgeo t)


omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem geodesicOn_mapCross
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M) (s : Set ℝ)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hgeo : IsGeodesicOn (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) gamma s) :
    IsGeodesicOn (I := J) g (fun t => Phi (gamma t)) s :=
  fun t ht => geoEq_mapCross (I := I) (J := J) g Phi gamma t hgamma (hgeo t ht)



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem geodesicOn_mapLocal
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M) (s : Set ℝ) (hs : IsOpen s)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ gamma s)
    (hgeo : IsGeodesicOn (I := I)
      (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi) gamma s) :
    IsGeodesicOn (I := J) g (fun t => Phi (gamma t)) s :=
  fun t ht => geoEq_mapCrossAt (I := I) (J := J) g Phi gamma t
    (hgamma.contMDiffAt (hs.mem_nhds ht)) (hgeo t ht)

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
