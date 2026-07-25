import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Exponential.Smoothness.UniformChartFlowBridge
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.Basic
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.OneForm
import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.TwoTensor
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.IntegralCurve.Transform



noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffelContraction_smul_left_right
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α (a • v) (a • w) y
      = (a * a) • chartChristoffelContraction (I := I) g α v w y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_smul]
  congr 1
  calc ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (a • v) * chartCoord (E := E) j (a • w)
      = ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          (a * chartCoord (E := E) i v) * (a * chartCoord (E := E) j w) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [chartCoord_smul, chartCoord_smul]
    _ = (a * a) * ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartFiberCoord_fiberScale
    (α : M) (c : ℝ) {q : TangentBundle I M}
    (hq : q.proj ∈ (chartAt H α).source) :
    chartFiberCoord (I := I) α
        (⟨q.proj, c • q.snd⟩ : TangentBundle I M) =
      c • chartFiberCoord (I := I) α q := by
  classical
  have hbase : q.proj ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hq
  have hcoe : ∀ w : E,
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ q.proj) w =
        (trivializationAt E (TangentSpace I) α
          (⟨q.proj, w⟩ : TangentBundle I M)).2 := by
    intro w
    have hcoe' :=
      (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem (R := ℝ) hbase
    change ((trivializationAt E (TangentSpace I) α).linearMapAt ℝ q.proj) w = _
    exact congrFun hcoe' w
  have hL : chartFiberCoord (I := I) α
      (⟨q.proj, c • q.snd⟩ : TangentBundle I M) =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ q.proj)
        (c • q.snd) := by
    rw [chartFiberCoord_def]; exact (hcoe (c • q.snd)).symm
  have hR : chartFiberCoord (I := I) α q =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ q.proj)
        q.snd := by
    rw [chartFiberCoord_def]; exact (hcoe q.snd).symm
  rw [hL, hR, map_smul]

section ChartCoordBridges

omit [NeZero (Module.finrank ℝ E)] in
theorem hasDerivWithinAt_chartPhaseVF_at_zero_section_within
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ} {t : ℝ}
    (ht : t ∈ S) (hsrc : (f t).proj ∈ (chartAt H α).source)
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) S) :
    HasDerivWithinAt
      (fun s' : ℝ => extChartAt I.tangent
        (⟨α, (0 : E)⟩ : TangentBundle I M) (f s'))
      (chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f t)))
      S t := by
  classical
  set q₀ : TangentBundle I M := (⟨α, (0 : E)⟩ : TangentBundle I M) with hq₀_def
  have hf_chsrc : f t ∈ (chartAt (ModelProd H E) q₀).source :=
    (mem_chartAt_modelProd_zero_source_iff (I := I) α (f t)).mpr hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t
    (hasMFDerivWithinAt_extChartAt (I := I.tangent) hf_chsrc) (hf t ht)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [mfderiv_chartAt_eq_tangentCoordChange hf_chsrc, hq₀_def]
  have hval :
      (tangentCoordChange I.tangent (f t) (⟨α, (0 : E)⟩ : TangentBundle I M) (f t))
          (geodesicVectorFieldChart (I := I) g α (f t)) =
        chartPhaseVF (I := I) g α
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f t)) := by
    trans (geodesicVectorFieldChartFiber (I := I) g α (f t))
    · exact tangentCoordChange_tangent_geodesicVF (I := I) g α (f t) hsrc
    · symm
      rw [extChartAt_tangent_zero_apply_chartFiber (I := I) α hsrc]
      rfl
  apply ContinuousLinearMap.ext_ring
  change (tangentCoordChange I.tangent (f t) (⟨α, (0 : E)⟩ : TangentBundle I M) (f t))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (geodesicVectorFieldChart (I := I) g α (f t))) 1) =
    (ContinuousLinearMap.toSpanSingleton ℝ
      (chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f t)))) 1
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  exact hval

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem hasMFDerivWithinAt_of_chartPhase_at_zero_section
    (α : M) {c : ℝ → TangentBundle I M} {S' : Set ℝ} {s₀ : ℝ} {w : E × E}
    (hcont : ContinuousWithinAt c S' s₀)
    (hsrc : (c s₀).proj ∈ (chartAt H α).source)
    (hd : HasDerivWithinAt
      (fun s => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (c s)) w S' s₀) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I.tangent c S' s₀
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (tangentCoordChange I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (c s₀) (c s₀) w))) := by
  classical
  set q₀ : TangentBundle I M := (⟨α, (0 : E)⟩ : TangentBundle I M) with hq₀
  have hcs0_mem_extq0 : c s₀ ∈ (extChartAt I.tangent q₀).source := by
    rw [extChartAt_source]
    exact (mem_chartAt_modelProd_zero_source_iff (I := I) α (c s₀)).mpr hsrc
  have hcs0_mem_extself : c s₀ ∈ (extChartAt I.tangent (c s₀)).source :=
    mem_extChartAt_source (c s₀)
  have hUnhds : c ⁻¹' (extChartAt I.tangent q₀).source ∈ 𝓝[S'] s₀ :=
    hcont.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds' (I := I.tangent) hcs0_mem_extq0)
  refine ⟨hcont, ?_⟩
  simp only [mfld_simps]
  change HasFDerivWithinAt (fun s => extChartAt I.tangent (c s₀) (c s))
    (ContinuousLinearMap.smulRight 1 (tangentCoordChange I.tangent q₀ (c s₀) (c s₀) w)) S' s₀
  have htrans : HasFDerivWithinAt
      ((extChartAt I.tangent (c s₀)) ∘ (extChartAt I.tangent q₀).symm)
      (tangentCoordChange I.tangent q₀ (c s₀) (c s₀))
      (range I.tangent)
      (extChartAt I.tangent q₀ (c s₀)) :=
    hasFDerivWithinAt_tangentCoordChange (I := I.tangent)
      (x := q₀) (y := c s₀) (z := c s₀)
      ⟨hcs0_mem_extq0, hcs0_mem_extself⟩
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at hd
  have hmaps : MapsTo (fun s => extChartAt I.tangent q₀ (c s))
      (S' ∩ c ⁻¹' (extChartAt I.tangent q₀).source) (range I.tangent) := by
    intro s hs
    exact extChartAt_target_subset_range q₀ ((extChartAt I.tangent q₀).map_source hs.2)
  have hcomp : HasFDerivWithinAt
      (((extChartAt I.tangent (c s₀)) ∘ (extChartAt I.tangent q₀).symm) ∘
        (fun s => extChartAt I.tangent q₀ (c s)))
      ((tangentCoordChange I.tangent q₀ (c s₀) (c s₀)).comp
        (ContinuousLinearMap.smulRight 1 w))
      (S' ∩ c ⁻¹' (extChartAt I.tangent q₀).source) s₀ :=
    HasFDerivWithinAt.comp s₀ htrans (hd.mono Set.inter_subset_left) hmaps
  have hfun_congr : Set.EqOn
      (((extChartAt I.tangent (c s₀)) ∘ (extChartAt I.tangent q₀).symm) ∘
        (fun s => extChartAt I.tangent q₀ (c s)))
      (fun s => extChartAt I.tangent (c s₀) (c s))
      (S' ∩ c ⁻¹' (extChartAt I.tangent q₀).source) := by
    intro s hs
    simp only [Function.comp_apply]
    rw [(extChartAt I.tangent q₀).left_inv hs.2]
  have hself : (fun s => extChartAt I.tangent (c s₀) (c s)) s₀ =
      (((extChartAt I.tangent (c s₀)) ∘ (extChartAt I.tangent q₀).symm) ∘
        (fun s => extChartAt I.tangent q₀ (c s))) s₀ := by
    simp only [Function.comp_apply]
    rw [(extChartAt I.tangent q₀).left_inv hcs0_mem_extq0]
  have hCLM_eq : (tangentCoordChange I.tangent q₀ (c s₀) (c s₀)).comp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w)
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (tangentCoordChange I.tangent q₀ (c s₀) (c s₀) w) := by
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul]
  rw [hCLM_eq] at hcomp
  have hcomp2 : HasFDerivWithinAt (fun s => extChartAt I.tangent (c s₀) (c s))
      (ContinuousLinearMap.smulRight 1 (tangentCoordChange I.tangent q₀ (c s₀) (c s₀) w))
      (S' ∩ c ⁻¹' (extChartAt I.tangent q₀).source) s₀ :=
    hcomp.congr hfun_congr.symm hself
  rwa [hasFDerivWithinAt_inter' hUnhds] at hcomp2

end ChartCoordBridges

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem hasMFDerivWithinAt_of_chartDeriv_self
    {c : ℝ → TangentBundle I M} {S' : Set ℝ} {s₀ : ℝ} {w : E × E}
    (hcont : ContinuousWithinAt c S' s₀)
    (hd : HasDerivWithinAt (fun s => extChartAt I.tangent (c s₀) (c s)) w S' s₀) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I.tangent c S' s₀
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (tangentCoordChange I.tangent (c s₀) (c s₀) (c s₀) w))) := by
  refine ⟨hcont, ?_⟩
  rw [tangentCoordChange_self (I := I.tangent) (mem_extChartAt_source (c s₀))]
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at hd
  simp only [mfld_simps] at hd ⊢
  convert hd using 1

omit [NeZero (Module.finrank ℝ E)] in
theorem geodesicVectorFieldChart_eq_zero_of_notMem_source
    (g : SmoothRiemannianMetric I M) (α : M) (p : TangentBundle I M)
    (hp : p.proj ∉ (chartAt H α).source) :
    geodesicVectorFieldChart (I := I) g α p = 0 := by
  unfold geodesicVectorFieldChart
  have hbase : p ∉ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [← geodesicChartDomain_eq_trivBaseSet]
    exact fun hh => hp (proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) hh)
  rw [Bundle.Trivialization.symm_apply_of_notMem _ hbase]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem extChartAt_tangent_zero_fiberScale (β : M) (c : ℝ) {q : TangentBundle I M}
    (hq : q.proj ∈ (chartAt H β).source) :
    extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)
        (⟨q.proj, c • q.snd⟩ : TangentBundle I M)
      = rescaleChartOrbit (E := E) c
        (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) q) := by
  rw [extChartAt_tangent_zero_apply_chartFiber (I := I) β hq,
      extChartAt_tangent_zero_apply_chartFiber (I := I) β
        (show (⟨q.proj, c • q.snd⟩ : TangentBundle I M).proj ∈ (chartAt H β).source from hq),
      rescaleChartOrbit_apply]
  exact Prod.ext rfl (chartFiberCoord_fiberScale (I := I) β c hq)

omit [NeZero (Module.finrank ℝ E)] in
theorem tangentCoordChange_zero_section_geodesicVF
    (g : SmoothRiemannianMetric I M) (α : M) (q : TangentBundle I M)
    (hq : q.proj ∈ (chartAt H α).source) :
    tangentCoordChange I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q q
      (geodesicVectorFieldChartFiber (I := I) g α q)
      = geodesicVectorFieldChart (I := I) g α q := by
  classical
  have hfwd := tangentCoordChange_tangent_geodesicVF (I := I) g α q hq
  rw [← hfwd, tangentCoordChange_comp (I := I.tangent)]
  · rw [tangentCoordChange_self (I := I.tangent) (mem_extChartAt_source q)]
  · have hself : q ∈ (extChartAt I.tangent q).source := mem_extChartAt_source q
    have hα : q ∈ (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
      rw [extChartAt_source]
      exact (mem_chartAt_modelProd_zero_source_iff (I := I) α q).mpr hq
    exact ⟨⟨hself, hα⟩, hself⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPhaseVF_extChartAt_zero_section
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p)
      = geodesicVectorFieldChartFiber (I := I) g α p := by
  rw [extChartAt_tangent_zero_apply_chartFiber (I := I) α hp]
  rfl

private theorem hasDerivAt_affine (c d s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => c * s + d) c s₀ := by
  have h1 : HasDerivAt (fun s : ℝ => c * s + d) (c * 1) s₀ :=
    ((hasDerivAt_id s₀).const_mul c).add_const d
  simpa using h1

private noncomputable def fiberRescaleCLM (c : ℝ) : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.id ℝ E).prodMap (c • (ContinuousLinearMap.id ℝ E))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem fiberRescaleCLM_apply (c : ℝ) (y : E × E) :
    fiberRescaleCLM (E := E) c y = (y.1, c • y.2) := by
  change ((ContinuousLinearMap.id ℝ E) y.1, (c • (ContinuousLinearMap.id ℝ E)) y.2) = _
  refine Prod.ext rfl ?_
  change (c • (ContinuousLinearMap.id ℝ E)) y.2 = c • y.2
  rw [ContinuousLinearMap.smul_apply]; rfl

omit [NeZero (Module.finrank ℝ E)] in
private theorem inchart_rescaledLift_chartPhase
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) S) (c d : ℝ)
    {s₀ : ℝ} (hs₀ : c * s₀ + d ∈ S)
    (hsrc : (f (c * s₀ + d)).proj ∈ (chartAt H α).source) :
    HasDerivWithinAt
      (fun s : ℝ => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M))
      (chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
          (⟨(f (c * s₀ + d)).proj, c • (f (c * s₀ + d)).snd⟩ : TangentBundle I M)))
      {s : ℝ | c * s + d ∈ S} s₀ := by
  classical
  set a : ℝ := c * s₀ + d with ha_def
  set aff : ℝ → ℝ := fun s => c * s + d with haff_def
  have haff_deriv : HasDerivWithinAt aff c {s : ℝ | c * s + d ∈ S} s₀ :=
    (hasDerivAt_affine c d s₀).hasDerivWithinAt
  have hmaps : MapsTo aff {s : ℝ | c * s + d ∈ S} S := fun s hs => hs
  have haff_s0 : aff s₀ = a := rfl
  have hfwd : HasDerivWithinAt
      (fun s' : ℝ => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s'))
      (chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f a))) S a :=
    hasDerivWithinAt_chartPhaseVF_at_zero_section_within (I := I) g α hs₀ hsrc hf
  have hcomp : HasDerivWithinAt
      ((fun s' : ℝ => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s')) ∘ aff)
      (c • chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f a)))
      {s : ℝ | c * s + d ∈ S} s₀ :=
    HasDerivWithinAt.scomp (x := s₀) (haff_s0 ▸ hfwd) haff_deriv hmaps
  have hcomp2 : HasDerivWithinAt
      (fun s => fiberRescaleCLM (E := E) c
        ((fun s' : ℝ => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s')) (aff s)))
      (fiberRescaleCLM (E := E) c (c • chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f a))))
      {s : ℝ | c * s + d ∈ S} s₀ :=
    (fiberRescaleCLM (E := E) c).hasFDerivAt.comp_hasDerivWithinAt s₀ hcomp
  have hderiv_eq :
      fiberRescaleCLM (E := E) c (c • chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f a)))
      = chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
          (⟨(f a).proj, c • (f a).snd⟩ : TangentBundle I M)) := by
    rw [extChartAt_tangent_zero_fiberScale (I := I) α c hsrc]
    set z : E × E := extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f a) with hz
    rw [fiberRescaleCLM_apply, rescaleChartOrbit_apply]
    have hpvf : chartPhaseVF (I := I) g α z =
        (z.2, -chartChristoffelContraction (I := I) g α z.2 z.2 z.1) := rfl
    have hrhs : chartPhaseVF (I := I) g α (z.1, c • z.2) =
        (c • z.2, -(c * c) • chartChristoffelContraction (I := I) g α z.2 z.2 z.1) := by
      have h0 : chartPhaseVF (I := I) g α (z.1, c • z.2) =
          (c • z.2, -chartChristoffelContraction (I := I) g α (c • z.2) (c • z.2) z.1) := rfl
      rw [h0]
      refine Prod.ext rfl ?_
      have hΓ : chartChristoffelContraction (I := I) g α (c • z.2) (c • z.2) z.1 =
          (c * c) • chartChristoffelContraction (I := I) g α z.2 z.2 z.1 :=
        chartChristoffelContraction_smul_left_right (I := I) g α c z.2 z.2 z.1
      change -chartChristoffelContraction (I := I) g α (c • z.2) (c • z.2) z.1 =
          -(c * c) • chartChristoffelContraction (I := I) g α z.2 z.2 z.1
      rw [hΓ, neg_smul]
    rw [hrhs, hpvf]
    simp only [Prod.smul_mk, smul_neg, smul_smul]
    refine Prod.ext rfl ?_
    rw [neg_smul]
  rw [hderiv_eq] at hcomp2
  have hf_cont : ContinuousWithinAt (fun s => f (aff s)) {s : ℝ | c * s + d ∈ S} s₀ :=
    ((haff_s0 ▸ hf.continuousWithinAt hs₀ :
      ContinuousWithinAt f S (aff s₀))).comp haff_deriv.continuousWithinAt hmaps
  have hproj_cont : ContinuousWithinAt (fun s => (f (aff s)).proj)
      {s : ℝ | c * s + d ∈ S} s₀ :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousWithinAt.comp hf_cont
      (mapsTo_univ _ _)
  have hUnhds : (fun s => (f (aff s)).proj) ⁻¹' (chartAt H α).source ∈
      𝓝[{s : ℝ | c * s + d ∈ S}] s₀ := by
    apply hproj_cont.preimage_mem_nhdsWithin
    refine (chartAt H α).open_source.mem_nhds ?_
    show (f (aff s₀)).proj ∈ (chartAt H α).source
    rw [haff_s0]; exact hsrc
  refine HasDerivWithinAt.congr_of_eventuallyEq hcomp2 ?_ ?_
  · filter_upwards [hUnhds] with s hs
    have hssrc : (f (aff s)).proj ∈ (chartAt H α).source := hs
    change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
          (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M)
      = fiberRescaleCLM (E := E) c
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f (aff s)))
    rw [extChartAt_tangent_zero_fiberScale (I := I) α c hssrc, fiberRescaleCLM_apply,
      rescaleChartOrbit_apply]
  · show extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
          (⟨(f (c * s₀ + d)).proj, c • (f (c * s₀ + d)).snd⟩ : TangentBundle I M)
      = fiberRescaleCLM (E := E) c
          ((fun s' : ℝ => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f s')) (aff s₀))
    have hssrc : (f (aff s₀)).proj ∈ (chartAt H α).source := by rw [haff_s0]; exact hsrc
    change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
          (⟨(f (c * s₀ + d)).proj, c • (f (c * s₀ + d)).snd⟩ : TangentBundle I M)
      = fiberRescaleCLM (E := E) c
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (f (aff s₀)))
    rw [extChartAt_tangent_zero_fiberScale (I := I) α c hssrc, fiberRescaleCLM_apply,
      rescaleChartOrbit_apply]

omit [NeZero (Module.finrank ℝ E)] in
private theorem offchart_rescaledLift_chartDeriv_self
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) S) (c d : ℝ)
    {s₀ : ℝ} (hs₀ : c * s₀ + d ∈ S)
    (hoff : (f (c * s₀ + d)).proj ∉ (chartAt H α).source) :
    HasDerivWithinAt
      (fun s : ℝ => extChartAt I.tangent
        (⟨(f (c * s₀ + d)).proj, c • (f (c * s₀ + d)).snd⟩ : TangentBundle I M)
        (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M))
      0 {s : ℝ | c * s + d ∈ S} s₀ := by
  classical
  set a : ℝ := c * s₀ + d with ha_def
  set aff : ℝ → ℝ := fun s => c * s + d with haff_def
  set β : M := (f a).proj with hβ
  have haff_deriv : HasDerivWithinAt aff c {s : ℝ | c * s + d ∈ S} s₀ :=
    (hasDerivAt_affine c d s₀).hasDerivWithinAt
  have hmaps : MapsTo aff {s : ℝ | c * s + d ∈ S} S := fun s hs => hs
  have haff_s0 : aff s₀ = a := rfl
  have hself_src : f a ∈ (extChartAt I.tangent (f a)).source := mem_extChartAt_source (f a)
  have hfwd : HasDerivWithinAt (fun s' => extChartAt I.tangent (f a) (f s'))
      (tangentCoordChange I.tangent (f a) (f a) (f a)
        (geodesicVectorFieldChart (I := I) g α (f a))) S a :=
    hf.hasDerivWithinAt (t₀ := a) hs₀ hself_src
  have hVzero : geodesicVectorFieldChart (I := I) g α (f a) = 0 :=
    geodesicVectorFieldChart_eq_zero_of_notMem_source (I := I) g α (f a) hoff
  rw [hVzero, tangentCoordChange_self (I := I.tangent) hself_src] at hfwd
  have hcomp : HasDerivWithinAt
      ((fun s' => extChartAt I.tangent (f a) (f s')) ∘ aff) (c • (0 : E × E))
      {s : ℝ | c * s + d ∈ S} s₀ :=
    HasDerivWithinAt.scomp (x := s₀) (haff_s0 ▸ hfwd) haff_deriv hmaps
  rw [smul_zero] at hcomp
  have hcomp2 : HasDerivWithinAt
      (fun s => fiberRescaleCLM (E := E) c ((fun s' => extChartAt I.tangent (f a) (f s')) (aff s)))
      (fiberRescaleCLM (E := E) c (0 : E × E)) {s : ℝ | c * s + d ∈ S} s₀ :=
    (fiberRescaleCLM (E := E) c).hasFDerivAt.comp_hasDerivWithinAt s₀ hcomp
  rw [map_zero] at hcomp2
  have hf_cont : ContinuousWithinAt (fun s => f (aff s)) {s : ℝ | c * s + d ∈ S} s₀ :=
    ((haff_s0 ▸ hf.continuousWithinAt hs₀ :
      ContinuousWithinAt f S (aff s₀))).comp haff_deriv.continuousWithinAt hmaps
  have hproj_cont : ContinuousWithinAt (fun s => (f (aff s)).proj)
      {s : ℝ | c * s + d ∈ S} s₀ :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousWithinAt.comp hf_cont
      (mapsTo_univ _ _)
  have hβsrc : β ∈ (chartAt H β).source := mem_chart_source H β
  have hpe : extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)
      = extChartAt I.tangent (f a) := by
    rw [hβ, FiberBundle.extChartAt, FiberBundle.extChartAt]
  have hUnhds : (fun s => (f (aff s)).proj) ⁻¹' (chartAt H β).source ∈
      𝓝[{s : ℝ | c * s + d ∈ S}] s₀ := by
    apply hproj_cont.preimage_mem_nhdsWithin
    refine (chartAt H β).open_source.mem_nhds ?_
    show (f (aff s₀)).proj ∈ (chartAt H β).source
    rw [haff_s0]; exact hβsrc
  refine HasDerivWithinAt.congr_of_eventuallyEq hcomp2 ?_ ?_
  · filter_upwards [hUnhds] with s hs
    have hssrc : (f (aff s)).proj ∈ (chartAt H β).source := hs
    change extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)
          (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M)
      = fiberRescaleCLM (E := E) c (extChartAt I.tangent (f a) (f (aff s)))
    rw [← hpe, extChartAt_tangent_zero_fiberScale (I := I) β c hssrc, fiberRescaleCLM_apply,
      rescaleChartOrbit_apply]
  · have hssrc : (f (aff s₀)).proj ∈ (chartAt H β).source := by rw [haff_s0]; exact hβsrc
    change extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)
          (⟨(f (c * s₀ + d)).proj, c • (f (c * s₀ + d)).snd⟩ : TangentBundle I M)
      = fiberRescaleCLM (E := E) c (extChartAt I.tangent (f a) (f (aff s₀)))
    rw [← hpe, extChartAt_tangent_zero_fiberScale (I := I) β c hssrc, fiberRescaleCLM_apply,
      rescaleChartOrbit_apply]

omit [NeZero (Module.finrank ℝ E)] in
private theorem rescaledLift_continuousWithinAt
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) S) (c d : ℝ)
    {s₀ : ℝ} (hs₀ : c * s₀ + d ∈ S) :
    ContinuousWithinAt
      (fun s => (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M))
      {s : ℝ | c * s + d ∈ S} s₀ := by
  classical
  set aff : ℝ → ℝ := fun s => c * s + d with haff
  set L : ℝ → TangentBundle I M :=
    fun s => (⟨(f (aff s)).proj, c • (f (aff s)).snd⟩ : TangentBundle I M) with hL
  have haff_cont : ContinuousWithinAt aff {s : ℝ | c * s + d ∈ S} s₀ :=
    (hasDerivAt_affine c d s₀).continuousAt.continuousWithinAt
  have hmaps : MapsTo aff {s : ℝ | c * s + d ∈ S} S := fun s hs => hs
  have hf_cont_a : ContinuousWithinAt f S (aff s₀) := hf.continuousWithinAt hs₀
  have hfaff_cont : ContinuousWithinAt (fun s => f (aff s)) {s : ℝ | c * s + d ∈ S} s₀ :=
    hf_cont_a.comp haff_cont hmaps
  rw [FiberBundle.continuousWithinAt_totalSpace] at hfaff_cont ⊢
  obtain ⟨hproj, hfib⟩ := hfaff_cont
  refine ⟨hproj, ?_⟩
  have hUnhds : (fun s => (f (aff s)).proj) ⁻¹' (chartAt H (L s₀).proj).source ∈
      𝓝[{s : ℝ | c * s + d ∈ S}] s₀ := by
    apply hproj.preimage_mem_nhdsWithin
    exact (chartAt H (L s₀).proj).open_source.mem_nhds (mem_chart_source H (L s₀).proj)
  have hcong : (fun s => ((trivializationAt E (TangentSpace I) (L s₀).proj) (L s)).2)
      =ᶠ[𝓝[{s : ℝ | c * s + d ∈ S}] s₀]
      (fun s => c • ((trivializationAt E (TangentSpace I) (L s₀).proj) (f (aff s))).2) := by
    filter_upwards [hUnhds] with s hs
    exact chartFiberCoord_fiberScale (I := I) (L s₀).proj c (q := f (aff s)) hs
  refine ContinuousWithinAt.congr_of_eventuallyEq (hfib.const_smul c) hcong ?_
  exact chartFiberCoord_fiberScale (I := I) (L s₀).proj c (q := f (aff s₀))
    (mem_chart_source H (L s₀).proj)

omit [NeZero (Module.finrank ℝ E)] in
theorem scaledTangentLift_transport
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → TangentBundle I M} {S : Set ℝ}
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) S)
    (c d : ℝ) :
    IsMIntegralCurveOn
      (fun s : ℝ =>
        (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M))
      (geodesicVectorFieldChart (I := I) g α)
      {s : ℝ | c * s + d ∈ S} := by
  classical
  set L : ℝ → TangentBundle I M :=
    fun s => (⟨(f (c * s + d)).proj, c • (f (c * s + d)).snd⟩ : TangentBundle I M) with hL
  intro s₀ hs₀
  have hs₀' : c * s₀ + d ∈ S := hs₀
  have hLcont : ContinuousWithinAt L {s : ℝ | c * s + d ∈ S} s₀ :=
    rescaledLift_continuousWithinAt (I := I) g α hf c d hs₀'
  by_cases hsrc : (f (c * s₀ + d)).proj ∈ (chartAt H α).source
  · have hdin := inchart_rescaledLift_chartPhase (I := I) g α hf c d hs₀' hsrc
    have hLsrc : (L s₀).proj ∈ (chartAt H α).source := hsrc
    have hrev := hasMFDerivWithinAt_of_chartPhase_at_zero_section (I := I) α (c := L) (s₀ := s₀)
      (w := chartPhaseVF (I := I) g α
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (L s₀)))
      hLcont hLsrc hdin
    have heq : geodesicVectorFieldChart (I := I) g α (L s₀)
        = tangentCoordChange I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (L s₀) (L s₀)
            (chartPhaseVF (I := I) g α
              (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) (L s₀))) := by
      rw [chartPhaseVF_extChartAt_zero_section (I := I) g α hLsrc,
          tangentCoordChange_zero_section_geodesicVF (I := I) g α (L s₀) hLsrc]
    rw [heq]
    exact hrev
  · have hdoff := offchart_rescaledLift_chartDeriv_self (I := I) g α hf c d hs₀' hsrc
    have hrev := hasMFDerivWithinAt_of_chartDeriv_self (I := I) (c := L) (s₀ := s₀) (w := 0)
      hLcont hdoff
    have hVzero : geodesicVectorFieldChart (I := I) g α (L s₀) = 0 :=
      geodesicVectorFieldChart_eq_zero_of_notMem_source (I := I) g α (L s₀) hsrc
    have heq : geodesicVectorFieldChart (I := I) g α (L s₀)
        = tangentCoordChange I.tangent (L s₀) (L s₀) (L s₀) (0 : E × E) := by
      rw [tangentCoordChange_self (I := I.tangent) (mem_extChartAt_source (L s₀)) (v := 0)]
      exact hVzero
    rw [heq]
    exact hrev

section AffinePathELengthReparam

open Manifold

variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
theorem pathELength_comp_affineHomeo
    (γ : ℝ → M) {a b : ℝ} (c d : ℝ) (hab : a ≤ b) (hc : 0 < c)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Set.Icc a b)) :
    pathELength I (fun s : ℝ => γ (c * s + d)) ((a - d) / c) ((b - d) / c)
      = pathELength I γ a b := by
  set f : ℝ → ℝ := fun s : ℝ => c * s + d with hf_def
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hfa : f ((a - d) / c) = a := by
    simp only [hf_def]
    rw [mul_div_cancel₀ _ hc_ne]
    ring
  have hfb : f ((b - d) / c) = b := by
    simp only [hf_def]
    rw [mul_div_cancel₀ _ hc_ne]
    ring
  have hab' : (a - d) / c ≤ (b - d) / c := by
    rw [div_le_div_iff_of_pos_right hc]
    linarith
  have hf_mono : MonotoneOn f (Set.Icc ((a - d) / c) ((b - d) / c)) := by
    intro x _ y _ hxy
    simp only [hf_def]
    have : c * x ≤ c * y := mul_le_mul_of_nonneg_left hxy hc.le
    linarith
  have hf_diff : DifferentiableOn ℝ f (Set.Icc ((a - d) / c) ((b - d) / c)) := by
    intro x _
    have hdiff : Differentiable ℝ f := by
      simp only [hf_def]
      exact ((differentiable_const c).mul differentiable_id).add (differentiable_const d)
    exact (hdiff x).differentiableWithinAt
  have hγ' : MDifferentiableOn 𝓘(ℝ, ℝ) I γ
      (Set.Icc (f ((a - d) / c)) (f ((b - d) / c))) := by
    rw [hfa, hfb]; exact hγ
  have hmain :
      pathELength I (γ ∘ f) ((a - d) / c) ((b - d) / c)
        = pathELength I γ (f ((a - d) / c)) (f ((b - d) / c)) :=
    pathELength_comp_of_monotoneOn (I := I) (γ := γ) hab' hf_mono hf_diff hγ'
  rw [hfa, hfb] at hmain
  exact hmain

end AffinePathELengthReparam

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
