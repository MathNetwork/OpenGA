import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ChartFlowVelocitySlice
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow



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

section ChartCoordRescaling

variable [I.Boundaryless]

def rescaleChartOrbit (a : ℝ) : E × E → E × E :=
  fun z => (z.1, a • z.2)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleChartOrbit_apply (a : ℝ) (z : E × E) :
    rescaleChartOrbit a z = (z.1, a • z.2) := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma rescaleChartOrbit_mk (a : ℝ) (x v : E) :
    rescaleChartOrbit (E := E) a (x, v) = (x, a • v) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPhaseVF_rescale
    (g : SmoothRiemannianMetric I M) (α : M)
    (a : ℝ) (x v : E) :
    chartPhaseVF (I := I) g α (x, a • v) =
      (a • v, -(a * a) • chartChristoffelContraction (I := I) g α v v x) := by
  classical
  have h0 : chartPhaseVF (I := I) g α (x, a • v) =
      (a • v, -chartChristoffelContraction (I := I) g α (a • v) (a • v) x) := rfl
  rw [h0]
  refine Prod.ext rfl ?_
  have hΓ : chartChristoffelContraction (I := I) g α (a • v) (a • v) x =
      (a * a) • chartChristoffelContraction (I := I) g α v v x :=
    chartChristoffelContraction_smul_smul (I := I) g α a v x
  change -chartChristoffelContraction (I := I) g α (a • v) (a • v) x =
      -(a * a) • chartChristoffelContraction (I := I) g α v v x
  rw [hΓ, neg_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma hasDerivAt_rescaled_orbit
    {g : SmoothRiemannianMetric I M} {α : M}
    {c : ℝ → E × E} {s₀ a : ℝ}
    (hd : HasDerivAt c (chartPhaseVF (I := I) g α (c (a * s₀))) (a * s₀)) :
    HasDerivAt (fun s : ℝ => rescaleChartOrbit (E := E) a (c (a * s)))
      (chartPhaseVF (I := I) g α
        (rescaleChartOrbit (E := E) a (c (a * s₀)))) s₀ := by
  classical
  set z : E × E := c (a * s₀) with hz_def
  have hmul : HasDerivAt (fun s : ℝ => a * s) a s₀ := by
    have : HasDerivAt (fun s : ℝ => a * s) (a * 1) s₀ := (hasDerivAt_id s₀).const_mul a
    simpa using this
  have hcomp : HasDerivAt (fun s : ℝ => c (a * s))
      (a • chartPhaseVF (I := I) g α z) s₀ := hd.scomp s₀ hmul
  set rescale : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearMap.id ℝ E).prodMap (a • (ContinuousLinearMap.id ℝ E))
    with hrescale_def
  have hrescale_apply : ∀ y : E × E, rescale y = (y.1, a • y.2) := by
    intro y
    change ((ContinuousLinearMap.id ℝ E) y.1, (a • (ContinuousLinearMap.id ℝ E)) y.2) =
        (y.1, a • y.2)
    refine Prod.ext rfl ?_
    change (a • (ContinuousLinearMap.id ℝ E)) y.2 = a • y.2
    rw [ContinuousLinearMap.smul_apply]
    rfl
  have hrescaled_eq : (fun s : ℝ => rescale (c (a * s))) =
      (fun s : ℝ => rescaleChartOrbit (E := E) a (c (a * s))) := by
    funext s
    simp [rescaleChartOrbit, hrescale_apply]
  have hcomp_rescale : HasDerivAt (fun s : ℝ => rescale (c (a * s)))
      (rescale (a • chartPhaseVF (I := I) g α z)) s₀ :=
    rescale.hasFDerivAt.comp_hasDerivAt s₀ hcomp
  rw [hrescaled_eq] at hcomp_rescale
  have hrhs_eq :
      rescale (a • chartPhaseVF (I := I) g α z) =
        chartPhaseVF (I := I) g α
          (rescaleChartOrbit (E := E) a (c (a * s₀))) := by
    rw [hrescale_apply]
    have h_rescaled_form : rescaleChartOrbit (E := E) a (c (a * s₀)) =
        (z.1, a • z.2) := rfl
    rw [h_rescaled_form]
    rw [chartPhaseVF_rescale (I := I) g α a z.1 z.2]
    have hpvf : chartPhaseVF (I := I) g α z =
        (z.2, -chartChristoffelContraction (I := I) g α z.2 z.2 z.1) := rfl
    rw [hpvf]
    simp only [Prod.smul_mk, smul_neg, smul_smul]
    refine Prod.ext rfl ?_
    rw [neg_smul]
  rw [← hrhs_eq]
  exact hcomp_rescale

end ChartCoordRescaling

section UniformBridge

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

def UniformChartFlowBridge (g : SmoothRiemannianMetric I M) (p : M) : Prop :=
  ∃ (Φ : (E × E) × ℝ → E × E) (t' ρ : ℝ), 0 < t' ∧ 0 < ρ ∧
    ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t') (0 : E) ∧
    ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
      (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
        chartFlowCandidate (I := I) Φ p t' v

end UniformBridge

section Headline

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem expMap_contMDiffAt_zero_of_uniformChartFlowBridge
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : UniformChartFlowBridge (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) := by
  classical
  obtain ⟨Φ, t', ρ, ht'_pos, hρ_pos, hcand_cd, heq⟩ := h
  set F : E → M := fun w : E =>
    chartFlowCandidate (I := I) Φ p t' ((1 / t') • w)
    with hF_def
  have hsmul_cd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun w : E => (1 / t') • w) := by
    have : ContDiff ℝ ∞ (fun w : E => (1 / t') • w) :=
      (contDiff_const.smul contDiff_id)
    have h1 : ContDiff ℝ 1 (fun w : E => (1 / t') • w) :=
      this.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    exact h1.contMDiff
  have hsmul_cda : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun w : E => (1 / t') • w) (0 : E) := hsmul_cd.contMDiffAt
  have hval0 : (1 / t') • (0 : E) = 0 := smul_zero _
  have hF_cd : ContMDiffAt 𝓘(ℝ, E) I 1 F (0 : E) := by
    have hcand_cd' : ContMDiffAt 𝓘(ℝ, E) I 1
        (chartFlowCandidate (I := I) Φ p t')
        ((fun w : E => (1 / t') • w) (0 : E)) := by
      change ContMDiffAt 𝓘(ℝ, E) I 1
          (chartFlowCandidate (I := I) Φ p t') ((1 / t') • (0 : E))
      rw [hval0]
      exact hcand_cd
    have hcomp : ContMDiffAt 𝓘(ℝ, E) I 1
        ((chartFlowCandidate (I := I) Φ p t') ∘ (fun w : E => (1 / t') • w))
        (0 : E) := hcand_cd'.comp (0 : E) hsmul_cda
    exact hcomp
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  have hev :
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        =ᶠ[𝓝 (0 : E)] F := by
    have hsmul_cont : Continuous (fun w : E => (1 / t') • w) :=
      continuous_const.smul continuous_id
    have hsmul_at0_zero : (fun w : E => (1 / t') • w) (0 : E) = 0 := hval0
    have hpre : (fun w : E => (1 / t') • w) ⁻¹' Metric.ball (0 : E) ρ ∈ 𝓝 (0 : E) := by
      have hnhd : Metric.ball (0 : E) ρ ∈ 𝓝 ((fun w : E => (1 / t') • w) (0 : E)) := by
        rw [hsmul_at0_zero]
        exact Metric.ball_mem_nhds _ hρ_pos
      exact hsmul_cont.continuousAt.preimage_mem_nhds hnhd
    filter_upwards [hpre] with w hw
    have hheq := heq ((1 / t') • w) hw
    have htv_eq_w : t' • ((1 / t') • w) = w := by
      rw [smul_smul, mul_one_div, div_self ht'_ne, one_smul]
    rw [htv_eq_w] at hheq
    change (expMap (I := I) g p (show TangentSpace I p from w) : M) = F w
    rw [hF_def]
    exact hheq
  exact hF_cd.congr_of_eventuallyEq hev

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem expMap_contMDiffAt_zero_exists
    (g : SmoothRiemannianMetric I M) (p : M)
    (huniform : ∃ (Φ : (E × E) × ℝ → E × E) (t' ρ : ℝ), 0 < t' ∧ 0 < ρ ∧
      ContMDiffAt 𝓘(ℝ, E) I 1
        (chartFlowCandidate (I := I) Φ p t') (0 : E) ∧
      ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
        (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
          chartFlowCandidate (I := I) Φ p t' v) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
  expMap_contMDiffAt_zero_of_uniformChartFlowBridge (I := I) (g := g) (p := p) huniform

end Headline

section UniformBridgePointwise

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartFlowCandidate_zero_matches_expMap_at_origin
    (g : SmoothRiemannianMetric I M) (p : M)
    {Φ : (E × E) × ℝ → E × E}
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E))) :
    chartFlowCandidate (I := I) Φ p 0 (0 : E) =
      expMap (I := I) g p (show TangentSpace I p from (0 : E)) := by
  classical
  rw [show expMap (I := I) g p (show TangentSpace I p from (0 : E)) = p from
    expMap_zero (I := I) g p]
  exact chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit

end UniformBridgePointwise

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
