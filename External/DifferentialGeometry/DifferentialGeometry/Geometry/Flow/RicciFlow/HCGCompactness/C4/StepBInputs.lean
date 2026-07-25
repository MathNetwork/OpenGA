import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Comparison.ExpBallDiffeo
import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricKoszul
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepAInputs

set_option autoImplicit false
set_option linter.style.longLine false































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]





noncomputable def normalTransition
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : X.M) : E → E :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  fun z =>
    normalChartAt (I := I) X.metric y
      (expMapDiffeo (I := I) X.metric x z)











noncomputable def normalCoordMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    E -> (E →L[Real] E →L[Real] Real) :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  fun z =>
    let D : E →L[Real] TangentSpace I (expMapDiffeo (I := I) Y.metric x z) :=
      mfderiv 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) z
    (ContinuousLinearMap.precomp Real D).comp
      ((Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)).comp D)







omit [NeZero (Module.finrank ℝ E)] in
theorem expMapDiffeo_contMDiffOn_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ δ : ℝ, 0 < δ ∧
      ContMDiffOn 𝓘(Real, E) I ∞
        (fun w => expMapDiffeo (I := I) Y.metric x w)
        (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hforward⟩ :=
    expMap_contMDiffAt_infty_of_norm_lt (I := I) Y.metric x
  refine ⟨δ, hδ, ?_⟩
  have hexp : ContMDiffOn 𝓘(Real, E) I ∞
      (fun w : E => (expMap (I := I) Y.metric x (show TangentSpace I x from w) : Y.M))
      (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
    intro w hw
    have hwδ : ‖w‖ < δ := by
      have := hw.1; rw [Metric.mem_ball, dist_zero_right] at this; exact this
    exact (hforward w hwδ).contMDiffWithinAt
  exact hexp.congr (fun w hw => expMapDiffeo_apply_eq (I := I) Y.metric x hw.2)




omit [NeZero (Module.finrank ℝ E)] in
theorem normalCoordMetric_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (z v w : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalCoordMetric (I := I) Y x z v w =
      Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  simp only [normalCoordMetric, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rfl



omit [NeZero (Module.finrank ℝ E)] in
theorem normalMetric_zero
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (c : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalCoordMetric (I := I) Y c 0 = Y.metric.inner c := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ext v w
  rw [normalCoordMetric_apply (I := I), expMapDiffeo_zero (I := I)]
  exact normalChartAt_metric_pullback_at_origin (I := I) Y.metric c v w

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




theorem radialEnorm_normal
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      ⟨Y.metric.toRiemannianMetric⟩
    ∀ (t : Real), ‖t • v‖ < expMapC2Radius (I := I) Y.metric x →
    ‖mfderiv 𝓘(Real, Real) I
        (fun s : Real => (expMap (I := I) Y.metric x
          (show TangentSpace I x from (s • v)) : Y.M)) t (1 : Real)‖ₑ =
      ENNReal.ofReal (Real.sqrt (normalCoordMetric (I := I) Y x (t • v) v v)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  intro t ht
  have hsrc : t • v ∈ (expMapDiffeo (I := I) Y.metric x).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x ht
  have hev : expMapDiffeo (I := I) Y.metric x =ᶠ[nhds (t • v)]
      (fun z : E => (expMap (I := I) Y.metric x
        (show TangentSpace I x from z) : Y.M)) := by
    refine Filter.eventuallyEq_of_mem
      ((expMapDiffeo (I := I) Y.metric x).open_source.mem_nhds hsrc) ?_
    intro z hz
    exact expMapDiffeo_apply_eq (I := I) Y.metric x hz
  rw [mfderiv_exp_radial (I := I) Y.metric x v t ht]
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  have hinner :
      (inner Real
        (mfderiv 𝓘(Real, E) I
          (fun z : E => (expMap (I := I) Y.metric x
            (show TangentSpace I x from z) : Y.M)) (t • v)
          (show TangentSpace I x from v))
        (mfderiv 𝓘(Real, E) I
          (fun z : E => (expMap (I := I) Y.metric x
            (show TangentSpace I x from z) : Y.M)) (t • v)
          (show TangentSpace I x from v)) : Real) =
        Y.metric.inner
          (expMap (I := I) Y.metric x (show TangentSpace I x from (t • v)))
          (mfderiv 𝓘(Real, E) I
            (fun z : E => (expMap (I := I) Y.metric x
              (show TangentSpace I x from z) : Y.M)) (t • v)
            (show TangentSpace I x from v))
          (mfderiv 𝓘(Real, E) I
            (fun z : E => (expMap (I := I) Y.metric x
              (show TangentSpace I x from z) : Y.M)) (t • v)
            (show TangentSpace I x from v)) := rfl
  rw [hinner, normalCoordMetric_apply (I := I),
    expMapDiffeo_apply_eq (I := I) Y.metric x hsrc, hev.mfderiv_eq]







omit [NeZero (Module.finrank ℝ E)] in
private theorem expMapDiffeo_pushforward_section_contMDiffOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {U : Set E}
    (hU : IsOpen U)
    (hf : letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          ContMDiffOn 𝓘(Real, E) I ∞ (fun w => expMapDiffeo (I := I) Y.metric x w) U)
    (v : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, E)) ∞
      (fun z => TotalSpace.mk' E (E := fun b : Y.M => TangentSpace I b)
        (expMapDiffeo (I := I) Y.metric x z)
        (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)) U := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle

  have htm := hf.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hU.uniqueMDiffOn

  have hσ : ContMDiff 𝓘(Real, E) (𝓘(Real, E)).tangent ∞
      (fun z : E => (TotalSpace.mk' E z v : TangentBundle 𝓘(Real, E) E)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E => v)).mpr contDiff_const

  have hcomp : ContMDiffOn 𝓘(Real, E) I.tangent ∞
      (fun z => tangentMapWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U
        (TotalSpace.mk' E z v)) U :=
    htm.comp (hσ.contMDiffOn (s := U)) (fun z hz => hz)
  refine hcomp.congr ?_
  intro z hz
  have hmf : mfderivWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U z
      = mfderiv 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) z :=
    mfderivWithin_of_isOpen hU hz
  change TotalSpace.mk' E (E := fun b : Y.M => TangentSpace I b)
      (expMapDiffeo (I := I) Y.metric x z)
      (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
      = tangentMapWithin 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) U
          (TotalSpace.mk' E z v)
  dsimp only [tangentMapWithin]
  rw [hmf]

set_option synthInstance.maxHeartbeats 800000 in






omit [NeZero (Module.finrank ℝ E)] in
theorem normalCoordMetric_contDiffOn_of_smooth
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) {S : Set E}
    (hU : IsOpen S)
    (hf : letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          ContMDiffOn 𝓘(Real, E) I ∞ (fun w => expMapDiffeo (I := I) Y.metric x w) S) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x) S := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle

  have hscalar : ∀ v w : E, ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
      (fun z => Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
          (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
          (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w))
      S := by
    intro v w
    have hg : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun z => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun b : Y.M => TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
          (expMapDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)))
        S :=
      Y.metric.contMDiff.comp_contMDiffOn hf
    have hv := expMapDiffeo_pushforward_section_contMDiffOn (I := I) Y x hU hf v
    have hw := expMapDiffeo_pushforward_section_contMDiffOn (I := I) Y x hU hf w
    have htotal : ContMDiffOn 𝓘(Real, E) (I.prod 𝓘(Real, Real)) ∞
        (fun z => TotalSpace.mk' Real (E := Bundle.Trivial Y.M Real)
          (expMapDiffeo (I := I) Y.metric x z)
          (Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)
            (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
            (mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w)))
        S :=
      ContMDiffOn.clm_bundle_apply₂
        (E₁ := fun b : Y.M => TangentSpace I b) (E₂ := fun b : Y.M => TangentSpace I b)
        (E₃ := fun _ : Y.M => Real)
        (b := fun z => expMapDiffeo (I := I) Y.metric x z)
        (ψ := fun z => Y.metric.inner (expMapDiffeo (I := I) Y.metric x z))
        (v := fun z => mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z v)
        (w := fun z => mfderiv 𝓘(Real, E) I (fun u => expMapDiffeo (I := I) Y.metric x u) z w)
        hg hv hw
    intro z hz
    have h_at := htotal z hz
    rw [contMDiffWithinAt_totalSpace] at h_at
    exact h_at.2
  rw [contDiffOn_clm_apply]
  intro v
  rw [contDiffOn_clm_apply]
  intro w
  rw [← contMDiffOn_iff_contDiffOn]
  exact (hscalar v w).congr (fun z _ => normalCoordMetric_apply (I := I) Y x z v w)

set_option synthInstance.maxHeartbeats 800000 in






omit [NeZero (Module.finrank ℝ E)] in
theorem normalCoordMetric_contDiffOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ δ : ℝ, 0 < δ ∧
      ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x)
        (Metric.ball (0 : E) δ ∩ (expMapDiffeo (I := I) Y.metric x).source) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hf⟩ := expMapDiffeo_contMDiffOn_ball (I := I) Y x
  exact ⟨δ, hδ, normalCoordMetric_contDiffOn_of_smooth (I := I) Y x
    (Metric.isOpen_ball.inter (expMapDiffeo (I := I) Y.metric x).open_source) hf⟩












omit [NeZero (Module.finrank ℝ E)] in
theorem normalCoordMetric_contDiffOn_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x) (Metric.ball (0 : E) r) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨δ, hδ, hsm⟩ := normalCoordMetric_contDiffOn (I := I) Y x
  obtain ⟨r₀, hr₀, hsub⟩ :=
    Metric.isOpen_iff.mp (expMapDiffeo (I := I) Y.metric x).open_source 0
      (zero_mem_expMapDiffeo_source (I := I) Y.metric x)
  refine ⟨min δ r₀, lt_min hδ hr₀, hsm.mono fun z hz => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hz
  refine ⟨Metric.mem_ball.mpr ?_, hsub (Metric.mem_ball.mpr ?_)⟩
  · rw [dist_zero_right]; exact lt_of_lt_of_le hz (min_le_left _ _)
  · rw [dist_zero_right]; exact lt_of_lt_of_le hz (min_le_right _ _)







theorem expMapDiffeo_contMDiffOn_expBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E) I ∞
      (fun w => expMapDiffeo (I := I) Y.metric x w)
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have hexp : ContMDiffOn 𝓘(Real, E) I ∞
      (fun w : E => (expMap (I := I) Y.metric x (show TangentSpace I x from w) : Y.M))
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact (expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) Y.metric x hw).contMDiffWithinAt
  refine hexp.congr (fun w hw => ?_)
  rw [Metric.mem_ball, dist_zero_right] at hw
  exact expMapDiffeo_apply_eq (I := I) Y.metric x
    (mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x hw)







theorem normalCoordMetric_contDiffOn_expBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) Y x)
      (Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact normalCoordMetric_contDiffOn_of_smooth (I := I) Y x Metric.isOpen_ball
    (expMapDiffeo_contMDiffOn_expBall (I := I) Y x)







theorem contDiffOn_normalCoordMetric_of_subset_expBall
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (c : ∀ k : ℕ, (X.obj k).M) {U : Set E}
    (hsub : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj k).metric (c k))) :
    ∀ k, ContDiffOn Real (⊤ : ℕ∞) (normalCoordMetric (I := I) (X.obj k) (c k)) U :=
  fun k => (normalCoordMetric_contDiffOn_expBall (I := I) (X.obj k) (c k)).mono (hsub k)




def NormalCoordMetricEquivOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (U : Set E) :
    Prop :=
  forall z : E, z ∈ U -> forall v : E,
    (1 / 2 : Real) * ‖v‖ ^ 2 <= normalCoordMetric (I := I) Y x z v v ∧
      normalCoordMetric (I := I) Y x z v v <= 2 * ‖v‖ ^ 2

namespace NormalCoordMetricEquivOn



omit [NeZero (Module.finrank ℝ E)] in
theorem coercive
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : Y.M}
    {U : Set E} (h : NormalCoordMetricEquivOn (I := I) Y x U)
    {z : E} (hz : z ∈ U) :
    IsCoercive (normalCoordMetric (I := I) Y x z) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro v
  simpa [pow_two, mul_assoc] using (h z hz v).1



omit [NeZero (Module.finrank ℝ E)] in
theorem sharp_norm_le
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : Y.M}
    {U : Set E} (h : NormalCoordMetricEquivOn (I := I) Y x U)
    {z : E} (hz : z ∈ U) (eta : E →L[Real] Real) :
    ‖(h.coercive hz).sharp eta‖ <= 2 * ‖eta‖ := by
  have hbound := IsCoercive.sharp_norm_le (h.coercive hz)
    (c := (1 / 2 : Real)) (by norm_num)
    (fun v => by simpa [pow_two, mul_assoc] using (h z hz v).1) eta
  norm_num at hbound ⊢
  exact hbound

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [NeZero (Module.finrank ℝ E)] in
theorem abs_apply_le
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : Y.M}
    {U : Set E} (h : NormalCoordMetricEquivOn (I := I) Y x U)
    {z : E} (hz : z ∈ U) (v w : E) :
    |normalCoordMetric (I := I) Y x z v w| ≤ 2 * ‖v‖ * ‖w‖ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  let dExp : E →L[Real]
      TangentSpace I (expMapDiffeo (I := I) Y.metric x z) :=
    mfderiv 𝓘(Real, E) I
      (fun u ↦ expMapDiffeo (I := I) Y.metric x u) z
  have hcs :
      |normalCoordMetric (I := I) Y x z v w| ≤
        ‖dExp v‖ * ‖dExp w‖ := by
    rw [normalCoordMetric_apply (I := I)]
    exact abs_real_inner_le_norm (dExp v) (dExp w)
  have hvSq : ‖dExp v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [normalCoordMetric_apply (I := I)] using (h z hz v).2
  have hwSq : ‖dExp w‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [normalCoordMetric_apply (I := I)] using (h z hz w).2
  have hprodSq :
      (‖dExp v‖ * ‖dExp w‖) ^ 2 ≤ (2 * ‖v‖ * ‖w‖) ^ 2 := by
    have hmul := mul_le_mul hvSq hwSq (sq_nonneg ‖dExp w‖)
      (mul_nonneg (by norm_num) (sq_nonneg ‖v‖))
    nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]
  exact hcs.trans <| le_of_sq_le_sq hprodSq
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg v)) (norm_nonneg w))

end NormalCoordMetricEquivOn




set_option synthInstance.maxHeartbeats 800000 in



def NormalCoordMetricDerivBound
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) (p : Nat) (C : Real) : Prop :=
  forall z : E, z ∈ U ->
    ‖iteratedFDeriv Real p (normalCoordMetric (I := I) Y x) z‖ <= C



















structure NormalCoordMetricBoundInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  metricC : Nat -> Real
  metricC_nonneg : forall p : Nat, 0 <= metricC p


  radius : forall k : Nat, (X.obj k).M -> Real
  radius_pos : forall (k : Nat) (x : (X.obj k).M), 0 < radius k x


  metric_equiv :
    forall (k : Nat) (x : (X.obj k).M),
      NormalCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x))


  metric_deriv :
    forall (k p : Nat) (x : (X.obj k).M),
      NormalCoordMetricDerivBound (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x)) p (metricC p)

namespace NormalCoordMetricBoundInput



theorem half_le_gpConst
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (1 / 2 : Real) ≤ gpCoerciveConst (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  have h0 : (0 : E) ∈ Metric.ball 0 (h.radius k x) := by
    rw [Metric.mem_ball, dist_self]
    exact h.radius_pos k x
  apply le_gpCoerciveConst (I := I)
  intro v
  simpa only [normalMetric_zero (I := I) (X.obj k) x] using
    (h.metric_equiv k x 0 h0 v).1



set_option synthInstance.maxHeartbeats 800000 in


omit [NeZero (Module.finrank ℝ E)] in
theorem fderiv_apply_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {z : E}
    (hz : z ∈ Metric.ball (0 : E) (h.radius k x)) (u v w : E) :
    ‖fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z u v w‖ ≤
      h.metricC 1 * ‖u‖ * ‖v‖ * ‖w‖ := by
  let D := fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z
  let T := iteratedFDeriv Real 1 (normalCoordMetric (I := I) (X.obj k) x) z
  have hT : ‖T‖ ≤ h.metricC 1 := h.metric_deriv k 1 x z hz
  have hDu : ‖D u‖ ≤ h.metricC 1 * ‖u‖ := by
    calc
      ‖D u‖ = ‖T (fun _ : Fin 1 ↦ u)‖ := by
        simp only [D, T, iteratedFDeriv_one_apply]
      _ ≤ ‖T‖ * ∏ _ : Fin 1, ‖u‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖T‖ * ‖u‖ := by simp
      _ ≤ h.metricC 1 * ‖u‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg u)
  calc
    ‖D u v w‖ ≤ ‖D u‖ * ‖v‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm₂ (D u) v w
    _ ≤ (h.metricC 1 * ‖u‖) * ‖v‖ * ‖w‖ := by
      gcongr
    _ = h.metricC 1 * ‖u‖ * ‖v‖ * ‖w‖ := rfl






omit [NeZero (Module.finrank ℝ E)] in
theorem koszulVec_norm_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {z : E}
    (hz : z ∈ Metric.ball (0 : E) (h.radius k x)) (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
        (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w‖ ≤
      3 * h.metricC 1 * ‖v‖ * ‖w‖ := by
  have hraw := MetricKoszul.koszulVec_norm_le
    ((h.metric_equiv k x).coercive hz)
    (c := (1 / 2 : Real)) (by norm_num)
    (fun u ↦ by simpa [pow_two, mul_assoc] using (h.metric_equiv k x z hz u).1)
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z)
    (C := h.metricC 1) (h.metricC_nonneg 1)
    (h.fderiv_apply_le k x hz) v w
  norm_num at hraw ⊢
  ring_nf at hraw ⊢
  exact hraw




omit [NeZero (Module.finrank ℝ E)] in
theorem koszulVec_pair_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {z y : E}
    (hz : z ∈ Metric.ball (0 : E) (h.radius k x))
    (hy : y ∈ Metric.ball (0 : E) (h.radius k x))
    (hmetric :
      ‖normalCoordMetric (I := I) (X.obj k) x y -
          normalCoordMetric (I := I) (X.obj k) x z‖ ≤
        h.metricC 1 * ‖z - y‖)
    (hjet : ∀ u v w : E,
      ‖(fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z -
          fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) u v w‖ ≤
        (h.metricC 2 * ‖z - y‖) * ‖u‖ * ‖v‖ * ‖w‖)
    (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hy)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) v w‖ ≤
      (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) *
        ‖z - y‖ * ‖v‖ * ‖w‖ := by
  have hraw := MetricKoszul.koszulVec_sub_le
    ((h.metric_equiv k x).coercive hz)
    ((h.metric_equiv k x).coercive hy)
    (cB := (1 / 2 : Real)) (cC := (1 / 2 : Real))
    (by norm_num) (by norm_num)
    (fun u ↦ by simpa [pow_two, mul_assoc] using (h.metric_equiv k x z hz u).1)
    (fun u ↦ by simpa [pow_two, mul_assoc] using (h.metric_equiv k x y hy u).1)
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z)
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y)
    (Csub := h.metricC 2 * ‖z - y‖) (CF := h.metricC 1)
    (mul_nonneg (h.metricC_nonneg 2) (norm_nonneg _))
    (h.metricC_nonneg 1) hjet (h.fderiv_apply_le k x hy) v w
  norm_num at hraw
  have hC1 : 0 ≤ h.metricC 1 := h.metricC_nonneg 1
  calc
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hy)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) v w‖
        ≤ 2 * ((3 / 2 : Real) * (h.metricC 2 * ‖z - y‖) * ‖v‖ * ‖w‖) +
          2 * (‖normalCoordMetric (I := I) (X.obj k) x y -
              normalCoordMetric (I := I) (X.obj k) x z‖ *
            (2 * ((3 / 2 : Real) * h.metricC 1 * ‖v‖ * ‖w‖))) := hraw
    _ ≤ 2 * ((3 / 2 : Real) * (h.metricC 2 * ‖z - y‖) * ‖v‖ * ‖w‖) +
          2 * ((h.metricC 1 * ‖z - y‖) *
            (2 * ((3 / 2 : Real) * h.metricC 1 * ‖v‖ * ‖w‖))) := by
      gcongr
    _ = (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) *
          ‖z - y‖ * ‖v‖ * ‖w‖ := by
      ring

set_option synthInstance.maxHeartbeats 800000 in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private theorem fderiv_eval3
    {G : E → E →L[Real] E →L[Real] Real} {q : E}
    (hG : DifferentiableAt Real (fderiv Real G) q)
    (d u v w : E) :
    fderiv Real (fun p ↦ fderiv Real G p u v w) q d =
      fderiv Real (fderiv Real G) q d u v w := by
  letI : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedSpace
  have hu : HasFDerivAt (fun _ : E ↦ u) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) u
  have hv : HasFDerivAt (fun _ : E ↦ v) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) v
  have hw : HasFDerivAt (fun _ : E ↦ w) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) w
  have hfirst := hG.hasFDerivAt.clm_apply hu
  have hsecond := hfirst.clm_apply hv
  have hthird := hsecond.clm_apply hw
  have happ := DFunLike.congr_fun hthird.fderiv d
  simpa using happ

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in



theorem koszulVec_lip_on
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrExp :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆
        Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj k).metric x))
    {z y : E}
    (hz : z ∈ Metric.ball (0 : E) r)
    (hy : y ∈ Metric.ball (0 : E) r)
    (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hz))
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hy))
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) v w‖ ≤
      (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) *
        ‖z - y‖ * ‖v‖ * ‖w‖ := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  letI : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] (E →L[Real] Real)) :=
    ContinuousLinearMap.toNormedSpace
  let G := normalCoordMetric (I := I) (X.obj k) x
  let U := Metric.ball (0 : E) r
  have hsm : ContDiffOn Real (⊤ : ℕ∞) G U :=
    (normalCoordMetric_contDiffOn_expBall (I := I) (X.obj k) x).mono hrExp
  have hdiff : ∀ q ∈ U, DifferentiableAt Real G q := by
    intro q hq
    exact (hsm q hq).contDiffAt (Metric.isOpen_ball.mem_nhds hq) |>.differentiableAt (by simp)
  have hmetric : ‖G y - G z‖ ≤ h.metricC 1 * ‖z - y‖ := by
    have hmean := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := Real) (C := h.metricC 1) hdiff (fun q hq ↦ by
        rw [← norm_iteratedFDeriv_one (f := G)]
        exact h.metric_deriv k 1 x q (hrMetric hq)) hz hy
    calc
      ‖G y - G z‖ ≤ h.metricC 1 * ‖y - z‖ := hmean
      _ = h.metricC 1 * ‖z - y‖ := by rw [norm_sub_rev]
  have hdiffD : ∀ q ∈ U, DifferentiableAt Real (fderiv Real G) q := by
    intro q hq
    have hqsm := (hsm q hq).contDiffAt (Metric.isOpen_ball.mem_nhds hq)
    have hfdsm : ContDiffAt Real 1 (fderiv Real G) q :=
      hqsm.fderiv_right (m := 1) (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
    exact hfdsm.differentiableAt_one
  have hjet : ∀ u a b : E,
      ‖(fderiv Real G z - fderiv Real G y) u a b‖ ≤
        (h.metricC 2 * ‖z - y‖) * ‖u‖ * ‖a‖ * ‖b‖ := by
    intro u a b
    let F : E → Real := fun q ↦ fderiv Real G q u a b
    let C : Real := h.metricC 2 * ‖u‖ * ‖a‖ * ‖b‖
    have hC : 0 ≤ C := by
      dsimp only [C]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (h.metricC_nonneg 2) (norm_nonneg u)) (norm_nonneg a))
        (norm_nonneg b)
    have hFdiff : ∀ q ∈ U, DifferentiableAt Real F q := by
      intro q hq
      have hu : HasFDerivAt (fun _ : E ↦ u) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) u
      have ha : HasFDerivAt (fun _ : E ↦ a) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) a
      have hb : HasFDerivAt (fun _ : E ↦ b) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) b
      exact ((((hdiffD q hq).hasFDerivAt.clm_apply hu).clm_apply ha).clm_apply hb).differentiableAt
    have hFbound : ∀ q ∈ U, ‖fderiv Real F q‖ ≤ C := by
      intro q hq
      refine ContinuousLinearMap.opNorm_le_bound _ hC fun d ↦ ?_
      rw [fderiv_eval3 (hdiffD q hq) d u a b]
      have hdu :
          iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E) =
            fderiv Real (fderiv Real G) q d u := by
        rw [iteratedFDeriv_two_apply]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hdu]
      calc
        ‖iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E) a b‖ ≤
            ‖iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E)‖ * ‖a‖ * ‖b‖ :=
          ContinuousLinearMap.le_opNorm₂ _ a b
        _ ≤ (‖iteratedFDeriv Real 2 G q‖ *
              ∏ i : Fin 2, ‖(![d, u] : Fin 2 → E) i‖) * ‖a‖ * ‖b‖ := by
          gcongr
          exact (iteratedFDeriv Real 2 G q).le_opNorm _
        _ = (‖iteratedFDeriv Real 2 G q‖ * (‖d‖ * ‖u‖)) * ‖a‖ * ‖b‖ := by
          rw [Fin.prod_univ_two]
          simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        _ ≤ (h.metricC 2 * (‖d‖ * ‖u‖)) * ‖a‖ * ‖b‖ := by
          gcongr
          exact h.metric_deriv k 2 x q (hrMetric hq)
        _ = C * ‖d‖ := by
          dsimp only [C]
          ring
    have hmean := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := Real) (C := C) hFdiff hFbound hz hy
    calc
      ‖(fderiv Real G z - fderiv Real G y) u a b‖ = ‖F z - F y‖ := by
        simp only [F, ContinuousLinearMap.sub_apply]
      _ = ‖F y - F z‖ := norm_sub_rev _ _
      _ ≤ C * ‖y - z‖ := hmean
      _ = (h.metricC 2 * ‖z - y‖) * ‖u‖ * ‖a‖ * ‖b‖ := by
        dsimp only [C]
        rw [norm_sub_rev y z]
        ring
  exact h.koszulVec_pair_le k x (hrMetric hz) (hrMetric hy)
    (by simpa only [G] using hmetric)
    (by simpa only [G] using hjet) v w



theorem koszulVec_lip_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M)
    (hsub :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) (h.radius k x) ⊆
        Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj k).metric x))
    {z y : E}
    (hz : z ∈ Metric.ball (0 : E) (h.radius k x))
    (hy : y ∈ Metric.ball (0 : E) (h.radius k x))
    (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hy)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) v w‖ ≤
      (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) *
        ‖z - y‖ * ‖v‖ * ‖w‖ := by
  simpa using h.koszulVec_lip_on k x (fun _ hz' ↦ hz') hsub hz hy v w





theorem koszulAccel_lip_on
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrExp :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆
        Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj k).metric x))
    {z y : E × E} {R : Real} (hR : 0 ≤ R)
    (hz : z.1 ∈ Metric.ball (0 : E) r)
    (hy : y.1 ∈ Metric.ball (0 : E) r)
    (hzv : ‖z.2‖ ≤ R) (hyv : ‖y.2‖ ≤ R) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hz))
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z.1) z.2 z.2 -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hy))
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y.1) y.2 y.2‖ ≤
      ((6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) * R ^ 2 +
          6 * h.metricC 1 * R) * ‖z - y‖ := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  let Kz := MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hz))
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z.1)
  let Ky := MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hy))
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y.1)
  let A : Real := 6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg (h.metricC 1)))
      (mul_nonneg (by norm_num) (h.metricC_nonneg 2))
  have hC1 : 0 ≤ h.metricC 1 := h.metricC_nonneg 1
  have hposNorm : ‖z.1 - y.1‖ ≤ ‖z - y‖ := by
    simpa only [Prod.fst_sub] using norm_fst_le (z - y)
  have hvelNorm : ‖z.2 - y.2‖ ≤ ‖z - y‖ := by
    simpa only [Prod.snd_sub] using norm_snd_le (z - y)
  have hpos : ‖Kz z.2 z.2 - Ky z.2 z.2‖ ≤
      A * R ^ 2 * ‖z - y‖ := by
    have hraw := h.koszulVec_lip_on k x hrMetric hrExp hz hy z.2 z.2
    calc
      ‖Kz z.2 z.2 - Ky z.2 z.2‖ ≤
          A * ‖z.1 - y.1‖ * ‖z.2‖ * ‖z.2‖ := by
        simpa only [Kz, Ky, A] using hraw
      _ ≤ A * ‖z - y‖ * R * R := by gcongr
      _ = A * R ^ 2 * ‖z - y‖ := by ring
  have hvel : ‖Ky z.2 z.2 - Ky y.2 y.2‖ ≤
      6 * h.metricC 1 * R * ‖z - y‖ := by
    have hraw := MetricKoszul.koszulVec_diag_le
      ((h.metric_equiv k x).coercive (hrMetric hy))
      (c := (1 / 2 : Real)) (by norm_num)
      (fun u ↦ by
        simpa [pow_two, mul_assoc] using (h.metric_equiv k x y.1 (hrMetric hy) u).1)
      (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y.1)
      (C := h.metricC 1) hC1 (h.fderiv_apply_le k x (hrMetric hy)) z.2 y.2
    norm_num at hraw
    calc
      ‖Ky z.2 z.2 - Ky y.2 y.2‖ ≤
          2 * ((3 / 2 : Real) * h.metricC 1 *
            (‖z.2‖ + ‖y.2‖) * ‖z.2 - y.2‖) := by
        simpa only [Ky] using hraw
      _ = 3 * h.metricC 1 * (‖z.2‖ + ‖y.2‖) * ‖z.2 - y.2‖ := by ring
      _ ≤ 3 * h.metricC 1 * (R + R) * ‖z - y‖ := by gcongr
      _ = 6 * h.metricC 1 * R * ‖z - y‖ := by ring
  have hsplit : Kz z.2 z.2 - Ky y.2 y.2 =
      (Kz z.2 z.2 - Ky z.2 z.2) + (Ky z.2 z.2 - Ky y.2 y.2) := by
    abel
  rw [hsplit]
  calc
    ‖(Kz z.2 z.2 - Ky z.2 z.2) + (Ky z.2 z.2 - Ky y.2 y.2)‖ ≤
        ‖Kz z.2 z.2 - Ky z.2 z.2‖ + ‖Ky z.2 z.2 - Ky y.2 y.2‖ :=
      norm_add_le _ _
    _ ≤ A * R ^ 2 * ‖z - y‖ + 6 * h.metricC 1 * R * ‖z - y‖ :=
      add_le_add hpos hvel
    _ = (A * R ^ 2 + 6 * h.metricC 1 * R) * ‖z - y‖ := by ring
    _ = ((6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) * R ^ 2 +
          6 * h.metricC 1 * R) * ‖z - y‖ := by rfl


theorem koszulAccel_lip_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M)
    (hsub :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) (h.radius k x) ⊆
        Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj k).metric x))
    {z y : E × E} {R : Real} (hR : 0 ≤ R)
    (hz : z.1 ∈ Metric.ball (0 : E) (h.radius k x))
    (hy : y.1 ∈ Metric.ball (0 : E) (h.radius k x))
    (hzv : ‖z.2‖ ≤ R) (hyv : ‖y.2‖ ≤ R) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z.1) z.2 z.2 -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hy)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y.1) y.2 y.2‖ ≤
      ((6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) * R ^ 2 +
          6 * h.metricC 1 * R) * ‖z - y‖ := by
  simpa using h.koszulAccel_lip_on k x (fun _ hz' ↦ hz') hsub hR hz hy hzv hyv


def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) (f : Nat -> Nat) :
    NormalCoordMetricBoundInput (I := I) (X.subseq f) where
  metricC := h.metricC
  metricC_nonneg := h.metricC_nonneg
  radius := fun k x => h.radius (f k) x
  radius_pos := by
    intro k x
    exact h.radius_pos (f k) x
  metric_equiv := by
    intro k x
    simpa [PointedRiemannianSeq.subseq] using h.metric_equiv (f k) x
  metric_deriv := by
    intro k p x
    simpa [PointedRiemannianSeq.subseq] using h.metric_deriv (f k) p x

end NormalCoordMetricBoundInput













section NormalChartInftySmooth

open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space (TangentBundle I M)]







theorem normalChartAt_contMDiffAt_infty
    (g : SmoothRiemannianMetric I M) (p : M) {v₀ : E}
    (hv₀ : ‖v₀‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (normalChartAt (I := I) g p)
      (expMap (I := I) g p (show TangentSpace I p from v₀)) := by
  classical
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  set fexp : E → M := fun v => (expMap (I := I) g p (show TangentSpace I p from v)) with hfexp
  set q : M := fexp v₀ with hq
  set χ : M → E := ⇑(extChartAt I q) with hχ

  have hf_cd : ContMDiffAt 𝓘(ℝ, E) I ∞ fexp v₀ :=
    expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p hv₀

  have hmem_ball : v₀ ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv₀
  have hf_diffeo : IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1 fexp v₀ :=
    exp_isLocalDiffeomorphOn_ball (I := I) g p (le_refl _) ⟨v₀, hmem_ball⟩

  have hD1_inv : (mfderiv 𝓘(ℝ, E) I fexp v₀).IsInvertible :=
    ⟨hf_diffeo.mfderivToContinuousLinearEquiv one_ne_zero,
      hf_diffeo.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
  have hD2_inv : (mfderiv I 𝓘(ℝ, E) χ q).IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source q)

  have hχ_cd : ContMDiffAt I 𝓘(ℝ, E) ∞ χ q := contMDiffAt_extChartAt (I := I) (x := q)
  have hF_cd : ContDiffAt ℝ ∞ (χ ∘ fexp) v₀ := (hχ_cd.comp v₀ hf_cd).contDiffAt
  have h1 : HasMFDerivAt 𝓘(ℝ, E) I fexp v₀ (mfderiv 𝓘(ℝ, E) I fexp v₀) :=
    (hf_cd.mdifferentiableAt hne).hasMFDerivAt
  have h2 : HasMFDerivAt I 𝓘(ℝ, E) χ q (mfderiv I 𝓘(ℝ, E) χ q) :=
    (hχ_cd.mdifferentiableAt hne).hasMFDerivAt
  have hF_mfd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (χ ∘ fexp) v₀
      ((mfderiv I 𝓘(ℝ, E) χ q).comp (mfderiv 𝓘(ℝ, E) I fexp v₀)) := h2.comp v₀ h1


  have hF_fderiv0 := hasMFDerivAt_iff_hasFDerivAt.mp hF_mfd
  have hfd_inv : (fderiv ℝ (χ ∘ fexp) v₀).IsInvertible := by
    rw [hF_fderiv0.fderiv]; exact hD2_inv.comp hD1_inv
  obtain ⟨e, he⟩ := hfd_inv
  have hF_fderiv : HasFDerivAt (χ ∘ fexp) (e : E →L[ℝ] E) v₀ := by
    rw [he]; exact hF_fderiv0.differentiableAt.hasFDerivAt

  have hinv := hF_cd.to_localInverse hF_fderiv hne

  set Φ : OpenPartialHomeomorph E E :=
    hF_cd.toOpenPartialHomeomorph (χ ∘ fexp) hF_fderiv hne with hΦ
  have hloc_eq : hF_cd.localInverse hF_fderiv hne = Φ.symm := rfl
  rw [hloc_eq] at hinv

  have hv₀_Φsrc : v₀ ∈ Φ.source :=
    hF_cd.mem_toOpenPartialHomeomorph_source hF_fderiv hne
  have hv₀_src : v₀ ∈ (expMapDiffeo (I := I) g p).source := by
    have h := ball_subset_normalChartAt_target (I := I) g p hv₀
    rwa [normalChartAt_target_eq] at h
  have hq_tgt : q ∈ (expMapDiffeo (I := I) g p).target := by
    have hev : expMapDiffeo (I := I) g p v₀ = q := by
      rw [expMapDiffeo_apply_eq (I := I) g p hv₀_src]
    rw [← hev]; exact (expMapDiffeo (I := I) g p).map_source hv₀_src

  have hsymm_cm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Φ.symm (χ q) :=
    (contMDiffAt_iff_contDiffAt).mpr hinv
  have hcomp : ContMDiffAt I 𝓘(ℝ, E) ∞ (Φ.symm ∘ χ) q := hsymm_cm.comp q hχ_cd

  have hΦcoe : (Φ : E → E) = χ ∘ fexp :=
    hF_cd.toOpenPartialHomeomorph_coe hF_fderiv hne
  have hncq : normalChartAt (I := I) g p q = v₀ := by
    have hv₀_nctgt : v₀ ∈ (normalChartAt (I := I) g p).target := by
      rw [normalChartAt_target_eq]; exact hv₀_src
    have hq_eq : q = (normalChartAt (I := I) g p).symm v₀ := by
      rw [normalChartAt_symm_apply (I := I) g p hv₀_nctgt]
    rw [hq_eq]; exact normalChartAt_right_inv (I := I) g p hv₀_nctgt
  have hq_src : q ∈ (normalChartAt (I := I) g p).source := by
    rw [normalChartAt_source_eq]; exact hq_tgt
  have heqEv : normalChartAt (I := I) g p =ᶠ[nhds q] (Φ.symm ∘ χ) := by
    have hUopen : IsOpen ((normalChartAt (I := I) g p).source ∩
        normalChartAt (I := I) g p ⁻¹' Φ.source) :=
      ((normalChartAt_contMDiffOn (I := I) g p).continuousOn).isOpen_inter_preimage
        (normalChartAt (I := I) g p).open_source Φ.open_source
    have hqU : q ∈ (normalChartAt (I := I) g p).source ∩
        normalChartAt (I := I) g p ⁻¹' Φ.source :=
      ⟨hq_src, by rw [Set.mem_preimage, hncq]; exact hv₀_Φsrc⟩
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hqU) (fun q' hq' => ?_)
    obtain ⟨hq'_src, hq'_pre⟩ := hq'
    rw [Set.mem_preimage] at hq'_pre
    set v' := normalChartAt (I := I) g p q' with hv'def
    have hv'_symmsrc : v' ∈ (normalChartAt (I := I) g p).symm.source :=
      (normalChartAt (I := I) g p).map_source hq'_src
    have hfv' : fexp v' = q' := by
      show (expMap (I := I) g p (show TangentSpace I p from v') : M) = q'
      rw [← normalChartAt_symm_apply (I := I) g p hv'_symmsrc]
      exact normalChartAt_left_inv (I := I) g p hq'_src
    have hΦv' : Φ v' = χ q' := by
      have hc : (χ ∘ fexp) v' = χ q' := by rw [Function.comp_apply, hfv']
      rw [hΦcoe]; exact hc
    show normalChartAt (I := I) g p q' = (Φ.symm ∘ χ) q'
    rw [Function.comp_apply, ← hΦv', Φ.left_inv hq'_pre]
  exact hcomp.congr_of_eventuallyEq heqEv




theorem normalChartAt_contMDiffOn_infty
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (normalChartAt (I := I) g p)
      ((fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) ''
        Metric.ball (0 : E) (expMapC2Radius (I := I) g p)) := by
  rintro q ⟨v₀, hv₀ball, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv₀ball
  exact (normalChartAt_contMDiffAt_infty (I := I) g p hv₀ball).contMDiffWithinAt

end NormalChartInftySmooth

end HCGCompactness
end DifferentialGeometry
