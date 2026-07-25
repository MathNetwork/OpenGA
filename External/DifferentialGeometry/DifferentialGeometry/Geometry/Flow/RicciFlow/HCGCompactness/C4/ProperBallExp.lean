import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PointedEmetric








noncomputable section

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]




theorem properBall_to_exp
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (ms : MetricSpace Y.M)
    (hreal : ∀ x y : Y.M,
      (letI : EMetricSpace Y.M := Y.emetricSpace
       edist x y) =
      ENNReal.ofReal (letI : MetricSpace Y.M := ms
       dist x y))
    {c : Y.M} {R σ : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c)
    (hσ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R / Real.sqrt (gpCoerciveConst (I := I) Y.metric c) < σ) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := ms
    Metric.closedBall c R ⊆
      (fun v : E => expMap (I := I) Y.metric c
        (show TangentSpace I c from v)) '' Metric.ball 0 σ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  intro q hq
  have hdistLe : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    have h := hreal c q
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]
    exact ENNReal.ofReal_ne_top
  have hsmall :
      (riemannianEDist I c q).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact hdistLe.trans_lt hR
  obtain ⟨v, _hvTarget, _hvDomain, hvLen, hqEq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  refine ⟨v, ?_, hqEq.symm⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hcoerc : 0 < gpCoerciveConst (I := I) Y.metric c :=
    gpCoerciveConst_pos (I := I) Y.metric c
  have hsqrtPos : 0 < Real.sqrt (gpCoerciveConst (I := I) Y.metric c) :=
    Real.sqrt_pos.mpr hcoerc
  have hcoercLe :
      gpCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2 ≤ Y.metric.inner c v v :=
    gpCoerciveConst_le (I := I) Y.metric c v
  have hsqrtLe :
      Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ ≤
        Real.sqrt (Y.metric.inner c v v) := by
    have hrw :
        Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ =
          Real.sqrt (gpCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2) := by
      rw [Real.sqrt_mul hcoerc.le, Real.sqrt_sq (norm_nonneg v)]
    rw [hrw]
    exact Real.sqrt_le_sqrt hcoercLe
  have hmetricLe : Real.sqrt (Y.metric.inner c v v) ≤ R := by
    rw [hvLen, hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact hdistLe
  have hnormLe :
      ‖v‖ ≤ R / Real.sqrt (gpCoerciveConst (I := I) Y.metric c) := by
    rw [le_div_iff₀ hsqrtPos]
    calc
      ‖v‖ * Real.sqrt (gpCoerciveConst (I := I) Y.metric c) =
          Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ := by ring
      _ ≤ Real.sqrt (Y.metric.inner c v v) := hsqrtLe
      _ ≤ R := hmetricLe
  exact hnormLe.trans_lt hσ




theorem exp_sigma_maps
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (ms : MetricSpace Y.M)
    (hreal : ∀ p q : Y.M,
      (letI : EMetricSpace Y.M := Y.emetricSpace
       edist p q) =
      ENNReal.ofReal (letI : MetricSpace Y.M := ms
       dist p q))
    (x : Y.M) {lam : Real}
    (hmetric :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      ∀ z : E, Y.metric.inner x z z ≤ 2 * ‖z‖ ^ 2)
    (hC2 :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      8 * lam ≤ expMapC2Radius (I := I) Y.metric x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := ms
    Set.MapsTo
      (fun z : E => expMap (I := I) Y.metric x (show TangentSpace I x from z))
      (Metric.ball 0 (8 * lam)) (Metric.ball x (16 * lam)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := ms
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ y : Y.M, ∀ v : TangentSpace I y,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner y v v)) := by
    intro y v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  rw [Metric.mem_ball]
  have hzC2 : ‖z‖ < expMapC2Radius (I := I) Y.metric x := hz.trans_le hC2
  have hedLe := edist_exp_le_radius (I := I) Y.metric x z hEnorm hzC2
  have hed :
      riemannianEDist I x
          (expMap (I := I) Y.metric x (show TangentSpace I x from z)) =
        ENNReal.ofReal
          (dist x (expMap (I := I) Y.metric x (show TangentSpace I x from z))) := by
    have h := hreal x
      (expMap (I := I) Y.metric x (show TangentSpace I x from z))
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hdistSqrt :
      dist x (expMap (I := I) Y.metric x (show TangentSpace I x from z)) ≤
        Real.sqrt (Y.metric.inner x z z) := by
    rw [hed] at hedLe
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hedLe
  have hsqrtMetric : Real.sqrt (Y.metric.inner x z z) ≤ Real.sqrt 2 * ‖z‖ := by
    calc
      Real.sqrt (Y.metric.inner x z z) ≤ Real.sqrt (2 * ‖z‖ ^ 2) :=
        Real.sqrt_le_sqrt (hmetric z)
      _ = Real.sqrt 2 * ‖z‖ := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2),
          Real.sqrt_sq (norm_nonneg z)]
  have hsqrtTwo : Real.sqrt 2 < (2 : Real) := by
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)
    have hsqrtNonneg := Real.sqrt_nonneg (2 : Real)
    nlinarith
  have hrootNorm : Real.sqrt 2 * ‖z‖ ≤ 2 * ‖z‖ :=
    mul_le_mul_of_nonneg_right hsqrtTwo.le (norm_nonneg z)
  calc
    dist (expMap (I := I) Y.metric x (show TangentSpace I x from z)) x =
        dist x (expMap (I := I) Y.metric x (show TangentSpace I x from z)) := dist_comm _ _
    _ ≤ Real.sqrt (Y.metric.inner x z z) := hdistSqrt
    _ ≤ Real.sqrt 2 * ‖z‖ := hsqrtMetric
    _ ≤ 2 * ‖z‖ := hrootNorm
    _ < 16 * lam := by nlinarith

end HCGCompactness
end DifferentialGeometry
