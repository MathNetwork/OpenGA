import DifferentialGeometry.Analysis.Calculus.MapConvergenceDeriv
import DifferentialGeometry.Geometry.Exponential.NormalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhaseEndpoint

set_option autoImplicit false









noncomputable section

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace NormalRadiusProfile




theorem diag_end_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real)
    (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {Q : Set (E × E)} (hQ : IsOpen Q)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf)
    {Φ : Nat → (E × E) → Real → E × E}
    {ΦInf : (E × E) → Real → E × E}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    (hΦ : ∀ n z, z ∈ Q →
      Φ n z 0 = z ∧
      IsIntegralCurveOn (Φ n z)
        (fun _ ↦ MetricKoszul.metricSpray
          (normalCoordMetric (I := I) (X.obj n) (c n)))
        (Icc 0 1))
    (hΦInf : ∀ z, z ∈ Q →
      ΦInf z 0 = z ∧
      IsIntegralCurveOn (ΦInf z)
        (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1))
    (hstay : ∀ n z, z ∈ Q → ∀ t ∈ Icc (0 : Real) 1,
      (Φ n z t).1 ∈ Metric.ball 0 (h.phaseRadius R))
    (hstayInf : ∀ z, z ∈ Q → ∀ t ∈ Icc (0 : Real) 1,
      (ΦInf z t).1 ∈ Metric.ball 0 (h.phaseRadius R))
    (he : ∀ n, (e n : E × E → E × E) =
      fun z ↦ (z.1, (Φ n z 1).1)) :
    MapCInfConvOnCompacts Q
      (fun n ↦ (e n : E × E → E × E))
      (fun z ↦ (z.1, (ΦInf z 1).1)) := by
  have hg_cd : ∀ n, ContDiffOn Real ∞
      (normalCoordMetric (I := I) (X.obj n) (c n))
      (Metric.ball 0 (h.phaseRadius R)) := by
    intro n
    letI : TopologicalSpace (X.obj n).M := (X.obj n).topology
    letI : ChartedSpace H (X.obj n).M := (X.obj n).charted
    letI : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
    letI : T2Space (TangentBundle I (X.obj n).M) :=
      (X.obj n).t2TangentBundle
    apply (normalCoordMetric_contDiffOn_expBall (I := I) (X.obj n) (c n)).mono
    exact (h.phaseRadius_exp (hc n)).trans (Metric.ball_subset_ball (by
      nlinarith [Geometry.Riemannian.expMapC2Radius_pos
        (I := I) (X.obj n).metric (c n)]))
  have hg_co : ∀ n z, z ∈ Metric.ball (0 : E) (h.phaseRadius R) →
      IsCoercive (normalCoordMetric (I := I) (X.obj n) (c n) z) := by
    intro n z hz
    exact (hb.metric_equiv n (c n)).coercive (h.phaseRadius_metric (hc n) hz)
  have hgInf_co : ∀ z, z ∈ Metric.ball (0 : E) (h.phaseRadius R) →
      IsCoercive (gInf z) := by
    intro z hz
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using hgInf_lo z hz v
  have hconv := normalDiag_end_conv
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) (h.phaseRadius R)))
    hQ hg_cd hgInf_cd hg_co hgInf_co hg_conv hΦ hΦInf hstay hstayInf
  exact hconv.congr hQ
    (fun n z _hz ↦ congrFun (he n) z)
    (fun _z _hz ↦ rfl)

end NormalRadiusProfile
end HCGCompactness
end DifferentialGeometry
