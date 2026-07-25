import DifferentialGeometry.Analysis.ODE.PhaseEndpointInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhaseSmallness








noncomputable section

universe u uE uH

open Filter Set Topology Metric
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



theorem exists_normal_q
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) {r : Real} (hr : 0 < r) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < r ∧
      3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let threshold : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹
  have hthreshold : 0 < threshold := PhaseFlow.freeDiagInv_pos (E := E)
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < threshold :=
    htwo (normalPhaseErr_lt_ev (I := I) h hthreshold)
  obtain ⟨eps, heps, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := h.metricC 1
  have hC : 0 ≤ C := h.metricC_nonneg 1
  let accelBound : Real := 1 / (24 * (C + 1))
  have hden : 0 < 24 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccelBound : 0 < accelBound := one_div_pos.mpr hden
  let qReal : Real := min (eps / 4) (min (r / 8) accelBound)
  have hqReal : 0 < qReal := by
    dsimp only [qReal]
    exact lt_min (div_pos heps (by norm_num))
      (lt_min (div_pos hr (by norm_num)) haccelBound)
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have hqEps : qReal ≤ eps / 4 := by
    exact min_le_left _ _
  have hqRadius : qReal ≤ r / 8 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hqAccel : qReal ≤ accelBound := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hqBall : q ∈ Metric.ball (0 : NNReal) eps := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < eps
    rw [sub_zero, abs_of_pos hqReal]
    exact hqEps.trans_lt (div_lt_self heps (by norm_num))
  have herrQ : PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < threshold :=
    herr q hqBall
  have hqRadius' : 4 * qReal < r := by
    nlinarith
  have hqProd : qReal * (24 * (C + 1)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [accelBound, one_div] using hqAccel
  have hlinear : 12 * C * qReal ≤ 1 := by
    nlinarith
  have hmul : 0 ≤ qReal * (1 - 12 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hlinear)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hqReal
  · simpa only [q, NNReal.coe_mk] using hqRadius'
  · change 3 * C * (2 * qReal) ^ 2 ≤ qReal
    nlinarith
  · simpa only [threshold] using herrQ



theorem exists_normal_inv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real} (hr : 0 < r)
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x / 4)) :
    ∃ (q : NNReal) (Φ : (E × E) → Real → E × E)
        (e : OpenPartialHomeomorph (E × E) (E × E)) (δ : Real),
      0 < q ∧
      4 * (q : Real) < r ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ContinuousOn (Φ z) (Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ico 0 1,
        HasDerivWithinAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
          (Ici t) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc 0 1,
        Φ z t ∈ normalPhaseBox r (2 * q)) ∧
      0 < δ ∧
      e.source = Metric.ball (0 : E × E) q ∧
      (e : E × E → E × E) = (fun z ↦ (z.1, (Φ z 1).1)) ∧
      Metric.closedBall ((fun z ↦ (z.1, (Φ z 1).1)) 0) δ ⊆ e.target := by
  obtain ⟨q, hq, hqRadius, hqAccel, herr⟩ :=
    exists_normal_q (I := I) h hr
  obtain ⟨Φ, hΦ0, hΦcont, hΦderiv, hΦbox, happrox⟩ :=
    exists_normalFlow (I := I) h k x hrMetric hrQuarter q hq hqRadius hqAccel
  obtain ⟨e, δ, hδ, hsource, hcoe, htarget, _⟩ :=
    PhaseFlow.exists_quant_inv hq happrox herr
  exact ⟨q, Φ, e, δ, hq, hqRadius, hΦ0, hΦcont, hΦderiv, hΦbox,
    hδ, hsource, hcoe, htarget⟩

end HCGCompactness
end DifferentialGeometry
