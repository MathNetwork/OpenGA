import DifferentialGeometry.Analysis.ODE.PhaseFlowSmallness
import DifferentialGeometry.Analysis.ODE.PhaseEndpointInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhase

set_option autoImplicit false










noncomputable section

universe u uE uH

open Filter Set Topology
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace NormalRadiusProfile



def phaseRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) : Real :=
  h.ratio * hd.mu R / 4


theorem phaseRadius_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) : 0 < h.phaseRadius R := by
  dsimp only [phaseRadius]
  exact div_pos (h.floor_pos R) (by norm_num)



theorem phaseRadius_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    Metric.ball (0 : E) (h.phaseRadius R) ⊆
      Metric.ball (0 : E) (hb.radius k x) := by
  apply Metric.ball_subset_ball
  calc
    h.phaseRadius R ≤ h.ratio * hd.mu R := by
      dsimp only [phaseRadius]
      nlinarith [h.floor_pos R]
    _ ≤ hb.radius k x := h.floor_le_radius hx



theorem phaseRadius_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    Metric.ball (0 : E) (h.phaseRadius R) ⊆ Metric.ball (0 : E)
      (Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x / 4) := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  apply Metric.ball_subset_ball
  dsimp only [phaseRadius]
  exact div_le_div_of_nonneg_right (h.floor_le_exp hx) (by norm_num)

end NormalRadiusProfile



omit [NeZero (Module.finrank Real E)] in
@[simp] theorem normalPhaseK_zero
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) : normalPhaseK h 0 = 0 := by
  apply NNReal.eq
  simp [normalPhaseK]
  rfl



omit [NeZero (Module.finrank Real E)] in
theorem normalPhaseK_cont
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) :
    Continuous (normalPhaseK h) := by
  unfold normalPhaseK
  apply Continuous.subtype_mk
  fun_prop



omit [NeZero (Module.finrank Real E)] in
theorem normalPhaseK_lim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) :
    Tendsto (normalPhaseK h) (nhds 0) (nhds 0) := by
  have hcont : Tendsto (normalPhaseK h) (nhds (0 : NNReal))
      (nhds (normalPhaseK h 0)) := (normalPhaseK_cont h).continuousAt
  simpa using hcont



omit [NeZero (Module.finrank Real E)] in
theorem normalPhaseErr_lim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) :
    Tendsto (fun R ↦ PhaseFlow.phaseErr (normalPhaseK h R))
      (nhds 0) (nhds 0) :=
  PhaseFlow.phaseErr_tendsto.comp (normalPhaseK_lim h)



omit [NeZero (Module.finrank Real E)] in
theorem normalPhaseErr_lt_ev
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    {eps : NNReal} (heps : 0 < eps) :
    ∀ᶠ R in nhds 0, PhaseFlow.phaseErr (normalPhaseK h R) < eps :=
  normalPhaseErr_lim h (Iio_mem_nhds heps)





omit [NeZero (Module.finrank Real E)] in
theorem exists_normal_q_lt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    {r : Real} (hr : 0 < r) {eps : NNReal} (heps : 0 < eps) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < r ∧
      3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps := by
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps :=
    htwo (normalPhaseErr_lt_ev (I := I) h heps)
  obtain ⟨δ, hδ, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := h.metricC 1
  have hC : 0 ≤ C := h.metricC_nonneg 1
  let accelBound : Real := 1 / (24 * (C + 1))
  have hden : 0 < 24 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccelBound : 0 < accelBound := one_div_pos.mpr hden
  let qReal : Real := min (δ / 4) (min (r / 8) accelBound)
  have hqReal : 0 < qReal := by
    dsimp only [qReal]
    exact lt_min (div_pos hδ (by norm_num))
      (lt_min (div_pos hr (by norm_num)) haccelBound)
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have hqδ : qReal ≤ δ / 4 := min_le_left _ _
  have hqRadius : qReal ≤ r / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hqAccel : qReal ≤ accelBound :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqBall : q ∈ Metric.ball (0 : NNReal) δ := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < δ
    rw [sub_zero, abs_of_pos hqReal]
    exact hqδ.trans_lt (div_lt_self hδ (by norm_num))
  have herrQ : PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps :=
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
  refine ⟨q, ?_, ?_, ?_, herrQ⟩
  · exact_mod_cast hqReal
  · simpa only [q, NNReal.coe_mk] using hqRadius'
  · change 3 * C * (2 * qReal) ^ 2 ≤ qReal
    nlinarith

namespace NormalRadiusProfile





theorem exists_phase_q
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real)
    {eps : NNReal} (heps : 0 < eps) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < h.phaseRadius R ∧
      3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < eps :=
  exists_normal_q_lt (I := I) hb (h.phaseRadius_pos R) heps




theorem exists_phase_scale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aq aδ : Real,
      0 < aq ∧ 0 < aδ ∧
      ∀ R, 0 ≤ R →
        ∃ q : NNReal,
          (q : Real) = aq * hd.mu R ∧
          6 * (q : Real) < h.phaseRadius R ∧
          3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < 1 / 24 ∧
          aδ * hd.mu R ≤
            ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
              ((q : Real) / 2) := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  have hT : 0 < T := PhaseFlow.freeDiagInv_pos (E := E)
  have hTReal : (0 : Real) < T := by exact_mod_cast hT
  let epsInv : NNReal := T / (48 * (N + 1))
  have hepsInv : 0 < epsInv := by
    dsimp only [epsInv]
    exact div_pos hT (mul_pos (by norm_num) (by positivity))
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < epsInv :=
    htwo (normalPhaseErr_lt_ev (I := I) hb hepsInv)
  obtain ⟨eps, heps, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := hb.metricC 1
  have hC : 0 ≤ C := hb.metricC_nonneg 1
  have hμ0 : 0 < hd.mu 0 := hd.mu_pos 0
  let accelBound : Real := 1 / (36 * (C + 1))
  have hden : 0 < 36 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccel : 0 < accelBound := one_div_pos.mpr hden
  let aq : Real := min (h.ratio / 48)
    (min (eps / (2 * hd.mu 0)) (accelBound / hd.mu 0))
  have haq : 0 < aq := by
    dsimp only [aq]
    exact lt_min (div_pos h.ratio_pos (by norm_num))
      (lt_min (div_pos heps (mul_pos (by norm_num) hμ0))
        (div_pos haccel hμ0))
  let aδ : Real := (T : Real) * aq / 4
  have haδ : 0 < aδ := by
    dsimp only [aδ]
    exact div_pos (mul_pos hTReal haq) (by norm_num)
  refine ⟨aq, aδ, haq, haδ, ?_⟩
  intro R hR
  have hμR : 0 < hd.mu R := hd.mu_pos R
  have hμle : hd.mu R ≤ hd.mu 0 := hd.mu_antitone hR
  let qReal : Real := aq * hd.mu R
  have hqReal : 0 < qReal := mul_pos haq hμR
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have haqRatio : aq ≤ h.ratio / 48 := min_le_left _ _
  have haqEps : aq ≤ eps / (2 * hd.mu 0) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have haqAccel : aq ≤ accelBound / hd.mu 0 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqEps : qReal ≤ eps / 2 := by
    calc
      qReal = aq * hd.mu R := rfl
      _ ≤ aq * hd.mu 0 := mul_le_mul_of_nonneg_left hμle haq.le
      _ ≤ (eps / (2 * hd.mu 0)) * hd.mu 0 :=
        mul_le_mul_of_nonneg_right haqEps hμ0.le
      _ = eps / 2 := by field_simp [ne_of_gt hμ0]
  have hqAccel : qReal ≤ accelBound := by
    calc
      qReal = aq * hd.mu R := rfl
      _ ≤ aq * hd.mu 0 := mul_le_mul_of_nonneg_left hμle haq.le
      _ ≤ (accelBound / hd.mu 0) * hd.mu 0 :=
        mul_le_mul_of_nonneg_right haqAccel hμ0.le
      _ = accelBound := by field_simp [ne_of_gt hμ0]
  have hqBall : q ∈ Metric.ball (0 : NNReal) eps := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < eps
    rw [sub_zero, abs_of_pos hqReal]
    exact hqEps.trans_lt (half_lt_self heps)
  have herrQ : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < epsInv :=
    herr q hqBall
  have hN1 : (1 : NNReal) ≤ N + 1 := by
    exact le_add_of_nonneg_left N.2
  have hden_ge : (2 : NNReal) ≤ 48 * (N + 1) := by
    calc
      (2 : NNReal) = 2 * 1 := by norm_num
      _ ≤ 2 * (N + 1) := mul_le_mul_of_nonneg_left hN1 (by norm_num)
      _ ≤ 48 * (N + 1) :=
        mul_le_mul_of_nonneg_right (by norm_num) (N + 1).2
  have heps_le : epsInv ≤ T / 2 := by
    dsimp only [epsInv]
    exact div_le_div_of_nonneg_left T.2 (by norm_num) hden_ge
  have herrHalf : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T / 2 :=
    herrQ.trans_le heps_le
  have hqRadius : 6 * (q : Real) < h.phaseRadius R := by
    have haRatio : 6 * aq < h.ratio / 4 := by
      nlinarith [h.ratio_pos]
    calc
      6 * (q : Real) = (6 * aq) * hd.mu R := by
        change 6 * qReal = _
        dsimp only [qReal]
        ring
      _ < (h.ratio / 4) * hd.mu R := mul_lt_mul_of_pos_right haRatio hμR
      _ = h.phaseRadius R := by
        dsimp only [phaseRadius]
        ring
  have hqProd : qReal * (36 * (C + 1)) ≤ 1 := by
    calc
      qReal * (36 * (C + 1)) ≤ accelBound * (36 * (C + 1)) :=
        mul_le_mul_of_nonneg_right hqAccel hden.le
      _ = 1 := by
        dsimp only [accelBound]
        field_simp [ne_of_gt hden]
  have hlinear : 18 * C * qReal ≤ 1 := by
    nlinarith [mul_nonneg hC hqReal.le]
  have hmul : 0 ≤ qReal * (1 - 18 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hlinear)
  have hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real) := by
    change 3 * C * (2 * qReal) ^ 2 ≤ (2 / 3 : Real) * qReal
    nlinarith
  have herrOut : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T := by
    calc
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T / 2 := herrHalf
      _ < T := by exact_mod_cast (half_lt_self hTReal)
  have hinvErr :
      N * (T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < 1 / 24 := by
    let c : NNReal := PhaseFlow.phaseErr (normalPhaseK hb (2 * q))
    have hdenInv : 0 < 48 * (N + 1) :=
      mul_pos (by norm_num) (by positivity)
    have hsmall : c * (48 * (N + 1)) < T := by
      apply (lt_div_iff₀ hdenInv).mp
      simpa only [c, epsInv] using herrQ
    have hfac : 24 * N + 1 ≤ 48 * (N + 1) := by
      nlinarith [N.2]
    have hcFac : c * (24 * N + 1) < T :=
      (mul_le_mul_of_nonneg_left hfac c.2).trans_lt hsmall
    have honeFac : (1 : NNReal) ≤ 24 * N + 1 := by
      exact le_add_of_nonneg_left (mul_nonneg (by norm_num) N.2)
    have hct : c < T := by
      calc
        c = c * 1 := by rw [mul_one]
        _ ≤ c * (24 * N + 1) :=
          mul_le_mul_of_nonneg_left honeFac c.2
        _ < T := hcFac
    have hdiff : 0 < T - c := tsub_pos_iff_lt.mpr hct
    have hnum : 24 * (N * c) < T - c := by
      rw [lt_tsub_iff_right]
      calc
        24 * (N * c) + c = c * (24 * N + 1) := by ring
        _ < T := hcFac
    rw [show N * (T - c)⁻¹ * c = (N * c) / (T - c) by
      rw [div_eq_mul_inv]
      ring]
    rw [div_lt_iff₀ hdiff]
    rw [show (1 / 24 : NNReal) * (T - c) = (T - c) / 24 by ring]
    exact (lt_div_iff₀ (by norm_num : (0 : NNReal) < 24)).2 <| by
      simpa only [mul_comm] using hnum
  have herrReal :
      (PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : Real) < (T : Real) / 2 := by
    exact_mod_cast herrHalf
  have hmargin : (T : Real) / 2 ≤
      ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) := by
    rw [NNReal.coe_sub herrOut.le]
    linarith
  have hδlower : aδ * hd.mu R ≤
      ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) := by
    calc
      aδ * hd.mu R = ((T : Real) / 2) * (qReal / 2) := by
        dsimp only [aδ, qReal]
        ring
      _ ≤ ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
          (qReal / 2) :=
        mul_le_mul_of_nonneg_right hmargin (div_nonneg hqReal.le (by norm_num))
      _ = ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
          ((q : Real) / 2) := rfl
  exact ⟨q, rfl, hqRadius, hqAcc, herrOut, hinvErr, hδlower⟩

end NormalRadiusProfile

end HCGCompactness
end DifferentialGeometry
