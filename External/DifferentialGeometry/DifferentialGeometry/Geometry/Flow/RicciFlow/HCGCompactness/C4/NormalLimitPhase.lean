import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhaseConv

set_option autoImplicit false









noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology NNReal

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace NormalRadiusProfile



theorem limit_accel_bounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real)
    (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf)
    (V : NNReal) :
    let aInf : E × E → E := fun z ↦ (MetricKoszul.metricSpray gInf z).2
    LipschitzOnWith (normalPhaseK hb V) aInf
        (normalPhaseBox (h.phaseRadius R) V) ∧
      ∀ z ∈ normalPhaseBox (h.phaseRadius R) V,
        ‖aInf z‖ ≤ 3 * hb.metricC 1 * (V : Real) ^ 2 := by
  let U : Set E := Metric.ball 0 (h.phaseRadius R)
  let g : Nat → E → E →L[Real] E →L[Real] Real :=
    fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)
  let a : Nat → E × E → E :=
    fun n ↦ normalAccel (I := I) (X.obj n) (c n)
  let aInf : E × E → E := fun z ↦ (MetricKoszul.metricSpray gInf z).2
  have hg_cd : ∀ n, ContDiffOn Real ∞ (g n) U := by
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
  have hg_co : ∀ n z, z ∈ U → IsCoercive (g n z) := by
    intro n z hz
    exact (hb.metric_equiv n (c n)).coercive (h.phaseRadius_metric (hc n) hz)
  have hgInf_co : ∀ z, z ∈ U → IsCoercive (gInf z) := by
    intro z hz
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using hgInf_lo z hz v
  have hspray : MapCInfConvOnCompacts (U ×ˢ (Set.univ : Set E))
      (fun n ↦ MetricKoszul.metricSpray (g n))
      (MetricKoszul.metricSpray gInf) :=
    normalGeodesicSpray_conv Metric.isOpen_ball hg_cd hgInf_cd hg_co
      hgInf_co (by simpa only [U, g] using hg_conv)
  have hacc_tendsto : ∀ z ∈ normalPhaseBox (h.phaseRadius R) V,
      Tendsto (fun n ↦ a n z) atTop (nhds (aInf z)) := by
    intro z hz
    have hspray_z := tendsto_of_cInf hspray ⟨hz.1, Set.mem_univ z.2⟩
    have hsnd : Tendsto
        (fun n ↦ (MetricKoszul.metricSpray (g n) z).2) atTop
        (nhds (MetricKoszul.metricSpray gInf z).2) :=
      (continuous_snd.tendsto _).comp hspray_z
    have heq : (fun n ↦ (MetricKoszul.metricSpray (g n) z).2) =
        fun n ↦ a n z := by
      funext n
      letI : TopologicalSpace (X.obj n).M := (X.obj n).topology
      letI : ChartedSpace H (X.obj n).M := (X.obj n).charted
      letI : IsManifold I ∞ (X.obj n).M := (X.obj n).smooth
      letI : SigmaCompactSpace (X.obj n).M := (X.obj n).sigmaCompact
      letI : T2Space (X.obj n).M := (X.obj n).t2
      letI : T2Space (TangentBundle I (X.obj n).M) :=
        (X.obj n).t2TangentBundle
      have hphase := normalPhase_eq_spray (I := I) (X.obj n) (c n) z
        (h.phaseRadius_exp (hc n) hz.1)
        ((hb.metric_equiv n (c n)).coercive
          (h.phaseRadius_metric (hc n) hz.1))
      have hsndEq := congrArg Prod.snd hphase
      simpa only [g, a, PhaseFlow.phaseField] using hsndEq.symm
    rw [heq] at hsnd
    simpa only [aInf] using hsnd
  refine ⟨?_, ?_⟩
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hdist : Tendsto (fun n ↦ dist (a n x) (a n y)) atTop
        (nhds (dist (aInf x) (aInf y))) :=
      (continuous_dist.tendsto (aInf x, aInf y)).comp
        ((hacc_tendsto x hx).prodMk_nhds (hacc_tendsto y hy))
    refine le_of_tendsto hdist (Filter.Eventually.of_forall fun n ↦ ?_)
    have hlip := normalAccel_lip (I := I) hb n (c n)
      (h.phaseRadius_metric (hc n)) (h.phaseRadius_exp (hc n)) V
    rw [lipschitzOnWith_iff_dist_le_mul] at hlip
    simpa only [a] using hlip x hx y hy
  · intro z hz
    have hnorm : Tendsto (fun n ↦ ‖a n z‖) atTop (nhds ‖aInf z‖) :=
      (continuous_norm.tendsto (aInf z)).comp (hacc_tendsto z hz)
    exact le_of_tendsto hnorm (Filter.Eventually.of_forall fun n ↦
      normalAccel_norm (I := I) hb n (c n)
        (h.phaseRadius_metric (hc n)) (h.phaseRadius_exp (hc n)) V z hz)



theorem exists_limit_phase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real)
    (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf)
    (q : NNReal) (hq : 0 < q)
    (hqPos : 4 * (q : Real) < h.phaseRadius R)
    (hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real)) :
    ∃ ΦInf : (E × E) → Real → E × E,
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ΦInf z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        IsIntegralCurveOn (ΦInf z)
          (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ∀ t ∈ Icc (0 : Real) 1,
          (ΦInf z t).1 ∈ Metric.ball 0 (h.phaseRadius R)) ∧
      ΦInf 0 1 = 0 ∧
      ApproximatesLinearOn (fun z ↦ (z.1, (ΦInf z 1).1))
        PhaseFlow.freeDiag (Metric.closedBall (0 : E × E) q)
        (PhaseFlow.phaseErr (normalPhaseK hb (2 * q))) ∧
      ContDiffOn Real ∞ (fun z ↦ (z.1, (ΦInf z 1).1))
        (Metric.ball (0 : E × E) q) := by
  let U : Set E := Metric.ball 0 (h.phaseRadius R)
  let phaseU : Set (E × E) := U ×ˢ (Set.univ : Set E)
  let aInf : E × E → E := fun z ↦ (MetricKoszul.metricSpray gInf z).2
  let P : NNReal := 4 * q
  let V : NNReal := 2 * q
  let half : NNReal := 1 / 2
  let A : NNReal :=
    ⟨3 * hb.metricC 1 * (V : Real) ^ 2,
      mul_nonneg (mul_nonneg (by norm_num) (hb.metricC_nonneg 1))
        (sq_nonneg _)⟩
  have hP : 0 < P := by dsimp only [P]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  obtain ⟨haLipFull, haNormFull⟩ :=
    h.limit_accel_bounds R c hc hgInf_cd hgInf_lo hg_conv V
  have hbox : PhaseFlow.phaseBox (E := E) P V ⊆
      normalPhaseBox (h.phaseRadius R) V := by
    intro z hz
    refine ⟨?_, hz.2⟩
    rw [mem_ball_zero_iff]
    exact hz.1.trans_lt (by simpa only [P, NNReal.coe_mul,
      NNReal.coe_natCast] using hqPos)
  have haLip : LipschitzOnWith (normalPhaseK hb V) aInf
      (PhaseFlow.phaseBox (E := E) P V) := haLipFull.mono hbox
  have haNorm : ∀ z ∈ PhaseFlow.phaseBox (E := E) P V,
      ‖aInf z‖ ≤ (A : Real) := by
    intro z hz
    simpa only [A, NNReal.coe_mk] using haNormFull z (hbox hz)
  have hVP : V ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (2 : Real) * (q : Real) ≤ (1 / 2 : Real) * (4 * (q : Real))
    nlinarith
  have hAV : A ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (1 / 2 : Real) * (2 * (q : Real))
    nlinarith [hqAcc]
  have hhalf : (half : Real) ≤ 1 - (half : Real) := by norm_num [half]
  obtain ⟨ΦInf, hΦ⟩ := PhaseFlow.exists_fenced_sym (E := E)
    hP hV haLip haNorm hVP hAV hhalf
  have hqP : q ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (4 * (q : Real))
    nlinarith [q.coe_nonneg]
  have hqV : q ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (2 * (q : Real))
    nlinarith
  have hscale := PhaseFlow.scale_maps_ball (E := E) hP hV hqP hqV
  have hspec := fun z (hz : z ∈ Metric.closedBall (0 : E × E) q) ↦
    hΦ z (hscale hz)
  have hinit : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ΦInf z 0 = z := fun z hz ↦ (hspec z hz).1
  have hcont : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (ΦInf z) (Icc (-1) 1) := fun z hz ↦ (hspec z hz).2.1
  have hwithin : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Icc (-1 : Real) 1,
        HasDerivWithinAt (ΦInf z)
          (PhaseFlow.phaseField aInf (ΦInf z t)) (Icc (-1) 1) t :=
    fun z hz ↦ (hspec z hz).2.2.1
  have hderiv : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Ioo (-1 : Real) 1,
        HasDerivAt (ΦInf z) (PhaseFlow.phaseField aInf (ΦInf z t)) t :=
    fun z hz ↦ (hspec z hz).2.2.2.1
  have hmem : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Icc (-1 : Real) 1,
        ΦInf z t ∈ PhaseFlow.phaseBox P V :=
    fun z hz ↦ (hspec z hz).2.2.2.2
  have hsmall : Icc (0 : Real) 1 ⊆ Icc (-1) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hcurve : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      IsIntegralCurveOn (ΦInf z)
        (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1) := by
    intro z hz t ht
    have hder := (hwithin z hz t (hsmall ht)).mono hsmall
    simpa only [aInf, PhaseFlow.phaseField, MetricKoszul.metricSpray] using hder
  have hstay : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Icc (0 : Real) 1,
        (ΦInf z t).1 ∈ U := by
    intro z hz t ht
    have hpos := (hmem z hz t (hsmall ht)).1
    simpa only [U, mem_ball_zero_iff] using hpos.trans_lt (by
      simpa only [P, NNReal.coe_mul, NNReal.coe_natCast] using hqPos)
  have hcont01 : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (ΦInf z) (Icc 0 1) :=
    fun z hz ↦ (hcont z hz).mono hsmall
  have hderiv01 : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Ico (0 : Real) 1,
        HasDerivWithinAt (ΦInf z)
          (PhaseFlow.phaseField aInf (ΦInf z t)) (Ici t) t := by
    intro z hz t ht
    exact (hderiv z hz t ⟨by linarith [ht.1], ht.2⟩).hasDerivWithinAt
  have happ := PhaseFlow.phase_diag_approx haLip hinit hcont01 hderiv01
    (fun z hz t ht ↦ hmem z hz t (hsmall ⟨ht.1, ht.2.le⟩))
  have hzeroMem : (0 : E × E) ∈ Metric.closedBall (0 : E × E) q := by
    simp only [Metric.mem_closedBall, dist_self, q.coe_nonneg]
  have hzeroCurve : IsIntegralCurveOn (fun _ : Real ↦ (0 : E × E))
      (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1) := by
    intro t _ht
    simpa [MetricKoszul.metricSpray] using
      (hasDerivWithinAt_const (x := t) (s := Icc (0 : Real) 1)
        (c := (0 : E × E)))
  have hspraySmooth : ContDiffOn Real ∞ (MetricKoszul.metricSpray gInf)
      phaseU := by
    apply MetricKoszul.metricSpray_contDiffOn Metric.isOpen_ball hgInf_cd
    intro z hz
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using hgInf_lo z hz v
  have hzeroStay : Set.MapsTo (fun _ : Real ↦ (0 : E × E))
      (Icc (0 : Real) 1) phaseU := by
    intro t _ht
    refine ⟨?_, Set.mem_univ _⟩
    change (0 : E) ∈ Metric.ball 0 (h.phaseRadius R)
    simpa only [Metric.mem_ball, dist_self] using h.phaseRadius_pos R
  have hzeroEq : Set.EqOn (ΦInf 0) (fun _ : Real ↦ (0 : E × E))
      (Icc (0 : Real) 1) :=
    Analysis.ODE.Flow.orbit_unique_Icc_on (Ω := phaseU)
      (Metric.isOpen_ball.prod isOpen_univ) hspraySmooth
      (hcurve 0 hzeroMem) hzeroCurve
      (fun t ht ↦ ⟨hstay 0 hzeroMem t ht, Set.mem_univ _⟩)
      hzeroStay (hinit 0 hzeroMem)
  have hzeroEnd : ΦInf 0 1 = 0 := hzeroEq (by norm_num)
  have hslice : ContDiffOn Real ∞ (fun z ↦ ΦInf z 1)
      (Metric.ball (0 : E × E) q) := by
    exact Analysis.ODE.Flow.flow_slice_right_on
      (P := E × E) (E := E × E) (A := Metric.ball (0 : E × E) q)
      (a := 0) (b := 1) (a₀ := id) (γ := ΦInf)
      (Metric.isOpen_ball.prod isOpen_univ) hspraySmooth Metric.isOpen_ball
      contDiff_id.contDiffOn
      (fun z hz ↦ ⟨hinit z (Metric.ball_subset_closedBall hz),
        hcurve z (Metric.ball_subset_closedBall hz)⟩)
      (fun z hz t ht ↦ ⟨hstay z (Metric.ball_subset_closedBall hz) t ht,
        Set.mem_univ _⟩) 1 (by norm_num)
  have hendSmooth : ContDiffOn Real ∞
      (fun z ↦ (z.1, (ΦInf z 1).1)) (Metric.ball (0 : E × E) q) :=
    (contDiff_fst.contDiffOn : ContDiffOn Real ∞
      (fun z : E × E ↦ z.1) _).prodMk hslice.fst
  exact ⟨ΦInf, hinit, hcurve, hstay, hzeroEnd, happ, hendSmooth⟩



theorem exists_limit_diag
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real)
    (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf)
    (q : NNReal) (hq : 0 < q)
    (hqPos : 4 * (q : Real) < h.phaseRadius R)
    (hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real))
    (herr : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ (ΦInf : (E × E) → Real → E × E)
        (eInf : OpenPartialHomeomorph (E × E) (E × E))
        (deltaInf : Real),
      0 < deltaInf ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ΦInf z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        IsIntegralCurveOn (ΦInf z)
          (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ∀ t ∈ Icc (0 : Real) 1,
          (ΦInf z t).1 ∈ Metric.ball 0 (h.phaseRadius R)) ∧
      eInf.source = Metric.ball (0 : E × E) q ∧
      eInf 0 = 0 ∧
      (eInf : E × E → E × E) =
        (fun z ↦ (z.1, (ΦInf z 1).1)) ∧
      Metric.closedBall (0 : E × E) deltaInf ⊆ eInf.target ∧
      ContDiffOn Real ∞ (eInf : E × E → E × E) eInf.source ∧
      ContDiffOn Real ∞ eInf.symm eInf.target ∧
      (∀ z ∈ Metric.ball (0 : E) q,
        (z, z) ∈ eInf.target ∧ eInf.symm (z, z) = (z, 0)) ∧
      ApproximatesLinearOn
        (eInf.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        eInf.target
        (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q))) := by
  obtain ⟨ΦInf, hinit, hcurve, hstay, hzeroEnd, happ, hendSmooth⟩ :=
    h.exists_limit_phase R c hc hgInf_cd hgInf_lo hg_conv q hq hqPos hqAcc
  let f : E × E → E × E := fun z ↦ (z.1, (ΦInf z 1).1)
  obtain ⟨eInf, deltaInf, hdeltaInf, hsource, hcoe, htarget,
      _hdeltaEq, hinvApprox⟩ :=
    PhaseFlow.exists_quant_inv_bi hq (by simpa only [f] using happ) herr
  have hfzero : f 0 = 0 := by
    dsimp only [f]
    rw [hzeroEnd]
    rfl
  have hcoe_f : (eInf : E × E → E × E) = f := by
    simpa only [f] using hcoe
  have hezero : eInf 0 = 0 := by
    rw [hcoe_f]
    exact hfzero
  have htarget' : Metric.closedBall (0 : E × E) deltaInf ⊆
      eInf.target := by
    have hcenter : ((0 : E × E).1, (ΦInf 0 1).1) = (0 : E × E) := by
      rw [hzeroEnd]
      rfl
    rw [hcenter] at htarget
    exact htarget
  have hforwardSmooth : ContDiffOn Real ∞
      (eInf : E × E → E × E) eInf.source := by
    rw [hsource, hcoe_f]
    simpa only [f] using hendSmooth
  have happClosed : ApproximatesLinearOn f
      PhaseFlow.freeDiag (Metric.closedBall (0 : E × E) q)
      (PhaseFlow.phaseErr (normalPhaseK hb (2 * q))) := by
    simpa only [f] using happ
  have happOpen : ApproximatesLinearOn f
      PhaseFlow.freeDiag (Metric.ball (0 : E × E) q)
      (PhaseFlow.phaseErr (normalPhaseK hb (2 * q))) :=
    happClosed.mono_set Metric.ball_subset_closedBall
  have hendSmooth_f : ContDiffOn Real ∞ f
      (Metric.ball (0 : E × E) q) := by
    simpa only [f] using hendSmooth
  have hinvSmooth : ContDiffOn Real ∞ eInf.symm eInf.target :=
    PhaseFlow.inv_smooth_of_approx happOpen (Or.inr herr)
      Metric.isOpen_ball hendSmooth_f eInf hsource hcoe_f
  have hdiagInv : ∀ z ∈ Metric.ball (0 : E) q,
      (z, z) ∈ eInf.target ∧ eInf.symm (z, z) = (z, 0) := by
    intro z hz
    have hpClosed : (z, 0) ∈ Metric.closedBall (0 : E × E) q := by
      have hzClosed := Metric.ball_subset_closedBall hz
      rw [Metric.mem_closedBall] at hzClosed ⊢
      rw [Prod.dist_eq]
      change max (dist z (0 : E)) (dist (0 : E) 0) ≤ (q : Real)
      simpa only [dist_self, max_eq_left dist_nonneg] using hzClosed
    have hpOpen : (z, 0) ∈ Metric.ball (0 : E × E) q := by
      rw [Metric.mem_ball] at hz ⊢
      rw [Prod.dist_eq]
      change max (dist z (0 : E)) (dist (0 : E) 0) < (q : Real)
      simpa only [dist_self, max_eq_left dist_nonneg] using hz
    have hconstCurve : IsIntegralCurveOn (fun _ : Real ↦ (z, 0))
        (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1) := by
      intro t _ht
      simpa [MetricKoszul.metricSpray] using
        (hasDerivWithinAt_const (x := t) (s := Icc (0 : Real) 1)
          (c := (z, 0)))
    let phaseU : Set (E × E) :=
      Metric.ball (0 : E) (h.phaseRadius R) ×ˢ Set.univ
    have hspraySmooth : ContDiffOn Real ∞ (MetricKoszul.metricSpray gInf)
        phaseU := by
      apply MetricKoszul.metricSpray_contDiffOn Metric.isOpen_ball hgInf_cd
      intro w hw
      refine ⟨1 / 2, by norm_num, ?_⟩
      intro v
      simpa only [pow_two, mul_assoc] using hgInf_lo w hw v
    have hzPhase : z ∈ Metric.ball (0 : E) (h.phaseRadius R) := by
      rw [Metric.mem_ball] at hz ⊢
      have hqReal : (q : Real) < h.phaseRadius R := by
        nlinarith [q.coe_nonneg]
      exact hz.trans hqReal
    have hconstStay : Set.MapsTo (fun _ : Real ↦ (z, 0))
        (Icc (0 : Real) 1) phaseU := by
      intro t _ht
      exact ⟨hzPhase, Set.mem_univ _⟩
    have horbit : Set.EqOn (ΦInf (z, 0)) (fun _ : Real ↦ (z, 0))
        (Icc (0 : Real) 1) :=
      Analysis.ODE.Flow.orbit_unique_Icc_on (Ω := phaseU)
        (Metric.isOpen_ball.prod isOpen_univ) hspraySmooth
        (hcurve (z, 0) hpClosed) hconstCurve
        (fun t ht ↦ ⟨hstay (z, 0) hpClosed t ht, Set.mem_univ _⟩)
        hconstStay (hinit (z, 0) hpClosed)
    have hend : ΦInf (z, 0) 1 = (z, 0) := horbit (by norm_num)
    have heval : eInf (z, 0) = (z, z) := by
      rw [hcoe_f]
      dsimp only [f]
      rw [hend]
    have hpSource : (z, 0) ∈ eInf.source := by
      simpa only [hsource] using hpOpen
    have htargetDiag := eInf.map_source hpSource
    rw [heval] at htargetDiag
    have hleft := eInf.left_inv hpSource
    rw [heval] at hleft
    exact ⟨htargetDiag, hleft⟩
  exact ⟨ΦInf, eInf, deltaInf, hdeltaInf, hinit, hcurve, hstay,
    hsource, hezero, hcoe, htarget', hforwardSmooth, hinvSmooth,
    hdiagInv, hinvApprox⟩

end NormalRadiusProfile
end HCGCompactness
end DifferentialGeometry
