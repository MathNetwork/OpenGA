import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCPairTail











noncomputable section

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace HCGCompactness

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

set_option synthInstance.maxHeartbeats 100000 in


theorem liveMetric0_close
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    {psi : Nat → Nat}
    {gInf : E → (LiveSlot L inp.pack r → (E →L[Real] E →L[Real] Real))}
    (hconv : MapCInfConvOnCompacts Set.univ
      (fun k _ alpha => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0)
      gInf) :
    ∀ᶠ k in atTop, ∀ alpha : LiveSlot L inp.pack r, ∀ v : E,
      |normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 v v -
        gInf 0 alpha v v| ≤ (1 / 10 : Real) * ‖v‖ ^ 2 := by
  have htend := tendsto_of_cInf hconv (Set.mem_univ (0 : E))
  have hcoord : ∀ alpha : LiveSlot L inp.pack r,
      Tendsto
        (fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0)
        atTop (𝓝 (gInf 0 alpha)) :=
    tendsto_pi_nhds.mp htend
  have hall : ∀ᶠ k in atTop, ∀ alpha : LiveSlot L inp.pack r,
      dist
        (normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0)
        (gInf 0 alpha) < (1 / 10 : Real) :=
    Filter.eventually_all.mpr fun alpha =>
      (hcoord alpha).eventually <|
        Metric.ball_mem_nhds (gInf 0 alpha) (by norm_num : (0 : Real) < 1 / 10)
  filter_upwards [hall] with k hk
  intro alpha v
  have halpha :
      ‖normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 -
        gInf 0 alpha‖ ≤ (1 / 10 : Real) := by
    have hdist := (hk alpha).le
    let inst : SeminormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
      inferInstance
    have hnorm_eq (B : E →L[Real] E →L[Real] Real) :
        @norm (E →L[Real] E →L[Real] Real) inst.toNorm B = ‖B‖ := by
      rfl
    rw [@dist_eq_norm _ inst, hnorm_eq] at hdist
    exact hdist
  rw [show normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
      (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 v v -
        gInf 0 alpha v v =
      (normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 -
          gInf 0 alpha) v v by
    simp only [ContinuousLinearMap.sub_apply]]
  rw [← Real.norm_eq_abs]
  calc
    ‖(normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 -
        gInf 0 alpha) v v‖ ≤
        ‖normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
            (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 -
          gInf 0 alpha‖ * ‖v‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm₂ _ v v
    _ ≤ (1 / 10 : Real) * ‖v‖ * ‖v‖ := by gcongr
    _ = (1 / 10 : Real) * ‖v‖ ^ 2 := by ring

set_option synthInstance.maxHeartbeats 100000 in


theorem liveMetric0_symm
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    {psi : Nat → Nat}
    {gInf : E → (LiveSlot L inp.pack r → (E →L[Real] E →L[Real] Real))}
    (hconv : MapCInfConvOnCompacts Set.univ
      (fun k _ alpha => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0)
      gInf) :
    ∀ alpha : LiveSlot L inp.pack r, ∀ v w : E,
      gInf 0 alpha v w = gInf 0 alpha w v := by
  intro alpha v w
  have htendAll := tendsto_of_cInf hconv (Set.mem_univ (0 : E))
  have htend := (tendsto_pi_nhds.mp htendAll) alpha
  have heval (a b : E) : Continuous
      (fun B : E →L[Real] E →L[Real] Real => B a b) := by
    fun_prop
  have hvw := (heval v w).tendsto (gInf 0 alpha) |>.comp htend
  have hwv := (heval w v).tendsto (gInf 0 alpha) |>.comp htend
  have hstage :
      (fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 v w) =
      fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 w v := by
    funext k
    let Y := X.obj (L.φ (psi k))
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    rw [normalCoordMetric_apply (I := I), normalCoordMetric_apply (I := I)]
    exact Y.metric.symm _ _ _
  have hvw' : Filter.Tendsto
      (fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 v w)
      Filter.atTop (nhds (gInf 0 alpha v w)) := by
    simpa only [Function.comp_apply] using hvw
  have hwv' : Filter.Tendsto
      (fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0 w v)
      Filter.atTop (nhds (gInf 0 alpha w v)) := by
    simpa only [Function.comp_apply] using hwv
  rw [hstage] at hvw'
  exact tendsto_nhds_unique hvw' hwv'

set_option synthInstance.maxHeartbeats 100000 in









theorem MetricCompactnessInputs.exists_live_cores
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) :
    ∃ (psi : Nat → Nat) (_hpsi : StrictMono psi)
        (gInf : E →
          LiveSlot L inp.pack r → (E →L[Real] E →L[Real] Real))
        (U C0 C1 : LiveSlot L inp.pack r → Set E),
      ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
      MapCInfConvOnCompacts Set.univ
        (fun k _ alpha => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0)
        gInf ∧
      (∀ alpha, IsOpen (U alpha)) ∧
      (∀ alpha, U alpha ⊆
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
      (∀ alpha, IsCompact (C0 alpha)) ∧
      (∀ alpha, IsCompact (C1 alpha)) ∧
      (∀ alpha, C0 alpha ⊆ interior (C1 alpha)) ∧
      (∀ alpha, C1 alpha ⊆ U alpha) ∧
      (∀ alpha, Convex Real (C0 alpha)) ∧
      (∀ alpha, (0 : E) ∈ C0 alpha) ∧
      ∃ eta : LiveSlot L inp.pack r → Real,
      (∀ alpha, 0 < eta alpha) ∧
      ∀ᶠ k in atTop,
        let Y := X.obj (L.φ (psi k))
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (L.φ (psi k))).ms
        (∀ alpha : LiveSlot L inp.pack r,
          U alpha ⊆ Metric.ball 0
              (inp.normalBounds.radius (L.φ (psi k))
                (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
          U alpha ⊆ Metric.ball 0
              (expMapC2Radius (I := I) (X.obj (L.φ (psi k))).metric
                (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) (X.obj (L.φ (psi k))).metric
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
            (U alpha)
            (L.hatBall inp.decay inp.D P inp.pack r (psi k) alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                L.innerBall inp.decay inp.D P inp.pack r (psi k) gamma)) ∧
        L.hatSourceBall inp.decay P r (psi k) ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) (X.obj (L.φ (psi k))).metric
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z) ''
                interior (C0 alpha) ∧
        ∀ y ∈ L.hatSourceBall inp.decay P r (psi k),
          ∃ (alpha : LiveSlot L inp.pack r) (z : E),
            expMapDiffeo (I := I) (X.obj (L.φ (psi k))).metric
                (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z = y ∧
              Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) := by
  classical
  obtain ⟨psi, gInf, hpsi, hginf, hconv⟩ :=
    existsLiveMetric0 (I := I) inp.normalBounds P L inp.pack r
  let U : LiveSlot L inp.pack r → Set E := fun alpha =>
    {v | gInf 0 alpha v v < ((5 / 2 : Real) * L.lamInf (alpha.1 : Nat)) ^ 2}
  let C0 : LiveSlot L inp.pack r → Set E := fun alpha =>
    {v | gInf 0 alpha v v ≤
      (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2}
  let C1 : LiveSlot L inp.pack r → Set E := fun alpha =>
    {v | gInf 0 alpha v v ≤
      (99 / 16 : Real) * L.lamInf (alpha.1 : Nat) ^ 2}
  let Cdeep : LiveSlot L inp.pack r → Set E := fun alpha =>
    {v | gInf 0 alpha v v ≤
      (243 / 40 : Real) * L.lamInf (alpha.1 : Nat) ^ 2}
  have hequiv := liveMetric0_equiv (I := I) inp.normalBounds P L inp.pack r hconv
  have hsymm := liveMetric0_symm (I := I) inp P L r hconv
  have hclose := liveMetric0_close (I := I) inp P L r hconv
  have hscaled := hpsi.tendsto_atTop.eventually
    (L.scaled_cover inp.decay inp.hD P inp.realizes inp.pack r (9 / 4 : Real) (by norm_num))
  have halive : ∀ᶠ k in atTop, ∀ gamma ∈ Finset.range (inp.pack.A r),
      (seqCenter inp.decay inp.D P (L.φ (psi k)) gamma).isSome = L.alive gamma :=
    hpsi.tendsto_atTop.eventually <|
      (Filter.eventually_all_finset _).mpr fun gamma _ => L.alive_eventually gamma
  obtain ⟨hgp, hrad⟩ := inp.item3ScaleTails h8 hradD hradRatio P L r
  have hgpPsi := hpsi.tendsto_atTop.eventually hgp
  have hradPsi := hpsi.tendsto_atTop.eventually hrad
  have hmetric := inp.normalRadius.metricScaleTail inp.hD
    (item3Factor_pos inp.decay inp.D) hradRatio
    P inp.realizes L inp.pack r
  have hmetricPsi := hpsi.tendsto_atTop.eventually hmetric
  have hcenters : ∀ᶠ k in atTop, ∀ alpha : LiveSlot L inp.pack r,
      seqCenter inp.decay inp.D P (L.φ (psi k)) (alpha.1 : Nat) =
        some (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) :=
    Filter.eventually_all.mpr fun alpha =>
      hpsi.tendsto_atTop.eventually
        (seqCenterD_live inp.decay P L (alpha.1 : Nat) alpha.2)
  have hfactor : (8 : Real) ≤ item3RadiusFactor inp.decay inp.D := by
    have hExp : (1 : Real) ≤
        Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
      rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr
        (mul_nonneg inp.decay.C_nonneg
          (by nlinarith [(inp.decay.lambda_pos inp.hD 0).le]))
    rw [item3RadiusFactor]
    nlinarith
  have hopen : ∀ alpha, IsOpen (U alpha) := by
    intro alpha
    have hquad : Continuous (fun v : E => gInf 0 alpha v v) :=
      (gInf 0 alpha).continuous.clm_apply continuous_id
    exact isOpen_lt hquad continuous_const
  have hU8 : ∀ alpha, U alpha ⊆
      Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) := by
    intro alpha v hv
    have hlambda : 0 < L.lamInf (alpha.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
    have hlower := (hequiv alpha v).1
    have hvlt : gInf 0 alpha v v <
        ((5 / 2 : Real) * L.lamInf (alpha.1 : Nat)) ^ 2 := hv
    rw [Metric.mem_ball, dist_zero_right]
    by_contra hnot
    have hge : 8 * L.lamInf (alpha.1 : Nat) ≤ ‖v‖ := le_of_not_gt hnot
    nlinarith [sq_nonneg (‖v‖ - 8 * L.lamInf (alpha.1 : Nat))]
  have hC01 : ∀ alpha, C0 alpha ⊆ interior (C1 alpha) := by
    intro alpha
    have hquad : Continuous (fun v : E => gInf 0 alpha v v) :=
      (gInf 0 alpha).continuous.clm_apply continuous_id
    have hopen1 : IsOpen {v : E | gInf 0 alpha v v <
        (99 / 16 : Real) * L.lamInf (alpha.1 : Nat) ^ 2} :=
      isOpen_lt hquad continuous_const
    have hstrictSub : {v : E | gInf 0 alpha v v <
        (99 / 16 : Real) * L.lamInf (alpha.1 : Nat) ^ 2} ⊆ C1 alpha := by
      intro v hv
      change gInf 0 alpha v v <
        (99 / 16 : Real) * L.lamInf (alpha.1 : Nat) ^ 2 at hv
      exact hv.le
    intro v hv
    apply (interior_maximal hstrictSub hopen1)
    change gInf 0 alpha v v <
      (99 / 16 : Real) * L.lamInf (alpha.1 : Nat) ^ 2
    change gInf 0 alpha v v ≤
      (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2 at hv
    have hlambda : 0 < L.lamInf (alpha.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
    nlinarith [sq_pos_of_pos hlambda]
  have hC1U : ∀ alpha, C1 alpha ⊆ U alpha := by
    intro alpha v hv
    change gInf 0 alpha v v <
      ((5 / 2 : Real) * L.lamInf (alpha.1 : Nat)) ^ 2
    change gInf 0 alpha v v ≤
      (99 / 16 : Real) * L.lamInf (alpha.1 : Nat) ^ 2 at hv
    have hlambda : 0 < L.lamInf (alpha.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
    nlinarith [sq_pos_of_pos hlambda]
  have hC0compact : ∀ alpha, IsCompact (C0 alpha) := by
    intro alpha
    have hquad : Continuous (fun v : E => gInf 0 alpha v v) :=
      (gInf 0 alpha).continuous.clm_apply continuous_id
    have hclosed : IsClosed (C0 alpha) := by
      exact isClosed_le hquad continuous_const
    have hbounded : Bornology.IsBounded (C0 alpha) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨8 * L.lamInf (alpha.1 : Nat), fun v hv => ?_⟩
      have hvU : v ∈ U alpha :=
        hC1U alpha (interior_subset (hC01 alpha hv))
      have hvlt : ‖v‖ < 8 * L.lamInf (alpha.1 : Nat) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hU8 alpha hvU
      exact hvlt.le
    exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded
  have hC1compact : ∀ alpha, IsCompact (C1 alpha) := by
    intro alpha
    have hquad : Continuous (fun v : E => gInf 0 alpha v v) :=
      (gInf 0 alpha).continuous.clm_apply continuous_id
    have hclosed : IsClosed (C1 alpha) := by
      exact isClosed_le hquad continuous_const
    have hbounded : Bornology.IsBounded (C1 alpha) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨8 * L.lamInf (alpha.1 : Nat), fun v hv => ?_⟩
      have hvlt : ‖v‖ < 8 * L.lamInf (alpha.1 : Nat) := by
        simpa only [Metric.mem_ball, dist_zero_right] using
          hU8 alpha (hC1U alpha hv)
      exact hvlt.le
    exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded
  have hC0convex : ∀ alpha, Convex Real (C0 alpha) := by
    intro alpha
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    change gInf 0 alpha x x ≤
      (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2 at hx
    change gInf 0 alpha y y ≤
      (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2 at hy
    change gInf 0 alpha (a • x + b • y) (a • x + b • y) ≤
      (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2
    have hdiff : 0 ≤ gInf 0 alpha (x - y) (x - y) :=
      (mul_nonneg (by norm_num) (sq_nonneg ‖x - y‖)).trans
        (hequiv alpha (x - y)).1
    calc
      gInf 0 alpha (a • x + b • y) (a • x + b • y) =
          a * gInf 0 alpha x x + b * gInf 0 alpha y y -
            a * b * gInf 0 alpha (x - y) (x - y) := by
        simp only [map_add, map_smul, map_sub,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [hsymm alpha y x]
        have hb_eq : b = 1 - a := by linarith
        rw [hb_eq]
        ring
      _ ≤ a * gInf 0 alpha x x + b * gInf 0 alpha y y :=
        sub_le_self _ (mul_nonneg (mul_nonneg ha hb) hdiff)
      _ ≤ a * ((49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2) +
          b * ((49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha)
          (mul_le_mul_of_nonneg_left hy hb)
      _ = (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2 := by
        rw [← add_mul, hab, one_mul]
  have hC0zero : ∀ alpha, (0 : E) ∈ C0 alpha := by
    intro alpha
    change gInf 0 alpha 0 0 ≤
      (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2
    simp only [map_zero]
    positivity
  have hdeepC0 : ∀ alpha, Cdeep alpha ⊆ interior (C0 alpha) := by
    intro alpha
    have hquad : Continuous (fun v : E => gInf 0 alpha v v) :=
      (gInf 0 alpha).continuous.clm_apply continuous_id
    have hopen0 : IsOpen {v : E | gInf 0 alpha v v <
        (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2} :=
      isOpen_lt hquad continuous_const
    have hstrictSub : {v : E | gInf 0 alpha v v <
        (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2} ⊆ C0 alpha := by
      intro v hv
      change gInf 0 alpha v v <
        (49 / 8 : Real) * L.lamInf (alpha.1 : Nat) ^ 2 at hv
      exact hv.le
    intro v hv
    apply interior_maximal hstrictSub hopen0
    change gInf 0 alpha v v ≤
      (243 / 40 : Real) * L.lamInf (alpha.1 : Nat) ^ 2 at hv
    have hlambda : 0 < L.lamInf (alpha.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
    exact hv.trans_lt <| mul_lt_mul_of_pos_right (by norm_num)
      (sq_pos_of_pos hlambda)
  have hdeepCompact : ∀ alpha, IsCompact (Cdeep alpha) := by
    intro alpha
    have hquad : Continuous (fun v : E => gInf 0 alpha v v) :=
      (gInf 0 alpha).continuous.clm_apply continuous_id
    have hclosed : IsClosed (Cdeep alpha) := isClosed_le hquad continuous_const
    exact (hC0compact alpha).of_isClosed_subset hclosed
      ((hdeepC0 alpha).trans interior_subset)
  choose eta heta_pos heta_sub using fun alpha =>
    (hdeepCompact alpha).exists_cthickening_subset_open
      isOpen_interior (hdeepC0 alpha)
  refine ⟨psi, hpsi, gInf, U, C0, C1, hginf, hconv, hopen, hU8,
    hC0compact, hC1compact, hC01, hC1U, hC0convex, hC0zero,
    eta, heta_pos, ?_⟩
  filter_upwards [hclose, hscaled, halive, hgpPsi, hradPsi, hmetricPsi, hcenters]
    with k hclosek hscaledk halivek hgpk hradk hmetrick hcentersk
  let Y := X.obj (L.φ (psi k))
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := (P (L.φ (psi k))).ms
  constructor
  · intro alpha
    have hcenterk : seqCenter inp.decay inp.D P (L.φ (psi k)) (alpha.1 : Nat) =
        some (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) :=
      hcentersk alpha
    have hUfac : U alpha ⊆
        Metric.ball 0
          (item3RadiusFactor inp.decay inp.D * L.lamInf (alpha.1 : Nat)) :=
      (hU8 alpha).trans <| Metric.ball_subset_ball <|
        mul_le_mul_of_nonneg_right hfactor
          (inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))).le
    refine ⟨hUfac.trans (Metric.ball_subset_ball
      (hmetrick alpha.1 _ hcenterk)),
      hUfac.trans (Metric.ball_subset_ball (hradk alpha.1 _ hcenterk).2), ?_⟩
    intro v hv
    let c : Y.M := seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)
    have hlambda : 0 < L.lamInf (alpha.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
    have hlower := (hequiv alpha v).1
    have hvlt : gInf 0 alpha v v <
        ((5 / 2 : Real) * L.lamInf (alpha.1 : Nat)) ^ 2 := hv
    have herr := hclosek alpha v
    have hstage : normalCoordMetric (I := I) Y c 0 v v <
        (3 * L.lamInf (alpha.1 : Nat)) ^ 2 := by
      rw [abs_le] at herr
      nlinarith
    have hzero : (0 : E) ∈ Metric.ball 0
        (inp.normalBounds.radius (L.φ (psi k)) c) := by
      rw [Metric.mem_ball, dist_self]
      exact inp.normalBounds.radius_pos _ _
    have hnonneg : 0 ≤ normalCoordMetric (I := I) Y c 0 v v :=
      (inp.normalBounds.metric_equiv (L.φ (psi k)) c 0 hzero v).1.trans'
        (mul_nonneg (by norm_num) (sq_nonneg ‖v‖))
    have hsqrt : Real.sqrt (Y.metric.inner c v v) <
        3 * L.lamInf (alpha.1 : Nat) := by
      rw [← normalMetric_zero (I := I) Y c]
      apply (sq_lt_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num) hlambda.le)).mp
      calc
        Real.sqrt (normalCoordMetric (I := I) Y c 0 v v) ^ 2 =
            normalCoordMetric (I := I) Y c 0 v v := Real.sq_sqrt hnonneg
        _ < (3 * L.lamInf (alpha.1 : Nat)) ^ 2 := hstage
    have hsmall : Real.sqrt (Y.metric.inner c v v) <
        expRadiusGp (I := I) Y.metric c :=
      hsqrt.trans <| (by
        have := hgpk alpha.1 c hcenterk
        nlinarith)
    have hvnorm := norm_lt_expMapC2Radius_of_sqrt_inner_lt
      (I := I) Y.metric c hsmall
    have hvsrc := mem_expMapDiffeo_source_of_norm_lt_radius
      (I := I) Y.metric c hvnorm
    have hdist := properExpDist (I := I) Y (P (L.φ (psi k))) c hsmall
    have hexp : expMapDiffeo (I := I) Y.metric c v =
        expMap (I := I) Y.metric c (show TangentSpace I c from v) :=
      expMapDiffeo_apply_eq (I := I) Y.metric c hvsrc
    have hinner : expMapDiffeo (I := I) Y.metric c v ∈
        L.innerBall inp.decay inp.D P inp.pack r (psi k) alpha.1 := by
      simp only [NetLimitData.innerBall, hcenterk]
      change dist (expMapDiffeo (I := I) Y.metric c v) c <
        3 * L.lamInf (alpha.1 : Nat)
      rw [hexp, dist_comm, hdist]
      exact hsqrt
    exact ⟨L.innerBall_subset_hat inp.decay inp.hD P inp.pack r (psi k) alpha.1 hinner,
      mem_iUnion.mpr ⟨alpha.1, hinner⟩⟩
  · have hselect : ∀ y ∈ L.hatSourceBall inp.decay P r (psi k),
        ∃ (alpha : LiveSlot L inp.pack r) (v : E),
          v ∈ Cdeep alpha ∧
            expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) v = y := by
      intro y hy
      have hydist : dist y Y.basepoint ≤ r := by
        simpa only [NetLimitData.hatSourceBall, Metric.mem_closedBall] using hy
      obtain ⟨gamma, hgamma, c, hcenter, hyc⟩ := hscaledk y hydist
      have haliveGamma : L.alive gamma = true := by
        have hsome : (seqCenter inp.decay inp.D P (L.φ (psi k)) gamma).isSome = true := by
          simp only [hcenter, Option.isSome_some]
        exact (halivek gamma (Finset.mem_range.mpr hgamma)).symm.trans hsome
      let alpha : LiveSlot L inp.pack r := ⟨⟨gamma, hgamma⟩, haliveGamma⟩
      have hcD : seqCenterD inp.decay P L (psi k) gamma = c := by
        have := seqCenterD_some inp.decay P L (psi k) gamma
          (by simp only [hcenter, Option.isSome_some])
        rw [hcenter] at this
        exact Option.some.inj this.symm
      have hgpC := hgpk ⟨gamma, hgamma⟩ c hcenter
      have hlambda : 0 < L.lamInf gamma :=
        inp.decay.lambda_pos inp.hD (L.rInf gamma)
      have hyball : y ∈ Metric.ball c (4 * L.lamInf gamma) := by
        rw [Metric.mem_ball]
        exact hyc.trans <|
          mul_lt_mul_of_pos_right (by norm_num : (9 / 4 : Real) < 4) hlambda
      obtain ⟨v, hvtgt, _hvdom, hvlen, hyexp⟩ :=
        properBallNormal (I := I) Y (P (L.φ (psi k))) hgpC hyball
      have hvsrc : v ∈ (expMapDiffeo (I := I) Y.metric c).source := by
        simpa only [normalChartAt_target_eq] using hvtgt
      have hzero : (0 : E) ∈ Metric.ball 0
          (inp.normalBounds.radius (L.φ (psi k)) c) := by
        rw [Metric.mem_ball, dist_self]
        exact inp.normalBounds.radius_pos _ _
      have hstageLower : (1 / 2 : Real) * ‖v‖ ^ 2 ≤ Y.metric.inner c v v := by
        rw [← normalMetric_zero (I := I) Y c]
        exact (inp.normalBounds.metric_equiv (L.φ (psi k)) c 0 hzero v).1
      have hmetricNonneg : 0 ≤ Y.metric.inner c v v :=
        hstageLower.trans' (mul_nonneg (by norm_num) (sq_nonneg ‖v‖))
      have hstageSq : Y.metric.inner c v v = dist c y ^ 2 := by
        rw [← hvlen, Real.sq_sqrt hmetricNonneg]
      have herr := hclosek alpha v
      rw [hcD, normalMetric_zero (I := I) Y c, abs_le] at herr
      have hdistLt : dist c y < (9 / 4 : Real) * L.lamInf gamma := by
        simpa only [dist_comm] using hyc
      have hdistSq : dist c y ^ 2 <
          ((9 / 4 : Real) * L.lamInf gamma) ^ 2 :=
        (sq_lt_sq₀ dist_nonneg
          (mul_nonneg (by norm_num) hlambda.le)).2 hdistLt
      have hvdeep : v ∈ Cdeep alpha := by
        have hnormStage : ‖v‖ ^ 2 ≤ 2 * Y.metric.inner c v v := by
          nlinarith [hstageLower]
        have hqInfBase : gInf 0 alpha v v ≤
            Y.metric.inner c v v + (1 / 10 : Real) * ‖v‖ ^ 2 := by
          calc
            gInf 0 alpha v v = Y.metric.inner c v v -
                (Y.metric.inner c v v - gInf 0 alpha v v) := by ring
            _ ≤ Y.metric.inner c v v - (-(1 / 10 : Real) * ‖v‖ ^ 2) :=
              by
                simpa only [neg_mul] using
                  sub_le_sub_left herr.1 (Y.metric.inner c v v)
            _ = Y.metric.inner c v v + (1 / 10 : Real) * ‖v‖ ^ 2 := by ring
        have hqInfStage : gInf 0 alpha v v ≤
            (6 / 5 : Real) * Y.metric.inner c v v := by
          calc
            _ ≤ Y.metric.inner c v v + (1 / 10 : Real) * ‖v‖ ^ 2 := hqInfBase
            _ ≤ Y.metric.inner c v v +
                (1 / 10 : Real) * (2 * Y.metric.inner c v v) :=
              by
                gcongr
            _ = (6 / 5 : Real) * Y.metric.inner c v v := by ring
        have hqInfLe : gInf 0 alpha v v ≤ (6 / 5 : Real) * dist c y ^ 2 := by
          rw [← hstageSq]
          exact hqInfStage
        have hscale0 : (6 / 5 : Real) * dist c y ^ 2 <
            (243 / 40 : Real) * L.lamInf gamma ^ 2 := by
          have hlamSq : 0 < L.lamInf gamma ^ 2 := sq_pos_of_pos hlambda
          nlinarith
        exact (hqInfLe.trans_lt hscale0).le
      refine ⟨alpha, v, hvdeep, ?_⟩
      simp only [alpha]
      rw [hcD]
      rw [expMapDiffeo_apply_eq (I := I) Y.metric c hvsrc]
      exact hyexp.symm
    constructor
    · intro y hy
      obtain ⟨alpha, v, hvdeep, hvexp⟩ := hselect y hy
      exact mem_iUnion.mpr ⟨alpha, ⟨v, hdeepC0 alpha hvdeep, hvexp⟩⟩
    · intro y hy
      obtain ⟨alpha, v, hvdeep, hvexp⟩ := hselect y hy
      refine ⟨alpha, v, hvexp, ?_⟩
      exact (Metric.closedBall_subset_cthickening hvdeep (eta alpha)).trans
        (heta_sub alpha)

set_option synthInstance.maxHeartbeats 100000 in


theorem MetricCompactnessInputs.exists_live_source_cover
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) :
    ∃ (psi : Nat → Nat) (_hpsi : StrictMono psi)
        (gInf : E →
          LiveSlot L inp.pack r → (E →L[Real] E →L[Real] Real))
        (U : LiveSlot L inp.pack r → Set E),
      ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
      MapCInfConvOnCompacts Set.univ
        (fun k _ alpha => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) 0)
        gInf ∧
      (∀ alpha, IsOpen (U alpha)) ∧
      (∀ alpha, U alpha ⊆
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
      ∀ᶠ k in atTop,
        let Y := X.obj (L.φ (psi k))
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (L.φ (psi k))).ms
        (∀ alpha : LiveSlot L inp.pack r,
          U alpha ⊆ Metric.ball 0
              (inp.normalBounds.radius (L.φ (psi k))
                (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
          U alpha ⊆ Metric.ball 0
              (expMapC2Radius (I := I) (X.obj (L.φ (psi k))).metric
                (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) (X.obj (L.φ (psi k))).metric
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
            (U alpha)
            (L.hatBall inp.decay inp.D P inp.pack r (psi k) alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                L.innerBall inp.decay inp.D P inp.pack r (psi k) gamma)) ∧
        L.hatSourceBall inp.decay P r (psi k) ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) (X.obj (L.φ (psi k))).metric
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z) '' U alpha := by
  obtain ⟨psi, hpsi, gInf, U, C0, C1, hginf, hconv, hopen, hU8,
      _hC0, _hC1, hC01, hC1U, _hconvex, _hzero,
      _eta, _heta, hcover⟩ :=
    inp.exists_live_cores h8 hradD hradRatio P L r
  refine ⟨psi, hpsi, gInf, U, hginf, hconv, hopen, hU8, ?_⟩
  filter_upwards [hcover] with k hk
  refine ⟨hk.1, ?_⟩
  intro y hy
  obtain ⟨alpha, v, hv, rfl⟩ := mem_iUnion.mp (hk.2.1 hy)
  refine mem_iUnion.mpr ⟨alpha, v, ?_, rfl⟩
  exact hC1U alpha (interior_subset (hC01 alpha (interior_subset hv)))

end HCGCompactness
end DifferentialGeometry
