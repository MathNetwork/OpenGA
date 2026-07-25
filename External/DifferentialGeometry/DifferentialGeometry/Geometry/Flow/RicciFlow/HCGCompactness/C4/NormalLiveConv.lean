import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalMetricConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchCage

set_option autoImplicit false










noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace MetricCompactnessInputs



theorem exists_live_diag
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let R := 2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real)
    ∃ (psi : Nat → Nat)
        (gInf : E →
          (LiveSlot L inp.pack r → (E →L[Real] E →L[Real] Real)))
        (qStage qInf : LiveSlot L inp.pack r → NNReal)
        (deltaStage deltaInf : LiveSlot L inp.pack r → Real)
        (e : LiveSlot L inp.pack r →
          Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : LiveSlot L inp.pack r →
          OpenPartialHomeomorph (E × E) (E × E)),
      StrictMono psi ∧
      (∀ k (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (L.φ (psi k))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))
          (X.obj (L.φ (psi k))).basepoint ≤ R) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) gInf
        (Metric.ball 0 (inp.normalRadius.phaseRadius R)) ∧
      MapCInfConvOnCompacts
        (Metric.ball 0 (inp.normalRadius.phaseRadius R))
        (fun k z alpha ↦ normalCoordMetric (I := I)
          (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
        gInf ∧
      (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z (alpha : LiveSlot L inp.pack r) ↦ normalCoordMetric (I := I)
          (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
        (Metric.ball 0 (inp.normalRadius.phaseRadius R))) ∧
      (∀ z ∈ Metric.ball (0 : E) (inp.normalRadius.phaseRadius R),
        ∀ alpha v,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z alpha v v ∧
            gInf z alpha v v ≤ 2 * ‖v‖ ^ 2) ∧
      let index : Nat → Nat := fun k ↦ L.φ (psi k)
      let Xpsi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : LiveSlot L inp.pack r → ∀ k : Nat, (Xpsi.obj k).M :=
        fun alpha k ↦ seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)
      ∀ alpha,
        HasDiagPairConv (I := I) (hcomplete.subseq index)
          (PointedRiemannianSeq.connected_subseq hconn index)
          (c alpha) (qStage alpha) (qInf alpha)
          (deltaStage alpha) (deltaInf alpha) (e alpha) (eInf alpha) := by
  classical
  dsimp only
  obtain ⟨psi, gInf, hpsi, hcenter, hgInf, hconv, hstage, hequiv⟩ :=
    inp.exists_live_metric P L r
  let index : Nat → Nat := fun k ↦ L.φ (psi k)
  let Xpsi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
  let c : LiveSlot L inp.pack r → ∀ k : Nat, (Xpsi.obj k).M :=
    fun alpha k ↦ seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)
  have hpair : ∀ alpha,
      ∃ (qStage qInf : NNReal) (deltaStage deltaInf : Real)
          (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
          (eInf : OpenPartialHomeomorph (E × E) (E × E)),
        HasDiagPairConv (I := I) (hcomplete.subseq index)
          (PointedRiemannianSeq.connected_subseq hconn index)
          (c alpha) qStage qInf deltaStage deltaInf e eInf := by
    intro alpha
    have hc : ∀ k,
        (inp.decay.subseq index).dist k (c alpha k)
          (Xpsi.obj k).basepoint ≤
            2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real) := by
      intro k
      simpa only [index, Xpsi, c, InjRadiusDecayInput.subseq,
        PointedRiemannianSeq.subseq] using hcenter k alpha
    have hgInfAlpha : ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z ↦ gInf z alpha)
        (Metric.ball 0 (inp.normalRadius.phaseRadius
          (2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real)))) :=
      contDiffOn_pi.mp hgInf alpha
    have hgInfAlphaLo : ∀ z ∈ Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius
          (2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real))),
        ∀ v : E, (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z alpha v v :=
      fun z hz v ↦ (hequiv z hz alpha v).1
    have hgInfAlphaConv : MapCInfConvOnCompacts
        (Metric.ball 0 (inp.normalRadius.phaseRadius
          (2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real))))
        (fun k ↦ normalCoordMetric (I := I) (Xpsi.obj k) (c alpha k))
        (fun z ↦ gInf z alpha) := by
      simpa only [index, Xpsi, c, PointedRiemannianSeq.subseq] using
        (mapCInf_apply Metric.isOpen_ball hconv hstage hgInf alpha)
    simpa only [MetricCompactnessInputs.subseq, NormalRadiusProfile.subseq,
        InjRadiusDecayInput.subseq, NormalCoordMetricBoundInput.subseq,
        NormalRadiusProfile.phaseRadius] using
      (inp.normalRadius.subseq index).exists_diagPair_conv
        (hcomplete.subseq index)
        (PointedRiemannianSeq.connected_subseq hconn index)
        (2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real)) (c alpha) hc
        hgInfAlpha hgInfAlphaLo hgInfAlphaConv
  choose qStage qInf deltaStage deltaInf e eInf hpair using hpair
  refine ⟨psi, gInf, qStage, qInf, deltaStage, deltaInf, e, eInf,
    hpsi, hcenter, hgInf, hconv, hstage, hequiv, ?_⟩
  simpa only [index, Xpsi, c] using hpair



theorem exists_slot_diag
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (hq : ∀ alpha, 0 < q alpha)
    (hqWide : ∀ alpha,
      6 * (q alpha : Real) < inp.normalRadius.phaseRadius
        (L.rInf (alpha.1 : Nat) + 1))
    (hqAcc : ∀ alpha,
      3 * inp.normalBounds.metricC 1 * (2 * (q alpha : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q alpha : Real))
    (herr : ∀ alpha,
      PhaseFlow.phaseErr (normalPhaseK inp.normalBounds (2 * q alpha)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹)
    (hinvErr : ∀ alpha,
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr
              (normalPhaseK inp.normalBounds (2 * q alpha)))⁻¹ *
          PhaseFlow.phaseErr
            (normalPhaseK inp.normalBounds (2 * q alpha)) < 1 / 24) :
    ∃ (psi : Nat → Nat)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real))
        (deltaStage deltaInf : LiveSlot L inp.pack r → Real)
        (e : LiveSlot L inp.pack r →
          Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : LiveSlot L inp.pack r →
          OpenPartialHomeomorph (E × E) (E × E)),
      StrictMono psi ∧
      (∀ n (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (L.φ (psi n))
          (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat))
          (X.obj (L.φ (psi n))).basepoint ≤
            L.rInf (alpha.1 : Nat) + 1) ∧
      (∀ alpha : LiveSlot L inp.pack r,
        let Ralpha := L.rInf (alpha.1 : Nat) + 1
        let Ualpha := Metric.ball (0 : E)
          (inp.normalRadius.phaseRadius Ralpha)
        ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
        MapCInfConvOnCompacts Ualpha
          (fun n => normalCoordMetric (I := I)
            (X.obj (L.φ (psi n)))
            (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat)))
          (gInf alpha) ∧
        ∀ z ∈ Ualpha, ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
            gInf alpha z v v ≤ 2 * ‖v‖ ^ 2) ∧
      let index : Nat → Nat := fun n => L.φ (psi n)
      let Xpsi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xpsi.obj n).M :=
        fun alpha n => seqCenterD inp.decay P L (psi n) (alpha.1 : Nat)
      ∀ alpha,
        HasDiagPairConv (I := I) (hcomplete.subseq index)
          (PointedRiemannianSeq.connected_subseq hconn index)
          (c alpha) (q alpha) (q alpha / 2)
          (deltaStage alpha) (deltaInf alpha) (e alpha) (eInf alpha) ∧
        ∀ n, NormalDiagFence (I := I) (Xpsi.obj n) (c alpha n)
          (q alpha) (e alpha n) := by
  classical
  obtain ⟨psi, gInf, hpsi, hcenter, hmetric⟩ :=
    inp.exists_slot_metric P L r
  let index : Nat → Nat := fun n => L.φ (psi n)
  let Xpsi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
  let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xpsi.obj n).M :=
    fun alpha n => seqCenterD inp.decay P L (psi n) (alpha.1 : Nat)
  have hpair : ∀ alpha,
      ∃ (deltaStage deltaInf : Real)
          (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
          (eInf : OpenPartialHomeomorph (E × E) (E × E)),
        HasDiagPairConv (I := I) (hcomplete.subseq index)
          (PointedRiemannianSeq.connected_subseq hconn index)
          (c alpha) (q alpha) (q alpha / 2)
          deltaStage deltaInf e eInf ∧
        ∀ n, NormalDiagFence (I := I) (Xpsi.obj n) (c alpha n)
          (q alpha) (e n) := by
    intro alpha
    let Ralpha : Real := L.rInf (alpha.1 : Nat) + 1
    have hc : ∀ n,
        (inp.decay.subseq index).dist n (c alpha n)
          (Xpsi.obj n).basepoint ≤ Ralpha := by
      intro n
      simpa only [Ralpha, index, Xpsi, c, InjRadiusDecayInput.subseq,
        PointedRiemannianSeq.subseq] using hcenter n alpha
    have hm := hmetric alpha
    dsimp only at hm
    have hgInfLo : ∀ z ∈ Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius Ralpha), ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v :=
      fun z hz v => (hm.2.2 z hz v).1
    have hgConv : MapCInfConvOnCompacts
        (Metric.ball (0 : E) (inp.normalRadius.phaseRadius Ralpha))
        (fun n => normalCoordMetric (I := I) (Xpsi.obj n) (c alpha n))
        (gInf alpha) := by
      simpa only [Ralpha, index, Xpsi, c, PointedRiemannianSeq.subseq] using hm.2.1
    simpa only [Ralpha, NormalRadiusProfile.subseq,
        InjRadiusDecayInput.subseq, NormalCoordMetricBoundInput.subseq,
        NormalRadiusProfile.phaseRadius] using
      (inp.normalRadius.subseq index).exists_diagPair_at
        (hcomplete.subseq index)
        (PointedRiemannianSeq.connected_subseq hconn index)
        Ralpha (c alpha) hc (q alpha) (hq alpha) (hqWide alpha)
        (hqAcc alpha) (herr alpha) (hinvErr alpha)
        hm.1 hgInfLo hgConv
  choose deltaStage deltaInf e eInf hpair using hpair
  exact ⟨psi, gInf, deltaStage, deltaInf, e, eInf,
    hpsi, hcenter, hmetric, hpair⟩




theorem exists_diag_full
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (aMin : Real)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hq : ∀ alpha, 0 < q alpha)
    (hδ : ∀ alpha, 0 < δ alpha)
    (hqWide : ∀ alpha,
      6 * (q alpha : Real) < inp.normalRadius.phaseRadius
        (L.rInf (alpha.1 : Nat) + 1))
    (hqAcc : ∀ alpha,
      3 * inp.normalBounds.metricC 1 * (2 * (q alpha : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q alpha : Real))
    (herr : ∀ alpha,
      PhaseFlow.phaseErr (normalPhaseK inp.normalBounds (2 * q alpha)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹)
    (hinvErr : ∀ alpha,
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr
              (normalPhaseK inp.normalBounds (2 * q alpha)))⁻¹ *
          PhaseFlow.phaseErr
            (normalPhaseK inp.normalBounds (2 * q alpha)) < 1 / 24)
    (hbranch : Filter.Eventually
      (fun n ↦ HasLiveBrFull (I := I) P L inp.pack r n
        hcomplete hconn aMin q δ) Filter.atTop)
    (Q : Nat → Prop) (hQ : Filter.Eventually Q Filter.atTop) :
    ∃ (psi : Nat → Nat) (hpsi : StrictMono psi)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real))
        (deltaInf : LiveSlot L inp.pack r → Real)
        (e : LiveSlot L inp.pack r →
          Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : LiveSlot L inp.pack r →
          OpenPartialHomeomorph (E × E) (E × E)),
      (∀ n (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (L.φ (psi n))
          (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat))
          (X.obj (L.φ (psi n))).basepoint ≤
            L.rInf (alpha.1 : Nat) + 1) ∧
      (∀ n, Q (psi n)) ∧
      (∀ alpha : LiveSlot L inp.pack r,
        let Ralpha := L.rInf (alpha.1 : Nat) + 1
        let Ualpha := Metric.ball (0 : E)
          (inp.normalRadius.phaseRadius Ralpha)
        ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
        MapCInfConvOnCompacts Ualpha
          (fun n ↦ normalCoordMetric (I := I)
            (X.obj (L.φ (psi n)))
            (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat)))
          (gInf alpha) ∧
        ∀ z ∈ Ualpha, ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
            gInf alpha z v v ≤ 2 * ‖v‖ ^ 2) ∧
      let Lpsi := L.subseq hpsi
      (∀ n, HasLiveBrFull (I := I) P Lpsi inp.pack r n
        hcomplete hconn aMin q δ) ∧
      let index : Nat → Nat := fun n ↦ L.φ (psi n)
      let Xpsi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xpsi.obj n).M :=
        fun alpha n ↦ seqCenterD inp.decay P Lpsi n (alpha.1 : Nat)
      ∀ alpha,
        HasDiagPairConv (I := I) (hcomplete.subseq index)
          (PointedRiemannianSeq.connected_subseq hconn index)
          (c alpha) (q alpha) (q alpha / 2)
          (δ alpha) (deltaInf alpha) (e alpha) (eInf alpha) ∧
        ∀ n, NormalDiagFence (I := I) (Xpsi.obj n)
          (c alpha n) (q alpha) (e alpha n) := by
  classical
  obtain ⟨psi0, gInf, deltaStage, deltaInf, e0, eInf,
      hpsi0, hcenter0, hmetric0, hpair0⟩ :=
    inp.exists_slot_diag P L r hcomplete hconn q hq hqWide hqAcc herr hinvErr
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hpsi0.tendsto_atTop.eventually (hbranch.and hQ))
  let shift : Nat → Nat := fun n ↦ n + N
  have hshift : StrictMono shift := by
    simpa only [shift] using strictMono_id.add_const N
  let psi : Nat → Nat := psi0 ∘ shift
  have hpsi : StrictMono psi := hpsi0.comp hshift
  let Lpsi := L.subseq hpsi
  have hbranchAll : ∀ n,
      HasLiveBrFull (I := I) P Lpsi inp.pack r n
        hcomplete hconn aMin q δ := by
    intro n
    have hn := (hN (shift n) (by simp only [shift]; omega)).1
    simpa only [Lpsi, psi, HasLiveBrFull, NetLimitData.subseq,
      Function.comp_apply, seqCenterD_subseq] using hn
  have hQAll : ∀ n, Q (psi n) := by
    intro n
    exact (hN (shift n) (by simp only [shift]; omega)).2
  have hselected : ∀ (alpha : LiveSlot L inp.pack r) n,
      ∃ e : OpenPartialHomeomorph (E × E) (E × E),
        IsNormalDiag (I := I) (X.obj (L.φ (psi n)))
          (hcomplete.complete (L.φ (psi n))) (hconn (L.φ (psi n)))
          (seqCenterD inp.decay P Lpsi n (alpha.1 : Nat))
          (q alpha) (δ alpha) e ∧
        NormalDiagFence (I := I) (X.obj (L.φ (psi n)))
          (seqCenterD inp.decay P Lpsi n (alpha.1 : Nat)) (q alpha) e := by
    intro alpha n
    have hfull := hbranchAll n alpha
    dsimp only [HasNormalBrFull] at hfull
    rcases hfull with ⟨_hq, e, he, hf, _⟩
    exact ⟨e, he, hf⟩
  choose e hnormal hfence using hselected
  have hcenter : ∀ n (alpha : LiveSlot L inp.pack r),
      inp.decay.dist (L.φ (psi n))
        (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat))
        (X.obj (L.φ (psi n))).basepoint ≤
          L.rInf (alpha.1 : Nat) + 1 := by
    intro n alpha
    exact hcenter0 (shift n) alpha
  have hmetric : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      let Ualpha := Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius Ralpha)
      ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
      MapCInfConvOnCompacts Ualpha
        (fun n ↦ normalCoordMetric (I := I)
          (X.obj (L.φ (psi n)))
          (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat)))
        (gInf alpha) ∧
      ∀ z ∈ Ualpha, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
          gInf alpha z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro alpha
    obtain ⟨hcd, hconv, hequiv⟩ := hmetric0 alpha
    exact ⟨hcd, hconv.comp_tendsto_atTop hshift.tendsto_atTop, hequiv⟩
  let index0 : Nat → Nat := fun n ↦ L.φ (psi0 n)
  let X0 : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index0
  let c0 : LiveSlot L inp.pack r → ∀ n : Nat, (X0.obj n).M :=
    fun alpha n ↦ seqCenterD inp.decay P L (psi0 n) (alpha.1 : Nat)
  have hpair : ∀ alpha,
      let index : Nat → Nat := fun n ↦ L.φ (psi n)
      let Xpsi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : ∀ n : Nat, (Xpsi.obj n).M :=
        fun n ↦ seqCenterD inp.decay P Lpsi n (alpha.1 : Nat)
      HasDiagPairConv (I := I) (hcomplete.subseq index)
        (PointedRiemannianSeq.connected_subseq hconn index)
        c (q alpha) (q alpha / 2) (δ alpha) (deltaInf alpha)
        (e alpha) (eInf alpha) := by
    intro alpha
    have hcan := (hpair0 alpha).1.subseq shift hshift.tendsto_atTop
    have hcanFence : ∀ n,
        NormalDiagFence (I := I) ((X0.subseq shift).obj n)
          (c0 alpha (shift n)) (q alpha) (e0 alpha (shift n)) := by
      intro n
      exact (hpair0 alpha).2 (shift n)
    have hsel := hcan.congr_stage hcanFence (hδ alpha)
      (hnormal alpha) (hfence alpha)
    simpa only [index0, X0, c0, psi, Lpsi, PointedRiemannianSeq.subseq,
      NetLimitData.subseq, Function.comp_apply, seqCenterD_subseq] using hsel
  refine ⟨psi, hpsi, gInf, deltaInf, e, eInf,
    hcenter, hQAll, hmetric, hbranchAll, ?_⟩
  dsimp only
  intro alpha
  exact ⟨hpair alpha, hfence alpha⟩

end MetricCompactnessInputs
end HCGCompactness
end DifferentialGeometry
