import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageComparison

set_option autoImplicit false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}


def IsStableNet
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) : Prop :=
  ∀ a b : Nat,
    (∀ᶠ k in atTop,
      BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
    (∀ᶠ k in atTop,
      ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k))


def HasStageRefine
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) : Prop :=
  ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
      (U : LiveSlot L inp.pack r → Set E)
      (C0 C1 : LiveSlot L inp.pack r → Set E)
      (aInf : (alpha : LiveSlot L inp.pack r) →
        Fin (inp.pack.A r) → E → Real)
      (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
        InterSlot L inp.pack r alpha → E → E)
      (gInf : LiveSlot L inp.pack r →
        E → (E →L[Real] E →L[Real] Real)),
    HasStageJetData inp P L hr phi hphi hconn U C0 C1
      aInf Jinf Jbarinf gInf



def HasStageSeed
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) : Prop :=
  IsStableNet inp P L0 ∧
    ∀ (L : NetLimitData inp.decay inp.D P), IsStableNet inp P L →
      ∀ (r : Real) (hr : 0 ≤ r),
        HasStageRefine inp P L hconn r hr


theorem HasStageSeed.refine
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn)
    (L : NetLimitData inp.decay inp.D P) (hstable : IsStableNet inp P L)
    (r : Real) (hr : 0 ≤ r) :
    HasStageRefine inp P L hconn r hr :=
  hseed.2 L hstable r hr



theorem HasStageSeed.subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (r : Real) (hr : 0 ≤ r) :
    HasStageRefine inp P (L0.subseq hψ) hconn r hr := by
  apply hseed.refine inp P L0 hconn (L0.subseq hψ) _ r hr
  exact NetLimitData.stable_subseq inp.decay P L0 hψ hseed.1




theorem MetricCompactBase.exists_stage_seed
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    ∃ (inp : MetricCompactnessInputs (I := I) X)
        (L0 : NetLimitData inp.decay inp.D
          (inp.properMetrics hcomplete hconn)),
      HasStageSeed inp (inp.properMetrics hcomplete hconn) L0 hconn := by
  classical
  obtain ⟨aMin, haMin, hread⟩ :=
    exists_hat_cm_min (I := I) b.normalRadius b.realizes
      hcomplete hconn
  let c0 :=
    (8 * Real.exp b.decay.C / aMin) * b.normalRadius.gpRatio
  obtain ⟨D, hD_one, _hmuD, hc0, h8, _h16, hradD, hradRatio, hcap⟩ :=
    b.exists_item3D c0
  have hD : 0 < D := zero_lt_one.trans hD_one
  let inp := MetricCompactnessInputs.ofBase b D hD hcap
  have h8' : (8 : Real) < inp.normalRadius.gpRatio * inp.D := by
    simpa only [inp, MetricCompactnessInputs.ofBase] using h8
  have hradD' : 2 * item3RadiusFactor inp.decay inp.D < inp.D := by
    simpa only [inp, MetricCompactnessInputs.ofBase] using hradD
  have hradRatio' : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D := by
    simpa only [inp, MetricCompactnessInputs.ofBase] using hradRatio
  have hc0' :
      (8 * Real.exp inp.decay.C / aMin) * inp.normalRadius.gpRatio <
        inp.normalRadius.gpRatio * inp.D := by
    simpa only [inp, c0, MetricCompactnessInputs.ofBase] using hc0
  have hphys : 8 * Real.exp inp.decay.C < aMin * inp.D :=
    inp.physScale_of_extra haMin hc0'
  let P := inp.properMetrics hcomplete hconn
  obtain ⟨L0, hstable0⟩ := inp.exists_stable_net P
  refine ⟨inp, L0, ?_⟩
  dsimp only [HasStageSeed]
  refine ⟨hstable0, ?_⟩
  intro L hstable r hr
  dsimp only [IsStableNet] at hstable
  dsimp only [HasStageRefine]
  obtain ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, hconv,
      hptsTail⟩ :=
    inp.exists_supp_pts_fin h8' hradD' hradRatio' P L hstable r hr hconn
  let Lphi := L.subseq hphi
  obtain ⟨q, δ, hqdata, hqWide, hqAcc, herr, hinvErr,
      hbranchTail, hscaleTail, hreadTail⟩ :=
    hread inp.hD hphys P Lphi inp.pack r
  have hqdata0 : ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rhoMin := aMin * inp.decay.mu Rgamma
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
        2 * rhoMin < (q gamma : Real) := by
    simpa only [Lphi, NetLimitData.subseq] using hqdata
  have hqWide0 : ∀ gamma : LiveSlot L inp.pack r,
      6 * (q gamma : Real) < inp.normalRadius.phaseRadius
        (L.rInf (gamma.1 : Nat) + 1) := by
    simpa only [Lphi, NetLimitData.subseq] using hqWide
  have hqAcc0 := hqAcc
  have herr0 := herr
  have hinvErr0 := hinvErr
  simp only [Lphi, NetLimitData.subseq] at hqAcc0 herr0 hinvErr0
  have hC1q : ∀ gamma : LiveSlot L inp.pack r,
      C1 gamma ⊆ Metric.ball 0 ((q gamma : Real) / 2) := by
    intro gamma z hz
    have hconv0 := hconv
    dsimp only [HasSuppConvData] at hconv0
    have hzBall := (hconv0.2.1 gamma)
      ((hconv0.2.2.2.2.2.1 gamma) hz)
    have hlam := lamInf_lt_halfMin inp.decay inp.hD hphys P L
      (gamma.1 : Nat)
    have hqGamma := hqdata0 gamma
    dsimp only at hqGamma
    rw [Metric.mem_ball] at hzBall ⊢
    linarith [hqGamma.2.2.2]
  have hcapTail : ∀ᶠ n in Filter.atTop,
      HasSuppCmData (I := I) inp P L r hr phi hphi n
        hcomplete hconn U aInf q δ := by
    filter_upwards [hptsTail, hreadTail] with n hn hreadN
    let Y := X.obj (Lphi.φ n)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn (Lphi.φ n)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
      Y.riemBundle (I := I)
    letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M :=
      MetricComplete.complete (I := I) Y (hcomplete.complete (Lphi.φ n))
    letI : MetricSpace Y.M :=
      HopfRinow.riemMetricSpace (I := I) (M := Y.M)
    let beta := fun (k : Nat) (alpha : LiveSlot L inp.pack r) =>
      seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
    let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
        (gamma : Fin (inp.pack.A r)) =>
      rawWeights
        (cutRaw
          (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
          (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
        z gamma
    let chi := fun (alpha : LiveSlot L inp.pack r) =>
      NormalCoordinates.normalChartAt (I := I) Y.metric (beta n alpha)
    let sourceBall := Lphi.hatSourceBall inp.decay P r n
    let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      sourceBall ∩ (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    let localWeight := fun (alpha : LiveSlot L inp.pack r)
        (x : Y.M) (gamma : Fin (inp.pack.A r)) =>
      weightInf alpha (chi alpha x) gamma
    let pairPts : (alpha : LiveSlot L inp.pack r) →
        InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
      fun alpha target a b x =>
        (chi alpha).symm
          (normalTransition (I := I) (X.obj (Lphi.φ b))
            (beta b target.1) (beta b alpha)
            (normalTransition (I := I) (X.obj (Lphi.φ a))
              (beta a alpha) (beta a target.1) (chi alpha x)))
    let pts := fun (alpha : LiveSlot L inp.pack r) =>
      totalPts (X := X) pairPts alpha
    dsimp only at hn hreadN
    rcases hn with ⟨hcompact, hcover, hhat, hweight, hpts⟩
    dsimp only [HasSuppCmData]
    refine ⟨hcompact, ?_⟩
    dsimp only [HasSuppCmFin]
    have hlocal := fun alpha =>
      hreadN.2 alpha (sourcePatch alpha) (hhat alpha)
        (localWeight alpha) (hweight alpha) (pts alpha) (hpts alpha)
    choose radSeq hpos hactive hsmall hcapLocal using hlocal
    refine ⟨radSeq, hcover, hhat, hweight, hpos, hactive, ?_, ?_⟩
    · intro epsilon hepsilon
      exact finite_cover_two_tail hcover
        (fun alpha a b x => radSeq alpha a b x < epsilon)
        (fun alpha => hsmall alpha epsilon hepsilon)
    · exact finite_cover_two_tail hcover _ hcapLocal
  have hq : ∀ alpha : LiveSlot L inp.pack r, 0 < q alpha := by
    intro alpha
    have h := hqdata0 alpha
    dsimp only at h
    exact h.1
  have hδ : ∀ alpha : LiveSlot L inp.pack r, 0 < δ alpha := by
    intro alpha
    have h := hqdata0 alpha
    dsimp only at h
    exact h.2.1
  have hqWidePhi : ∀ alpha : LiveSlot L inp.pack r,
      6 * (q alpha : Real) < inp.normalRadius.phaseRadius
        (Lphi.rInf (alpha.1 : Nat) + 1) := by
    simpa only [Lphi, NetLimitData.subseq] using hqWide0
  let ScaleAt : Nat → Prop := fun n =>
    ∀ gamma : LiveSlot L inp.pack r,
      let Rgamma := Lphi.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      let x := seqCenterD inp.decay P Lphi n (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (Lphi.φ n)).M :=
        (X.obj (Lphi.φ n)).topology
      letI : ChartedSpace H (X.obj (Lphi.φ n)).M :=
        (X.obj (Lphi.φ n)).charted
      letI : IsManifold I ∞ (X.obj (Lphi.φ n)).M :=
        (X.obj (Lphi.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (Lphi.φ n)).M) :=
        (X.obj (Lphi.φ n)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆
          normalQuarter (I := I) (X.obj (Lphi.φ n)) x ∧
        rho ≤ inp.normalBounds.radius (Lphi.φ n) x ∧
        rho / 2 ≤ expRadiusGp
          (I := I) (X.obj (Lphi.φ n)).metric x
  let Q : Nat → Prop := fun n =>
    HasSuppCmData (I := I) inp P L r hr phi hphi n
        hcomplete hconn U aInf q δ ∧
      ScaleAt n
  have hQ : ∀ᶠ n in Filter.atTop, Q n := by
    filter_upwards [hcapTail, hscaleTail] with n hcapN hscaleN
    exact ⟨hcapN, hscaleN⟩
  obtain ⟨psi, hpsi, gInf, deltaInf, e, eInf,
      _hcenter0, hQAll, hmetric0, hbranchAll, hpair0⟩ :=
    inp.exists_diag_full P Lphi r hcomplete hconn aMin q δ hq hδ
      hqWidePhi hqAcc0 herr0 hinvErr0 hbranchTail Q hQ
  let theta := phi ∘ psi
  have htheta : StrictMono theta := hphi.comp hpsi
  let Ltheta := L.subseq htheta
  have hconvTheta :
      HasSuppConvData (I := I) inp P L r hr theta htheta U C0 C1
        aInf Jinf Jbarinf := by
    simpa only [theta] using
      HasSuppConvData.subseq inp P L r hr hphi U C0 C1 aInf Jinf Jbarinf
        hconv hpsi
  have hmetric : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      let Ualpha := Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius Ralpha)
      ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
      MapCInfConvOnCompacts Ualpha
        (fun n => normalCoordMetric (I := I)
          (X.obj (Ltheta.φ n))
          (seqCenterD inp.decay P Ltheta n (alpha.1 : Nat)))
        (gInf alpha) ∧
      ∀ z ∈ Ualpha, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
          gInf alpha z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro alpha
    simpa only [Lphi, Ltheta, theta, NetLimitData.subseq,
      Function.comp_apply, seqCenterD_subseq] using hmetric0 alpha
  have hbranchTheta : ∀ n,
      HasLiveBrFull (I := I) P Ltheta inp.pack r n
        hcomplete hconn aMin q δ := by
    intro n
    simpa only [Lphi, Ltheta, theta, HasLiveBrFull, NetLimitData.subseq,
      Function.comp_apply, seqCenterD_subseq] using hbranchAll n
  have hscaleAll : ∀ n (gamma : LiveSlot L inp.pack r),
      let Rgamma := Ltheta.rInf (gamma.1 : Nat) + 1
      let rho := aMin * inp.decay.mu Rgamma
      let x := seqCenterD inp.decay P Ltheta n (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (Ltheta.φ n)).M :=
        (X.obj (Ltheta.φ n)).topology
      letI : ChartedSpace H (X.obj (Ltheta.φ n)).M :=
        (X.obj (Ltheta.φ n)).charted
      letI : IsManifold I ∞ (X.obj (Ltheta.φ n)).M :=
        (X.obj (Ltheta.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (Ltheta.φ n)).M) :=
        (X.obj (Ltheta.φ n)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆
          normalQuarter (I := I) (X.obj (Ltheta.φ n)) x ∧
        rho ≤ inp.normalBounds.radius (Ltheta.φ n) x ∧
        rho / 2 ≤ expRadiusGp
          (I := I) (X.obj (Ltheta.φ n)).metric x := by
    intro n gamma
    have hn := hQAll n
    dsimp only [Q] at hn
    simpa only [ScaleAt, Lphi, Ltheta, theta, NetLimitData.subseq,
      Function.comp_apply, seqCenterD_subseq] using hn.2 gamma
  let index : Nat → Nat := fun n => Ltheta.φ n
  let Xtheta : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
  let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xtheta.obj n).M :=
    fun alpha n => seqCenterD inp.decay P Ltheta n (alpha.1 : Nat)
  have hpair : ∀ alpha,
      HasDiagPairConv (I := I) (hcomplete.subseq index)
          (PointedRiemannianSeq.connected_subseq hconn index)
          (c alpha) (q alpha) (q alpha / 2)
          (δ alpha) (deltaInf alpha) (e alpha) (eInf alpha) ∧
        ∀ n, NormalDiagFence (I := I) (Xtheta.obj n)
          (c alpha n) (q alpha) (e alpha n) := by
    intro alpha
    simpa only [index, Xtheta, c, Lphi, Ltheta, theta,
      PointedRiemannianSeq.subseq, NetLimitData.subseq,
      Function.comp_apply, seqCenterD_subseq] using hpair0 alpha
  obtain ⟨_W, _PhiInf, _rootRho, _Phi3, _hroot, _hreadRoot, hjet⟩ :=
    hconvTheta.exists_stage_tail inp aMin haMin hphys h8' hradD'
      hradRatio' P L hstable hr theta htheta U C0 C1 aInf Jinf Jbarinf
      hcomplete hconn q δ hqdata0 hqAcc0 hC1q hbranchTheta hscaleAll
      deltaInf e eInf (fun alpha => (hpair alpha).1)
      (fun alpha n => (hpair alpha).2 n)
  obtain ⟨hgp, _hrad⟩ :=
    inp.item3ScaleTails h8' hradD' hradRatio' P L r
  have hgpTheta : Item3GpScaleTail (I := I) inp.decay inp.D P
      (L.subseq htheta) inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r htheta
  have hbase : HasStageBaseTail (I := I) inp P L hr theta htheta hconn := by
    dsimp only [HasStageBaseTail]
    filter_upwards [hgpTheta] with k hk
    intro l
    exact stageCompare_base inp P (L.subseq htheta) r hr hconn k l hk
  have hmetric' : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      let Ualpha := Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius Ralpha)
      C1 alpha ⊆ Ualpha ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
      MapCInfConvOnCompacts Ualpha
        (fun n => normalCoordMetric (I := I)
          (X.obj ((L.subseq htheta).φ n))
          (seqCenterD inp.decay P (L.subseq htheta) n
            (alpha.1 : Nat)))
        (gInf alpha) ∧
      ∀ z ∈ Ualpha, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
          gInf alpha z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro alpha
    rcases hmetric alpha with ⟨hgInf, hconvMetric, hequiv⟩
    refine ⟨?_, hgInf, hconvMetric, hequiv⟩
    have hqPos : 0 < (q alpha : Real) := by
      exact_mod_cast (hqdata0 alpha).1
    have hhalfSix : (q alpha : Real) / 2 < 6 * (q alpha : Real) := by
      linarith
    have hhalfPhase : (q alpha : Real) / 2 <
        inp.normalRadius.phaseRadius (L.rInf (alpha.1 : Nat) + 1) :=
      hhalfSix.trans (hqWide0 alpha)
    exact (hC1q alpha).trans (Metric.ball_subset_ball hhalfPhase.le)
  refine ⟨theta, htheta, U, C0, C1, aInf, Jinf, Jbarinf, gInf, ?_⟩
  dsimp only [HasStageJetData]
  exact ⟨hconvTheta, hmetric', hjet, hbase⟩

end HCGCompactness
end DifferentialGeometry
