import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageFill
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageCenter
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchConvexity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchCage
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCHatReadout
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSupportCapstone
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalMetricExtend
import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoIFT

set_option autoImplicit false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}




theorem uniqueStage_of_fill
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat)
    (qstar : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M)
    (join : (X.obj (L.φ l)).M → (X.obj (L.φ l)).M → Real →
      (X.obj (L.φ l)).M)
    (p : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M)
    (rad : (X.obj (L.φ k)).M → Real)
    (x : (X.obj (L.φ k)).M)
    (hcm :
      let Y := X.obj (L.φ l)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn (L.φ l)
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      let i0 := baseIndex inp.decay inp.realizes inp.pack hs
      let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
        rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          y gamma
      CenterInput (I := I) Y.metric (mu x)
        (centerAverage.activeFill mu (stageTarget inp P L s k l) qstar x)
        join (p x) (rad x)) :
    HasUniqueStageCenter inp P L s hs hconn k l x := by
  let Y := X.obj (L.φ l)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn (L.φ l)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
    rawWeights
      (cutRaw
        (seqAtom inp.decay inp.hD P L inp.pack s k i0)
        (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
      y gamma
  have huniq := centerAverage.uniqueMin_activeFill (I := I) Y.metric mu
    (stageTarget inp P L s k l) qstar join p rad x hcm
  simpa only [HasUniqueStageCenter, i0, mu] using huniq



theorem stageCompare_eq_cm
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (s : Real) (hs : 0 ≤ s)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (k l : Nat)
    (qstar : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M)
    (join : (X.obj (L.φ l)).M → (X.obj (L.φ l)).M → Real →
      (X.obj (L.φ l)).M)
    (p : (X.obj (L.φ k)).M → (X.obj (L.φ l)).M)
    (rad : (X.obj (L.φ k)).M → Real)
    (x : (X.obj (L.φ k)).M)
    (hx : x ∈ L.hatSourceBall inp.decay P s k)
    (hcm :
      let Y := X.obj (L.φ l)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn (L.φ l)
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      let i0 := baseIndex inp.decay inp.realizes inp.pack hs
      let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
        rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          y gamma
      CenterInput (I := I) Y.metric (mu x)
        (centerAverage.activeFill mu (stageTarget inp P L s k l) qstar x)
        join (p x) (rad x)) :
    stageComparisonMap inp P L s hs hconn k l x =
      let Y := X.obj (L.φ l)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn (L.φ l)
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      let i0 := baseIndex inp.decay inp.realizes inp.pack hs
      let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
        rawWeights
          (cutRaw
            (seqAtom inp.decay inp.hD P L inp.pack s k i0)
            (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
          y gamma
      centerOfMass (I := I) Y.metric (mu x)
        (centerAverage.activeFill mu (stageTarget inp P L s k l) qstar x)
        join (p x) (rad x) hcm := by
  let Y := X.obj (L.φ l)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn (L.φ l)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  let i0 := baseIndex inp.decay inp.realizes inp.pack hs
  let mu := fun (y : (X.obj (L.φ k)).M) (gamma : Fin (inp.pack.A s)) =>
    rawWeights
      (cutRaw
        (seqAtom inp.decay inp.hD P L inp.pack s k i0)
        (seqAtom inp.decay inp.hD P L inp.pack s k) i0)
      y gamma
  let q := centerOfMass (I := I) Y.metric (mu x)
    (centerAverage.activeFill mu (stageTarget inp P L s k l) qstar x)
    join (p x) (rad x) hcm
  change stageComparisonMap inp P L s hs hconn k l x = q
  have huniq := uniqueStage_of_fill (I := I) inp P L s hs hconn k l
    qstar join p rad x hcm
  rw [stageCompare_choose (I := I) inp P L s hs hconn k l x hx huniq]
  apply huniq.unique
  · exact Classical.choose_spec huniq.exists
  · intro z
    rw [← centerAverage.energy_activeFill (I := I) Y.metric mu
      (stageTarget inp P L s k l) qstar x q,
      ← centerAverage.energy_activeFill (I := I) Y.metric mu
        (stageTarget inp P L s k l) qstar x z]
    exact centerOfMass.min hcm z



theorem HasSuppConvData.pts_target_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      ∀ (alpha : LiveSlot L inp.pack r) (z : E), z ∈ U alpha →
        ∀ gamma : Fin (inp.pack.A r),
          stageWeightSub inp P L hr phi hphi alpha k z gamma ≠ 0 →
            let Lphi := L.subseq hphi
            let Yk := X.obj (Lphi.φ k)
            let Yl := X.obj (Lphi.φ l)
            letI : TopologicalSpace Yk.M := Yk.topology
            letI : ChartedSpace H Yk.M := Yk.charted
            letI : IsManifold I ∞ Yk.M := Yk.smooth
            letI : T2Space Yk.M := Yk.t2
            letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
            letI : TopologicalSpace Yl.M := Yl.topology
            letI : ChartedSpace H Yl.M := Yl.charted
            letI : IsManifold I ∞ Yl.M := Yl.smooth
            letI : T2Space Yl.M := Yl.t2
            letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
            let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
            let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
              (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
            chiL.symm (stagePtsSub inp P L phi hphi alpha k l z gamma) =
                stageTarget inp P Lphi r k l (chiK.symm z) gamma ∧
              chiL (stageTarget inp P Lphi r k l (chiK.symm z) gamma) =
                stagePtsSub inp P L phi hphi alpha k l z gamma := by
  classical
  let Lphi := L.subseq hphi
  letI (alpha : LiveSlot L inp.pack r) :
      Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  have hpts := hdata.pts_eq_ne inp h8 hradD hradRatio P L hstable hr
    phi hphi U C0 C1 aInf Jinf Jbarinf
  obtain ⟨hgp, hrad⟩ := inp.item3ScaleTails h8 hradD hradRatio P L r
  have hgpPhi : Item3GpScaleTail (I := I) inp.decay inp.D P
      Lphi inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r hphi
  have hradPhi : Item3RadiusTail (I := I) inp.decay inp.D P
      Lphi inp.pack r (item3RadiusFactor inp.decay inp.D) :=
    hrad.subseq inp.decay inp.D P L inp.pack r
      (item3RadiusFactor inp.decay inp.D) hphi
  have hcenters : ∀ᶠ k in Filter.atTop,
      ∀ beta : LiveSlot L inp.pack r,
        seqCenter inp.decay inp.D P (Lphi.φ k) (beta.1 : Nat) =
          some (seqCenterD inp.decay P Lphi k (beta.1 : Nat)) :=
    Filter.eventually_all.mpr fun beta =>
      seqCenterD_live inp.decay P Lphi (beta.1 : Nat) (by
        simpa only [Lphi, NetLimitData.subseq] using beta.2)
  have hfactor : (8 : Real) ≤ item3RadiusFactor inp.decay inp.D := by
    have hExp : (1 : Real) ≤
        Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
      rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr
        (mul_nonneg inp.decay.C_nonneg
          (by nlinarith [(inp.decay.lambda_pos inp.hD 0).le]))
    rw [item3RadiusFactor]
    nlinarith
  have hrev : ∀ᶠ l in Filter.atTop,
      ∀ (alpha : LiveSlot L inp.pack r)
        (target : InterSlot L inp.pack r alpha),
        NormalOverlapOn (I := I) (X.obj (Lphi.φ l))
          (seqCenterD inp.decay P Lphi l (target.1.1 : Nat))
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) := by
    refine Filter.eventually_all.mpr fun alpha => ?_
    refine Filter.eventually_all.mpr fun target => ?_
    have hinterRev : ∀ᶠ n in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf
          (target.1.1 : Nat) (alpha.1 : Nat) (L.φ n) :=
      target.2.mono fun _ hn =>
        BInter.symm inp.decay inp.D P L.lamInf hn
    have ht := hphi.tendsto_atTop.eventually
      (inp.pair_overlap_tail hradD hradRatio P L r
        target.1 alpha hinterRev)
    exact ht.mono fun l hl => by
      simpa only [Lphi, NetLimitData.subseq, Function.comp_apply,
        seqCenterD_subseq, NetLimitData.subseq_lamInf] using
          hl.2.2.2.2.2.1
  have hall := hpts.and (hgpPhi.and (hradPhi.and (hcenters.and hrev)))
  rw [Filter.eventually_atTop] at hall
  rcases hall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk l hl
  rcases hN k hk with ⟨hptsK, hgpK, hradK, hcentersK, _hrevK⟩
  have hrevL := (hN l hl).2.2.2.2
  intro alpha z hz gamma hweight
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  obtain ⟨target, htarget, hraw⟩ :=
    hptsK alpha l z hz gamma hweight
  have hC2gamma : 8 * L.lamInf (target.1.1 : Nat) ≤
      expMapC2Radius (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) := by
    have hscale : 8 * Lphi.lamInf (target.1.1 : Nat) ≤
        item3RadiusFactor inp.decay inp.D *
          Lphi.lamInf (target.1.1 : Nat) :=
      mul_le_mul_of_nonneg_right hfactor
        (inp.decay.lambda_pos inp.hD
          (L.rInf (target.1.1 : Nat))).le
    have hcenter := hcentersK target.1
    have hradTarget := hradK target.1.1
      (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) (by
        simpa only using hcenter)
    simpa only [Lphi, NetLimitData.subseq_lamInf] using
      hscale.trans hradTarget.2
  let alphaPhi : LiveSlot Lphi inp.pack r :=
    ⟨alpha.1, by simpa only [Lphi, NetLimitData.subseq] using alpha.2⟩
  have hsmall : normalTransition (I := I) Yk
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) z ∈
      Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat)) := by
    have hs := stageWeight_small inp P Lphi hr alphaPhi k hgpK
      target.1.1 (by
        simpa only [Lphi, NetLimitData.subseq_lamInf] using hC2gamma) z (by
          simpa only [stageWeightSub, stageWeight, alphaPhi, Lphi,
            htarget] using hweight)
    simpa only [alphaPhi, Lphi, NetLimitData.subseq_lamInf] using hs
  have hv : normalTransition (I := I) Yk
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)) z ∈
      Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) := by
    rw [Metric.mem_ball] at ⊢
    rw [Metric.mem_closedBall] at hsmall
    have hlam : 0 < L.lamInf (target.1.1 : Nat) :=
      inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat))
    nlinarith
  have hsrc : stageTarget inp P Lphi r k l
        ((NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z)
        target.1.1 ∈
      (NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).source := by
    have hov := (hrevL alpha target _ hv).2
    simpa only [stageTarget, normalTransition, Yk, Yl] using hov
  subst gamma
  rw [hraw]
  exact ⟨stageTarget_local (I := I) inp P Lphi r k l
      alpha.1 target.1.1 z hsrc,
    stageTarget_chart (I := I) inp P Lphi r k l
      alpha.1 target.1.1 z⟩




theorem HasSuppConvData.pts_target_dist
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r)
    (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      ∀ gamma : Fin (inp.pack.A r),
        stageWeightSub inp P L hr phi hphi alpha k z gamma ≠ 0 →
          let Lphi := L.subseq hphi
          let Yk := X.obj (Lphi.φ k)
          let Yl := X.obj (Lphi.φ l)
          letI : TopologicalSpace Yk.M := Yk.topology
          letI : ChartedSpace H Yk.M := Yk.charted
          letI : IsManifold I ∞ Yk.M := Yk.smooth
          letI : T2Space Yk.M := Yk.t2
          letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
          letI : TopologicalSpace Yl.M := Yl.topology
          letI : ChartedSpace H Yl.M := Yl.charted
          letI : IsManifold I ∞ Yl.M := Yl.smooth
          letI : T2Space Yl.M := Yl.t2
          letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
          letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
          let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
            (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
          dist (chiL.symm z)
            (stageTarget inp P Lphi r k l (chiK.symm z) gamma) < eps := by
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hC0U : C0 alpha ⊆ U alpha :=
    hC01.trans (interior_subset.trans hC1U)
  obtain ⟨Nt, htarget⟩ := hdata.pts_target_tail inp h8 hradD hradRatio
    P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf
  obtain ⟨Nd, hdist⟩ := hdata.pts_dist_tail inp P L hr phi hphi U C0 C1
    aInf Jinf Jbarinf alpha eps heps
  refine ⟨max Nt Nd, ?_⟩
  intro k hk l hl z hz gamma hweight
  have hkT : Nt ≤ k := (le_max_left Nt Nd).trans hk
  have hlT : Nt ≤ l := (le_max_left Nt Nd).trans hl
  have hkD : Nd ≤ k := (le_max_right Nt Nd).trans hk
  have hlD : Nd ≤ l := (le_max_right Nt Nd).trans hl
  have heq := htarget k hkT l hlT alpha z (hC0U hz) gamma hweight
  have hclose := hdist k hkD l hlD z hz gamma
  dsimp only at heq ⊢
  rw [← heq.1]
  exact hclose




theorem HasSuppConvData.actual_cm_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let rho := aMin * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1)
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hqAcc : ∀ gamma : LiveSlot L inp.pack r,
      3 * inp.normalBounds.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q gamma : Real))
    (hbranch : ∀ᶠ n in Filter.atTop,
      HasLiveBrFull (I := I) P (L.subseq hphi) inp.pack r n
        hcomplete hconn aMin q δ)
    (hscale : ∀ᶠ n in Filter.atTop,
      ∀ gamma : LiveSlot L inp.pack r,
        let Lphi := L.subseq hphi
        let rho := aMin * inp.decay.mu (Lphi.rInf (gamma.1 : Nat) + 1)
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
            (I := I) (X.obj (Lphi.φ n)).metric x)
    (alpha : LiveSlot L inp.pack r)
    (eps : Real) (heps : 0 < eps) :
    ∃ rad : Real, 0 < rad ∧ rad < eps ∧
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
        let Lphi := L.subseq hphi
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : IsManifold I 1 Yl.M := IsManifold.of_le
          (I := I) (M := Yl.M) (n := ∞) (by decide)
        letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
        letI : T2Space Yl.M := Yl.t2
        letI : ConnectedSpace Yl.M := hconn (Lphi.φ l)
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        letI : TopologicalSpace.MetrizableSpace Yl.M :=
          Manifold.metrizableSpace I Yl.M
        letI : T3Space Yl.M := inferInstance
        letI : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
          Yl.riemBundle (I := I)
        letI : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
          Yl.riemInner (I := I)
        letI : IsContinuousRiemannianBundle E
            (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
        letI : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
        letI : CompleteSpace Yl.M :=
          MetricComplete.complete (I := I) Yl (hcomplete.complete (Lphi.φ l))
        letI : MetricSpace Yl.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
        let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
        let mu := stageWeightSub inp P L hr phi hphi alpha k
        let stagePts := fun w gamma =>
          stageTarget inp P Lphi r k l (chiK.symm w) gamma
        let qstar := fun w => chiL.symm w
        let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
        ∃ hcm : CenterInput (I := I) Yl.metric (mu z)
            (centerAverage.activeFill mu stagePts qstar z)
            join (qstar z) rad,
          HasHatCmStrictAt (I := I) inp.decay P Lphi inp.pack r l
            hcomplete hconn q δ alpha (mu z)
            (centerAverage.activeFill mu stagePts qstar z)
            join (qstar z) rad hcm ∧
          dist
              (chiL (centerOfMass (I := I) Yl.metric (mu z)
                (centerAverage.activeFill mu stagePts qstar z)
                join (qstar z) rad hcm))
              z ≤ 4 * rad := by
  let Lphi := L.subseq hphi
  let rhoBase := aMin * inp.decay.mu (L.rInf (alpha.1 : Nat) + 1)
  let gap := rhoBase / 2 - 4 * L.lamInf (alpha.1 : Nat)
  have hgap : 0 < gap := by
    dsimp only [gap, rhoBase]
    linarith [lamInf_lt_halfMin inp.decay inp.hD hphys P L
      (alpha.1 : Nat)]
  let rad := min (gap / 12) (eps / 2)
  have hrad : 0 < rad := by
    dsimp only [rad]
    exact lt_min (div_pos hgap (by norm_num)) (div_pos heps (by norm_num))
  have hradEps : rad < eps := by
    have hle : rad ≤ eps / 2 := min_le_right _ _
    linarith
  have hcageReal : 4 * L.lamInf (alpha.1 : Nat) + 6 * rad <
      rhoBase / 2 := by
    have hradGap : rad ≤ gap / 12 := min_le_left _ _
    dsimp only [gap] at hradGap
    nlinarith
  have hcage : ENNReal.ofReal
        (4 * L.lamInf (alpha.1 : Nat) + 6 * rad) <
      ENNReal.ofReal (rhoBase / 2) := by
    exact (ENNReal.ofReal_lt_ofReal_iff
      (div_pos (mul_pos haMin (inp.decay.mu_pos _)) (by norm_num))).2 (by
        simpa only [rhoBase] using hcageReal)
  obtain ⟨hgp, _hradTail⟩ :=
    inp.item3ScaleTails h8 hradD hradRatio P L r
  have hweightEv := hdata.weightSub_ev inp P L hr hgp phi hphi
    U C0 C1 aInf Jinf Jbarinf
  rw [Filter.eventually_atTop] at hweightEv
  rcases hweightEv with ⟨Nw, hweight⟩
  obtain ⟨Np, hpts⟩ := hdata.pts_target_dist inp h8 hradD hradRatio
    P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf alpha rad hrad
  rw [Filter.eventually_atTop] at hbranch hscale
  rcases hbranch with ⟨Nb, hbranch⟩
  rcases hscale with ⟨Ns, hscale⟩
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hC0U : C0 alpha ⊆ U alpha :=
    hC01.trans (interior_subset.trans hC1U)
  refine ⟨rad, hrad, hradEps, max (max Nw Np) (max Nb Ns), ?_⟩
  intro k hk l hl z hz
  have hkW : Nw ≤ k := by omega
  have hkP : Np ≤ k := by omega
  have hlP : Np ≤ l := by omega
  have hlB : Nb ≤ l := by omega
  have hlS : Ns ≤ l := by omega
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : IsManifold I 1 Yl.M := IsManifold.of_le
    (I := I) (M := Yl.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  letI : T2Space Yl.M := Yl.t2
  letI : ConnectedSpace Yl.M := hconn (Lphi.φ l)
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Yl.M :=
    Manifold.metrizableSpace I Yl.M
  letI : T3Space Yl.M := inferInstance
  letI : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
    Yl.riemBundle (I := I)
  letI : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
    Yl.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
  letI : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
  letI : CompleteSpace Yl.M :=
    MetricComplete.complete (I := I) Yl (hcomplete.complete (Lphi.φ l))
  letI : MetricSpace Yl.M :=
    HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
    (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let mu := stageWeightSub inp P L hr phi hphi alpha k
  let stagePts := fun w gamma =>
    stageTarget inp P Lphi r k l (chiK.symm w) gamma
  let qstar := fun w => chiL.symm w
  let p := qstar z
  let x0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let rho := aMin * inp.decay.mu (L.rInf (alpha.1 : Nat) + 1)
  let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
  let pts := centerAverage.activeFill mu stagePts qstar z
  have hmu := hweight k hkW alpha
  have hzU : z ∈ U alpha := hC0U hz
  have hactive : ∀ gamma, mu z gamma ≠ 0 →
      dist p (stagePts z gamma) < rad := by
    intro gamma hne
    have hproper := hpts k hkP l hlP z hz gamma hne
    have hhd : inp.decay.dist (Lphi.φ l) p (stagePts z gamma) < rad := by
      rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ l)]
      exact hproper
    have hed : riemannianEDist I p (stagePts z gamma) =
        ENNReal.ofReal (inp.decay.dist (Lphi.φ l) p (stagePts z gamma)) := by
      have hrealize := inp.realizes.edist_eq (Lphi.φ l) p (stagePts z gamma)
      simpa [PointedRiemannianManifold.emetricSpace] using hrealize
    rw [HopfRinow.riemMetric_dist_eq, hed,
      ENNReal.toReal_ofReal (inp.realizes.dist_nonneg
        (Lphi.φ l) p (stagePts z gamma))]
    exact hhd
  have hptsFilled : ∀ gamma, dist p (pts gamma) < rad := by
    simpa only [pts, p] using
      centerAverage.activeFill_close
        (g := Yl.metric) (μ := mu) (pts := stagePts) (qstar := qstar)
        (x := z) hrad hactive
  have hpHat : p ∈
      Lphi.hatBall inp.decay inp.D P inp.pack r l alpha.1 := by
    have hpGeom :=
      ((hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf l alpha).2.2
        hzU).1
    simpa only [p, qstar, chiL, Lphi] using hpGeom
  have hproperCenter :
      (letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
       dist p x0) < 4 * L.lamInf (alpha.1 : Nat) := by
    have hhat := hat_dist_centerD inp.decay P Lphi inp.pack r hpHat
    simpa only [x0, Lphi, NetLimitData.subseq_lamInf] using hhat
  have hhdCenter : inp.decay.dist (Lphi.φ l) p x0 <
      4 * L.lamInf (alpha.1 : Nat) := by
    rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ l) p x0]
    exact hproperCenter
  have hedCenter : riemannianEDist I p x0 =
      ENNReal.ofReal (inp.decay.dist (Lphi.φ l) p x0) := by
    have hrealize := inp.realizes.edist_eq (Lphi.φ l) p x0
    simpa [PointedRiemannianManifold.emetricSpace] using hrealize
  have hpq : dist x0 p ≤ 4 * L.lamInf (alpha.1 : Nat) := by
    rw [dist_comm, HopfRinow.riemMetric_dist_eq, hedCenter,
      ENNReal.toReal_ofReal (inp.realizes.dist_nonneg (Lphi.φ l) p x0)]
    exact hhdCenter.le
  have hscaleL := hscale l hlS alpha
  dsimp only [Lphi] at hscaleL
  rcases hscaleL with ⟨hquarter, hρmetric, hρexp⟩
  have hfull := hbranch l hlB alpha
  rcases hqdata alpha with ⟨_hq, _hδ, hρ, hρq⟩
  have hstrict : StrictDistInput (I := I) Yl.metric pts join p rad := by
    simpa only [Yl, x0, rho, pts, join, Lphi, NetLimitData.subseq] using
      HasNormalBrFull.strict_dist (I := I) inp.normalBounds (Lphi.φ l)
        (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) x0 hfull
        (hqAcc alpha) pts p rad (4 * L.lamInf (alpha.1 : Nat))
        hquarter hρ hρq hρmetric hρexp hrad hpq hptsFilled hcage
  let hcomplete' :=
    NetLimitData.sourceComplete (I := I) inp.decay P Lphi l hcomplete
      (hconn (Lphi.φ l))
  have hcm : CenterInput (I := I) Yl.metric (mu z) pts join p rad := by
    simpa only [pts, p] using
      centerAverage.inputOfFillSelf (I := I)
        (g := Yl.metric) (μ := mu) (pts := stagePts) (join := join)
        (r := fun _ => rad) (qstar := qstar) z hcomplete' hrad hactive
        (hmu.nonneg z hzU) (hmu.pos z hzU) hstrict
  have hcage2 : ENNReal.ofReal
        (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) <
      ENNReal.ofReal (rhoBase / 2) := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans_lt hcage
    nlinarith [hrad]
  have hqdataPhi : ∀ gamma : LiveSlot Lphi inp.pack r,
      let rhoGamma := aMin * inp.decay.mu
        (Lphi.rInf (gamma.1 : Nat) + 1)
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoGamma ∧
        2 * rhoGamma < (q gamma : Real) := by
    intro gamma
    simpa only [Lphi, NetLimitData.subseq] using hqdata gamma
  have hbranchScale : ∀ gamma : LiveSlot Lphi inp.pack r,
      let rhoGamma := aMin * inp.decay.mu
        (Lphi.rInf (gamma.1 : Nat) + 1)
      let xGamma := seqCenterD inp.decay P Lphi l (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (Lphi.φ l)).M :=
        (X.obj (Lphi.φ l)).topology
      letI : ChartedSpace H (X.obj (Lphi.φ l)).M :=
        (X.obj (Lphi.φ l)).charted
      letI : IsManifold I ∞ (X.obj (Lphi.φ l)).M :=
        (X.obj (Lphi.φ l)).smooth
      letI : T2Space (TangentBundle I (X.obj (Lphi.φ l)).M) :=
        (X.obj (Lphi.φ l)).t2TangentBundle
      HasNormalBrFull (I := I) (X.obj (Lphi.φ l))
          (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) xGamma
          (q gamma) (δ gamma) rhoGamma ∧
        rhoGamma ≤ inp.normalBounds.radius (Lphi.φ l) xGamma ∧
        rhoGamma / 2 ≤ expRadiusGp
          (I := I) (X.obj (Lphi.φ l)).metric xGamma := by
    intro gamma
    have hfullGamma := hbranch l hlB gamma
    have hscaleGamma := hscale l hlS gamma
    dsimp only [Lphi] at hscaleGamma ⊢
    exact ⟨hfullGamma, hscaleGamma.2.1, hscaleGamma.2.2⟩
  have hout := exists_hat_cm_sol_at (I := I) inp.decay P inp.realizes
    Lphi inp.pack r l hcomplete hconn q δ hqdataPhi hbranchScale alpha
    (mu z) pts join p rad hcm (hmu.sum_one z hzU) hpHat hcage2
  let c := centerOfMass (I := I) Yl.metric (mu z) pts join p rad hcm
  have hcMem : c ∈ Metric.closedBall p (2 * rad) := by
    simpa only [c] using centerOfMass.mem hcm
  have hpc : dist p c ≤ 2 * rad := by
    simpa only [dist_comm] using Metric.mem_closedBall.mp hcMem
  have hjoinDist {t : Real} (ht : 0 ≤ t) :
      dist p (join p c t) ≤ dist p c * t := by
    have hed := minJoin_edist_le (I := I) Yl.metric
      (normal_enorm (I := I) Yl) p c ht
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
    have hmul : 0 ≤ (riemannianEDist I p c).toReal * t :=
      mul_nonneg ENNReal.toReal_nonneg ht
    rw [ENNReal.toReal_ofReal hmul] at hmono
    simpa only [join, ← HopfRinow.riemMetric_dist_eq] using hmono
  have hjoin : Set.MapsTo (join p c) (Set.Icc (0 : Real) 1)
      (chiL.source ∩ chiL ⁻¹' Metric.ball (0 : E) rhoBase) := by
    intro t ht
    have hpt : dist p (join p c t) ≤ 2 * rad := by
      calc
        dist p (join p c t) ≤ dist p c * t := hjoinDist ht.1
        _ ≤ dist p c * 1 :=
          mul_le_mul_of_nonneg_left ht.2 dist_nonneg
        _ ≤ 2 * rad := by simpa only [mul_one] using hpc
    have hxt : dist x0 (join p c t) ≤
        4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
      calc
        dist x0 (join p c t) ≤ dist x0 p + dist p (join p c t) :=
          dist_triangle _ _ _
        _ ≤ 4 * L.lamInf (alpha.1 : Nat) + 2 * rad :=
          add_le_add hpq hpt
    have htReal : (riemannianEDist I x0 (join p c t)).toReal ≤
        4 * L.lamInf (alpha.1 : Nat) + 2 * rad := by
      rw [← HopfRinow.riemMetric_dist_eq]
      exact hxt
    have htExp : (riemannianEDist I x0 (join p c t)).toReal <
        expRadiusGp (I := I) Yl.metric x0 := by
      apply htReal.trans_lt
      calc
        4 * L.lamInf (alpha.1 : Nat) + 2 * rad < rhoBase / 2 := by
          nlinarith [hrad]
        _ ≤ expRadiusGp (I := I) Yl.metric x0 := by
          simpa only [rho, rhoBase, Lphi, NetLimitData.subseq] using hρexp
    have htControl := inp.normalBounds.chart_mem_norm_le (Lphi.φ l) x0
      (join p c t) ⟨Exponential.riemannianEDist_ne_top (I := I) _ _, htExp⟩
    refine ⟨htControl.1, ?_⟩
    change chiL (join p c t) ∈ Metric.ball (0 : E) rhoBase
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖chiL (join p c t)‖ ≤
          2 * (riemannianEDist I x0 (join p c t)).toReal := by
        simpa only [chiL, Yl, x0, Lphi] using htControl.2
      _ ≤ 2 * (4 * L.lamInf (alpha.1 : Nat) + 2 * rad) :=
        mul_le_mul_of_nonneg_left htReal (by norm_num)
      _ < rhoBase := by nlinarith [hcageReal, hrad]
  have hEquiv : NormalCoordMetricEquivOn (I := I) Yl x0
      (Metric.ball (0 : E) rhoBase) := by
    intro w hw v
    exact inp.normalBounds.metric_equiv (Lphi.φ l) x0 w
      (Metric.ball_subset_ball hρmetric hw) v
  have hchart := NormalCoordMetricEquivOn.chart_dist_le
    (I := I) Yl (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l))
      (normal_enorm (I := I) Yl) hEquiv hjoin
  have hchart' : dist (chiL p) (chiL c) ≤ Real.sqrt 2 * dist p c := by
    simpa only [chiL, ← HopfRinow.riemMetric_dist_eq] using hchart
  obtain ⟨_hRad, hExp, _hMaps⟩ :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf l alpha
  have hzTarget : z ∈ chiL.target := by
    have hzBall := hExp hzU
    have hzNorm : ‖z‖ < expMapC2Radius (I := I) Yl.metric x0 := by
      simpa only [Metric.mem_ball, dist_zero_right, Yl, x0, Lphi] using hzBall
    simpa only [chiL, Yl, x0, Lphi] using
      Geometry.Riemannian.ball_subset_normalChartAt_target
        (I := I) Yl.metric x0 hzNorm
  have hpDecode : chiL p = z := by
    simpa only [p, qstar] using chiL.right_inv hzTarget
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    linarith [Real.sqrt_two_lt_three_halves]
  have hcoord : dist (chiL c) z ≤ 4 * rad := by
    rw [← hpDecode, dist_comm]
    calc
      dist (chiL p) (chiL c) ≤ Real.sqrt 2 * dist p c := hchart'
      _ ≤ Real.sqrt 2 * (2 * rad) :=
        mul_le_mul_of_nonneg_left hpc (Real.sqrt_nonneg 2)
      _ ≤ 2 * (2 * rad) :=
        mul_le_mul_of_nonneg_right hsqrt (mul_nonneg (by norm_num) hrad.le)
      _ = 4 * rad := by ring
  refine ⟨hcm, ?_, ?_⟩
  · simpa only [mu, stagePts, qstar, pts, p, join] using hout
  · simpa only [mu, stagePts, qstar, pts, p, join, c] using hcoord



def HasStageRootReadout
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (C0 : LiveSlot L inp.pack r → Set E)
    (alpha : LiveSlot L inp.pack r)
    (Phi3 : Nat → Nat → Nat → E → E) : Prop :=
  ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
    let Lphi := L.subseq hphi
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    chiK.symm z ∈ Lphi.hatSourceBall inp.decay P r k →
      chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z)) =
          Phi3 l k l z ∧
        Phi3 l k l z ∈ normalBall (I := I) Yl
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat)) ∧
        stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z) =
            chiL.symm (Phi3 l k l z) ∧
        stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z) ∈
          (normalExpPD (I := I) Yl
            (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).target



theorem HasSuppConvData.stage_root_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let rho := aMin * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1)
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hqAcc : ∀ gamma : LiveSlot L inp.pack r,
      3 * inp.normalBounds.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q gamma : Real))
    (hbranch : ∀ᶠ n in Filter.atTop,
      HasLiveBrFull (I := I) P (L.subseq hphi) inp.pack r n
        hcomplete hconn aMin q δ)
    (hscale : ∀ᶠ n in Filter.atTop,
      ∀ gamma : LiveSlot L inp.pack r,
        let Lphi := L.subseq hphi
        let rho := aMin * inp.decay.mu (Lphi.rInf (gamma.1 : Nat) + 1)
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
            (I := I) (X.obj (Lphi.φ n)).metric x)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (hdiag :
      let Lphi := L.subseq hphi
      ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (δ alpha) (e n))
    (hfence :
      let Lphi := L.subseq hphi
      ∀ n, NormalDiagFence (I := I) (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat)) (q alpha) (e n))
    (W : Set E) (PhiInf : E → E) (rootRho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rootRho Phi3) :
    HasStageRootReadout inp P L hr phi hphi hconn C0 alpha Phi3 := by
  dsimp only [HasStageRootReadout]
  rcases hroot with
    ⟨_hW, _hWcpt, hC1W, hrootRho, hPhiInf, _htriple,
      Nroot, hrootTail⟩
  have heps : 0 < rootRho / 4 := by positivity
  obtain ⟨rad, hrad, hradSmall, Ncm, hcmTail⟩ :=
    hdata.actual_cm_tail inp aMin haMin hphys h8 hradD hradRatio
      P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf
      hcomplete hconn q δ hqdata hqAcc hbranch hscale alpha
      (rootRho / 4) heps
  obtain ⟨Ntgt, htgtTail⟩ :=
    hdata.pts_target_tail inp h8 hradD hradRatio P L hstable hr
      phi hphi U C0 C1 aInf Jinf Jbarinf
  refine ⟨max Nroot (max Ncm Ntgt), ?_⟩
  intro k hk l hl z hz hx
  have hkRoot : Nroot ≤ k := by omega
  have hlRoot : Nroot ≤ l := by omega
  have hkCm : Ncm ≤ k := by omega
  have hlCm : Ncm ≤ l := by omega
  have hkTgt : Ntgt ≤ k := by omega
  have hlTgt : Ntgt ≤ l := by omega
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : IsManifold I 1 Yl.M := IsManifold.of_le
    (I := I) (M := Yl.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  letI : T2Space Yl.M := Yl.t2
  letI : ConnectedSpace Yl.M := hconn (Lphi.φ l)
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Yl.M :=
    Manifold.metrizableSpace I Yl.M
  letI : T3Space Yl.M := inferInstance
  letI : RiemannianBundle (fun y : Yl.M ↦ TangentSpace I y) :=
    Yl.riemBundle (I := I)
  letI : (y : Yl.M) → InnerProductSpace Real (TangentSpace I y) :=
    Yl.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Yl.M ↦ TangentSpace I y) := Yl.riemBundle_cont (I := I)
  letI : EMetricSpace Yl.M := Yl.emetricSpace (I := I)
  letI : CompleteSpace Yl.M :=
    MetricComplete.complete (I := I) Yl (hcomplete.complete (Lphi.φ l))
  letI : MetricSpace Yl.M :=
    HopfRinow.riemMetricSpace (I := I) (M := Yl.M)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
    (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
  let mu := stageWeightSub inp P L hr phi hphi alpha k
  let stagePts := fun w gamma =>
    stageTarget inp P Lphi r k l (chiK.symm w) gamma
  let qstar := fun w => chiL.symm w
  let p := qstar z
  let x0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let join := minJoin (I := I) Yl.metric (normal_enorm (I := I) Yl)
  let pts := centerAverage.activeFill mu stagePts qstar z
  have hcmOut := hcmTail k hkCm l hlCm z hz
  dsimp only at hcmOut
  rcases hcmOut with ⟨hcm, hstrict, hcoord⟩
  let c := centerOfMass (I := I) Yl.metric (mu z) pts join p rad hcm
  let zc := chiL c
  let xi : Fin (inp.pack.A r) → E := fun i => chiL (pts i)
  have hzcClose : dist zc z < rootRho := by
    have hfour : 4 * rad < rootRho := by nlinarith [hradSmall]
    have hcoordLe : dist zc z ≤ 4 * rad := by
      simpa only [zc, c, mu, pts, join, p, qstar, stagePts, chiL] using
        hcoord
    exact hcoordLe.trans_lt hfour
  rcases hstrict with ⟨hqSel, eSel, heSel, hfSel, hread⟩
  dsimp only at hread
  rcases hread with ⟨hcSource, htgtSel, hzcBall, hchartSel, _hderiv⟩
  have hselZero : invVelSum eSel (mu z) xi zc = 0 := by
    apply (IsNormalDiag.chartCm_zero_iff (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l))
      x0 hqSel heSel hfSel zc (mu z) xi ?_ ?_).mp
    · simpa only [zc, xi, c, x0, Yl, Lphi, mu, pts, join, p] using
        hchartSel
    · simpa only [zc, xi, c, x0, Yl, Lphi, mu, pts, join, p] using
        htgtSel
    · simpa only [zc, c, x0, Yl, Lphi, mu, pts, join, p] using hzcBall
  have heCanon : IsNormalDiag (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) x0
      (q alpha) (δ alpha) (e l) := by
    simpa only [Lphi, Yl, x0] using hdiag l
  have hfCanon : NormalDiagFence (I := I) Yl x0 (q alpha) (e l) := by
    simpa only [Lphi, Yl, x0] using hfence l
  have heq : e l ≈ eSel :=
    IsNormalDiag.eqOnSource (I := I) Yl
      (hcomplete.complete (Lphi.φ l)) (hconn (Lphi.φ l)) x0
      heCanon hfCanon heSel hfSel
  have hcanonXiZero : invVelSum (e l) (mu z) xi zc = 0 := by
    calc
      invVelSum (e l) (mu z) xi zc = invVelSum eSel (mu z) xi zc :=
        (invVelSum_congr_br eSel (e l) (mu z) xi zc (Setoid.symm heq)
          (fun i _hne => by
            simpa only [zc, xi, c, mu, pts, join, p] using htgtSel i)).symm
      _ = 0 := hselZero
  obtain ⟨_hU, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hzU : z ∈ U alpha := hC1U (interior_subset (hC01 hz))
  have hxi : ∀ i, mu z i ≠ 0 →
      xi i = stagePtsSub inp P L phi hphi alpha k l z i := by
    intro i hi
    have hdecode := htgtTail k hkTgt l hlTgt alpha z hzU i hi
    dsimp only at hdecode
    dsimp only [xi, pts]
    simp only [centerAverage.activeFill, hi, ↓reduceIte]
    simpa only [stagePts, chiL, chiK, Lphi, Yk, Yl] using hdecode.2
  have hcanonPtsZero : invVelSum (e l) (mu z)
      (stagePtsSub inp P L phi hphi alpha k l z) zc = 0 := by
    calc
      invVelSum (e l) (mu z)
          (stagePtsSub inp P L phi hphi alpha k l z) zc =
          invVelSum (e l) (mu z) xi zc :=
        (invVelSum_congr_ne (e l) (mu z) xi
          (stagePtsSub inp P L phi hphi alpha k l z) zc hxi).symm
      _ = 0 := hcanonXiZero
  have hstageZero : stageInvVelSub inp P L hr phi hphi alpha e
      l k l (z, zc) = 0 := by
    simpa only [stageInvVelSub, stageCfgSub, mu] using hcanonPtsZero
  have hzC1 : z ∈ C1 alpha := interior_subset (hC01 hz)
  have hzClosure : z ∈ closure W := subset_closure (hC1W hzC1)
  have hrootData := hrootTail l hlRoot k hkRoot l hlRoot
  have hspec := hrootData.2 z hzClosure
  rcases hspec with
    ⟨_hPhiClose, _hPhiZero, _hInvertible, _hPhiTarget, huniq⟩
  have hPhiInfZ : PhiInf z = z := by
    simpa only [id_eq] using hPhiInf hzC1
  have hzcTube : dist zc (PhiInf z) < rootRho := by
    rw [hPhiInfZ]
    exact hzcClose
  have hcenterRoot : zc = Phi3 l k l z :=
    (huniq zc hzcTube).mp hstageZero
  let x : Yk.M := chiK.symm z
  let i0 := baseIndex inp.decay inp.realizes inp.pack hr
  let muM := fun (y : Yk.M) (gamma : Fin (inp.pack.A r)) =>
    rawWeights
      (cutRaw
        (seqAtom inp.decay inp.hD P Lphi inp.pack r k i0)
        (seqAtom inp.decay inp.hD P Lphi inp.pack r k) i0)
      y gamma
  let qstarM : Yk.M → Yl.M := fun _ => p
  let pM : Yk.M → Yl.M := fun _ => p
  let radM : Yk.M → Real := fun _ => rad
  have hmu : muM x = mu z := by
    funext gamma
    simpa only [muM, x, mu, i0, Lphi, Yk, chiK] using
      (stageWeightSub_eq (I := I) inp P L hr phi hphi alpha k z gamma).symm
  have hptsEq : centerAverage.activeFill muM
      (stageTarget inp P Lphi r k l) qstarM x = pts := by
    funext gamma
    simp only [centerAverage.activeFill]
    rw [congrFun hmu gamma]
    rfl
  have hcmM : CenterInput (I := I) Yl.metric (muM x)
      (centerAverage.activeFill muM (stageTarget inp P Lphi r k l)
        qstarM x) join (pM x) (radM x) := by
    rw [hmu, hptsEq]
    simpa only [pM, radM] using hcm
  have hmap := stageCompare_eq_cm (I := I) inp P Lphi r hr hconn k l
    qstarM join pM radM x hx hcmM
  have hcGlobal : c = centerOfMass (I := I) Yl.metric (muM x)
      (centerAverage.activeFill muM (stageTarget inp P Lphi r k l)
        qstarM x) join (pM x) (radM x) hcmM := by
    apply centerOfMass.unique hcmM c
    intro y
    rw [hmu, hptsEq]
    simpa only [c] using centerOfMass.min hcm y
  have hmapC : stageComparisonMap inp P Lphi r hr hconn k l x = c := by
    exact hmap.trans hcGlobal.symm
  have hchartReadout :
      chiL (stageComparisonMap inp P Lphi r hr hconn k l x) =
        Phi3 l k l z := by
    rw [hmapC]
    exact hcenterRoot
  have hrootBall : Phi3 l k l z ∈ normalBall (I := I) Yl x0 := by
    rw [← hcenterRoot]
    simpa only [zc, x0, Yl, Lphi, c, mu, pts, join, p] using hzcBall
  have hdecode : chiL.symm zc = c := by
    apply chiL.left_inv
    simpa only [chiL, x0, Yl, Lphi, c, mu, pts, join, p] using hcSource
  have hmapDecode :
      stageComparisonMap inp P Lphi r hr hconn k l x =
        chiL.symm (Phi3 l k l z) := by
    calc
      stageComparisonMap inp P Lphi r hr hconn k l x = c := hmapC
      _ = chiL.symm zc := hdecode.symm
      _ = chiL.symm (Phi3 l k l z) := congrArg chiL.symm hcenterRoot
  have htarget :
      stageComparisonMap inp P Lphi r hr hconn k l x ∈
        (normalExpPD (I := I) Yl x0).target := by
    rw [hmapDecode]
    have hout := (normalExpPD (I := I) Yl x0).map_source
      (by simpa only [normalExpPD_source] using hrootBall)
    simpa only [normalExpPD, chiL, x0, Yl, Lphi] using hout
  exact ⟨hchartReadout, hrootBall, hmapDecode, htarget⟩




theorem HasSuppConvData.stage_jet_of_root
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (alpha : LiveSlot L inp.pack r)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : Set E) (PhiInf : E → E) (rootRho : Real)
    (Phi3 : Nat → Nat → Nat → E → E)
    (hroot : HasStageRootCube inp P L hr phi hphi C1 alpha e
      W PhiInf rootRho Phi3)
    (hread : HasStageRootReadout inp P L hr phi hphi hconn C0 alpha Phi3)
    (R : Real) (hRr : R < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      let Fkl := fun w =>
        chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm w))
      z ∈ interior (C0 alpha) →
      chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
        stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z) ∈
            (normalExpPD (I := I) Yl
              (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).target ∧
          ContDiffAt Real ∞ Fkl z ∧
          ∀ j ≤ p, mapDerivNorm j Fkl id z ≤ eps := by
  obtain ⟨_hU, hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  let Lphi := L.subseq hphi
  let Psi : Nat → Nat → E → E := fun k l =>
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    fun w => chiL
      (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm w))
  let S : Nat → E → Prop := fun k z =>
    let Yk := X.obj (Lphi.φ k)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    z ∈ interior (C0 alpha) ∧
      chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k
  dsimp only [HasStageRootReadout] at hread
  obtain ⟨Nread, hreadTail⟩ := hread
  have hEq : ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
      S k z → Psi k l =ᶠ[nhds z] Phi3 l k l := by
    refine ⟨Nread, ?_⟩
    intro k hk l hl z _hz hSz
    let Yk := X.obj (Lphi.φ k)
    let Yl := X.obj (Lphi.φ l)
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
      (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
    change z ∈ interior (C0 alpha) ∧
      chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k at hSz
    have hzU : z ∈ U alpha :=
      hC1U (interior_subset (hC01 (interior_subset hSz.1)))
    obtain ⟨_hRad, hExp, _hMaps⟩ :=
      hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
    have hzBall := hExp hzU
    have hzNorm : ‖z‖ < expMapC2Radius (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) := by
      simpa only [Metric.mem_ball, dist_zero_right, Yk, Lphi] using hzBall
    have hzTarget : z ∈ chiK.target := by
      simpa only [chiK, Yk, Lphi] using
        Geometry.Riemannian.ball_subset_normalChartAt_target
          (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) hzNorm
    have hchi : ContinuousAt chiK.symm z :=
      (NormalCoordinates.normalChartAt_symm_contMDiffOn (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).continuousOn.continuousAt
          (chiK.open_target.mem_nhds hzTarget)
    have hbigNhd : Lphi.hatSourceBall inp.decay P r k ∈ nhds (chiK.symm z) :=
      NetLimitData.hatSource_nhds (I := I) (X := X) inp.decay P Lphi
        (n := k) (R := R) (s := r) hRr hSz.2
    have hsource : ∀ᶠ y in nhds z,
        chiK.symm y ∈ Lphi.hatSourceBall inp.decay P r k :=
      hchi.eventually hbigNhd
    have hreadKL := hreadTail k hk l hl
    change (fun w => chiL
      (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm w)))
        =ᶠ[nhds z] Phi3 l k l
    filter_upwards [isOpen_interior.mem_nhds hSz.1, hsource] with y hy hySource
    exact (hreadKL y (interior_subset hy) hySource).1
  obtain ⟨N, hN⟩ := hroot.at_tail inp P L hr phi hphi C1 alpha e
    W PhiInf rootRho Phi3 hC0 hC01 Psi S hEq p eps heps
  refine ⟨max N Nread, ?_⟩
  intro k hk l hl z hz
  dsimp only
  intro hzInt hxR
  have hSk : S k z := by
    dsimp only [S]
    exact ⟨hzInt, hxR⟩
  have hkRoot : N ≤ k := (Nat.le_max_left N Nread).trans hk
  have hlRoot : N ≤ l := (Nat.le_max_left N Nread).trans hl
  have hkRead : Nread ≤ k := (Nat.le_max_right N Nread).trans hk
  have hlRead : Nread ≤ l := (Nat.le_max_right N Nread).trans hl
  have hout := hN k hkRoot l hlRoot z hz hSk
  let Yk := X.obj (Lphi.φ k)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  have hxBig : chiK.symm z ∈ Lphi.hatSourceBall inp.decay P r k :=
    mem_of_mem_nhds (NetLimitData.hatSource_nhds
      (I := I) (X := X) inp.decay P Lphi
      (n := k) (R := R) (s := r) hRr hxR)
  have htarget := (hreadTail k hkRead l hlRead z hz hxBig).2.2.2
  refine ⟨?_, ?_⟩
  · simpa only [chiK, Yk, Lphi] using htarget
  · simpa only [Psi] using hout



def HasStageJetTail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (C0 : LiveSlot L inp.pack r → Set E)
    (R : Real) (p : Nat) (eps : Real) : Prop :=
  ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
    ∀ alpha : LiveSlot L inp.pack r, ∀ z ∈ C0 alpha,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      let Fkl := fun w =>
        chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm w))
      z ∈ interior (C0 alpha) →
      chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
        stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z) ∈
            (normalExpPD (I := I) Yl
              (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).target ∧
          ContDiffAt Real ∞ Fkl z ∧
          ∀ j ≤ p, mapDerivNorm j Fkl id z ≤ eps



theorem HasStageJetTail.subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (C0 : LiveSlot L inp.pack r → Set E)
    (R : Real) (p : Nat) (eps : Real)
    (h : HasStageJetTail inp P L hr phi hphi hconn C0 R p eps)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasStageJetTail inp P L hr (phi ∘ ψ) (hphi.comp hψ)
      hconn C0 R p eps := by
  dsimp only [HasStageJetTail] at h ⊢
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro k hk l hl alpha z hz
  have hkψ : N ≤ ψ k := hk.trans (hψ.id_le k)
  have hlψ : N ≤ ψ l := hl.trans (hψ.id_le l)
  have hmap :
      stageComparisonMap inp P (L.subseq (hphi.comp hψ)) r hr hconn k l =
        stageComparisonMap inp P (L.subseq hphi) r hr hconn (ψ k) (ψ l) := by
    simpa only [NetLimitData.subseq, Function.comp_apply] using
      (stageCompare_subseq (I := I) inp P (L.subseq hphi) r hr hconn hψ k l)
  have hball :
      (L.subseq (hphi.comp hψ)).hatSourceBall inp.decay P R k =
        (L.subseq hphi).hatSourceBall inp.decay P R (ψ k) := rfl
  rw [hmap, hball]
  simpa only [NetLimitData.subseq_phi, Function.comp_apply,
    seqCenterD_subseq] using hN (ψ k) hkψ (ψ l) hlψ alpha z hz



theorem HasSuppConvData.stage_jet_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (e : (alpha : LiveSlot L inp.pack r) →
      Nat → OpenPartialHomeomorph (E × E) (E × E))
    (W : LiveSlot L inp.pack r → Set E)
    (PhiInf : LiveSlot L inp.pack r → E → E)
    (rootRho : LiveSlot L inp.pack r → Real)
    (Phi3 : LiveSlot L inp.pack r → Nat → Nat → Nat → E → E)
    (hroot : ∀ alpha, HasStageRootCube inp P L hr phi hphi C1 alpha
      (e alpha) (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha))
    (hread : ∀ alpha,
      HasStageRootReadout inp P L hr phi hphi hconn C0 alpha (Phi3 alpha))
    (R : Real) (hRr : R < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    HasStageJetTail inp P L hr phi hphi hconn C0 R p eps := by
  classical
  dsimp only [HasStageJetTail]
  have hlocal : ∀ alpha : LiveSlot L inp.pack r,
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z ∈ C0 alpha,
        let Lphi := L.subseq hphi
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : T2Space Yl.M := Yl.t2
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
        let Fkl := fun w =>
          chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm w))
        z ∈ interior (C0 alpha) →
        chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
          stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z) ∈
              (normalExpPD (I := I) Yl
                (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))).target ∧
            ContDiffAt Real ∞ Fkl z ∧
            ∀ j ≤ p, mapDerivNorm j Fkl id z ≤ eps := by
    intro alpha
    exact hdata.stage_jet_of_root inp P L hr phi hphi U C0 C1 aInf
      Jinf Jbarinf hconn alpha (e alpha) (W alpha) (PhiInf alpha)
      (rootRho alpha) (Phi3 alpha) (hroot alpha) (hread alpha)
      R hRr p eps heps
  letI := Fintype.ofFinite (LiveSlot L inp.pack r)
  choose N hN using hlocal
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk l hl alpha z hz
  have hAlpha : N alpha ≤ Finset.univ.sup N :=
    Finset.le_sup (f := N) (Finset.mem_univ alpha)
  exact hN alpha k (hAlpha.trans hk) l (hAlpha.trans hl) z hz




theorem HasSuppConvData.exists_stage_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (aMin : Real) (haMin : 0 < aMin)
    (hphys : 8 * Real.exp inp.decay.C < aMin * inp.D)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (hdata : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real)
    (hqdata : ∀ gamma : LiveSlot L inp.pack r,
      let rho := aMin * inp.decay.mu (L.rInf (gamma.1 : Nat) + 1)
      0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
        2 * rho < (q gamma : Real))
    (hqAcc : ∀ gamma : LiveSlot L inp.pack r,
      3 * inp.normalBounds.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q gamma : Real))
    (hC1q : ∀ gamma : LiveSlot L inp.pack r,
      C1 gamma ⊆ Metric.ball 0 ((q gamma : Real) / 2))
    (hbranch : ∀ n, HasLiveBrFull (I := I) P (L.subseq hphi)
      inp.pack r n hcomplete hconn aMin q δ)
    (hscale : ∀ n (gamma : LiveSlot L inp.pack r),
      let Lphi := L.subseq hphi
      let rho := aMin * inp.decay.mu (Lphi.rInf (gamma.1 : Nat) + 1)
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
          (I := I) (X.obj (Lphi.φ n)).metric x)
    (deltaInf : LiveSlot L inp.pack r → Real)
    (e : LiveSlot L inp.pack r →
      Nat → OpenPartialHomeomorph (E × E) (E × E))
    (eInf : LiveSlot L inp.pack r →
      OpenPartialHomeomorph (E × E) (E × E))
    (hpair :
      let Lphi := L.subseq hphi
      let index : Nat → Nat := fun n => Lphi.φ n
      let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
        fun alpha n => seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      ∀ alpha, HasDiagPairConv (I := I) (hcomplete.subseq index)
        (PointedRiemannianSeq.connected_subseq hconn index)
        (c alpha) (q alpha) (q alpha / 2) (δ alpha) (deltaInf alpha)
        (e alpha) (eInf alpha))
    (hfence :
      let Lphi := L.subseq hphi
      let index : Nat → Nat := fun n => Lphi.φ n
      let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
        fun alpha n => seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      ∀ alpha n, NormalDiagFence (I := I) (Xphi.obj n)
        (c alpha n) (q alpha) (e alpha n)) :
    ∃ (W : LiveSlot L inp.pack r → Set E)
        (PhiInf : LiveSlot L inp.pack r → E → E)
        (rootRho : LiveSlot L inp.pack r → Real)
        (Phi3 : LiveSlot L inp.pack r → Nat → Nat → Nat → E → E),
      (∀ alpha, HasStageRootCube inp P L hr phi hphi C1 alpha
        (e alpha) (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha)) ∧
      (∀ alpha,
        HasStageRootReadout inp P L hr phi hphi hconn C0 alpha (Phi3 alpha)) ∧
      ∀ R, R < r → ∀ p eps, 0 < eps →
        HasStageJetTail inp P L hr phi hphi hconn C0 R p eps := by
  classical
  let Lphi := L.subseq hphi
  let index : Nat → Nat := fun n => Lphi.φ n
  let Xphi : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
  let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xphi.obj n).M :=
    fun alpha n => seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
  dsimp only at hpair hfence
  have hcube : ∀ alpha : LiveSlot L inp.pack r,
      ∃ (W : Set E) (PhiInf : E → E) (rootRho : Real)
          (Phi3 : Nat → Nat → Nat → E → E),
        HasStageRootCube inp P L hr phi hphi C1 alpha (e alpha)
          W PhiInf rootRho Phi3 := by
    intro alpha
    exact hdata.exists_stage_cube inp P L hr phi hphi U C0 C1 aInf
      Jinf Jbarinf alpha (hpair alpha) (by simpa only using hC1q alpha)
  choose W PhiInf rootRho Phi3 hroot using hcube
  have hread : ∀ alpha : LiveSlot L inp.pack r,
      HasStageRootReadout inp P L hr phi hphi hconn C0 alpha
        (Phi3 alpha) := by
    intro alpha
    have hdiag : ∀ n, IsNormalDiag (I := I) (X.obj (Lphi.φ n))
        (hcomplete.complete (Lphi.φ n)) (hconn (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (δ alpha) (e alpha n) := by
      simpa only [Xphi, index, c, PointedRiemannianSeq.subseq] using
        (hpair alpha).2.2.2.2.2.1
    have hfenceAlpha : ∀ n, NormalDiagFence (I := I)
        (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat))
        (q alpha) (e alpha n) := by
      simpa only [Xphi, index, c, PointedRiemannianSeq.subseq] using
        hfence alpha
    exact hdata.stage_root_tail inp aMin haMin hphys h8 hradD hradRatio
      P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf hcomplete hconn
      q δ hqdata hqAcc (Filter.Eventually.of_forall hbranch)
      (Filter.Eventually.of_forall hscale) alpha (e alpha) hdiag hfenceAlpha
      (W alpha) (PhiInf alpha) (rootRho alpha) (Phi3 alpha) (hroot alpha)
  refine ⟨W, PhiInf, rootRho, Phi3, hroot, hread, ?_⟩
  intro R hRr p eps heps
  exact hdata.stage_jet_tail inp P L hr phi hphi U C0 C1 aInf Jinf
    Jbarinf hconn e W PhiInf rootRho Phi3 hroot hread R hRr p eps heps



def HasStageBaseTail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) : Prop :=
  let Lphi := L.subseq hphi
  ∀ᶠ k in Filter.atTop, ∀ l,
    stageComparisonMap inp P Lphi r hr hconn k l
        (X.obj (Lphi.φ k)).basepoint =
      (X.obj (Lphi.φ l)).basepoint



theorem HasStageBaseTail.subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (h : HasStageBaseTail inp P L hr phi hphi hconn)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasStageBaseTail inp P L hr (phi ∘ ψ) (hphi.comp hψ) hconn := by
  dsimp only [HasStageBaseTail] at h ⊢
  filter_upwards [hψ.tendsto_atTop.eventually h] with k hk
  intro l
  have hL : L.subseq (hphi.comp hψ) = (L.subseq hphi).subseq hψ := by
    cases L
    rfl
  rw [hL]
  have hmap := stageCompare_subseq (I := I) inp P (L.subseq hphi)
    r hr hconn hψ k l
  rw [hmap]
  simpa only [NetLimitData.subseq_phi, Function.comp_apply] using hk (ψ l)




def HasStageJetData
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real)) : Prop :=
  HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf ∧
  (∀ alpha,
    let Lphi := L.subseq hphi
    let Ralpha := L.rInf (alpha.1 : Nat) + 1
    let Ualpha := Metric.ball (0 : E)
      (inp.normalRadius.phaseRadius Ralpha)
    C1 alpha ⊆ Ualpha ∧
    ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
    MapCInfConvOnCompacts Ualpha
      (fun n => normalCoordMetric (I := I)
        (X.obj (Lphi.φ n))
        (seqCenterD inp.decay P Lphi n (alpha.1 : Nat)))
      (gInf alpha) ∧
    ∀ z ∈ Ualpha, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
        gInf alpha z v v ≤ 2 * ‖v‖ ^ 2) ∧
  (∀ R, R < r → ∀ p eps, 0 < eps →
    HasStageJetTail inp P L hr phi hphi hconn C0 R p eps) ∧
  HasStageBaseTail inp P L hr phi hphi hconn



theorem HasStageJetData.subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (h : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasStageJetData (I := I) inp P L hr (phi ∘ ψ) (hphi.comp hψ)
      hconn U C0 C1 aInf Jinf Jbarinf gInf := by
  rcases h with ⟨hdata, hmetric, hjets, hbase⟩
  refine ⟨hdata.subseq inp P L r hr hphi U C0 C1 aInf Jinf Jbarinf hψ,
    ?_, ?_, hbase.subseq inp P L hr hphi hconn hψ⟩
  · intro alpha
    rcases hmetric alpha with ⟨hC1, hgInf, hconv, hequiv⟩
    exact ⟨hC1, hgInf, hconv.comp_tendsto_atTop hψ.tendsto_atTop, hequiv⟩
  · intro R hR p eps heps
    exact (hjets R hR p eps heps).subseq inp P L hr hphi hconn C0 R p eps hψ



theorem HasStageJetData.hloc_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    (R : Real) (hRr : R < r) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞)
        (stageComparisonMap inp P Lphi r hr hconn k l)
        (Lphi.hatSourceBall inp.decay P R k) := by
  classical
  rcases hstage with ⟨hdata, _hmetric, hjets, _hbase⟩
  let Rmid := (R + r) / 2
  have hRmid : R < Rmid := by
    dsimp only [Rmid]
    linarith
  have hmidr : Rmid < r := by
    dsimp only [Rmid]
    linarith
  obtain ⟨N, hN⟩ := hjets Rmid hmidr 1 (1 / 2 : Real) (by norm_num)
  refine ⟨N, ?_⟩
  intro k hk l hl
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let F := stageComparisonMap inp P Lphi r hr hconn k l
  rintro ⟨x, hx⟩
  have hxLarge : x ∈ Lphi.hatSourceBall inp.decay P r k := by
    letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    exact cball_subset_of_le hRr.le
      (by simpa only [NetLimitData.hatSourceBall, Yk] using hx)
  have hcover := hdata.source_cover inp P L r hr U C0 C1 aInf
    Jinf Jbarinf k
  obtain ⟨alpha, z, hzInt, hzx⟩ :=
    Set.mem_iUnion.mp (hcover hxLarge)
  let xk0 := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let xl0 := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.normalChartAt (I := I) Yk.metric xk0
  let chiL := NormalCoordinates.normalChartAt (I := I) Yl.metric xl0
  have hxEq : chiK.symm z = x := by
    simpa only [chiK, xk0, Yk, Lphi] using hzx
  obtain ⟨_hUopen, _hC0, _hC1, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨_hRad, hExp, _hMaps⟩ :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
  have hzC0 : z ∈ C0 alpha := interior_subset hzInt
  have hzU : z ∈ U alpha :=
    hC1U (interior_subset (hC01 hzC0))
  have hzBall := hExp hzU
  have hzNormal : z ∈ normalBall (I := I) Yk xk0 := by
    simpa only [normalBall, Yk, xk0, Lphi] using hzBall
  have hzNorm : ‖z‖ < expMapC2Radius (I := I) Yk.metric xk0 := by
    change z ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) Yk.metric xk0) at hzNormal
    simpa only [Metric.mem_ball, dist_zero_right] using hzNormal
  have hzTarget : z ∈ chiK.target := by
    simpa only [chiK] using
      Geometry.Riemannian.ball_subset_normalChartAt_target
        (I := I) Yk.metric xk0 hzNorm
  let c := (normalExpPD (I := I) Yk xk0).symm
  let d := (normalExpPD (I := I) Yl xl0).symm
  have hzSource : z ∈ (normalExpPD (I := I) Yk xk0).source := by
    simpa only [normalExpPD_source] using hzNormal
  have hnormalEq : normalExpPD (I := I) Yk xk0 z = x := by
    simpa only [normalExpPD, chiK, xk0, Yk, Lphi] using hxEq
  have hxc : x ∈ c.source := by
    have hout := (normalExpPD (I := I) Yk xk0).map_source hzSource
    rw [hnormalEq] at hout
    simpa only [c] using hout
  have hcx : c x = z := by
    have hout := (normalExpPD (I := I) Yk xk0).left_inv hzSource
    rw [hnormalEq] at hout
    simpa only [c] using hout
  let Bmid : Set Yk.M :=
    letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    Metric.ball Yk.basepoint Rmid
  have hBopen : IsOpen Bmid := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          Bmid := by
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      exact Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  let V : Set E :=
    interior (C0 alpha) ∩ (chiK.target ∩ chiK.symm ⁻¹' Bmid)
  have hV : IsOpen V := by
    dsimp only [V]
    exact isOpen_interior.inter
      (chiK.toOpenPartialHomeomorph.continuousOn_invFun.isOpen_inter_preimage
        chiK.open_target hBopen)
  have hxBmid : x ∈ Bmid := by
    letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
    exact Metric.closedBall_subset_ball hRmid
      (by simpa only [Bmid, NetLimitData.hatSourceBall, Yk] using hx)
  have hcxV : c x ∈ V := by
    rw [hcx]
    refine ⟨hzInt, hzTarget, ?_⟩
    change chiK.symm z ∈ Bmid
    rw [hxEq]
    exact hxBmid
  have hjetAt (w : E) (hw : w ∈ V) :
      stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm w) ∈
          (normalExpPD (I := I) Yl xl0).target ∧
        ContDiffAt Real ∞
          (fun u => chiL
            (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm u))) w ∧
        ∀ j ≤ 1,
          mapDerivNorm j
            (fun u => chiL
              (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm u)))
            id w ≤ (1 / 2 : Real) := by
    have hwMid : chiK.symm w ∈
        Lphi.hatSourceBall inp.decay P Rmid k := by
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      exact Metric.ball_subset_closedBall
        (by simpa only [V, Bmid] using hw.2.2)
    simpa only [Lphi, Yk, Yl, xk0, xl0, chiK, chiL] using
      hN k hk l hl alpha w (interior_subset hw.1) hw.1 hwMid
  have hmap : Set.MapsTo (fun w => F (c.symm w)) V d.source := by
    intro w hw
    have hout := (hjetAt w hw).1
    simpa only [F, c, d, normalExpPD, chiK, xk0, Yk, Lphi] using hout
  have hG : ContDiffOn Real ∞ (fun w => d (F (c.symm w))) V := by
    intro w hw
    have hout := (hjetAt w hw).2.1
    have hout' : ContDiffAt Real ∞ (fun u => d (F (c.symm u))) w := by
      simpa only [F, c, d, normalExpPD, chiK, chiL, xk0, xl0, Yk, Yl,
        Lphi] using hout
    exact hout'.contDiffWithinAt
  have hinv : ∀ w ∈ V,
      (fderiv Real (fun u => d (F (c.symm u))) w).IsInvertible := by
    intro w hw
    have hcd := (hjetAt w hw).2.1
    have hdiff : DifferentiableAt Real
        (fun u => chiL
          (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm u))) w :=
      hcd.differentiableAt (by simp)
    have hneu := neumannOfDerivNorm hdiff ((hjetAt w hw).2.2 1 le_rfl)
    have hlt :
        ‖ContinuousLinearMap.id Real E -
          fderiv Real
            (fun u => chiL
              (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm u))) w‖ <
            1 :=
      hneu.trans_lt (by norm_num)
    have hout := Coordinates.isInvertible_of_norm_id_sub_lt hlt
    simpa only [F, c, d, normalExpPD, chiK, chiL, xk0, xl0, Yk, Yl,
      Lphi] using hout
  exact Coordinates.hlocAt_of_coord c d hV hxc hcxV hmap hG hinv



theorem MetricCompactBase.exists_stage_data
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) :
    ∃ (inp : MetricCompactnessInputs (I := I) X)
        (L : NetLimitData inp.decay inp.D
          (inp.properMetrics hcomplete hconn))
        (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real)),
      let P := inp.properMetrics hcomplete hconn
      HasStageJetData inp P L hr phi hphi hconn U C0 C1
        aInf Jinf Jbarinf gInf := by
  classical
  obtain ⟨aMin, haMin, inp, L, phi, hphi, U, C0, C1, aInf, Jinf,
      Jbarinf, q, δ, gInf, deltaInf, e, eInf, hAll⟩ :=
    b.exists_supp_diag_fin hcomplete hconn r hr
  let P := inp.properMetrics hcomplete hconn
  dsimp only at hAll
  obtain ⟨hdata, hAll⟩ := hAll
  obtain ⟨hstable, hAll⟩ := hAll
  obtain ⟨hphys, hAll⟩ := hAll
  obtain ⟨h8, hAll⟩ := hAll
  obtain ⟨hradD, hAll⟩ := hAll
  obtain ⟨hradRatio, hAll⟩ := hAll
  obtain ⟨hqdata, hAll⟩ := hAll
  obtain ⟨hqWide, hAll⟩ := hAll
  obtain ⟨hqAcc, hAll⟩ := hAll
  obtain ⟨_herr, hAll⟩ := hAll
  obtain ⟨_hinvErr, hAll⟩ := hAll
  obtain ⟨hC1q, hAll⟩ := hAll
  obtain ⟨_hcenter, hAll⟩ := hAll
  obtain ⟨hmetric, hAll⟩ := hAll
  obtain ⟨hbranch, hAll⟩ := hAll
  obtain ⟨hscale, hAll⟩ := hAll
  obtain ⟨hpairFence, _hcap⟩ := hAll
  obtain ⟨W, PhiInf, rootRho, Phi3, hroot, hread, hjet⟩ :=
    hdata.exists_stage_tail inp aMin haMin hphys h8 hradD hradRatio
      P L hstable hr phi hphi U C0 C1 aInf Jinf Jbarinf hcomplete hconn
      q δ hqdata hqAcc hC1q hbranch hscale deltaInf e eInf
      (fun alpha => (hpairFence alpha).1)
      (fun alpha n => (hpairFence alpha).2 n)
  obtain ⟨hgp, _hrad⟩ :=
    inp.item3ScaleTails h8 hradD hradRatio P L r
  have hgpPhi : Item3GpScaleTail (I := I) inp.decay inp.D P
      (L.subseq hphi) inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r hphi
  have hbase : HasStageBaseTail (I := I) inp P L hr phi hphi hconn := by
    dsimp only [HasStageBaseTail]
    filter_upwards [hgpPhi] with k hk
    intro l
    exact stageCompare_base inp P (L.subseq hphi) r hr hconn k l hk
  have hmetric' : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      let Ualpha := Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius Ralpha)
      C1 alpha ⊆ Ualpha ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
      MapCInfConvOnCompacts Ualpha
        (fun n => normalCoordMetric (I := I)
          (X.obj ((L.subseq hphi).φ n))
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)))
        (gInf alpha) ∧
      ∀ z ∈ Ualpha, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
          gInf alpha z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro alpha
    dsimp only
    refine ⟨?_, hmetric alpha⟩
    have hqPos : 0 < (q alpha : Real) := by
      exact_mod_cast (hqdata alpha).1
    have hhalfSix : (q alpha : Real) / 2 < 6 * (q alpha : Real) := by
      linarith
    have hhalfPhase : (q alpha : Real) / 2 <
        inp.normalRadius.phaseRadius (L.rInf (alpha.1 : Nat) + 1) :=
      hhalfSix.trans (hqWide alpha)
    exact (hC1q alpha).trans (Metric.ball_subset_ball hhalfPhase.le)
  refine ⟨inp, L, phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, gInf, ?_⟩
  dsimp only [HasStageJetData]
  exact ⟨hdata, hmetric', hjet, hbase⟩

end HCGCompactness
end DifferentialGeometry
