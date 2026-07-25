import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCHatReadout
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalLiveConv

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





def HasSuppCmFin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (sourceBall : Set (X.obj (L.φ n)).M)
    (sourcePatch : LiveSlot L pb r → Set (X.obj (L.φ n)).M)
    (mu : LiveSlot L pb r → (X.obj (L.φ n)).M → Fin (pb.A r) → Real)
    (ptsSeq : LiveSlot L pb r → Nat → Nat → (X.obj (L.φ n)).M →
      Fin (pb.A r) → (X.obj (L.φ n)).M) : Prop :=
  let Y := X.obj (L.φ n)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn (L.φ n)
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
    MetricComplete.complete (I := I) Y (hcomplete.complete (L.φ n))
  letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  ∃ radSeq : LiveSlot L pb r → Nat → Nat → Y.M → Real,
    sourceBall ⊆ ⋃ alpha : LiveSlot L pb r, sourcePatch alpha ∧
    (∀ alpha, sourcePatch alpha ⊆
      L.hatBall hd D P pb r n alpha.1) ∧
    (∀ alpha, centerAverage.WeightDataOn (sourcePatch alpha)
      (fun _ : Fin (pb.A r) => Set.univ) (mu alpha)) ∧
    (∀ alpha a b x, x ∈ sourcePatch alpha → 0 < radSeq alpha a b x) ∧
    (∀ alpha a b x, x ∈ sourcePatch alpha → ∀ gamma,
      mu alpha x gamma ≠ 0 →
        dist x (ptsSeq alpha a b x gamma) < radSeq alpha a b x) ∧
    (∀ epsilon > 0, ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ alpha, ∀ x ∈ sourcePatch alpha,
        radSeq alpha a b x < epsilon) ∧
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ alpha, ∀ x ∈ sourcePatch alpha,
        let join := minJoin (I := I) Y.metric (normal_enorm (I := I) Y)
        let pts := centerAverage.activeFill (mu alpha) (ptsSeq alpha a b)
          (fun y => y) x
        ∃ hcm : CenterInput (I := I) Y.metric (mu alpha x) pts join x
            (radSeq alpha a b x),
          HasHatCmStrictAt (I := I) hd P L pb r n hcomplete hconn q δ alpha
            (mu alpha x) pts join x (radSeq alpha a b x) hcm



theorem HasSuppCmFin.subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real} {n : Nat}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M}
    {q : LiveSlot L pb r → NNReal} {δ : LiveSlot L pb r → Real}
    {ψ : Nat → Nat} (hψ : StrictMono ψ)
    {sourceBall : Set (X.obj (L.φ (ψ n))).M}
    {sourcePatch : LiveSlot L pb r → Set (X.obj (L.φ (ψ n))).M}
    {mu : LiveSlot L pb r → (X.obj (L.φ (ψ n))).M → Fin (pb.A r) → Real}
    {ptsSeq : LiveSlot L pb r → Nat → Nat → (X.obj (L.φ (ψ n))).M →
      Fin (pb.A r) → (X.obj (L.φ (ψ n))).M}
    (h : HasSuppCmFin (I := I) hd P L pb r (ψ n) hcomplete hconn q δ
      sourceBall sourcePatch mu ptsSeq) :
    HasSuppCmFin (I := I) hd P (L.subseq hψ) pb r n hcomplete hconn q δ
      sourceBall sourcePatch mu
      (fun alpha a b x gamma ↦ ptsSeq alpha (ψ a) (ψ b) x gamma) := by
  classical
  dsimp only [HasSuppCmFin] at h ⊢
  rcases h with ⟨radSeq, hcover, hhat, hweight, hpos, hactive,
    hsmall, N, hN⟩
  let radSeq' := fun alpha a b x ↦ radSeq alpha (ψ a) (ψ b) x
  refine ⟨radSeq', hcover, ?_, hweight, ?_, ?_, ?_, N, ?_⟩
  · intro alpha
    simpa only [NetLimitData.hatBall_subseq] using hhat alpha
  · intro alpha a b x hx
    exact hpos alpha (ψ a) (ψ b) x hx
  · intro alpha a b x hx gamma hgamma
    exact hactive alpha (ψ a) (ψ b) x hx gamma hgamma
  · intro epsilon hepsilon
    obtain ⟨Nε, hNε⟩ := hsmall epsilon hepsilon
    refine ⟨Nε, fun a ha b hb alpha x hx ↦ ?_⟩
    exact hNε (ψ a) (ha.trans (hψ.id_le a))
      (ψ b) (hb.trans (hψ.id_le b)) alpha x hx
  · intro a ha b hb alpha x hx
    have hout := hN (ψ a) (ha.trans (hψ.id_le a))
      (ψ b) (hb.trans (hψ.id_le b)) alpha x hx
    simpa only [radSeq', NetLimitData.subseq_phi,
      Function.comp_apply] using hout





def HasSuppCmData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (q : LiveSlot L inp.pack r → NNReal)
    (δ : LiveSlot L inp.pack r → Real) : Prop :=
  let Lphi := L.subseq hphi
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
  letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
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
  let pts := fun (alpha : LiveSlot L inp.pack r) a b x gamma =>
    totalPts (X := X) pairPts alpha a b x gamma
  HasCompactCover sourceBall sourcePatch ∧
    HasSuppCmFin (I := I) inp.decay P Lphi inp.pack r n
      hcomplete hconn q δ sourceBall sourcePatch localWeight pts



theorem HasSuppCmData.subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {inp : MetricCompactnessInputs (I := I) X}
    {P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j)}
    {L : NetLimitData inp.decay inp.D P} {r : Real} {hr : 0 ≤ r} {n : Nat}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M}
    {U : LiveSlot L inp.pack r → Set E}
    {aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real}
    {q : LiveSlot L inp.pack r → NNReal}
    {δ : LiveSlot L inp.pack r → Real}
    {phi ψ : Nat → Nat} {hphi : StrictMono phi} (hψ : StrictMono ψ)
    (h : HasSuppCmData (I := I) inp P L r hr phi hphi (ψ n)
      hcomplete hconn U aInf q δ) :
    HasSuppCmData (I := I) inp P L r hr (phi ∘ ψ) (hphi.comp hψ) n
      hcomplete hconn U aInf q δ := by
  classical
  dsimp only [HasSuppCmData] at h ⊢
  rcases h with ⟨hcover, hcm⟩
  refine ⟨?_, ?_⟩
  · simpa only [NetLimitData.subseq_phi, Function.comp_apply,
      seqCenterD_subseq, NetLimitData.hatSourceBall_subseq] using hcover
  · have hsub := hcm.subseq hψ
    simpa only [NetLimitData.subseq, Function.comp_apply,
      seqCenterD_subseq, NetLimitData.hatSourceBall_subseq, totalPts] using hsub




def HasSourceCmFin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (sourceBall : Set (X.obj (L.φ n)).M)
    (sourcePatch : LiveSlot L pb r → Set (X.obj (L.φ n)).M)
    (mu : LiveSlot L pb r → (X.obj (L.φ n)).M → Fin (pb.A r) → Real)
    (ptsSeq : LiveSlot L pb r → Nat → Nat → (X.obj (L.φ n)).M →
      Fin (pb.A r) → (X.obj (L.φ n)).M) : Prop :=
  let Y := X.obj (L.φ n)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn (L.φ n)
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
    MetricComplete.complete (I := I) Y (hcomplete.complete (L.φ n))
  letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  ∃ radSeq : LiveSlot L pb r → Nat → Nat → Y.M → Real,
    (∀ alpha a b x, x ∈ sourcePatch alpha → 0 < radSeq alpha a b x) ∧
    (∀ alpha a b x, x ∈ sourcePatch alpha → ∀ gamma,
      mu alpha x gamma ≠ 0 →
        dist x (ptsSeq alpha a b x gamma) < radSeq alpha a b x) ∧
    (∀ epsilon > 0, ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ alpha, ∀ x ∈ sourcePatch alpha,
        radSeq alpha a b x < epsilon) ∧
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
      ∀ x ∈ sourceBall,
        ∃ alpha : LiveSlot L pb r, x ∈ sourcePatch alpha ∧
          let join := minJoin (I := I) Y.metric (normal_enorm (I := I) Y)
          let pts := centerAverage.activeFill (mu alpha) (ptsSeq alpha a b)
            (fun y => y) x
          ∃ hcm : CenterInput (I := I) Y.metric (mu alpha x) pts join x
              (radSeq alpha a b x),
            HasHatCmStrictAt (I := I) hd P L pb r n hcomplete hconn q δ alpha
              (mu alpha x) pts join x (radSeq alpha a b x) hcm



theorem HasSuppCmFin.toSource
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real} {n : Nat}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M}
    {q : LiveSlot L pb r → NNReal} {δ : LiveSlot L pb r → Real}
    {sourceBall : Set (X.obj (L.φ n)).M}
    {sourcePatch : LiveSlot L pb r → Set (X.obj (L.φ n)).M}
    {mu : LiveSlot L pb r → (X.obj (L.φ n)).M → Fin (pb.A r) → Real}
    {ptsSeq : LiveSlot L pb r → Nat → Nat → (X.obj (L.φ n)).M →
      Fin (pb.A r) → (X.obj (L.φ n)).M}
    (h : HasSuppCmFin (I := I) hd P L pb r n hcomplete hconn q δ
      sourceBall sourcePatch mu ptsSeq) :
    HasSourceCmFin (I := I) hd P L pb r n hcomplete hconn q δ
      sourceBall sourcePatch mu ptsSeq := by
  classical
  dsimp only [HasSuppCmFin] at h
  rcases h with ⟨radSeq, hcover, _hhat, _hweight, hpos, hactive,
    hsmall, N, hN⟩
  dsimp only [HasSourceCmFin]
  refine ⟨radSeq, hpos, hactive, hsmall, N, ?_⟩
  intro a ha b hb x hx
  rcases Set.mem_iUnion.mp (hcover hx) with ⟨alpha, hxalpha⟩
  exact ⟨alpha, hxalpha, hN a ha b hb alpha x hxalpha⟩




theorem MetricCompactBase.exists_supp_cm_fin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ (aMin : Real) (_haMin : 0 < aMin)
        (inp : MetricCompactnessInputs (I := I) X)
        (L : NetLimitData inp.decay inp.D
          (inp.properMetrics hcomplete hconn))
        (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (q : LiveSlot L inp.pack r → NNReal)
        (δ : LiveSlot L inp.pack r → Real),
      let P := inp.properMetrics hcomplete hconn
      let Lphi := L.subseq hphi
      let beta := fun (n : Nat) (alpha : LiveSlot L inp.pack r) =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
          (gamma : Fin (inp.pack.A r)) =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma
      HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1 aInf Jinf Jbarinf ∧
      (∀ a b : Nat,
        (∀ᶠ k in Filter.atTop,
          BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
        (∀ᶠ k in Filter.atTop,
          ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k))) ∧
      8 * Real.exp inp.decay.C < aMin * inp.D ∧
      (8 : Real) < inp.normalRadius.gpRatio * inp.D ∧
      2 * item3RadiusFactor inp.decay inp.D < inp.D ∧
      2 * item3RadiusFactor inp.decay inp.D <
        inp.normalRadius.ratio * inp.D ∧
      (∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rhoMin := aMin * inp.decay.mu Rgamma
        0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
          2 * rhoMin < (q gamma : Real)) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        6 * (q gamma : Real) < inp.normalRadius.phaseRadius
          (L.rInf (gamma.1 : Nat) + 1)) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        3 * inp.normalBounds.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real)) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        PhaseFlow.phaseErr
            (normalPhaseK inp.normalBounds (2 * q gamma)) < T) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        N * (T - PhaseFlow.phaseErr
              (normalPhaseK inp.normalBounds (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr
              (normalPhaseK inp.normalBounds (2 * q gamma)) < 1 / 24) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        C1 gamma ⊆ Metric.ball 0 ((q gamma : Real) / 2)) ∧
      Filter.Eventually
        (fun n ↦ HasLiveBrFull (I := I) P Lphi inp.pack r n
          hcomplete hconn aMin q δ)
        Filter.atTop ∧
      (∀ᶠ n in Filter.atTop, ∀ gamma : LiveSlot L inp.pack r,
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
            (I := I) (X.obj (Lphi.φ n)).metric x) ∧
      ∀ᶠ n in Filter.atTop,
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
        HasCompactCover sourceBall sourcePatch ∧
          HasSuppCmFin (I := I) inp.decay P Lphi inp.pack r n
            hcomplete hconn q δ sourceBall sourcePatch localWeight pts := by
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
  obtain ⟨L, hstable⟩ := inp.exists_stable_net P
  obtain ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, hconv, hptsTail⟩ :=
    inp.exists_supp_pts_fin h8' hradD' hradRatio' P L hstable r hr hconn
  let Lphi := L.subseq hphi
  obtain ⟨q, δ, hqdata, hqWide, hqAcc, herr, hinvErr,
      hbranchTail, hscaleTail, hreadTail⟩ :=
    hread inp.hD hphys P Lphi inp.pack r
  refine ⟨aMin, haMin, inp, L, phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf,
    q, δ, ?_⟩
  dsimp only
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
  refine ⟨hconv, hstable, hphys, h8', hradD', hradRatio', hqdata0, hqWide0,
    hqAcc0, herr0, hinvErr0,
    ?_, hbranchTail, hscaleTail, ?_⟩
  · intro gamma z hz
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
  · filter_upwards [hptsTail, hreadTail] with n hn hreadN
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
    change HasCompactCover sourceBall sourcePatch ∧
      HasSuppCmFin (I := I) inp.decay P Lphi inp.pack r n
        hcomplete hconn q δ sourceBall sourcePatch localWeight pts
    refine ⟨hcompact, ?_⟩
    · dsimp only [HasSuppCmFin]
      have hlocal := fun alpha =>
        hreadN.2 alpha (sourcePatch alpha) (hhat alpha)
          (localWeight alpha) (hweight alpha) (pts alpha) (hpts alpha)
      choose radSeq hpos hactive hsmall hcap using hlocal
      refine ⟨radSeq, hcover, hhat, hweight, hpos, hactive, ?_, ?_⟩
      · intro epsilon hepsilon
        exact finite_cover_two_tail hcover
          (fun alpha a b x => radSeq alpha a b x < epsilon)
          (fun alpha => hsmall alpha epsilon hepsilon)
      · exact finite_cover_two_tail hcover _ hcap






theorem MetricCompactBase.exists_supp_diag_fin
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ (aMin : Real) (_haMin : 0 < aMin)
        (inp : MetricCompactnessInputs (I := I) X)
        (L : NetLimitData inp.decay inp.D
          (inp.properMetrics hcomplete hconn))
        (theta : Nat → Nat) (htheta : StrictMono theta)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (q : LiveSlot L inp.pack r → NNReal)
        (δ : LiveSlot L inp.pack r → Real)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real))
        (deltaInf : LiveSlot L inp.pack r → Real)
        (e : LiveSlot L inp.pack r →
          Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : LiveSlot L inp.pack r →
          OpenPartialHomeomorph (E × E) (E × E)),
      let P := inp.properMetrics hcomplete hconn
      let Ltheta := L.subseq htheta
      let index : Nat → Nat := fun n ↦ Ltheta.φ n
      let Xtheta : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
      let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xtheta.obj n).M :=
        fun alpha n ↦ seqCenterD inp.decay P Ltheta n (alpha.1 : Nat)
      HasSuppConvData (I := I) inp P L r hr theta htheta U C0 C1
          aInf Jinf Jbarinf ∧
      (∀ a b : Nat,
        (∀ᶠ k in Filter.atTop,
          BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
        (∀ᶠ k in Filter.atTop,
          ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k))) ∧
      8 * Real.exp inp.decay.C < aMin * inp.D ∧
      (8 : Real) < inp.normalRadius.gpRatio * inp.D ∧
      2 * item3RadiusFactor inp.decay inp.D < inp.D ∧
      2 * item3RadiusFactor inp.decay inp.D <
        inp.normalRadius.ratio * inp.D ∧
      (∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rhoMin := aMin * inp.decay.mu Rgamma
        0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
          2 * rhoMin < (q gamma : Real)) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        6 * (q gamma : Real) < inp.normalRadius.phaseRadius
          (L.rInf (gamma.1 : Nat) + 1)) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        3 * inp.normalBounds.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
          (2 / 3 : Real) * (q gamma : Real)) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        PhaseFlow.phaseErr
            (normalPhaseK inp.normalBounds (2 * q gamma)) < T) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        N * (T - PhaseFlow.phaseErr
              (normalPhaseK inp.normalBounds (2 * q gamma)))⁻¹ *
            PhaseFlow.phaseErr
              (normalPhaseK inp.normalBounds (2 * q gamma)) < 1 / 24) ∧
      (∀ gamma : LiveSlot L inp.pack r,
        C1 gamma ⊆ Metric.ball 0 ((q gamma : Real) / 2)) ∧
      (∀ n (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (Ltheta.φ n) (c alpha n)
          (X.obj (Ltheta.φ n)).basepoint ≤
            L.rInf (alpha.1 : Nat) + 1) ∧
      (∀ alpha : LiveSlot L inp.pack r,
        let Ralpha := L.rInf (alpha.1 : Nat) + 1
        let Ualpha := Metric.ball (0 : E)
          (inp.normalRadius.phaseRadius Ralpha)
        ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
        MapCInfConvOnCompacts Ualpha
          (fun n ↦ normalCoordMetric (I := I)
            (X.obj (Ltheta.φ n)) (c alpha n))
          (gInf alpha) ∧
        ∀ z ∈ Ualpha, ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
            gInf alpha z v v ≤ 2 * ‖v‖ ^ 2) ∧
      (∀ n, HasLiveBrFull (I := I) P Ltheta inp.pack r n
        hcomplete hconn aMin q δ) ∧
      (∀ n (gamma : LiveSlot L inp.pack r),
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
            (I := I) (X.obj (Ltheta.φ n)).metric x) ∧
      (∀ alpha,
        HasDiagPairConv (I := I) (hcomplete.subseq index)
          (PointedRiemannianSeq.connected_subseq hconn index)
          (c alpha) (q alpha) (q alpha / 2)
          (δ alpha) (deltaInf alpha) (e alpha) (eInf alpha) ∧
        ∀ n, NormalDiagFence (I := I) (Xtheta.obj n)
          (c alpha n) (q alpha) (e alpha n)) ∧
      ∀ n, HasSuppCmData (I := I) inp P L r hr theta htheta n
        hcomplete hconn U aInf q δ := by
  classical
  obtain ⟨aMin, haMin, inp, L, phi, hphi, U, C0, C1, aInf, Jinf,
      Jbarinf, q, δ, hconv, hstable, hphys, h8, hradD, hradRatio, hqdata, hqWide,
      hqAcc, herr, hinvErr,
      hcore, hbranch, hscaleTail, hcapTail⟩ :=
    b.exists_supp_cm_fin hcomplete hconn r hr
  let P := inp.properMetrics hcomplete hconn
  let Lphi := L.subseq hphi
  have hq : ∀ alpha : LiveSlot L inp.pack r, 0 < q alpha := by
    intro alpha
    have h := hqdata alpha
    dsimp only at h
    exact h.1
  have hδ : ∀ alpha : LiveSlot L inp.pack r, 0 < δ alpha := by
    intro alpha
    have h := hqdata alpha
    dsimp only at h
    exact h.2.1
  have hqWidePhi : ∀ alpha : LiveSlot L inp.pack r,
      6 * (q alpha : Real) < inp.normalRadius.phaseRadius
        (Lphi.rInf (alpha.1 : Nat) + 1) := by
    simpa only [Lphi, NetLimitData.subseq] using hqWide
  let ScaleAt : Nat → Prop := fun n ↦
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
  let Q : Nat → Prop := fun n ↦
    HasSuppCmData (I := I) inp P L r hr phi hphi n
        hcomplete hconn U aInf q δ ∧
      ScaleAt n
  have hQ : ∀ᶠ n in Filter.atTop, Q n := by
    filter_upwards [hcapTail, hscaleTail] with n hcap hscale
    exact ⟨hcap, hscale⟩
  obtain ⟨psi, hpsi, gInf, deltaInf, e, eInf,
      hcenter0, hQAll, hmetric0, hbranchAll, hpair0⟩ :=
    inp.exists_diag_full P Lphi r hcomplete hconn aMin q δ hq hδ
      hqWidePhi hqAcc herr hinvErr hbranch Q hQ
  let theta := phi ∘ psi
  have htheta : StrictMono theta := hphi.comp hpsi
  let Ltheta := L.subseq htheta
  have hconvTheta :
      HasSuppConvData (I := I) inp P L r hr theta htheta U C0 C1
        aInf Jinf Jbarinf := by
    simpa only [theta] using
      HasSuppConvData.subseq inp P L r hr hphi U C0 C1 aInf Jinf Jbarinf
        hconv hpsi
  have hcenter : ∀ n (alpha : LiveSlot L inp.pack r),
      inp.decay.dist (Ltheta.φ n)
        (seqCenterD inp.decay P Ltheta n (alpha.1 : Nat))
        (X.obj (Ltheta.φ n)).basepoint ≤
          L.rInf (alpha.1 : Nat) + 1 := by
    intro n alpha
    simpa only [Lphi, Ltheta, theta, NetLimitData.subseq,
      Function.comp_apply, seqCenterD_subseq] using hcenter0 n alpha
  have hmetric : ∀ alpha : LiveSlot L inp.pack r,
      let Ralpha := L.rInf (alpha.1 : Nat) + 1
      let Ualpha := Metric.ball (0 : E)
        (inp.normalRadius.phaseRadius Ralpha)
      ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
      MapCInfConvOnCompacts Ualpha
        (fun n ↦ normalCoordMetric (I := I)
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
  let index : Nat → Nat := fun n ↦ Ltheta.φ n
  let Xtheta : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
  let c : LiveSlot L inp.pack r → ∀ n : Nat, (Xtheta.obj n).M :=
    fun alpha n ↦ seqCenterD inp.decay P Ltheta n (alpha.1 : Nat)
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
  have hcapAll : ∀ n,
      HasSuppCmData (I := I) inp P L r hr theta htheta n
        hcomplete hconn U aInf q δ := by
    intro n
    have hQn := hQAll n
    dsimp only [Q] at hQn
    have hn := HasSuppCmData.subseq (I := I) hpsi hQn.1
    simpa only [Q, theta] using hn
  refine ⟨aMin, haMin, inp, L, theta, htheta, U, C0, C1, aInf, Jinf,
    Jbarinf, q, δ, gInf, deltaInf, e, eInf, ?_⟩
  dsimp only
  exact ⟨hconvTheta, hstable, hphys, h8, hradD, hradRatio, hqdata, hqWide, hqAcc,
    herr, hinvErr, hcore,
    hcenter, hmetric, hbranchTheta, hscaleAll, hpair, hcapAll⟩





theorem MetricCompactBase.exists_cm_on_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) :
    ∃ (aMin : Real) (_haMin : 0 < aMin)
        (inp : MetricCompactnessInputs (I := I) X)
        (L : NetLimitData inp.decay inp.D
          (inp.properMetrics hcomplete hconn))
        (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (q : LiveSlot L inp.pack r → NNReal)
        (δ : LiveSlot L inp.pack r → Real),
      let P := inp.properMetrics hcomplete hconn
      let Lphi := L.subseq hphi
      let beta := fun (n : Nat) (alpha : LiveSlot L inp.pack r) =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
          (gamma : Fin (inp.pack.A r)) =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma
      (∀ gamma : LiveSlot L inp.pack r,
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rhoMin := aMin * inp.decay.mu Rgamma
        0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
          2 * rhoMin < (q gamma : Real)) ∧
      ∀ᶠ n in Filter.atTop,
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
        HasSourceCmFin (I := I) inp.decay P Lphi inp.pack r n
          hcomplete hconn q δ sourceBall sourcePatch localWeight pts := by
  obtain ⟨aMin, haMin, inp, L, phi, hphi, U, _C0, _C1, aInf, _Jinf,
      _Jbarinf, q, δ, _hconv, _hstable, _hphys, _h8, _hradD, _hradRatio, hqdata,
      _hqWide, _hqAcc, _herr, _hinvErr, _hcore, _hbranch, _hscale, htail⟩ :=
    b.exists_supp_cm_fin hcomplete hconn r hr
  refine ⟨aMin, haMin, inp, L, phi, hphi, U, aInf, q, δ, ?_⟩
  dsimp only
  refine ⟨hqdata, ?_⟩
  filter_upwards [htail] with n hn
  exact hn.2.toSource

end HCGCompactness
end DifferentialGeometry
