import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchCage
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchConvexity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU

set_option autoImplicit false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
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



def HasHatCmEqn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (mu : Fin (pb.A r) → Real)
    (pts : Fin (pb.A r) → (X.obj (L.φ n)).M)
    (join : (X.obj (L.φ n)).M → (X.obj (L.φ n)).M → Real →
      (X.obj (L.φ n)).M)
    (x : (X.obj (L.φ n)).M) (rad : Real)
    (hcm :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
        (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle (I := I)
      letI : (z : (X.obj (L.φ n)).M) →
          InnerProductSpace Real (TangentSpace I z) :=
        (X.obj (L.φ n)).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        (X.obj (L.φ n)).emetricSpace (I := I)
      letI : CompleteSpace (X.obj (L.φ n)).M :=
        MetricComplete.complete (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n))
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      CenterInput (I := I) (X.obj (L.φ n)).metric mu pts join x rad) : Prop :=
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ n)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ n)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ n)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n))
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  ∃ gamma : LiveSlot L pb r,
    ∃ (hq : 0 < q gamma)
        (e : OpenPartialHomeomorph (E × E) (E × E))
        (he : IsNormalDiag (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n)) (hconn (L.φ n))
          (seqCenterD hd P L n (gamma.1 : Nat)) (q gamma) (δ gamma) e),
      NormalDiagFence (I := I) (X.obj (L.φ n))
          (seqCenterD hd P L n (gamma.1 : Nat)) (q gamma) e ∧
        let x0 := seqCenterD hd P L n (gamma.1 : Nat)
        let B := IsNormalDiag.toBranch (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n)) (hconn (L.φ n)) x0 hq he
        let c := centerOfMass (I := I) (X.obj (L.φ n)).metric
          mu pts join x rad hcm
        let xi : Fin (pb.A r) → E := fun i =>
          NormalCoordinates.normalChartAt
            (I := I) (X.obj (L.φ n)).metric x0 (pts i)
        chartCmEqnB (I := I) (X.obj (L.φ n)).metric
          (normal_enorm (I := I) (X.obj (L.φ n))) x0 B
          (NormalCoordinates.normalChartAt
            (I := I) (X.obj (L.φ n)).metric x0 c)
          (mu, xi) = 0



def HasHatCmStrictAt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (alpha : LiveSlot L pb r)
    (mu : Fin (pb.A r) → Real)
    (pts : Fin (pb.A r) → (X.obj (L.φ n)).M)
    (join : (X.obj (L.φ n)).M → (X.obj (L.φ n)).M → Real →
      (X.obj (L.φ n)).M)
    (x : (X.obj (L.φ n)).M) (rad : Real)
    (hcm :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
        (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle (I := I)
      letI : (z : (X.obj (L.φ n)).M) →
          InnerProductSpace Real (TangentSpace I z) :=
        (X.obj (L.φ n)).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        (X.obj (L.φ n)).emetricSpace (I := I)
      letI : CompleteSpace (X.obj (L.φ n)).M :=
        MetricComplete.complete (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n))
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      CenterInput (I := I) (X.obj (L.φ n)).metric mu pts join x rad) : Prop :=
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ n)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ n)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ n)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n))
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  ∃ (hq : 0 < q alpha)
        (e : OpenPartialHomeomorph (E × E) (E × E))
        (he : IsNormalDiag (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n)) (hconn (L.φ n))
          (seqCenterD hd P L n (alpha.1 : Nat)) (q alpha) (δ alpha) e),
      NormalDiagFence (I := I) (X.obj (L.φ n))
          (seqCenterD hd P L n (alpha.1 : Nat)) (q alpha) e ∧
        let x0 := seqCenterD hd P L n (alpha.1 : Nat)
        let B := IsNormalDiag.toBranch (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n)) (hconn (L.φ n)) x0 hq he
        let c := centerOfMass (I := I) (X.obj (L.φ n)).metric
          mu pts join x rad hcm
        let z := NormalCoordinates.normalChartAt
          (I := I) (X.obj (L.φ n)).metric x0 c
        let xi : Fin (pb.A r) → E := fun i =>
          NormalCoordinates.normalChartAt
            (I := I) (X.obj (L.φ n)).metric x0 (pts i)
        c ∈ (NormalCoordinates.normalChartAt
            (I := I) (X.obj (L.φ n)).metric x0).source ∧
          (∀ i, (z, xi i) ∈ e.target) ∧
            z ∈ normalBall (I := I) (X.obj (L.φ n)) x0 ∧
            chartCmEqnB (I := I) (X.obj (L.φ n)).metric
                (normal_enorm (I := I) (X.obj (L.φ n))) x0 B
                z (mu, xi) = 0 ∧
              ∃ Lcm : E ≃L[Real] E,
                HasFDerivAt
                    (fun u : E => chartCmEqnB (I := I) (X.obj (L.φ n)).metric
                      (normal_enorm (I := I) (X.obj (L.φ n))) x0 B
                      u (mu, xi))
                    (Lcm : E →L[Real] E) z ∧
                  ∃ (f : ((Fin (pb.A r) → Real) × (Fin (pb.A r) → E)) → E)
                      (Df : ((Fin (pb.A r) → Real) ×
                        (Fin (pb.A r) → E)) →L[Real] E),
                    f (mu, xi) = z ∧ HasStrictFDerivAt f Df (mu, xi) ∧
                      (∀ᶠ params in nhds (mu, xi),
                        chartCmEqnB (I := I) (X.obj (L.φ n)).metric
                          (normal_enorm (I := I) (X.obj (L.φ n))) x0 B
                          (f params) params = 0) ∧
                      (∀ᶠ zp in nhds (z, (mu, xi)),
                        chartCmEqnB (I := I) (X.obj (L.φ n)).metric
                            (normal_enorm (I := I) (X.obj (L.φ n))) x0 B
                          zp.1 zp.2 = 0 →
                          zp.1 = f zp.2)



def HasHatCmStrict
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (mu : Fin (pb.A r) → Real)
    (pts : Fin (pb.A r) → (X.obj (L.φ n)).M)
    (join : (X.obj (L.φ n)).M → (X.obj (L.φ n)).M → Real →
      (X.obj (L.φ n)).M)
    (x : (X.obj (L.φ n)).M) (rad : Real)
    (hcm :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
        (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle (I := I)
      letI : (z : (X.obj (L.φ n)).M) →
          InnerProductSpace Real (TangentSpace I z) :=
        (X.obj (L.φ n)).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        (X.obj (L.φ n)).emetricSpace (I := I)
      letI : CompleteSpace (X.obj (L.φ n)).M :=
        MetricComplete.complete (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n))
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      CenterInput (I := I) (X.obj (L.φ n)).metric mu pts join x rad) : Prop :=
  ∃ alpha : LiveSlot L pb r,
    HasHatCmStrictAt (I := I) hd P L pb r n hcomplete hconn q δ alpha
      mu pts join x rad hcm







theorem exists_hat_cm_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (hprof : NormalRadiusProfile hd hb)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    ∃ aMin : Real, 0 < aMin ∧
      ∀ {D : Real} (_hD : 0 < D)
        (_hphys : 8 * Real.exp hd.C < aMin * D)
        (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
        (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real),
        ∃ q : LiveSlot L pb r → NNReal,
          ∃ δ : LiveSlot L pb r → Real,
            (∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rhoMin := aMin * hd.mu Rgamma
              0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
                2 * rhoMin < (q gamma : Real)) ∧
            ∀ᶠ n in Filter.atTop,
              letI : TopologicalSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).topology
              letI : ChartedSpace H (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).charted
              letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).smooth
              letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
                (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
              letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).sigmaCompact
              letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
              letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
              letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                (X.obj (L.φ n)).t2TangentBundle
              letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                Manifold.metrizableSpace I (X.obj (L.φ n)).M
              letI : T3Space (X.obj (L.φ n)).M := inferInstance
              letI : RiemannianBundle
                  (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                (X.obj (L.φ n)).riemBundle (I := I)
              letI : (x : (X.obj (L.φ n)).M) →
                  InnerProductSpace Real (TangentSpace I x) :=
                (X.obj (L.φ n)).riemInner (I := I)
              letI : IsContinuousRiemannianBundle E
                  (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                (X.obj (L.φ n)).riemBundle_cont (I := I)
              letI : EMetricSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).emetricSpace (I := I)
              letI : CompleteSpace (X.obj (L.φ n)).M :=
                MetricComplete.complete (I := I) (X.obj (L.φ n))
                  (hcomplete.complete (L.φ n))
              letI : MetricSpace (X.obj (L.φ n)).M :=
                HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
              (∀ gamma : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
                seqCenter hd D P (L.φ n) (gamma : Nat) = some c →
                  c = seqCenterD hd P L n (gamma : Nat) ∧
                    4 * L.lamInf (gamma : Nat) <
                      expRadiusGp (I := I) (X.obj (L.φ n)).metric c) ∧
              ∀ (rho :
                  letI : TopologicalSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).topology
                  letI : ChartedSpace H (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).charted
                  letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).smooth
                  letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).sigmaCompact
                  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
                  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
                  SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
                    (Metric.closedBall (X.obj (L.φ n)).basepoint r))
                (_hrho :
                  letI : TopologicalSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).topology
                  letI : ChartedSpace H (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).charted
                  letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).smooth
                  letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).sigmaCompact
                  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
                  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
                  rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
                    (NetLimitData.hatBall (I := I) (X := X) hd D P L pb r n gamma :
                      Set (X.obj (L.φ n)).M)))
                (ptsSeq : Nat → Nat → (X.obj (L.φ n)).M → Fin (pb.A r) →
                  (X.obj (L.φ n)).M)
                (_hpts :
                  letI : TopologicalSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).topology
                  letI : ChartedSpace H (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).charted
                  letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).smooth
                  letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).sigmaCompact
                  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
                  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                    (X.obj (L.φ n)).t2TangentBundle
                  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
                  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                    Manifold.metrizableSpace I (X.obj (L.φ n)).M
                  letI : T3Space (X.obj (L.φ n)).M := inferInstance
                  letI : RiemannianBundle
                      (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                    (X.obj (L.φ n)).riemBundle (I := I)
                  letI : (x : (X.obj (L.φ n)).M) →
                      InnerProductSpace Real (TangentSpace I x) :=
                    (X.obj (L.φ n)).riemInner (I := I)
                  letI : IsContinuousRiemannianBundle E
                      (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                    (X.obj (L.φ n)).riemBundle_cont (I := I)
                  letI : EMetricSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).emetricSpace (I := I)
                  letI : CompleteSpace (X.obj (L.φ n)).M :=
                    MetricComplete.complete (I := I) (X.obj (L.φ n))
                      (hcomplete.complete (L.φ n))
                  letI : MetricSpace (X.obj (L.φ n)).M :=
                    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
                  ∀ gamma : Fin (pb.A r), ∀ eps : Real, eps > 0 → ∃ N : Nat,
                    ∀ a ≥ N, ∀ b ≥ N, ∀ x : (X.obj (L.φ n)).M,
                      x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                        x ∈ (NetLimitData.hatBall
                          (I := I) (X := X) hd D P L pb r n gamma :
                            Set (X.obj (L.φ n)).M) →
                          dist x (ptsSeq a b x gamma) < eps),
                  letI : TopologicalSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).topology
                  letI : ChartedSpace H (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).charted
                  letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).smooth
                  letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).sigmaCompact
                  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
                  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                    (X.obj (L.φ n)).t2TangentBundle
                  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
                  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                    Manifold.metrizableSpace I (X.obj (L.φ n)).M
                  letI : T3Space (X.obj (L.φ n)).M := inferInstance
                  letI : RiemannianBundle
                      (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                    (X.obj (L.φ n)).riemBundle (I := I)
                  letI : (x : (X.obj (L.φ n)).M) →
                      InnerProductSpace Real (TangentSpace I x) :=
                    (X.obj (L.φ n)).riemInner (I := I)
                  letI : IsContinuousRiemannianBundle E
                      (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                    (X.obj (L.φ n)).riemBundle_cont (I := I)
                  letI : EMetricSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).emetricSpace (I := I)
                  letI : CompleteSpace (X.obj (L.φ n)).M :=
                    MetricComplete.complete (I := I) (X.obj (L.φ n))
                      (hcomplete.complete (L.φ n))
                  letI : MetricSpace (X.obj (L.φ n)).M :=
                    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
                  ∃ radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real,
                    (∀ a b x,
                      x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                        0 < radSeq a b x) ∧
                    (∀ a b x,
                      x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                        ∀ gamma : Fin (pb.A r), rho gamma x ≠ 0 →
                          dist x (ptsSeq a b x gamma) < radSeq a b x) ∧
                    (∀ eps : Real, eps > 0 → ∃ N : Nat,
                      ∀ a ≥ N, ∀ b ≥ N, ∀ x : (X.obj (L.φ n)).M,
                        x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                          radSeq a b x < eps) ∧
                    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x : (X.obj (L.φ n)).M,
                        x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                          ∀ (join : (X.obj (L.φ n)).M → (X.obj (L.φ n)).M →
                            Real → (X.obj (L.φ n)).M),
                            StrictDistInput (I := I) (X.obj (L.φ n)).metric
                              (centerAverage.activeFill
                                (fun y gamma ↦ rho gamma y) (ptsSeq a b)
                                (fun y ↦ y) x)
                              join x (radSeq a b x) →
                              ∃ hcm : CenterInput (I := I)
                                (X.obj (L.φ n)).metric (fun gamma ↦ rho gamma x)
                                (centerAverage.activeFill
                                  (fun y gamma ↦ rho gamma y) (ptsSeq a b)
                                  (fun y ↦ y) x)
                                join x (radSeq a b x),
                                HasHatCmEqn (I := I) hd P L pb r n hcomplete hconn
                                  q δ (fun gamma ↦ rho gamma x)
                                  (centerAverage.activeFill
                                    (fun y gamma ↦ rho gamma y) (ptsSeq a b)
                                    (fun y ↦ y) x)
                                  join x (radSeq a b x) hcm := by
  classical
  obtain ⟨aMin, haMin, hmin⟩ :=
    exists_slot_min (I := I) hprof hre hcomplete hconn
  refine ⟨aMin, haMin, ?_⟩
  intro D _hD _hphys P L pb r
  obtain ⟨q, δ, hqdata, _hqWide, _hqAcc, _herr, _hinvErr, _hquarter,
      hbranch⟩ := hmin P L pb r
  refine ⟨q, δ, hqdata, ?_⟩
  filter_upwards [hbranch, aliveSlots_tail hd P L pb r] with n hn hstable
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ n)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ n)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ n)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n))
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  constructor
  · intro gamma c hc
    have halive : L.alive (gamma : Nat) = true := by
      simpa [hc] using (hstable gamma).symm
    let gammaLive : LiveSlot L pb r := ⟨gamma, halive⟩
    have hcD : c = seqCenterD hd P L n (gamma : Nat) := by
      simp [seqCenterD, hc]
    refine ⟨hcD, ?_⟩
    have hfloor := (hn gammaLive).2.2
    rw [hcD]
    exact (lamInf_lt_halfMin hd _hD _hphys P L (gamma : Nat)).trans_le
      (by simpa only [gammaLive] using hfloor)
  · intro rho _hrho ptsSeq _hpts
    obtain ⟨radSeq, hpos, hactive, htail⟩ :=
      NetLimitData.exists_hat_radius (I := I) hd P L pb r n rho _hrho ptsSeq
        (hconn (L.φ n)) _hpts
    refine ⟨radSeq, hpos, hactive, htail, ?_⟩
    obtain ⟨N, hN⟩ := exists_rad_cage hd _hD haMin _hphys P L pb r n
      (NetLimitData.hatSourceBall (I := I) hd P L r n) radSeq htail
    refine ⟨N, ?_⟩
    intro a ha b hbN x hx join hstrict
    let weights : (X.obj (L.φ n)).M → Fin (pb.A r) → Real :=
      fun y gamma ↦ rho gamma y
    let pts := centerAverage.activeFill weights (ptsSeq a b) (fun y ↦ y) x
    let hcomplete' :=
      NetLimitData.sourceComplete (I := I) hd P L n hcomplete (hconn (L.φ n))
    have hdata := NetLimitData.hatPOUDataTwo
      (I := I) hd P L pb r n rho _hrho a b hx
    have hcm : CenterInput (I := I) (X.obj (L.φ n)).metric
        (fun gamma ↦ rho gamma x) pts join x (radSeq a b x) := by
      simpa only [weights, pts] using
        centerAverage.inputOfFillSelf (I := I)
          (g := (X.obj (L.φ n)).metric) (μ := weights)
          (pts := ptsSeq a b) (join := join) (r := radSeq a b)
          (qstar := fun y ↦ y) x hcomplete' (hpos a b x hx)
          (hactive a b x hx) hdata.1.1 hdata.1.2.1 hstrict
    refine ⟨hcm, ?_⟩
    have hout := exists_hat_cm_eqn (I := I) hd P hre L pb r n hcomplete hconn
      q δ hstable hqdata hn (fun gamma ↦ rho gamma x) pts join x
      (radSeq a b x) hcm hdata.2 (hN a ha b hbN x hx)
    simpa only [HasHatCmEqn] using hout



theorem exists_hat_cm_tail_support
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (hprof : NormalRadiusProfile hd hb)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    ∃ aMin : Real, 0 < aMin ∧
      ∀ {D : Real} (hD : 0 < D)
        (hphys : 8 * Real.exp hd.C < aMin * D)
        (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
        (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real),
        ∃ q : LiveSlot L pb r → NNReal,
          ∃ δ : LiveSlot L pb r → Real,
            (∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rhoMin := aMin * hd.mu Rgamma
              0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
                2 * rhoMin < (q gamma : Real)) ∧
            ∀ᶠ n in Filter.atTop,
              letI : TopologicalSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).topology
              letI : ChartedSpace H (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).charted
              letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).smooth
              letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
                (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
              letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).sigmaCompact
              letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
              letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
              letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                (X.obj (L.φ n)).t2TangentBundle
              letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                Manifold.metrizableSpace I (X.obj (L.φ n)).M
              letI : T3Space (X.obj (L.φ n)).M := inferInstance
              letI : RiemannianBundle
                  (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
                (X.obj (L.φ n)).riemBundle (I := I)
              letI : (x : (X.obj (L.φ n)).M) →
                  InnerProductSpace Real (TangentSpace I x) :=
                (X.obj (L.φ n)).riemInner (I := I)
              letI : IsContinuousRiemannianBundle E
                  (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
                (X.obj (L.φ n)).riemBundle_cont (I := I)
              letI : EMetricSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).emetricSpace (I := I)
              letI : CompleteSpace (X.obj (L.φ n)).M :=
                MetricComplete.complete (I := I) (X.obj (L.φ n))
                  (hcomplete.complete (L.φ n))
              letI : MetricSpace (X.obj (L.φ n)).M :=
                HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
              (∀ gamma : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
                seqCenter hd D P (L.φ n) (gamma : Nat) = some c →
                  c = seqCenterD hd P L n (gamma : Nat) ∧
                    4 * L.lamInf (gamma : Nat) <
                      expRadiusGp (I := I) (X.obj (L.φ n)).metric c) ∧
              ∀ (alpha : LiveSlot L pb r)
                (s : Set (X.obj (L.φ n)).M)
                (hs : s ⊆ NetLimitData.hatBall (I := I) (X := X)
                  hd D P L pb r n alpha.1)
                (mu : (X.obj (L.φ n)).M → Fin (pb.A r) → Real)
                (hmu : centerAverage.WeightDataOn s
                  (fun _ : Fin (pb.A r) => Set.univ) mu)
                (ptsSeq : Nat → Nat → (X.obj (L.φ n)).M →
                  Fin (pb.A r) → (X.obj (L.φ n)).M)
                (hpts : ∀ gamma : Fin (pb.A r), ∀ epsilon : Real,
                  0 < epsilon → ∃ N : Nat,
                    ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x ∈ s, mu x gamma ≠ 0 →
                        dist x (ptsSeq a b x gamma) < epsilon),
                  ∃ radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real,
                    (∀ a b x, x ∈ s → 0 < radSeq a b x) ∧
                    (∀ a b x, x ∈ s → ∀ gamma, mu x gamma ≠ 0 →
                      dist x (ptsSeq a b x gamma) < radSeq a b x) ∧
                    (∀ epsilon > 0, ∃ N : Nat,
                      ∀ a ≥ N, ∀ b ≥ N,
                        ∀ x ∈ s, radSeq a b x < epsilon) ∧
                    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x ∈ s,
                        ∀ join : (X.obj (L.φ n)).M →
                            (X.obj (L.φ n)).M → Real → (X.obj (L.φ n)).M,
                          StrictDistInput (I := I) (X.obj (L.φ n)).metric
                            (centerAverage.activeFill mu (ptsSeq a b)
                              (fun y => y) x)
                            join x (radSeq a b x) →
                          ∃ hcm : CenterInput (I := I)
                              (X.obj (L.φ n)).metric (mu x)
                              (centerAverage.activeFill mu (ptsSeq a b)
                                (fun y => y) x)
                              join x (radSeq a b x),
                            HasHatCmStrictAt (I := I) hd P L pb r n hcomplete hconn
                              q δ alpha (mu x)
                              (centerAverage.activeFill mu (ptsSeq a b)
                                (fun y => y) x)
                              join x (radSeq a b x) hcm := by
  classical
  obtain ⟨aMin, haMin, hmin⟩ :=
    exists_slot_min (I := I) hprof hre hcomplete hconn
  refine ⟨aMin, haMin, ?_⟩
  intro D hD hphys P L pb r
  obtain ⟨q, δ, hqdata, _hqWide, _hqAcc, _herr, _hinvErr, _hquarter,
      hbranch⟩ := hmin P L pb r
  refine ⟨q, δ, hqdata, ?_⟩
  filter_upwards [hbranch, aliveSlots_tail hd P L pb r] with n hn hstable
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ n)).M => TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ n)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ n)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ n)).M => TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ n)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n))
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  constructor
  · intro gamma c hc
    have halive : L.alive (gamma : Nat) = true := by
      simpa [hc] using (hstable gamma).symm
    let gammaLive : LiveSlot L pb r := ⟨gamma, halive⟩
    have hcD : c = seqCenterD hd P L n (gamma : Nat) := by
      simp [seqCenterD, hc]
    refine ⟨hcD, ?_⟩
    have hfloor := (hn gammaLive).2.2
    rw [hcD]
    exact (lamInf_lt_halfMin hd hD hphys P L (gamma : Nat)).trans_le
      (by simpa only [gammaLive] using hfloor)
  · intro alpha s hs mu hmu ptsSeq hpts
    obtain ⟨radSeq, hpos, hactive, htail⟩ :=
      centerAverage.exists_active_radius
        (s := s) (target := fun x => x)
        (μSeq := fun _ _ => mu) (ptsSeq := ptsSeq) hpts
    refine ⟨radSeq, ?_, ?_, htail, ?_⟩
    · intro a b x _hx
      exact hpos a b x
    · intro a b x hx gamma hne
      exact hactive a b x hx gamma hne
    · obtain ⟨N, hN⟩ := exists_rad_cage hd hD haMin hphys P L pb r n
        s radSeq htail
      refine ⟨N, ?_⟩
      intro a ha b hbN x hx join hstrict
      let pts := centerAverage.activeFill mu (ptsSeq a b) (fun y => y) x
      let hcomplete' :=
        NetLimitData.sourceComplete (I := I) hd P L n hcomplete (hconn (L.φ n))
      have hcm : CenterInput (I := I) (X.obj (L.φ n)).metric
          (mu x) pts join x (radSeq a b x) := by
        simpa only [pts] using
          centerAverage.inputOfFillSelf (I := I)
            (g := (X.obj (L.φ n)).metric) (μ := mu)
            (pts := ptsSeq a b) (join := join) (r := radSeq a b)
            (qstar := fun y => y) x hcomplete' (hpos a b x)
            (hactive a b x hx) (hmu.nonneg x hx) (hmu.pos x hx) hstrict
      refine ⟨hcm, ?_⟩
      have hout := exists_hat_cm_sol_at (I := I) hd P hre L pb r n
        hcomplete hconn q δ hqdata hn alpha (mu x) pts join x
        (radSeq a b x) hcm (hmu.sum_one x hx) (hs hx)
        (hN a ha b hbN x hx alpha)
      simpa only [HasHatCmStrictAt] using hout




theorem exists_hat_cm_min
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (hprof : NormalRadiusProfile hd hb)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aMin : Real, 0 < aMin ∧
      ∀ {D : Real} (hD : 0 < D)
        (hphys : 8 * Real.exp hd.C < aMin * D)
        (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
        (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real),
        ∃ q : LiveSlot L pb r → NNReal,
          ∃ δ : LiveSlot L pb r → Real,
            (∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rhoMin := aMin * hd.mu Rgamma
              0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
                2 * rhoMin < (q gamma : Real)) ∧
            (∀ gamma : LiveSlot L pb r,
              6 * (q gamma : Real) <
                hprof.phaseRadius (L.rInf (gamma.1 : Nat) + 1)) ∧
            (∀ gamma : LiveSlot L pb r,
              3 * hb.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
                (2 / 3 : Real) * (q gamma : Real)) ∧
            (∀ gamma : LiveSlot L pb r,
              PhaseFlow.phaseErr (normalPhaseK hb (2 * q gamma)) < T) ∧
            (∀ gamma : LiveSlot L pb r,
              N * (T - PhaseFlow.phaseErr
                    (normalPhaseK hb (2 * q gamma)))⁻¹ *
                  PhaseFlow.phaseErr (normalPhaseK hb (2 * q gamma)) < 1 / 24) ∧
            Filter.Eventually
              (fun n ↦ HasLiveBrFull (I := I) P L pb r n
                hcomplete hconn aMin q δ)
              Filter.atTop ∧
            (∀ᶠ n in Filter.atTop, ∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              let x := seqCenterD hd P L n (gamma.1 : Nat)
              letI : TopologicalSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).topology
              letI : ChartedSpace H (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).charted
              letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).smooth
              letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                (X.obj (L.φ n)).t2TangentBundle
              Metric.ball (0 : E) rho ⊆
                  normalQuarter (I := I) (X.obj (L.φ n)) x ∧
                rho ≤ hb.radius (L.φ n) x ∧
                rho / 2 ≤ expRadiusGp
                  (I := I) (X.obj (L.φ n)).metric x) ∧
            ∀ᶠ n in Filter.atTop,
              letI : TopologicalSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).topology
              letI : ChartedSpace H (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).charted
              letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).smooth
              letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
                (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
              letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).sigmaCompact
              letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
              letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
              letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                (X.obj (L.φ n)).t2TangentBundle
              letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                Manifold.metrizableSpace I (X.obj (L.φ n)).M
              letI : T3Space (X.obj (L.φ n)).M := inferInstance
              letI : RiemannianBundle
                  (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
                (X.obj (L.φ n)).riemBundle (I := I)
              letI : (x : (X.obj (L.φ n)).M) →
                  InnerProductSpace Real (TangentSpace I x) :=
                (X.obj (L.φ n)).riemInner (I := I)
              letI : IsContinuousRiemannianBundle E
                  (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
                (X.obj (L.φ n)).riemBundle_cont (I := I)
              letI : EMetricSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).emetricSpace (I := I)
              letI : CompleteSpace (X.obj (L.φ n)).M :=
                MetricComplete.complete (I := I) (X.obj (L.φ n))
                  (hcomplete.complete (L.φ n))
              letI : MetricSpace (X.obj (L.φ n)).M :=
                HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
              (∀ gamma : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
                seqCenter hd D P (L.φ n) (gamma : Nat) = some c →
                  c = seqCenterD hd P L n (gamma : Nat) ∧
                    4 * L.lamInf (gamma : Nat) <
                      expRadiusGp (I := I) (X.obj (L.φ n)).metric c) ∧
              ∀ (alpha : LiveSlot L pb r)
                (s : Set (X.obj (L.φ n)).M)
                (hs : s ⊆ NetLimitData.hatBall (I := I) (X := X)
                  hd D P L pb r n alpha.1)
                (mu : (X.obj (L.φ n)).M → Fin (pb.A r) → Real)
                (hmu : centerAverage.WeightDataOn s
                  (fun _ : Fin (pb.A r) => Set.univ) mu)
                (ptsSeq : Nat → Nat → (X.obj (L.φ n)).M →
                  Fin (pb.A r) → (X.obj (L.φ n)).M)
                (hpts : ∀ gamma : Fin (pb.A r), ∀ epsilon : Real,
                  0 < epsilon → ∃ N : Nat,
                    ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x ∈ s, mu x gamma ≠ 0 →
                        dist x (ptsSeq a b x gamma) < epsilon),
                  ∃ radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real,
                    (∀ a b x, x ∈ s → 0 < radSeq a b x) ∧
                    (∀ a b x, x ∈ s → ∀ gamma, mu x gamma ≠ 0 →
                      dist x (ptsSeq a b x gamma) < radSeq a b x) ∧
                    (∀ epsilon > 0, ∃ N : Nat,
                      ∀ a ≥ N, ∀ b ≥ N,
                        ∀ x ∈ s, radSeq a b x < epsilon) ∧
                    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x ∈ s,
                        let join := minJoin (I := I) (X.obj (L.φ n)).metric
                          (normal_enorm (I := I) (X.obj (L.φ n)))
                        let pts := centerAverage.activeFill mu (ptsSeq a b)
                          (fun y => y) x
                        ∃ hcm : CenterInput (I := I)
                            (X.obj (L.φ n)).metric (mu x) pts join x
                            (radSeq a b x),
                          HasHatCmStrictAt (I := I) hd P L pb r n hcomplete hconn
                            q δ alpha (mu x) pts join x (radSeq a b x) hcm := by
  classical
  obtain ⟨aMin, haMin, hmin⟩ :=
    exists_slot_min (I := I) hprof hre hcomplete hconn
  refine ⟨aMin, haMin, ?_⟩
  intro D hD hphys P L pb r
  obtain ⟨q, δ, hqdata, hqWide, hqAcc, herr, hinvErr, hquarter, hbranch⟩ :=
    hmin P L pb r
  have hbranchFull : Filter.Eventually
      (fun n ↦ HasLiveBrFull (I := I) P L pb r n
        hcomplete hconn aMin q δ) Filter.atTop := by
    filter_upwards [hbranch] with n hn
    intro gamma
    exact (hn gamma).1
  have hscale : ∀ᶠ n in Filter.atTop, ∀ gamma : LiveSlot L pb r,
      let Rgamma := L.rInf (gamma.1 : Nat) + 1
      let rho := aMin * hd.mu Rgamma
      let x := seqCenterD hd P L n (gamma.1 : Nat)
      letI : TopologicalSpace (X.obj (L.φ n)).M :=
        (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M :=
        (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
        (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆
          normalQuarter (I := I) (X.obj (L.φ n)) x ∧
        rho ≤ hb.radius (L.φ n) x ∧
        rho / 2 ≤ expRadiusGp
          (I := I) (X.obj (L.φ n)).metric x := by
    filter_upwards [hquarter, hbranch] with n hquarterN hn
    intro gamma
    exact ⟨hquarterN gamma, (hn gamma).2⟩
  refine ⟨q, δ, hqdata, hqWide, hqAcc, herr, hinvErr,
    hbranchFull, hscale, ?_⟩
  filter_upwards [hbranch, hquarter, aliveSlots_tail hd P L pb r] with
      n hn hquarterN hstable
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ n)).M => TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ n)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ n)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ n)).M => TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ n)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n))
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  constructor
  · intro gamma c hc
    have halive : L.alive (gamma : Nat) = true := by
      simpa [hc] using (hstable gamma).symm
    let gammaLive : LiveSlot L pb r := ⟨gamma, halive⟩
    have hcD : c = seqCenterD hd P L n (gamma : Nat) := by
      simp [seqCenterD, hc]
    refine ⟨hcD, ?_⟩
    have hfloor := (hn gammaLive).2.2
    rw [hcD]
    exact (lamInf_lt_halfMin hd hD hphys P L (gamma : Nat)).trans_le
      (by simpa only [gammaLive] using hfloor)
  · intro alpha s hs mu hmu ptsSeq hpts
    obtain ⟨radSeq, hpos, hactive, htail⟩ :=
      centerAverage.exists_active_radius
        (s := s) (target := fun x => x)
        (μSeq := fun _ _ => mu) (ptsSeq := ptsSeq) hpts
    refine ⟨radSeq, ?_, ?_, htail, ?_⟩
    · intro a b x _hx
      exact hpos a b x
    · intro a b x hx gamma hne
      exact hactive a b x hx gamma hne
    · have htail3 : ∀ epsilon > 0, ∃ N : Nat,
          ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ s,
            3 * radSeq a b x < epsilon := by
        intro epsilon hepsilon
        obtain ⟨N, hN⟩ := htail (epsilon / 3) (div_pos hepsilon (by norm_num))
        refine ⟨N, ?_⟩
        intro a ha b hbN x hx
        nlinarith [hN a ha b hbN x hx]
      obtain ⟨N, hN⟩ := exists_rad_cage hd hD haMin hphys P L pb r n
        s (fun a b x => 3 * radSeq a b x) htail3
      refine ⟨N, ?_⟩
      intro a ha b hbN x hx
      let pts := centerAverage.activeFill mu (ptsSeq a b) (fun y => y) x
      let join := minJoin (I := I) (X.obj (L.φ n)).metric
        (normal_enorm (I := I) (X.obj (L.φ n)))
      let x0 := seqCenterD hd P L n (alpha.1 : Nat)
      let rho0 := aMin * hd.mu (L.rInf (alpha.1 : Nat) + 1)
      rcases hqdata alpha with ⟨_hq, _hδ, hρ, hρq⟩
      rcases hn alpha with ⟨hfull, hρmetric, hρexp⟩
      have hproper :
          (letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
           dist x x0) < 4 * L.lamInf (alpha.1 : Nat) := by
        simpa only [x0] using hat_dist_centerD hd P L pb r (hs hx)
      have hhd : hd.dist (L.φ n) x x0 < 4 * L.lamInf (alpha.1 : Nat) := by
        rw [← ProperMetricOn.dist_eq hd hre P (L.φ n) x x0]
        exact hproper
      have hed : riemannianEDist I x x0 =
          ENNReal.ofReal (hd.dist (L.φ n) x x0) := by
        have hrealize := hre.edist_eq (L.φ n) x x0
        simpa [PointedRiemannianManifold.emetricSpace] using hrealize
      have hpq : dist x0 x ≤ 4 * L.lamInf (alpha.1 : Nat) := by
        rw [dist_comm, HopfRinow.riemMetric_dist_eq, hed,
          ENNReal.toReal_ofReal (hre.dist_nonneg (L.φ n) x x0)]
        exact hhd.le
      have hptsFilled : ∀ gamma, dist x (pts gamma) < radSeq a b x := by
        simpa only [pts] using centerAverage.activeFill_close
          (g := (X.obj (L.φ n)).metric) (μ := mu) (pts := ptsSeq a b)
            (qstar := fun y => y) (x := x) (hpos a b x)
            (hactive a b x hx)
      have hcage6 : ENNReal.ofReal
            (4 * L.lamInf (alpha.1 : Nat) + 6 * radSeq a b x) <
          ENNReal.ofReal (rho0 / 2) := by
        have hc := hN a ha b hbN x hx alpha
        have heq : 4 * L.lamInf (alpha.1 : Nat) +
            2 * (3 * radSeq a b x) =
            4 * L.lamInf (alpha.1 : Nat) + 6 * radSeq a b x := by
          ring
        rw [heq] at hc
        simpa only [rho0] using hc
      have hstrict : StrictDistInput (I := I) (X.obj (L.φ n)).metric
          pts join x (radSeq a b x) := by
        simpa only [pts, join, x0, rho0] using
          HasNormalBrFull.strict_dist (I := I) hb (L.φ n)
            (hcomplete.complete (L.φ n)) (hconn (L.φ n)) x0 hfull
            (hqAcc alpha) pts x (radSeq a b x)
            (4 * L.lamInf (alpha.1 : Nat)) (hquarterN alpha)
            hρ hρq hρmetric hρexp (hpos a b x) hpq hptsFilled hcage6
      let hcomplete' :=
        NetLimitData.sourceComplete (I := I) hd P L n hcomplete (hconn (L.φ n))
      have hcm : CenterInput (I := I) (X.obj (L.φ n)).metric
          (mu x) pts join x (radSeq a b x) := by
        simpa only [pts, join] using
          centerAverage.inputOfFillSelf (I := I)
            (g := (X.obj (L.φ n)).metric) (μ := mu)
            (pts := ptsSeq a b) (join := join) (r := radSeq a b)
            (qstar := fun y => y) x hcomplete' (hpos a b x)
            (hactive a b x hx) (hmu.nonneg x hx) (hmu.pos x hx) hstrict
      have hradCage : ENNReal.ofReal
            (4 * L.lamInf (alpha.1 : Nat) + 2 * radSeq a b x) <
          ENNReal.ofReal (rho0 / 2) := by
        apply (ENNReal.ofReal_le_ofReal ?_).trans_lt hcage6
        nlinarith [hpos a b x]
      refine ⟨hcm, ?_⟩
      have hout := exists_hat_cm_sol_at (I := I) hd P hre L pb r n
        hcomplete hconn q δ hqdata hn alpha (mu x) pts join x
        (radSeq a b x) hcm (hmu.sum_one x hx) (hs hx) hradCage
      simpa only [HasHatCmStrictAt, pts, join] using hout

end HCGCompactness
end DifferentialGeometry
