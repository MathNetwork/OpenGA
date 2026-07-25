import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomJoin

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]




theorem atomWeight_of_atoms
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist)
    (pb : hd.PackingBound D) (r : Real) (hr : 0 ≤ r)
    (hgp : ∀ k, Item3GpScaleAt (I := I) hd D P L pb r k)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M)
    (U : Set E) (hU : IsOpen U)
    (hcoverU : ∀ k,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma))
    (aInf : Fin (pb.A r) → E → Real)
    (hdead : ∀ gamma : Fin (pb.A r),
      L.alive (gamma : Nat) = false → aInf gamma = 0)
    (hatom : ∀ gamma : Fin (pb.A r),
      MapCInfConvOnCompacts U
        (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k)
        (aInf gamma))
    (hatomSmooth : ∀ k (gamma : Fin (pb.A r)),
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (seqAtomChart (I := I) hd hD P L pb r beta gamma k) U)
    (hatomInfSmooth : ∀ gamma : Fin (pb.A r),
      ContDiffOn Real (∞ : WithTop ℕ∞) (aInf gamma) U) :
    let atom : Nat → Fin (pb.A r) → E → Real := fun k gamma =>
      seqAtomChart (I := I) hd hD P L pb r beta gamma k
    let atomPi : Nat → E → (Fin (pb.A r) → Real) := fun k z gamma => atom k gamma z
    let atomInf : E → (Fin (pb.A r) → Real) := fun z gamma => aInf gamma z
    let i0 := baseIndex hd hre pb hr
    let weight : Nat → E → (Fin (pb.A r) → Real) := fun k z gamma =>
      rawWeights (cutRaw (atom k i0) (atom k) i0) z gamma
    let weightInf : E → (Fin (pb.A r) → Real) := fun z gamma =>
      rawWeights (cutRaw (aInf i0) aInf i0) z gamma
    (∀ gamma : Fin (pb.A r),
      L.alive (gamma : Nat) = false → aInf gamma = 0) ∧
    (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (atomPi k) U) ∧
    ContDiffOn Real (∞ : WithTop ℕ∞) atomInf U ∧
    MapCInfConvOnCompacts U atomPi atomInf ∧
    (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (weight k) U) ∧
    ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U ∧
    MapCInfConvOnCompacts U weight weightInf := by
  classical
  let atom : Nat → Fin (pb.A r) → E → Real := fun k gamma =>
    seqAtomChart (I := I) hd hD P L pb r beta gamma k
  let atomPi : Nat → E → (Fin (pb.A r) → Real) := fun k z gamma => atom k gamma z
  let atomInf : E → (Fin (pb.A r) → Real) := fun z gamma => aInf gamma z
  have hatomPi : MapCInfConvOnCompacts U atomPi atomInf :=
    mapCInfConv_pi (E' := E) (Q := Real) hU hatom
      (fun gamma k => hatomSmooth k gamma) hatomInfSmooth
  have hatomPiSmooth (k : Nat) :
      ContDiffOn Real (∞ : WithTop ℕ∞) (atomPi k) U :=
    contDiffOn_pi.mpr fun gamma => hatomSmooth k gamma
  have hatomInfPiSmooth :
      ContDiffOn Real (∞ : WithTop ℕ∞) atomInf U :=
    contDiffOn_pi.mpr hatomInfSmooth
  let i0 := baseIndex hd hre pb hr
  have hcover (k : Nat) (z : E) (hz : z ∈ U) :
      ∃ gamma, atom k gamma z = 1 := by
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp (hcoverU k hz)
    refine ⟨gamma, ?_⟩
    change seqAtom hd hD P L pb r k gamma
      (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z) = 1
    exact seqAtom_one hd hD P L pb r k (hgp k) gamma hgamma
  have hbase (k : Nat) (z : E) (_hz : z ∈ U) :
      atom k i0 z ∈ Set.Icc (0 : Real) 1 := by
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    change seqAtom hd hD P L pb r k i0
      (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z) ∈
        Set.Icc (0 : Real) 1
    exact seqAtom_Icc hd hD P L pb r k i0 _
  have hnn (k : Nat) (z : E) (_hz : z ∈ U) :
      ∀ gamma, 0 ≤ atom k gamma z := by
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    intro gamma
    change 0 ≤ seqAtom hd hD P L pb r k gamma
      (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
    exact seqAtom_nonneg hd hD P L pb r k gamma _
  have hweight (gamma : Fin (pb.A r)) :=
    cutWeights_conv hU hatom (fun k gamma => hatomSmooth k gamma)
      hatomInfSmooth i0 hbase hnn hcover gamma
  have hraw (gamma : Fin (pb.A r)) :=
    cutRaw_conv hU hatom (fun k gamma => hatomSmooth k gamma)
      hatomInfSmooth i0 gamma
  have hrawc (k : Nat) (gamma : Fin (pb.A r)) :=
    cutRaw_contDiffOn (fun q => hatomSmooth k q) i0 gamma
  have hrawcinf (gamma : Fin (pb.A r)) :=
    cutRaw_contDiffOn hatomInfSmooth i0 gamma
  have hden (k : Nat) (z : E) (hz : z ∈ U) :
      (∑ gamma, cutRaw (atom k i0) (atom k) i0 gamma z) ≠ 0 := by
    have hh := cutRaw_sum_half (hbase k z hz) (hnn k z hz) (hcover k z hz)
    linarith
  have hdenInf (z : E) (hz : z ∈ U) :
      (∑ gamma, cutRaw (aInf i0) aInf i0 gamma z) ≠ 0 := by
    have hsum : Filter.Tendsto
        (fun k => ∑ gamma, cutRaw (atom k i0) (atom k) i0 gamma z)
        Filter.atTop (nhds (∑ gamma, cutRaw (aInf i0) aInf i0 gamma z)) :=
      tendsto_finset_sum Finset.univ fun gamma _ => tendsto_of_cInf (hraw gamma) hz
    have hh : (1 / 2 : Real) ≤ ∑ gamma, cutRaw (aInf i0) aInf i0 gamma z :=
      ge_of_tendsto hsum (Filter.Eventually.of_forall fun k =>
        cutRaw_sum_half (hbase k z hz) (hnn k z hz) (hcover k z hz))
    linarith
  have hweightSmooth (k : Nat) (gamma : Fin (pb.A r)) :
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z => rawWeights (cutRaw (atom k i0) (atom k) i0) z gamma) U := by
    simpa only [rawWeights, normWeights] using
      normWeights_contDiffOn (fun q => hrawc k q) (fun z hz => hden k z hz) gamma
  have hweightInfSmooth (gamma : Fin (pb.A r)) :
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z => rawWeights (cutRaw (aInf i0) aInf i0) z gamma) U := by
    simpa only [rawWeights, normWeights] using
      normWeights_contDiffOn hrawcinf hdenInf gamma
  let weight : Nat → E → (Fin (pb.A r) → Real) := fun k z gamma =>
    rawWeights (cutRaw (atom k i0) (atom k) i0) z gamma
  let weightInf : E → (Fin (pb.A r) → Real) := fun z gamma =>
    rawWeights (cutRaw (aInf i0) aInf i0) z gamma
  have hweightPi : MapCInfConvOnCompacts U weight weightInf :=
    mapCInfConv_pi (E' := E) (Q := Real) hU hweight
      (fun gamma k => hweightSmooth k gamma) hweightInfSmooth
  have hweightPiSmooth (k : Nat) :
      ContDiffOn Real (∞ : WithTop ℕ∞) (weight k) U :=
    contDiffOn_pi.mpr fun gamma => hweightSmooth k gamma
  have hweightInfPiSmooth :
      ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U :=
    contDiffOn_pi.mpr hweightInfSmooth
  dsimp only
  exact ⟨hdead, hatomPiSmooth, hatomInfPiSmooth, hatomPi,
    hweightPiSmooth, hweightInfPiSmooth, hweightPi⟩



private theorem existsAtomWeightCore
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist)
    (pb : hd.PackingBound D) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M)
    (U : Set E) (hU : IsOpen U)
    (hUx : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (beta k)))
    (hcoverU : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma))
    (hjoint :
      ∃ (psi : Nat → Nat)
          (gInf : E → (LiveSlot L pb r → (E →L[Real] E →L[Real] Real)))
          (Jinf : LiveSlot L pb r → E → E),
        StrictMono psi ∧
        ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ gamma => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
            (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0) gInf ∧
        ∀ gamma : LiveSlot L pb r,
          ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf gamma) U ∧
          MapCInfConvOnCompacts U
            (fun k => normalTransition (I := I) (X.obj (L.φ (psi k)))
              (beta (psi k)) (seqCenterD hd P L (psi k) (gamma.1 : Nat)))
            (Jinf gamma) ∧
          (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
            (normalTransition (I := I) (X.obj (L.φ (psi k)))
              (beta (psi k)) (seqCenterD hd P L (psi k) (gamma.1 : Nat))) U) ∧
          (∀ k, NormalOverlapOn (I := I) (X.obj (L.φ (psi k)))
            (beta (psi k)) (seqCenterD hd P L (psi k) (gamma.1 : Nat)) U) ∧
          (∀ k, seqCenter hd D P (L.φ (psi k)) (gamma.1 : Nat) =
            some (seqCenterD hd P L (psi k) (gamma.1 : Nat)))) :
    ∃ (psi : Nat -> Nat) (hpsi : StrictMono psi)
        (aInf : Fin (pb.A r) -> E -> Real),
      let Lpsi := L.subseq hpsi
      let betapsi : ∀ k, (X.obj (Lpsi.φ k)).M := fun k => beta (psi k)
      let atom : Nat -> Fin (pb.A r) -> E -> Real := fun k gamma =>
        seqAtomChart (I := I) hd hD P Lpsi pb r betapsi gamma k
      let atomPi : Nat -> E -> (Fin (pb.A r) -> Real) := fun k z gamma => atom k gamma z
      let atomInf : E -> (Fin (pb.A r) -> Real) := fun z gamma => aInf gamma z
      let i0 := baseIndex hd hre pb hr
      let weight : Nat -> E -> (Fin (pb.A r) -> Real) := fun k z gamma =>
        rawWeights (cutRaw (atom k i0) (atom k) i0) z gamma
      let weightInf : E -> (Fin (pb.A r) -> Real) := fun z gamma =>
        rawWeights (cutRaw (aInf i0) aInf i0) z gamma
      (∀ gamma : Fin (pb.A r),
        Lpsi.alive (gamma : Nat) = false -> aInf gamma = 0) ∧
      (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (atomPi k) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) atomInf U ∧
      MapCInfConvOnCompacts U atomPi atomInf ∧
      (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (weight k) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U ∧
      MapCInfConvOnCompacts U weight weightInf := by
  classical
  obtain ⟨psi0, gInf, Jinf, hpsi0, hginf, hg, hJ⟩ :=
    hjoint
  have htail : ∀ᶠ k in Filter.atTop,
      (letI : TopologicalSpace (X.obj (L.φ (psi0 k))).M :=
          (X.obj (L.φ (psi0 k))).topology
       letI : ChartedSpace H (X.obj (L.φ (psi0 k))).M :=
          (X.obj (L.φ (psi0 k))).charted
       letI : IsManifold I ∞ (X.obj (L.φ (psi0 k))).M :=
          (X.obj (L.φ (psi0 k))).smooth
       letI : T2Space (TangentBundle I (X.obj (L.φ (psi0 k))).M) :=
          (X.obj (L.φ (psi0 k))).t2TangentBundle
       U ⊆ Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj (L.φ (psi0 k))).metric
            (beta (psi0 k)))) ∧
      (letI : TopologicalSpace (X.obj (L.φ (psi0 k))).M :=
          (X.obj (L.φ (psi0 k))).topology
       letI : ChartedSpace H (X.obj (L.φ (psi0 k))).M :=
          (X.obj (L.φ (psi0 k))).charted
       letI : IsManifold I ∞ (X.obj (L.φ (psi0 k))).M :=
          (X.obj (L.φ (psi0 k))).smooth
       letI : T2Space (TangentBundle I (X.obj (L.φ (psi0 k))).M) :=
          (X.obj (L.φ (psi0 k))).t2TangentBundle
       Set.MapsTo
          (fun z => expMapDiffeo (I := I) (X.obj (L.φ (psi0 k))).metric
            (beta (psi0 k)) z)
          U (⋃ gamma : Fin (pb.A r),
            L.innerBall hd D P pb r (psi0 k) gamma)) ∧
      Item3GpScaleAt (I := I) hd D P L pb r (psi0 k) := by
    filter_upwards
      [hpsi0.tendsto_atTop.eventually hUx,
        hpsi0.tendsto_atTop.eventually hcoverU,
        hpsi0.tendsto_atTop.eventually hgp]
      with k hkUx hkcover hkgp
    exact ⟨hkUx, hkcover, hkgp⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  let tau : Nat -> Nat := fun k => k + N
  have htau : StrictMono tau := by
    simpa only [tau] using strictMono_id.add_const N
  let psi : Nat -> Nat := psi0 ∘ tau
  have hpsi : StrictMono psi := by
    simpa only [psi] using hpsi0.comp htau
  have htailAt (k : Nat) :=
    hN (tau k) (by simpa only [tau] using Nat.le_add_left N k)
  let Lpsi := L.subseq hpsi
  let Xpsi := X.subseq Lpsi.φ
  let betapsi : ∀ k, (Xpsi.obj k).M := fun k => beta (psi k)
  let center : LiveSlot L pb r -> ∀ k, (Xpsi.obj k).M := fun gamma k =>
    seqCenterD hd P Lpsi k (gamma.1 : Nat)
  have hgsub := hg.comp_subseq htau
  have hgpsi : MapCInfConvOnCompacts U
      (fun k (_ : E) (gamma : LiveSlot L pb r) =>
        normalCoordMetric (I := I) (Xpsi.obj k) (center gamma k) 0) gInf := by
    change MapCInfConvOnCompacts U
      (fun k (_ : E) (gamma : LiveSlot L pb r) =>
        normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0) gInf
    intro K hK hKU p
    simpa only [psi, Function.comp_apply] using
      hgsub K hK (hKU.trans (Set.subset_univ U)) p
  have hginfU : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U :=
    hginf.mono (Set.subset_univ U)
  have hJpsi (gamma : LiveSlot L pb r) :
      MapCInfConvOnCompacts U
        (fun k => normalTransition (I := I) (Xpsi.obj k)
          (betapsi k) (center gamma k)) (Jinf gamma) := by
    change MapCInfConvOnCompacts U
      (fun k => normalTransition (I := I) (X.obj (L.φ (psi k)))
        (beta (psi k)) (seqCenterD hd P L (psi k) (gamma.1 : Nat)))
      (Jinf gamma)
    simpa only [psi, Function.comp_apply] using (hJ gamma).2.1.comp_subseq htau
  have hJcpsi (gamma : LiveSlot L pb r) (k : Nat) :
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (normalTransition (I := I) (Xpsi.obj k)
          (betapsi k) (center gamma k)) U := by
    change ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj (L.φ (psi k)))
        (beta (psi k)) (seqCenterD hd P L (psi k) (gamma.1 : Nat))) U
    simpa only [psi, Function.comp_apply] using (hJ gamma).2.2.1 (tau k)
  have hsrcpsi (gamma : LiveSlot L pb r) (k : Nat) (z : E) (hz : z ∈ U) :
      letI : TopologicalSpace (Xpsi.obj k).M := (Xpsi.obj k).topology
      letI : ChartedSpace H (Xpsi.obj k).M := (Xpsi.obj k).charted
      letI : IsManifold I ∞ (Xpsi.obj k).M := (Xpsi.obj k).smooth
      letI : T2Space (Xpsi.obj k).M := (Xpsi.obj k).t2
      letI : T2Space (TangentBundle I (Xpsi.obj k).M) :=
        (Xpsi.obj k).t2TangentBundle
      expMapDiffeo (I := I) (Xpsi.obj k).metric (betapsi k) z ∈
        (normalChartAt (I := I) (Xpsi.obj k).metric (center gamma k)).source := by
    letI : TopologicalSpace (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).topology
    letI : ChartedSpace H (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).charted
    letI : IsManifold I ∞ (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).smooth
    letI : T2Space (X.obj (L.φ (psi k))).M := (X.obj (L.φ (psi k))).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ (psi k))).M) :=
      (X.obj (L.φ (psi k))).t2TangentBundle
    change expMapDiffeo (I := I) (X.obj (L.φ (psi k))).metric
        (beta (psi k)) z ∈
      (normalChartAt (I := I) (X.obj (L.φ (psi k))).metric
        (seqCenterD hd P L (psi k) (gamma.1 : Nat))).source
    simpa only [psi, Function.comp_apply] using
      (((hJ gamma).2.2.2.1 (tau k)) z hz).2
  have hliveAtom (gamma : LiveSlot L pb r) :=
    stepCAtom_conv (I := I) (X := Xpsi) center betapsi
      (fun gamma => Lpsi.lamInf (gamma.1 : Nat))
      (fun gamma => hd.lambda_pos hD (Lpsi.rInf (gamma.1 : Nat)))
      hU hgpsi hginfU hJpsi hJcpsi (fun gamma => (hJ gamma).1) hsrcpsi gamma
  let aInf : Fin (pb.A r) -> E -> Real := fun gamma =>
    if hgamma : Lpsi.alive (gamma : Nat) = true then
      fun z => stepCBump (Lpsi.lamInf (gamma : Nat))
        (hd.lambda_pos hD (Lpsi.rInf (gamma : Nat)))
        (gInf z (⟨gamma, hgamma⟩ : LiveSlot L pb r)
          (Jinf ⟨gamma, hgamma⟩ z) (Jinf ⟨gamma, hgamma⟩ z))
    else fun _ => 0
  have hliveForSeq : ∀ gamma : Fin (pb.A r),
      Lpsi.alive (gamma : Nat) = true ->
      MapCInfConvOnCompacts U
        (fun k => stepCAtomChart (I := I) (X.obj (Lpsi.φ k))
          (betapsi k) (seqCenterD hd P Lpsi k (gamma : Nat))
          (Lpsi.lamInf (gamma : Nat))
          (hd.lambda_pos hD (Lpsi.rInf (gamma : Nat))))
        (aInf gamma) := by
    intro gamma hgamma
    have h := hliveAtom (⟨gamma, hgamma⟩ : LiveSlot L pb r)
    simpa only [Xpsi, center, PointedRiemannianSeq.subseq, aInf,
      dif_pos hgamma] using h
  have hatom0 :=
    seqAtoms_conv (I := I) hd hD P Lpsi pb r betapsi hU aInf hliveForSeq
  have hatom : ∀ gamma : Fin (pb.A r),
      MapCInfConvOnCompacts U
        (fun k => seqAtomChart (I := I) hd hD P Lpsi pb r betapsi gamma k)
        (aInf gamma) := by
    intro gamma
    by_cases hgamma : Lpsi.alive (gamma : Nat) = true
    · simpa [aInf, hgamma] using hatom0 gamma
    · simpa [aInf, hgamma] using hatom0 gamma
  have hdead : ∀ gamma : Fin (pb.A r),
      Lpsi.alive (gamma : Nat) = false -> aInf gamma = 0 := by
    intro gamma hgamma
    simp only [aInf, hgamma, Bool.false_eq_true, ↓reduceDIte]
    funext x
    rfl
  have hgpPsi (k : Nat) : Item3GpScaleAt (I := I) hd D P Lpsi pb r k := by
    exact (htailAt k).2.2
  have hUxPsi (k : Nat) :
      letI : TopologicalSpace (X.obj (Lpsi.φ k)).M := (X.obj (Lpsi.φ k)).topology
      letI : ChartedSpace H (X.obj (Lpsi.φ k)).M := (X.obj (Lpsi.φ k)).charted
      letI : IsManifold I ∞ (X.obj (Lpsi.φ k)).M := (X.obj (Lpsi.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (Lpsi.φ k)).M) :=
        (X.obj (Lpsi.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (Lpsi.φ k)).metric (betapsi k)) := by
    letI : TopologicalSpace (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).topology
    letI : ChartedSpace H (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).charted
    letI : IsManifold I ∞ (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ (psi k))).M) :=
      (X.obj (L.φ (psi k))).t2TangentBundle
    change U ⊆ Metric.ball (0 : E)
      (expMapC2Radius (I := I) (X.obj (L.φ (psi k))).metric (beta (psi k)))
    exact (htailAt k).1
  have hatomSmooth (k : Nat) (gamma : Fin (pb.A r)) :
      ContDiffOn Real (∞ : WithTop ℕ∞)
        (seqAtomChart (I := I) hd hD P Lpsi pb r betapsi gamma k) U :=
    seqAtomChart_smooth (I := I) hd hD P Lpsi pb r k (hgpPsi k)
      betapsi gamma (hUxPsi k)
  have hatomInfSmooth (gamma : Fin (pb.A r)) :
      ContDiffOn Real (∞ : WithTop ℕ∞) (aInf gamma) U := by
    by_cases hgamma : Lpsi.alive (gamma : Nat) = true
    · let live : LiveSlot L pb r := ⟨gamma, hgamma⟩
      have hquad : ContDiffOn Real (∞ : WithTop ℕ∞)
          (fun z => gInf z live (Jinf live z) (Jinf live z)) U :=
        ((contDiffOn_pi.mp hginfU live).clm_apply (hJ live).1).clm_apply
          (hJ live).1
      simpa only [aInf, dif_pos hgamma, live] using
        (stepCBump (Lpsi.lamInf (gamma : Nat))
          (hd.lambda_pos hD (Lpsi.rInf (gamma : Nat)))).contDiff.comp_contDiffOn hquad
    · simpa [aInf, hgamma] using
        (contDiffOn_const :
          ContDiffOn Real (∞ : WithTop ℕ∞) (fun _ : E => (0 : Real)) U)
  have hcoverPsi (k : Nat) :
      letI : TopologicalSpace (X.obj (Lpsi.φ k)).M := (X.obj (Lpsi.φ k)).topology
      letI : ChartedSpace H (X.obj (Lpsi.φ k)).M := (X.obj (Lpsi.φ k)).charted
      letI : IsManifold I ∞ (X.obj (Lpsi.φ k)).M := (X.obj (Lpsi.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (Lpsi.φ k)).M) :=
        (X.obj (Lpsi.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (Lpsi.φ k)).metric (betapsi k) z)
        U (⋃ gamma : Fin (pb.A r), Lpsi.innerBall hd D P pb r k gamma) := by
    letI : TopologicalSpace (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).topology
    letI : ChartedSpace H (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).charted
    letI : IsManifold I ∞ (X.obj (L.φ (psi k))).M :=
      (X.obj (L.φ (psi k))).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ (psi k))).M) :=
      (X.obj (L.φ (psi k))).t2TangentBundle
    intro z hz
    have hm : expMapDiffeo (I := I) (X.obj (L.φ (psi k))).metric
          (beta (psi k)) z ∈
        ⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r (psi k) gamma := by
      simpa only [psi, Function.comp_apply] using (htailAt k).2.1 hz
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp hm
    exact Set.mem_iUnion.mpr ⟨gamma, by
      simpa only [Lpsi, NetLimitData.innerBall_subseq] using hgamma⟩
  refine ⟨psi, hpsi, aInf, ?_⟩
  exact atomWeight_of_atoms (I := I) hD P Lpsi hre pb r hr hgpPsi betapsi U hU
    hcoverPsi aInf hdead hatom hatomSmooth hatomInfSmooth



theorem existsAtomWeightH6_of_innerCover
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist)
    (pb : hd.PackingBound D) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (rho : Real) (beta : ∀ k : Nat, (X.obj (L.φ k)).M)
    (U : Set E) (hU : IsOpen U)
    (hovlJ : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (beta k)
        (seqCenterD hd P L k (gamma.1 : Nat)) U)
    (hUmetric : ∀ᶠ k in Filter.atTop,
      U ⊆ Metric.ball (0 : E) (metricInput.radius (L.φ k) (beta k)))
    (hUexp : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (beta k)))
    (hmapsJ : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z) U
        ((fun v : E => (expMap (I := I) (X.obj (L.φ k)).metric
            (seqCenterD hd P L k (gamma.1 : Nat))
            (show TangentSpace I (seqCenterD hd P L k (gamma.1 : Nat)) from v) :
              (X.obj (L.φ k)).M)) '' Metric.ball (0 : E) rho))
    (hVmetric : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))))
    (hVexp : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric
          (seqCenterD hd P L k (gamma.1 : Nat))))
    (hcoverU : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma)) :
    ∃ (psi : Nat -> Nat) (hpsi : StrictMono psi)
        (aInf : Fin (pb.A r) -> E -> Real),
      let Lpsi := L.subseq hpsi
      let betapsi : ∀ k, (X.obj (Lpsi.φ k)).M := fun k => beta (psi k)
      let atom : Nat -> Fin (pb.A r) -> E -> Real := fun k gamma =>
        seqAtomChart (I := I) hd hD P Lpsi pb r betapsi gamma k
      let atomPi : Nat -> E -> (Fin (pb.A r) -> Real) := fun k z gamma => atom k gamma z
      let atomInf : E -> (Fin (pb.A r) -> Real) := fun z gamma => aInf gamma z
      let i0 := baseIndex hd hre pb hr
      let weight : Nat -> E -> (Fin (pb.A r) -> Real) := fun k z gamma =>
        rawWeights (cutRaw (atom k i0) (atom k) i0) z gamma
      let weightInf : E -> (Fin (pb.A r) -> Real) := fun z gamma =>
        rawWeights (cutRaw (aInf i0) aInf i0) z gamma
      (∀ gamma : Fin (pb.A r),
        Lpsi.alive (gamma : Nat) = false -> aInf gamma = 0) ∧
      (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (atomPi k) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) atomInf U ∧
      MapCInfConvOnCompacts U atomPi atomInf ∧
      (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (weight k) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U ∧
      MapCInfConvOnCompacts U weight weightInf := by
  exact existsAtomWeightCore (I := I) hD P L hre pb r hr hgp beta U hU
    hUexp hcoverU
    (existsLiveJointH6 (I := I) metricInput P L pb r rho beta U hU
      hovlJ hUmetric hUexp hmapsJ hVmetric hVexp)



theorem existsAtomWeightH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    {hd : InjRadiusDecayInput (I := I) X} {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist)
    (pb : hd.PackingBound D) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) hd D P L pb r)
    (rho : Real) (beta : ∀ k : Nat, (X.obj (L.φ k)).M)
    (U : Set E) (hU : IsOpen U)
    (hovlJ : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (beta k)
        (seqCenterD hd P L k (gamma.1 : Nat)) U)
    (hUmetric : ∀ᶠ k in Filter.atTop,
      U ⊆ Metric.ball (0 : E) (metricInput.radius (L.φ k) (beta k)))
    (hUexp : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (beta k)))
    (hmapsJ : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z) U
        ((fun v : E => (expMap (I := I) (X.obj (L.φ k)).metric
            (seqCenterD hd P L k (gamma.1 : Nat))
            (show TangentSpace I (seqCenterD hd P L k (gamma.1 : Nat)) from v) :
              (X.obj (L.φ k)).M)) '' Metric.ball (0 : E) rho))
    (hVmetric : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))))
    (hVexp : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric
          (seqCenterD hd P L k (gamma.1 : Nat))))
    (hbetaU : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (L.hatSourceBall hd P r k)) :
    ∃ (psi : Nat -> Nat) (hpsi : StrictMono psi)
        (aInf : Fin (pb.A r) -> E -> Real),
      let Lpsi := L.subseq hpsi
      let betapsi : ∀ k, (X.obj (Lpsi.φ k)).M := fun k => beta (psi k)
      let atom : Nat -> Fin (pb.A r) -> E -> Real := fun k gamma =>
        seqAtomChart (I := I) hd hD P Lpsi pb r betapsi gamma k
      let atomPi : Nat -> E -> (Fin (pb.A r) -> Real) := fun k z gamma => atom k gamma z
      let atomInf : E -> (Fin (pb.A r) -> Real) := fun z gamma => aInf gamma z
      let i0 := baseIndex hd hre pb hr
      let weight : Nat -> E -> (Fin (pb.A r) -> Real) := fun k z gamma =>
        rawWeights (cutRaw (atom k i0) (atom k) i0) z gamma
      let weightInf : E -> (Fin (pb.A r) -> Real) := fun z gamma =>
        rawWeights (cutRaw (aInf i0) aInf i0) z gamma
      (∀ gamma : Fin (pb.A r),
        Lpsi.alive (gamma : Nat) = false -> aInf gamma = 0) ∧
      (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (atomPi k) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) atomInf U ∧
      MapCInfConvOnCompacts U atomPi atomInf ∧
      (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (weight k) U) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) weightInf U ∧
      MapCInfConvOnCompacts U weight weightInf := by
  have hcover := L.innerBall_cover hd hD P hre pb r
  have hcoverU : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma) := by
    filter_upwards [hbetaU, hcover] with k hmap hinner
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    intro z hz
    apply hinner
    simpa only [NetLimitData.hatSourceBall] using hmap hz
  exact existsAtomWeightH6_of_innerCover (I := I) metricInput hD P L hre pb r hr
    hgp rho beta U hU hovlJ hUmetric hUexp hmapsJ hVmetric hVexp hcoverU

end HCGCompactness
end DifferentialGeometry
