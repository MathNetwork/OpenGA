import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactnessSubseq
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciFlowConvergence

set_option autoImplicit false
set_option linter.style.longLine false






















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]







def pointedCGHMaps_of_atZero
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat)
    (rmaps : PointedRiemannianCGMaps (I := I) (X.atZero (I := I))
      (L.atTime (I := I) 0) subseq) :
    PointedCGHMaps (I := I) X (L.atTime 0) subseq where
  partialDiffeomorph := rmaps.partialDiffeomorph
  source_exhausts := rmaps.source_exhausts
  base_mem := rmaps.base_mem
  basepoint_map := rmaps.basepoint_map





def pointedCGHMaps_of_manifold
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat)
    (rmaps : PointedRiemannianCGMaps (I := I) (X.atZero (I := I)) P subseq) :
    PointedCGHMaps (I := I) X P subseq where
  partialDiffeomorph := rmaps.partialDiffeomorph
  source_exhausts := rmaps.source_exhausts
  base_mem := rmaps.base_mem
  basepoint_map := rmaps.basepoint_map










def cghMaps_of_hL0
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (hL0 : L.atTime (I := I) 0 = mc.limit) :
    PointedCGHMaps (I := I) X (L.atTime 0) mc.subseq :=
  pointedCGHMaps_of_atZero (I := I) X L mc.subseq (hL0.symm ▸ mc.maps)





structure FlowLimitData
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I))) where

  L : PointedFlowData.{u, uE, uH} (I := I) X.D

  hL0 : L.atTime (I := I) 0 = mc.limit

  maps : PointedCGHMaps (I := I) X (L.atTime 0) mc.subseq

  scalar : ScalarPullbackTendsto (I := I) maps

  hσsrc : forall k : Nat,
    letI : TopologicalSpace (L.atTime 0).M := L.topology
    IsSigmaCompact (maps.source k)
  hσtgt : forall k : Nat,
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    IsSigmaCompact (maps.target k)

  refMetric : forall k : Nat,
    letI : TopologicalSpace (SourceDomain (I := I) maps k) := sourceDomTop (I := I) maps k
    letI : ChartedSpace H (SourceDomain (I := I) maps k) := sourceDomCharted (I := I) maps k
    letI : IsManifold I ∞ (SourceDomain (I := I) maps k) := sourceDomSmooth (I := I) maps k
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) maps k)


  conv : forall K : Set (L.atTime 0).M,
    forall _hK : letI : TopologicalSpace (L.atTime 0).M := L.topology; IsCompact K,
    forall p : Nat,
    forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
      forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t : Real, t ∈ Set.Icc a b ->
            ((SourceDomainMetricData.ofRestrictPullback (I := I)
              (Φ := maps) (k := k) (hσsrc k) (hσtgt k)
              (refMetric k) (letI : TopologicalSpace L.M := L.topology; letI : ChartedSpace H L.M := L.charted; letI : IsManifold I ∞ L.M := L.smooth; letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := (by change IsManifold I ∞ L.M; infer_instance); letI : SigmaCompactSpace L.M := L.sigmaCompact; letI : T2Space L.M := L.t2; L.S.family.metric)).derivNormSupOn (I := I) K p t) < ε





omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem flowLimit_upgrade
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (d : FlowLimitData (I := I) X mc) :
    CompactnessConclusion (I := I) X :=
  ⟨d.L, mc.subseq, mc.strictMono,
    ⟨SmoothCGHConverges.ofRestrictPullback (I := I)
      d.maps d.scalar d.hσsrc d.hσtgt d.refMetric (letI : TopologicalSpace d.L.M := d.L.topology; letI : ChartedSpace H d.L.M := d.L.charted; letI : IsManifold I ∞ d.L.M := d.L.smooth; letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) d.L.M := (by change IsManifold I ∞ d.L.M; infer_instance); letI : SigmaCompactSpace d.L.M := d.L.sigmaCompact; letI : T2Space d.L.M := d.L.t2; d.L.S.family.metric) d.conv⟩⟩








structure FlowUpgradeData
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I))) where

  φ : Nat -> Nat

  hφ : StrictMono φ

  data : FlowLimitData (I := I) X (mc.compSubseq φ hφ)

namespace FlowUpgradeData


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem toConclusion
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I))}
    (d : FlowUpgradeData (I := I) X mc) :
    CompactnessConclusion (I := I) X :=
  flowLimit_upgrade (I := I) X (mc.compSubseq d.φ d.hφ) d.data

end FlowUpgradeData

end HCGCompactness
end DifferentialGeometry
