import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBTransition

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







theorem existsLiveJointH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r rho : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M)
    (U : Set E) (hU : IsOpen U)
    (hovlJ : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (beta k)
        (seqCenterD hd P L k (gamma.1 : Nat)) U)
    (hUmetric : ∀ᶠ k in Filter.atTop,
      U ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (beta k)))
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
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U
        ((fun v : E => (expMap (I := I) (X.obj (L.φ k)).metric
            (seqCenterD hd P L k (gamma.1 : Nat))
            (show TangentSpace I (seqCenterD hd P L k (gamma.1 : Nat)) from v) :
              (X.obj (L.φ k)).M)) '' Metric.ball (0 : E) rho))
    (hVmetric : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k)
          (seqCenterD hd P L k (gamma.1 : Nat))))
    (hVexp : ∀ gamma : LiveSlot L pb r, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric
          (seqCenterD hd P L k (gamma.1 : Nat)))) :
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
          some (seqCenterD hd P L (psi k) (gamma.1 : Nat))) := by
  classical
  obtain ⟨psi1, gInf, hpsi1, hginf, hg⟩ :=
    existsLiveMetric0 (I := I) metricInput P L pb r
  have htail : ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
      NormalOverlapOn (I := I) (X.obj (L.φ (psi1 k))) (beta (psi1 k))
          (seqCenterD hd P L (psi1 k) (gamma.1 : Nat)) U ∧
        U ⊆ Metric.ball (0 : E)
          (metricInput.radius (L.φ (psi1 k)) (beta (psi1 k))) ∧
        (letI : TopologicalSpace (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).topology
         letI : ChartedSpace H (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).charted
         letI : IsManifold I ∞ (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).smooth
         letI : T2Space (TangentBundle I (X.obj (L.φ (psi1 k))).M) :=
            (X.obj (L.φ (psi1 k))).t2TangentBundle
         U ⊆ Metric.ball (0 : E) (expMapC2Radius (I := I)
            (X.obj (L.φ (psi1 k))).metric (beta (psi1 k)))) ∧
        (letI : TopologicalSpace (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).topology
         letI : ChartedSpace H (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).charted
         letI : IsManifold I ∞ (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).smooth
         letI : T2Space (TangentBundle I (X.obj (L.φ (psi1 k))).M) :=
            (X.obj (L.φ (psi1 k))).t2TangentBundle
         Set.MapsTo
            (fun z => expMapDiffeo (I := I) (X.obj (L.φ (psi1 k))).metric
              (beta (psi1 k)) z) U
            ((fun v : E => (expMap (I := I) (X.obj (L.φ (psi1 k))).metric
                (seqCenterD hd P L (psi1 k) (gamma.1 : Nat))
                (show TangentSpace I
                  (seqCenterD hd P L (psi1 k) (gamma.1 : Nat)) from v) :
                    (X.obj (L.φ (psi1 k))).M)) '' Metric.ball (0 : E) rho)) ∧
        Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
          (metricInput.radius (L.φ (psi1 k))
            (seqCenterD hd P L (psi1 k) (gamma.1 : Nat))) ∧
        (letI : TopologicalSpace (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).topology
         letI : ChartedSpace H (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).charted
         letI : IsManifold I ∞ (X.obj (L.φ (psi1 k))).M :=
            (X.obj (L.φ (psi1 k))).smooth
         letI : T2Space (TangentBundle I (X.obj (L.φ (psi1 k))).M) :=
            (X.obj (L.φ (psi1 k))).t2TangentBundle
         Metric.ball (0 : E) rho ⊆ Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj (L.φ (psi1 k))).metric
            (seqCenterD hd P L (psi1 k) (gamma.1 : Nat)))) ∧
        seqCenter hd D P (L.φ (psi1 k)) (gamma.1 : Nat) =
          some (seqCenterD hd P L (psi1 k) (gamma.1 : Nat)) := by
    filter_upwards
      [Filter.eventually_all.mpr (fun gamma =>
          hpsi1.tendsto_atTop.eventually (hovlJ gamma)),
        hpsi1.tendsto_atTop.eventually hUmetric,
        hpsi1.tendsto_atTop.eventually hUexp,
        Filter.eventually_all.mpr (fun gamma =>
          hpsi1.tendsto_atTop.eventually (hmapsJ gamma)),
        Filter.eventually_all.mpr (fun gamma =>
          hpsi1.tendsto_atTop.eventually (hVmetric gamma)),
        Filter.eventually_all.mpr (fun gamma =>
          hpsi1.tendsto_atTop.eventually (hVexp gamma)),
        Filter.eventually_all.mpr (fun gamma : LiveSlot L pb r =>
          hpsi1.tendsto_atTop.eventually
            (seqCenterD_live hd P L (gamma.1 : Nat) gamma.2))]
      with k hkOvl hkUmetric hkUexp hkMaps hkVmetric hkVexp hkLive
    exact fun gamma => ⟨hkOvl gamma, hkUmetric, hkUexp, hkMaps gamma,
      hkVmetric gamma, hkVexp gamma, hkLive gamma⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  let tau : Nat → Nat := fun k => k + N
  have htau : StrictMono tau := by
    simpa only [tau] using strictMono_id.add_const N
  have hgeom (k : Nat) (gamma : LiveSlot L pb r) :=
    hN (tau k) (by simpa only [tau] using Nat.le_add_left N k) gamma
  have hOvl k gamma := (hgeom k gamma).1
  have hUMetric k gamma := (hgeom k gamma).2.1
  have hUExp k gamma := (hgeom k gamma).2.2.1
  have hMaps k gamma := (hgeom k gamma).2.2.2.1
  have hVMetric k gamma := (hgeom k gamma).2.2.2.2.1
  have hVExp k gamma := (hgeom k gamma).2.2.2.2.2.1
  have hLive k gamma := (hgeom k gamma).2.2.2.2.2.2
  let J : Nat → E → (LiveSlot L pb r → E) := fun k z gamma =>
    normalTransition (I := I) (X.obj (L.φ (psi1 (tau k))))
      (beta (psi1 (tau k)))
      (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)) z
  have hsmooth : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (J k) U := by
    intro k
    refine contDiffOn_pi.mpr fun gamma => ?_
    exact contDiffOn_normalTransition (I := I) (X.obj (L.φ (psi1 (tau k))))
      (beta (psi1 (tau k)))
      (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat))
      (hUExp k gamma)
      ((hMaps k gamma).mono_right (Set.image_mono (hVExp k gamma)))
  have hcoord (k : Nat) (gamma : LiveSlot L pb r) : Set.MapsTo
      (normalTransition (I := I) (X.obj (L.φ (psi1 (tau k))))
        (beta (psi1 (tau k)))
        (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)))
      U (Metric.ball (0 : E) rho) := by
    letI : TopologicalSpace (X.obj (L.φ (psi1 (tau k)))).M :=
      (X.obj (L.φ (psi1 (tau k)))).topology
    letI : ChartedSpace H (X.obj (L.φ (psi1 (tau k)))).M :=
      (X.obj (L.φ (psi1 (tau k)))).charted
    letI : IsManifold I ∞ (X.obj (L.φ (psi1 (tau k)))).M :=
      (X.obj (L.φ (psi1 (tau k)))).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ (psi1 (tau k)))).M) :=
      (X.obj (L.φ (psi1 (tau k)))).t2TangentBundle
    intro z hz
    obtain ⟨v, hv, hvEq⟩ := hMaps k gamma hz
    have hvEq' :
        (expMap (I := I) (X.obj (L.φ (psi1 (tau k)))).metric
          (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat))
          (show TangentSpace I
            (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)) from v) :
            (X.obj (L.φ (psi1 (tau k)))).M) =
          expMapDiffeo (I := I) (X.obj (L.φ (psi1 (tau k)))).metric
            (beta (psi1 (tau k))) z := by
      simpa only using hvEq
    have hvTarget : v ∈ (normalChartAt (I := I)
        (X.obj (L.φ (psi1 (tau k)))).metric
        (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat))).target :=
      ball_subset_normalChartAt_target (I := I)
        (X.obj (L.φ (psi1 (tau k)))).metric
        (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat))
        (mem_ball_zero_iff.mp (hVExp k gamma hv))
    change normalChartAt (I := I) (X.obj (L.φ (psi1 (tau k)))).metric
        (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat))
        (expMapDiffeo (I := I) (X.obj (L.φ (psi1 (tau k)))).metric
          (beta (psi1 (tau k))) z) ∈ Metric.ball (0 : E) rho
    rw [← hvEq',
      ← normalChartAt_symm_apply (I := I)
        (X.obj (L.φ (psi1 (tau k)))).metric
        (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)) hvTarget,
      normalChartAt_right_inv (I := I)
        (X.obj (L.φ (psi1 (tau k)))).metric
        (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)) hvTarget]
    exact hv
  have hbddComp (gamma : LiveSlot L pb r) : IsometryDerivBoundsOn U
      (fun k z => normalTransition (I := I) (X.obj (L.φ (psi1 (tau k))))
        (beta (psi1 (tau k)))
        (seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat)) z) := by
    let f : Nat → Nat := fun k => L.φ (psi1 (tau k))
    have hbound := H6Isometry.normal_bounds_on (I := I)
      (X.subseq f) (NormalCoordMetricBoundInput.subseq (I := I) metricInput f)
      (fun k => beta (psi1 (tau k)))
      (fun k => seqCenterD hd P L (psi1 (tau k)) (gamma.1 : Nat))
      U (Metric.ball (0 : E) rho) hU Metric.isOpen_ball
      ⟨max rho 0, fun z hz =>
        (le_of_lt (mem_ball_zero_iff.mp hz)).trans (le_max_left _ _)⟩
      (fun k => by
        simpa only [NormalCoordMetricBoundInput.subseq, f] using hUMetric k gamma)
      (fun k => by
        simpa only [NormalCoordMetricBoundInput.subseq, f] using hVMetric k gamma)
      (fun k => by
        simpa only [PointedRiemannianSeq.subseq, f] using hUExp k gamma)
      (fun k => by
        simpa only [PointedRiemannianSeq.subseq, f] using hVExp k gamma)
      (fun k => by
        simpa only [PointedRiemannianSeq.subseq, f] using
          (contDiffOn_pi.mp (hsmooth k) gamma))
      (fun k => by
        simpa only [PointedRiemannianSeq.subseq, f] using hOvl k gamma)
      (fun k => by
        simpa only [PointedRiemannianSeq.subseq, f] using hcoord k gamma)
    simpa only [PointedRiemannianSeq.subseq, f] using hbound
  have hbdd : IsometryDerivBoundsOn U J := by
    apply IsometryDerivBoundsOn.pi hU
    · intro k gamma
      exact contDiffOn_pi.mp (hsmooth k) gamma
    · intro gamma
      simpa only [J] using hbddComp gamma
  obtain ⟨psi2, Jhat, hpsi2, hJhat, hJconv⟩ :=
    isometry_seq_cInf_on hU J hsmooth hbdd
  refine ⟨psi1 ∘ tau ∘ psi2, gInf, fun gamma z => Jhat z gamma,
    hpsi1.comp (htau.comp hpsi2), hginf, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hg.comp_subseq (htau.comp hpsi2)
  · intro gamma
    refine ⟨contDiffOn_pi.mp hJhat gamma, ?_, ?_, ?_, ?_⟩
    · have hcomponent := mapCInf_apply hU hJconv
        (fun k => hsmooth (psi2 k)) hJhat gamma
      simpa only [J, Function.comp_apply] using hcomponent
    · intro k
      simpa only [Function.comp_apply] using
        (contDiffOn_pi.mp (hsmooth (psi2 k)) gamma)
    · intro k
      simpa only [Function.comp_apply] using hOvl (psi2 k) gamma
    · intro k
      simpa only [Function.comp_apply] using hLive (psi2 k) gamma

end HCGCompactness
end DifferentialGeometry
