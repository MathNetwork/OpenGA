import DifferentialGeometry.Analysis.Calculus.MovingInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalDiagBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalLimitPhase

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



def HasDiagPairConv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (c : ∀ n : Nat, (X.obj n).M)
    (qStage qInf : NNReal) (deltaStage deltaInf : Real)
    (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
    (eInf : OpenPartialHomeomorph (E × E) (E × E)) : Prop :=
  0 < qStage ∧ 0 < qInf ∧ qInf < qStage ∧
  0 < deltaStage ∧ 0 < deltaInf ∧
  (∀ n, IsNormalDiag (I := I) (X.obj n)
    (hcomplete.complete n) (hconn n) (c n) qStage deltaStage (e n)) ∧
  eInf.source = Metric.ball (0 : E × E) qInf ∧
  eInf 0 = 0 ∧
  Metric.closedBall (0 : E × E) deltaInf ⊆ eInf.target ∧
  ContDiffOn Real ∞ (eInf : E × E → E × E) eInf.source ∧
  ContDiffOn Real ∞ eInf.symm eInf.target ∧
  (∀ z ∈ Metric.ball (0 : E) qInf,
    (z, z) ∈ eInf.target ∧ eInf.symm (z, z) = (z, 0)) ∧
  (∃ η : NNReal, η < 1 ∧
    ApproximatesLinearOn
      (eInf.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))
      eInf.target η) ∧
  MapCInfConvOnCompacts (Metric.ball (0 : E × E) qInf)
    (fun n ↦ (e n : E × E → E × E)) eInf ∧
  ∃ delta₀ : Real,
    0 < delta₀ ∧ delta₀ < min deltaStage deltaInf ∧
    eInf.symm '' Metric.closedBall 0 delta₀ ⊆ Metric.ball 0 qInf ∧
    Filter.Eventually
      (fun n : Nat ↦ Set.MapsTo (e n).symm
        (Metric.closedBall 0 delta₀) (Metric.ball 0 qInf))
      Filter.atTop ∧
    MapCInfConvOnCompacts (Metric.ball 0 delta₀)
      (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm



theorem HasDiagPairConv.subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    {c : ∀ n : Nat, (X.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaInf : Real}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (h : HasDiagPairConv (I := I) hcomplete hconn c
      qStage qInf deltaStage deltaInf e eInf)
    (f : Nat → Nat) (hf : Tendsto f Filter.atTop Filter.atTop) :
    HasDiagPairConv (I := I) (hcomplete.subseq f)
      (PointedRiemannianSeq.connected_subseq hconn f)
      (fun n => c (f n)) qStage qInf deltaStage deltaInf
      (fun n => e (f n)) eInf := by
  rcases h with
    ⟨hqStage, hqInf, hqInfStage, hdeltaStage, hdeltaInf,
      hnormal, hInfSource, hInfZero, hInfTarget, hInfC,
      hInfSymmC, hInfDiag, hInfApprox, hforward, delta0, hdelta0, hdelta0lt,
      himage, hstageMap, hinv⟩
  refine ⟨hqStage, hqInf, hqInfStage, hdeltaStage, hdeltaInf,
    ?_, hInfSource, hInfZero, hInfTarget, hInfC, hInfSymmC,
    hInfDiag, hInfApprox,
    hforward.comp_tendsto_atTop hf, delta0, hdelta0, hdelta0lt,
    himage, hf.eventually hstageMap, hinv.comp_tendsto_atTop hf⟩
  intro n
  simpa only [PointedRiemannianSeq.subseq] using hnormal (f n)



theorem HasDiagPairConv.congr_stage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    {c : ∀ n : Nat, (X.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaStage' deltaInf : Real}
    {e e' : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (h : HasDiagPairConv (I := I) hcomplete hconn c
      qStage qInf deltaStage deltaInf e eInf)
    (hfence : ∀ n, NormalDiagFence (I := I) (X.obj n) (c n)
      qStage (e n))
    (hdeltaStage' : 0 < deltaStage')
    (hnormal' : ∀ n, IsNormalDiag (I := I) (X.obj n)
      (hcomplete.complete n) (hconn n) (c n) qStage deltaStage' (e' n))
    (hfence' : ∀ n, NormalDiagFence (I := I) (X.obj n) (c n)
      qStage (e' n)) :
    HasDiagPairConv (I := I) hcomplete hconn c
      qStage qInf deltaStage' deltaInf e' eInf := by
  rcases h with
    ⟨hqStage, hqInf, hqInfStage, hdeltaStage, hdeltaInf,
      hnormal, hInfSource, hInfZero, hInfTarget, hInfC,
      hInfSymmC, hInfDiag, hInfApprox, hforward, delta0, hdelta0, hdelta0lt,
      himage, hstageMap, hinv⟩
  have heq : ∀ n, e n ≈ e' n := fun n ↦
    IsNormalDiag.eqOnSource (I := I) (X.obj n)
      (hcomplete.complete n) (hconn n) (c n)
      (hnormal n) (hfence n) (hnormal' n) (hfence' n)
  have hqInfStageReal : (qInf : Real) < qStage := by
    exact_mod_cast hqInfStage
  have hforward' : MapCInfConvOnCompacts
      (Metric.ball (0 : E × E) qInf)
      (fun n ↦ (e' n : E × E → E × E)) eInf := by
    apply hforward.congr Metric.isOpen_ball
    · intro n z hz
      have hzStage : z ∈ Metric.ball (0 : E × E) qStage :=
        Metric.ball_subset_ball hqInfStageReal.le hz
      have hzSource : z ∈ (e n).source := by
        rw [(hnormal n).1]
        exact hzStage
      exact ((heq n).eqOn hzSource).symm
    · intro z hz
      rfl
  let delta1 : Real := min delta0 deltaStage' / 2
  have hminPos : 0 < min delta0 deltaStage' :=
    lt_min hdelta0 hdeltaStage'
  have hdelta1 : 0 < delta1 := by
    dsimp only [delta1]
    positivity
  have hdelta1lt0 : delta1 < delta0 := by
    dsimp only [delta1]
    exact (half_lt_self hminPos).trans_le (min_le_left _ _)
  have hdelta1ltStage' : delta1 < deltaStage' := by
    dsimp only [delta1]
    exact (half_lt_self hminPos).trans_le (min_le_right _ _)
  have hdelta0ltStage : delta0 < deltaStage :=
    hdelta0lt.trans_le (min_le_left _ _)
  have hdelta0ltInf : delta0 < deltaInf :=
    hdelta0lt.trans_le (min_le_right _ _)
  have hdelta1ltStage : delta1 < deltaStage :=
    hdelta1lt0.trans hdelta0ltStage
  have hdelta1ltInf : delta1 < deltaInf :=
    hdelta1lt0.trans hdelta0ltInf
  have himage' : eInf.symm '' Metric.closedBall 0 delta1 ⊆
      Metric.ball 0 qInf := by
    intro z hz
    exact himage (Set.image_mono
      (Metric.closedBall_subset_closedBall hdelta1lt0.le) hz)
  have hstageMap' : Filter.Eventually
      (fun n : Nat ↦ Set.MapsTo (e' n).symm
        (Metric.closedBall 0 delta1) (Metric.ball 0 qInf))
      Filter.atTop := by
    filter_upwards [hstageMap] with n hn
    intro w hw
    have hw0 : w ∈ Metric.closedBall (0 : E × E) delta0 :=
      Metric.closedBall_subset_closedBall hdelta1lt0.le hw
    have hwStage : w ∈ Metric.closedBall (0 : E × E) deltaStage :=
      Metric.closedBall_subset_closedBall hdelta1ltStage.le hw
    have hwTarget : w ∈ (e n).target :=
      (hnormal n).2.2.2.1 hwStage
    rw [← (heq n).symm_eqOn_target hwTarget]
    exact hn hw0
  have hinvSmall : MapCInfConvOnCompacts (Metric.ball 0 delta1)
      (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm := by
    intro K hK hKU p
    exact hinv K hK
      (hKU.trans (Metric.ball_subset_ball hdelta1lt0.le)) p
  have hinv' : MapCInfConvOnCompacts (Metric.ball 0 delta1)
      (fun n ↦ ((e' n).symm : E × E → E × E)) eInf.symm := by
    apply hinvSmall.congr Metric.isOpen_ball
    · intro n w hw
      have hwStage : w ∈ Metric.closedBall (0 : E × E) deltaStage :=
        Metric.closedBall_subset_closedBall hdelta1ltStage.le
          (Metric.ball_subset_closedBall hw)
      have hwTarget : w ∈ (e n).target :=
        (hnormal n).2.2.2.1 hwStage
      exact ((heq n).symm_eqOn_target hwTarget).symm
    · intro w hw
      rfl
  exact ⟨hqStage, hqInf, hqInfStage, hdeltaStage', hdeltaInf,
    hnormal', hInfSource, hInfZero, hInfTarget, hInfC, hInfSymmC,
    hInfDiag, hInfApprox, hforward', delta1, hdelta1,
    lt_min hdelta1ltStage' hdelta1ltInf, himage', hstageMap', hinv'⟩



theorem HasDiagPairConv.inv_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    {c : ∀ n : Nat, (X.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaInf : Real}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (h : HasDiagPairConv (I := I) hcomplete hconn c
      qStage qInf deltaStage deltaInf e eInf) :
    ∃ delta0 : Real, 0 < delta0 ∧
      (∀ n, ContDiffOn Real ∞
        ((e n).symm : E × E → E × E) (Metric.ball 0 delta0)) ∧
      ContDiffOn Real ∞ (eInf.symm : E × E → E × E)
        (Metric.ball 0 delta0) ∧
      MapCInfConvOnCompacts (Metric.ball 0 delta0)
        (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm := by
  rcases h with
    ⟨_hqStage, _hqInf, _hqInfStage, _hdeltaStage, _hdeltaInf,
      hnormal, _hInfSource, _hInfZero, hInfTarget, _hInfC,
      hInfSymmC, _hInfDiag, _hInfApprox, _hforward,
      delta0, hdelta0, hdelta0lt,
      _himage, _hstageMap, hinv⟩
  have hdeltaStage : delta0 ≤ deltaStage :=
    le_of_lt (hdelta0lt.trans_le (min_le_left _ _))
  have hdeltaInf : delta0 ≤ deltaInf :=
    le_of_lt (hdelta0lt.trans_le (min_le_right _ _))
  have hstageTarget : ∀ n,
      Metric.ball (0 : E × E) delta0 ⊆ (e n).target := by
    intro n z hz
    exact (hnormal n).2.2.2.1
      (Metric.closedBall_subset_closedBall hdeltaStage
        (Metric.ball_subset_closedBall hz))
  have hInfTarget0 :
      Metric.ball (0 : E × E) delta0 ⊆ eInf.target := by
    intro z hz
    exact hInfTarget
      (Metric.closedBall_subset_closedBall hdeltaInf
        (Metric.ball_subset_closedBall hz))
  exact ⟨delta0, hdelta0,
    fun n ↦ (hnormal n).2.2.2.2.1.mono (hstageTarget n),
    hInfSymmC.mono hInfTarget0, hinv⟩



theorem HasDiagPairConv.exists_diag_inv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    {c : ∀ n : Nat, (X.obj n).M}
    {qStage qInf : NNReal} {deltaStage deltaInf : Real}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (h : HasDiagPairConv (I := I) hcomplete hconn c
      qStage qInf deltaStage deltaInf e eInf)
    {K : Set E} (hK : IsCompact K)
    (hKq : K ⊆ Metric.ball (0 : E) qInf) :
    ∃ V : Set (E × E),
      IsOpen V ∧ IsCompact (closure V) ∧
      (fun z : E ↦ (z, z)) '' K ⊆ V ∧
      closure V ⊆ eInf.target ∧
      eInf.symm '' closure V ⊆ Metric.ball (0 : E × E) qInf ∧
      Filter.Eventually
        (fun n : Nat ↦ closure V ⊆ (e n).target ∧
          Set.MapsTo (e n).symm (closure V)
            (Metric.ball (0 : E × E) qInf)) Filter.atTop ∧
      MapCInfConvOnCompacts V
        (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm := by
  rcases h with
    ⟨_hqStage, hqInf, hqInfStage, _hdeltaStage, _hdeltaInf,
      hnormal, hInfSource, _hInfZero, _hInfTarget, hInfC,
      hInfSymmC, hInfDiag, _hInfApprox, hforward,
      _delta0, _hdelta0, _hdelta0lt, _himage, _hstageMap, _hinv⟩
  let Q : Set (E × E) := Metric.ball 0 qInf
  let diag : E → E × E := fun z ↦ (z, z)
  let Kdiag : Set (E × E) := diag '' K
  have hKdiag : IsCompact Kdiag := by
    exact hK.image_of_continuousOn
      (continuous_id.prodMk continuous_id).continuousOn
  have hqInfReal : (0 : Real) < qInf := by exact_mod_cast hqInf
  have hqInfStageReal : (qInf : Real) < qStage := by
    exact_mod_cast hqInfStage
  have hclosureQ : closure Q ⊆ Metric.ball (0 : E × E) qStage := by
    change closure (Metric.ball (0 : E × E) qInf) ⊆
      Metric.ball 0 qStage
    rw [closure_ball 0 hqInfReal.ne']
    intro z hz
    rw [Metric.mem_closedBall, Metric.mem_ball] at *
    linarith
  have hsource : Filter.Eventually
      (fun n : Nat ↦ closure Q ⊆ (e n).source) Filter.atTop :=
    Filter.Eventually.of_forall fun n ↦ by
      rw [(hnormal n).1]
      exact hclosureQ
  have hstage_cd : ∀ n,
      ContDiffOn Real ∞ (e n : E × E → E × E) Q := by
    intro n
    exact (hnormal n).2.2.1.mono fun z hz ↦ by
      rw [(hnormal n).1]
      exact hclosureQ (subset_closure hz)
  have hInf_cd : ContDiffOn Real ∞
      (eInf : E × E → E × E) Q := by
    apply hInfC.mono
    rw [hInfSource]
  have hKt : Kdiag ⊆ eInf.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hInfDiag z (hKq hz)).1
  have hKQ : eInf.symm '' Kdiag ⊆ Q := by
    rintro _ ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    rw [(hInfDiag z (hKq hz)).2]
    change (z, 0) ∈ Metric.ball (0 : E × E) qInf
    rw [Metric.mem_ball, Prod.dist_eq]
    change max (dist z (0 : E)) (dist (0 : E) 0) < (qInf : Real)
    simpa only [dist_self, max_eq_left dist_nonneg] using hKq hz
  simpa only [Q, diag, Kdiag] using
    Analysis.OpenPartialHomeomorph.exists_symm_cInf
      Metric.isOpen_ball hKdiag hforward hsource hstage_cd hInf_cd
      hInfSymmC hKt hKQ

namespace NormalRadiusProfile




theorem exists_diagInv_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    (qStage qInf : NNReal) (hqInf : 0 < qInf)
    (hqInf_lt : qInf < qStage) (delta deltaInf : Real)
    (hdelta : 0 < delta) (hdeltaInf : 0 < deltaInf)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf)
    {Φ : Nat → (E × E) → Real → E × E}
    {ΦInf : (E × E) → Real → E × E}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (hΦ : ∀ n z, z ∈ Metric.closedBall (0 : E × E) qStage →
      Φ n z 0 = z ∧
      IsIntegralCurveOn (Φ n z)
        (fun _ ↦ MetricKoszul.metricSpray
          (normalCoordMetric (I := I) (X.obj n) (c n))) (Icc 0 1))
    (hΦInf : ∀ z, z ∈ Metric.closedBall (0 : E × E) qInf →
      ΦInf z 0 = z ∧
      IsIntegralCurveOn (ΦInf z)
        (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1))
    (hstay : ∀ n z, z ∈ Metric.closedBall (0 : E × E) qStage →
      ∀ t ∈ Icc (0 : Real) 1,
        (Φ n z t).1 ∈ Metric.ball 0 (h.phaseRadius R))
    (hstayInf : ∀ z, z ∈ Metric.closedBall (0 : E × E) qInf →
      ∀ t ∈ Icc (0 : Real) 1,
        (ΦInf z t).1 ∈ Metric.ball 0 (h.phaseRadius R))
    (he : ∀ n, (e n : E × E → E × E) =
      fun z ↦ (z.1, (Φ n z 1).1))
    (heInf : (eInf : E × E → E × E) =
      fun z ↦ (z.1, (ΦInf z 1).1))
    (hdiag : ∀ n, IsNormalDiag (I := I) (X.obj n)
      (hcomplete.complete n) (hconn n) (c n) qStage delta (e n))
    (hInf_source : eInf.source = Metric.ball (0 : E × E) qInf)
    (hInf_zero : eInf 0 = 0)
    (hInf_cd : ContDiffOn Real ∞ (eInf : E × E → E × E)
      eInf.source)
    (hInf_target : Metric.closedBall (0 : E × E) deltaInf ⊆
      eInf.target)
    (hInf_symm_cd : ContDiffOn Real ∞ eInf.symm eInf.target) :
    MapCInfConvOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun n ↦ (e n : E × E → E × E)) eInf ∧
      ∃ delta₀ : Real,
        0 < delta₀ ∧ delta₀ < min delta deltaInf ∧
        eInf.symm '' Metric.closedBall 0 delta₀ ⊆
          Metric.ball 0 qInf ∧
        Filter.Eventually
          (fun n : Nat ↦ Set.MapsTo (e n).symm
            (Metric.closedBall 0 delta₀)
            (Metric.ball 0 qInf)) Filter.atTop ∧
        MapCInfConvOnCompacts (Metric.ball 0 delta₀)
          (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm := by
  let Q : Set (E × E) := Metric.ball 0 qInf
  have hqInfReal : (0 : Real) < qInf := by exact_mod_cast hqInf
  have hqInfStage : (qInf : Real) < qStage := by exact_mod_cast hqInf_lt
  have hQStage : Q ⊆ Metric.closedBall (0 : E × E) qStage := by
    intro z hz
    change dist z 0 < (qInf : Real) at hz
    change dist z 0 ≤ (qStage : Real)
    linarith
  have hQInf : Q ⊆ Metric.closedBall (0 : E × E) qInf := by
    intro z hz
    exact Metric.ball_subset_closedBall hz
  have hforwardFormula := h.diag_end_conv R c hc Metric.isOpen_ball
    hgInf_cd hgInf_lo hg_conv
    (fun n z hz ↦ hΦ n z (hQStage hz))
    (fun z hz ↦ hΦInf z (hQInf hz))
    (fun n z hz ↦ hstay n z (hQStage hz))
    (fun z hz ↦ hstayInf z (hQInf hz)) he
  have hforward : MapCInfConvOnCompacts Q
      (fun n ↦ (e n : E × E → E × E)) eInf :=
    hforwardFormula.congr Metric.isOpen_ball
      (fun _n _z _hz ↦ rfl)
      (fun z _hz ↦ congrFun heInf z)
  have hclosureQ : closure Q ⊆ Metric.ball (0 : E × E) qStage := by
    change closure (Metric.ball (0 : E × E) qInf) ⊆
      Metric.ball 0 qStage
    rw [closure_ball 0 hqInfReal.ne']
    intro z hz
    rw [Metric.mem_closedBall, Metric.mem_ball] at *
    linarith
  have hsource : ∀ᶠ n in Filter.atTop, closure Q ⊆ (e n).source :=
    Filter.Eventually.of_forall fun n ↦ by
      rw [(hdiag n).1]
      exact hclosureQ
  have hstage_cd : ∀ n,
      ContDiffOn Real ∞ (e n : E × E → E × E) Q := by
    intro n
    exact (hdiag n).2.2.1.mono fun z hz ↦ by
      rw [(hdiag n).1]
      exact hclosureQ (subset_closure hz)
  have htarget : ∀ n,
      Metric.closedBall (0 : E × E) (min delta deltaInf) ⊆
        (e n).target := by
    intro n
    exact (Metric.closedBall_subset_closedBall (min_le_left delta deltaInf)).trans
      (hdiag n).2.2.2.1
  have htargetInf : Metric.closedBall (0 : E × E)
      (min delta deltaInf) ⊆ eInf.target :=
    (Metric.closedBall_subset_closedBall (min_le_right delta deltaInf)).trans hInf_target
  have hInf_cd' : ContDiffOn Real ∞
      (eInf : E × E → E × E) (interior eInf.source) :=
    hInf_cd.mono interior_subset
  have hInf_symm_cd' : ContDiffOn Real ∞ eInf.symm
      (Metric.ball (0 : E × E) (min delta deltaInf)) :=
    hInf_symm_cd.mono <|
      Metric.ball_subset_closedBall.trans <|
        (Metric.closedBall_subset_closedBall
          (min_le_right delta deltaInf)).trans hInf_target
  have hzero_source : (0 : E × E) ∈ eInf.source := by
    rw [hInf_source]
    simpa only [Metric.mem_ball, dist_self] using hqInfReal
  have hbase_eq : eInf.symm 0 = 0 := by
    have hleft := eInf.left_inv hzero_source
    simpa only [hInf_zero] using hleft
  have hbase : eInf.symm 0 ∈ Q := by
    change dist (eInf.symm 0) 0 < (qInf : Real)
    rw [hbase_eq]
    simpa only [dist_self] using hqInfReal
  refine ⟨hforward, ?_⟩
  exact Analysis.OpenPartialHomeomorph.exists_symm_convOn_ball Metric.isOpen_ball
    hforward hsource hstage_cd (lt_min hdelta hdeltaInf) htarget
    htargetInf hInf_cd' hInf_symm_cd' hbase




theorem exists_diagPair_at
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    (q : NNReal) (hq : 0 < q)
    (hqWide : 6 * (q : Real) < h.phaseRadius R)
    (hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    (herr : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹)
    (hinvErr :
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < 1 / 24)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf) :
    ∃ (deltaStage deltaInf : Real)
        (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : OpenPartialHomeomorph (E × E) (E × E)),
      HasDiagPairConv hcomplete hconn c q (q / 2)
        deltaStage deltaInf e eInf ∧
      ∀ n, NormalDiagFence (I := I) (X.obj n) (c n) q (e n) := by
  classical
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  obtain ⟨deltaStage, hdeltaStage, _hdeltaStageEq, hflow⟩ :=
    h.exists_flow_at hcomplete hconn R q hq hqWide hqAcc herr
  choose Φ e hΦ0 hΦcurve hΦstay he hdiag hfence using
    fun n ↦ hflow n (c n) (hc n)
  let qInf : NNReal := q / 2
  have hqInf : 0 < qInf := by
    dsimp only [qInf]
    positivity
  have hqInfStage : qInf < q := by
    dsimp only [qInf]
    exact div_lt_self hq (by norm_num)
  have hqInfRadius : 4 * (qInf : Real) < h.phaseRadius R := by
    have hqReal : (0 : Real) < q := by exact_mod_cast hq
    dsimp only [qInf]
    push_cast
    nlinarith
  have hqInfAcc : 3 * hb.metricC 1 * (2 * (qInf : Real)) ^ 2 ≤
      (qInf : Real) := by
    have hqReal : (0 : Real) ≤ q := by exact_mod_cast hq.le
    have hC : 0 ≤ hb.metricC 1 := hb.metricC_nonneg 1
    dsimp only [qInf]
    push_cast
    nlinarith [hqAcc]
  have hqInfTwo : 2 * qInf ≤ 2 * q := by
    exact mul_le_mul_of_nonneg_left hqInfStage.le (by norm_num)
  have hphaseK : normalPhaseK hb (2 * qInf) ≤ normalPhaseK hb (2 * q) :=
    normalPhaseK_mono hb hqInfTwo
  have herrLe : PhaseFlow.phaseErr (normalPhaseK hb (2 * qInf)) ≤
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) :=
    PhaseFlow.phaseErr_mono hphaseK
  have hqInfErr : PhaseFlow.phaseErr (normalPhaseK hb (2 * qInf)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ :=
    herrLe.trans_lt herr
  obtain ⟨ΦInf, eInf, deltaInf, hdeltaInf, hΦInf0, hΦInfCurve,
      hΦInfStay, hInfSource, hInfZero, heInf, hInfTarget,
      hInfSmooth, hInfSymmSmooth, hInfDiag, hInfApprox⟩ :=
    h.exists_limit_diag R c hc hgInf_cd hgInf_lo hg_conv qInf hqInf
      hqInfRadius hqInfAcc hqInfErr
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let cInf : NNReal := PhaseFlow.phaseErr (normalPhaseK hb (2 * qInf))
  let cStage : NNReal := PhaseFlow.phaseErr (normalPhaseK hb (2 * q))
  let η : NNReal := N * (N⁻¹ - cInf)⁻¹ * cInf
  have hInvMono : N * (N⁻¹ - cInf)⁻¹ * cInf ≤
      N * (N⁻¹ - cStage)⁻¹ * cStage := by
    exact PhaseFlow.invErr_mono (N := N)
      (by simpa only [cInf, cStage] using herrLe)
      (by simpa only [N, cStage] using herr)
  have hη : η < 1 := by
    calc
      η ≤ N * (N⁻¹ - cStage)⁻¹ * cStage := hInvMono
      _ < 1 / 24 := by simpa only [N, cStage] using hinvErr
      _ < 1 := by norm_num
  have hInfApproxη : ApproximatesLinearOn
      (eInf.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) eInf.target η := by
    simpa only [η, N, cInf] using hInfApprox
  obtain ⟨hforward, delta₀, hdelta₀, hdelta₀lt, hInfMaps,
      hstageMaps, hinverse⟩ :=
    h.exists_diagInv_conv hcomplete hconn R c hc q qInf hqInf
      hqInfStage deltaStage deltaInf hdeltaStage hdeltaInf
      hgInf_cd hgInf_lo hg_conv
      (fun n z hz ↦ ⟨hΦ0 n z hz, hΦcurve n z hz⟩)
      (fun z hz ↦ ⟨hΦInf0 z hz, hΦInfCurve z hz⟩)
      hΦstay hΦInfStay he heInf hdiag hInfSource hInfZero
      hInfSmooth hInfTarget hInfSymmSmooth
  refine ⟨deltaStage, deltaInf, e, eInf, ?_, hfence⟩
  simpa only [qInf] using
    (show HasDiagPairConv hcomplete hconn c q qInf
      deltaStage deltaInf e eInf from
      ⟨hq, hqInf, hqInfStage, hdeltaStage, hdeltaInf, hdiag,
        hInfSource, hInfZero, hInfTarget, hInfSmooth, hInfSymmSmooth,
        hInfDiag, ⟨η, hη, hInfApproxη⟩, hforward,
        delta₀, hdelta₀, hdelta₀lt, hInfMaps, hstageMaps, hinverse⟩)




theorem exists_diagPair_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf) :
    ∃ (qStage qInf : NNReal) (deltaStage deltaInf : Real)
        (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : OpenPartialHomeomorph (E × E) (E × E)),
      HasDiagPairConv hcomplete hconn c qStage qInf deltaStage deltaInf e eInf := by
  classical
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  obtain ⟨qStage, deltaStage, hqStage, _hqStageRadius, hdeltaStage,
      _hdeltaStageEq, hflow⟩ := h.exists_uniform_flow hcomplete hconn R
  choose Φ e hΦ0 hΦcurve hΦstay he hdiag using
    fun n ↦ hflow n (c n) (hc n)
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  let eps : NNReal := min T (T / (2 * (N + 1)))
  have hT : 0 < T := by
    simpa only [T, N] using PhaseFlow.freeDiagInv_pos (E := E)
  have hden : 0 < 2 * (N + 1) := by positivity
  have heps : 0 < eps := lt_min hT (div_pos hT hden)
  have hfourStage : (0 : Real) < 4 * (qStage : Real) := by positivity
  have hr : 0 < min (h.phaseRadius R) (4 * (qStage : Real)) :=
    lt_min (h.phaseRadius_pos R) hfourStage
  obtain ⟨qInf, hqInf, hqInfSmall, hqInfAcc, hqInfErr⟩ :=
    exists_normal_q_lt (I := I) hb hr heps
  have hqInfRadius : 4 * (qInf : Real) < h.phaseRadius R :=
    hqInfSmall.trans_le (min_le_left _ _)
  have hqInfStageReal : (qInf : Real) < qStage := by
    have hsmall : 4 * (qInf : Real) < 4 * (qStage : Real) :=
      hqInfSmall.trans_le (min_le_right _ _)
    linarith
  have hqInfStage : qInf < qStage := by exact_mod_cast hqInfStageReal
  have hqInfErrInv : PhaseFlow.phaseErr (normalPhaseK hb (2 * qInf)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ := by
    have hsmall : PhaseFlow.phaseErr (normalPhaseK hb (2 * qInf)) < T :=
      hqInfErr.trans_le (min_le_left _ _)
    simpa only [T, N] using hsmall
  have hqInfErrOne : PhaseFlow.phaseErr (normalPhaseK hb (2 * qInf)) <
      T / (2 * (N + 1)) :=
    hqInfErr.trans_le (min_le_right _ _)
  obtain ⟨ΦInf, eInf, deltaInf, hdeltaInf, hΦInf0, hΦInfCurve,
      hΦInfStay, hInfSource, hInfZero, heInf, hInfTarget,
      hInfSmooth, hInfSymmSmooth, hInfDiag, hInfApprox⟩ :=
    h.exists_limit_diag R c hc hgInf_cd hgInf_lo hg_conv qInf hqInf
      hqInfRadius hqInfAcc hqInfErrInv
  let η : NNReal := N * (T - PhaseFlow.phaseErr
    (normalPhaseK hb (2 * qInf)))⁻¹ *
      PhaseFlow.phaseErr (normalPhaseK hb (2 * qInf))
  have hη : η < 1 := by
    simpa only [η, T] using
      (PhaseFlow.invErr_lt_one (N := N) hqInfErrOne)
  have hInfApproxη : ApproximatesLinearOn
      (eInf.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E)) eInf.target η := by
    simpa only [η, T, N] using hInfApprox
  obtain ⟨hforward, delta₀, hdelta₀, hdelta₀lt, hInfMaps,
      hstageMaps, hinverse⟩ :=
    h.exists_diagInv_conv hcomplete hconn R c hc qStage qInf hqInf
      hqInfStage deltaStage deltaInf hdeltaStage hdeltaInf
      hgInf_cd hgInf_lo hg_conv
      (fun n z hz ↦ ⟨hΦ0 n z hz, hΦcurve n z hz⟩)
      (fun z hz ↦ ⟨hΦInf0 z hz, hΦInfCurve z hz⟩)
      hΦstay hΦInfStay he heInf hdiag hInfSource hInfZero
      hInfSmooth hInfTarget hInfSymmSmooth
  refine ⟨qStage, qInf, deltaStage, deltaInf, e, eInf, ?_⟩
  exact ⟨hqStage, hqInf, hqInfStage, hdeltaStage, hdeltaInf, hdiag,
    hInfSource, hInfZero, hInfTarget, hInfSmooth, hInfSymmSmooth,
    hInfDiag, ⟨η, hη, hInfApproxη⟩, hforward,
    delta₀, hdelta₀, hdelta₀lt, hInfMaps, hstageMaps, hinverse⟩

end NormalRadiusProfile
end HCGCompactness
end DifferentialGeometry
