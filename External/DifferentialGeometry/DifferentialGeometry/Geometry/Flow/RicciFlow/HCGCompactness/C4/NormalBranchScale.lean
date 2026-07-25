import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalDiagAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalDiagBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhaseSmallness

set_option autoImplicit false








noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem normalBrHat
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {a D c R : Real} (hD : 0 < D) (hc : c < a * D) :
    c * hd.lambda D R < a * hd.mu R := by
  rw [InjRadiusDecayInput.lambda]
  calc
    c * (hd.mu R / D) = (c / D) * hd.mu R := by ring
    _ < a * hd.mu R :=
      mul_lt_mul_of_pos_right ((div_lt_iff₀ hD).2 hc) (hd.mu_pos R)



def HasNormalBrFull
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (q : NNReal) (δ ρ : Real) : Prop := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  exact ∃ hq : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) Y hcomplete hconn x q δ e,
        NormalDiagFence (I := I) Y x q e ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) Y x w ∈
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom) ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) δ,
          normalPair (I := I) Y x w ∈
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom) ∧
        normalTanHome (I := I) Y x '' Metric.ball (0 : E × E) q =
          (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).hom.source ∧
        normalPairHome (I := I) Y x '' e.target =
          (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom ∧
        (∀ w ∈ e.target,
          (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).inv
              (normalPair (I := I) Y x w) =
            normalTangent (I := I) Y x (e.symm w)) ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) δ,
          (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).inv
              (normalPair (I := I) Y x w) =
            normalTangent (I := I) Y x (e.symm w)) ∧
        ∃ η : NNReal, η < 1 / 24 ∧
          ApproximatesLinearOn
            (e.symm : E × E → E × E)
            ((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E)) e.target η

namespace HasNormalBrFull



theorem mono
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ ρ ρ' : Real}
    (h : HasNormalBrFull (I := I) Y hcomplete hconn x q δ ρ)
    (hρ : ρ' ≤ ρ) :
    HasNormalBrFull (I := I) Y hcomplete hconn x q δ ρ' := by
  dsimp only [HasNormalBrFull] at h ⊢
  rcases h with ⟨hq, e, he, hfence, hclosed, hδdom, htransport⟩
  refine ⟨hq, e, he, hfence, ?_, hδdom, htransport⟩
  intro w hw
  exact hclosed w (Metric.closedBall_subset_closedBall hρ hw)



theorem toDom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ ρ : Real}
    (h : HasNormalBrFull (I := I) Y hcomplete hconn x q δ ρ) :
    HasNormalBranchDom (I := I) Y hcomplete hconn x q δ ρ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  change ∃ hq : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) Y hcomplete hconn x q δ e,
        NormalDiagFence (I := I) Y x q e ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) Y x w ∈
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom) ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) δ,
          normalPair (I := I) Y x w ∈
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom) ∧
        normalTanHome (I := I) Y x '' Metric.ball (0 : E × E) q =
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).hom.source ∧
        normalPairHome (I := I) Y x '' e.target =
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom ∧
        (∀ w ∈ e.target,
          (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).inv
              (normalPair (I := I) Y x w) =
            normalTangent (I := I) Y x (e.symm w)) ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) δ,
          (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).inv
              (normalPair (I := I) Y x w) =
            normalTangent (I := I) Y x (e.symm w)) ∧
        ∃ η : NNReal, η < 1 / 24 ∧
          ApproximatesLinearOn
            (e.symm : E × E → E × E)
            ((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E)) e.target η at h
  rcases h with ⟨hq, e, he, _hfence, hclosed, _hδdom, _⟩
  exact ⟨hq, e, he, hclosed⟩

end HasNormalBrFull



theorem normalBrAccept
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aq aδ aρ : Real,
      0 < aq ∧ 0 < aδ ∧ 0 < aρ ∧
      ∀ R, 0 ≤ R →
        ∃ (q : NNReal) (δ : Real),
          0 < q ∧ 0 < δ ∧
          (q : Real) = aq * hd.mu R ∧
          aδ * hd.mu R ≤ δ ∧
          6 * (q : Real) < h.phaseRadius R ∧
          3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < 1 / 24 ∧
          ∀ k (x : (X.obj k).M),
            hd.dist k x (X.obj k).basepoint ≤ R →
            HasNormalBrFull (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x q δ (aρ * hd.mu R) := by
  obtain ⟨aq, aδ, haq, haδ, hscale⟩ := h.exists_phase_scale
  let aρ : Real := min aδ (aq / 2)
  have haρ : 0 < aρ := by
    dsimp only [aρ]
    exact lt_min haδ (div_pos haq (by norm_num))
  refine ⟨aq, aδ, aρ, haq, haδ, haρ, ?_⟩
  intro R hR
  obtain ⟨q, hqeq, hqWide, hqAcc, herr, hinvErr, hδlower⟩ := hscale R hR
  have hqReal : (0 : Real) < q := by
    rw [hqeq]
    exact mul_pos haq (hd.mu_pos R)
  have hq : 0 < q := by exact_mod_cast hqReal
  let δ : Real :=
    ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
      ((q : Real) / 2)
  change aδ * hd.mu R ≤ δ at hδlower
  have hδ : 0 < δ :=
    (mul_pos haδ (hd.mu_pos R)).trans_le hδlower
  have hρ : 0 < aρ * hd.mu R := mul_pos haρ (hd.mu_pos R)
  have hρδ : aρ * hd.mu R ≤ δ := by
    exact (mul_le_mul_of_nonneg_right (min_le_left aδ (aq / 2))
      (hd.mu_nonneg R)).trans hδlower
  have hρq : aρ * hd.mu R < (q : Real) := by
    calc
      aρ * hd.mu R ≤ (aq / 2) * hd.mu R :=
        mul_le_mul_of_nonneg_right (min_le_right aδ (aq / 2)) (hd.mu_nonneg R)
      _ = (q : Real) / 2 := by rw [hqeq]; ring
      _ < (q : Real) := half_lt_self hqReal
  refine ⟨q, δ, hq, hδ, hqeq, hδlower, hqWide, hqAcc, herr, hinvErr, ?_⟩
  intro k x hx
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn k
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  have hrMetric := h.phaseRadius_metric hx
  have hrQuarter := h.phaseRadius_exp hx
  obtain ⟨δ', e, hδ', hδ'eq, he, hfence, hinvApprox⟩ :=
    normalDiagAtFull (I := I) hb k x (hcomplete.complete k) (hconn k)
      hrMetric hrQuarter q hq hqWide hqAcc herr
  have hδ'eq' : δ' = δ := by simpa only [δ] using hδ'eq
  subst δ'
  have hqPhase : (q : Real) < h.phaseRadius R := by
    nlinarith
  have hphaseFloor : h.phaseRadius R ≤ h.ratio * hd.mu R := by
    dsimp only [NormalRadiusProfile.phaseRadius]
    nlinarith [h.floor_pos R]
  have hqExp : (q : Real) <
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
    (hqPhase.trans_le hphaseFloor).trans_le (h.floor_le_exp hx)
  have hρExp : aρ * hd.mu R <
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
    hρq.trans hqExp
  have hclosed : ∀ w ∈ Metric.closedBall (0 : E × E) (aρ * hd.mu R),
      normalPair (I := I) (X.obj k) x w ∈
        (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
          (hconn k) x hq he).dom := by
    intro w hw
    exact IsNormalDiag.pair_mem_of_closed (I := I) (X.obj k)
      (hcomplete.complete k) (hconn k) x hq he hw hqExp hρδ hρExp
  have htransport := IsNormalDiag.full_transport (I := I) (X.obj k)
    (hcomplete.complete k) (hconn k) x hq he hfence
  have heData := he
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj k) x (e z) =
        diagExp (I := I) (X.obj k).metric (normal_enorm (I := I) (X.obj k))
          (normalTangent (I := I) (X.obj k) x z) at heData
  have hδtarget : Metric.closedBall (0 : E × E) δ ⊆ e.target :=
    heData.2.2.2.1
  have hδdom : ∀ w ∈ Metric.closedBall (0 : E × E) δ,
      normalPair (I := I) (X.obj k) x w ∈
        (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
          (hconn k) x hq he).dom := by
    intro w hw
    rw [← htransport.2.1]
    exact ⟨w, hδtarget hw, normalPairHome_apply (I := I) (X.obj k) x w⟩
  have hδinv : ∀ w ∈ Metric.closedBall (0 : E × E) δ,
      (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
          (hconn k) x hq he).inv (normalPair (I := I) (X.obj k) x w) =
        normalTangent (I := I) (X.obj k) x (e.symm w) := by
    intro w hw
    exact htransport.2.2 w (hδtarget hw)
  change ∃ hq' : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
          x q δ e,
        NormalDiagFence (I := I) (X.obj k) x q e ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) (aρ * hd.mu R),
          normalPair (I := I) (X.obj k) x w ∈
            (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).dom) ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) δ,
          normalPair (I := I) (X.obj k) x w ∈
            (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).dom) ∧
        normalTanHome (I := I) (X.obj k) x '' Metric.ball (0 : E × E) q =
            (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).hom.source ∧
        normalPairHome (I := I) (X.obj k) x '' e.target =
            (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).dom ∧
        (∀ w ∈ e.target,
          (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).inv (normalPair (I := I) (X.obj k) x w) =
            normalTangent (I := I) (X.obj k) x (e.symm w)) ∧
        (∀ w ∈ Metric.closedBall (0 : E × E) δ,
          (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).inv (normalPair (I := I) (X.obj k) x w) =
            normalTangent (I := I) (X.obj k) x (e.symm w)) ∧
        ∃ η : NNReal, η < 1 / 24 ∧
          ApproximatesLinearOn
            (e.symm : E × E → E × E)
            ((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E)) e.target η
  exact ⟨hq, e, he, hfence, hclosed, hδdom, htransport.1,
    htransport.2.1, htransport.2.2, hδinv, _, hinvErr, hinvApprox⟩




theorem normalMinScale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aq aδ aMin : Real,
      0 < aq ∧ 0 < aδ ∧ 0 < aMin ∧
      ∀ R, 0 ≤ R →
        ∃ (q : NNReal) (δ : Real),
          0 < q ∧ 0 < δ ∧
          (q : Real) = aq * hd.mu R ∧
          aδ * hd.mu R ≤ δ ∧
          6 * (q : Real) < h.phaseRadius R ∧
          3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < 1 / 24 ∧
          2 * (aMin * hd.mu R) < (q : Real) ∧
          ∀ k (x : (X.obj k).M),
            hd.dist k x (X.obj k).basepoint ≤ R →
            letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
            letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
            letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
            letI : T2Space (TangentBundle I (X.obj k).M) :=
              (X.obj k).t2TangentBundle
            HasNormalBrFull (I := I) (X.obj k) (hcomplete.complete k)
                (hconn k) x q δ (aMin * hd.mu R) ∧
              aMin * hd.mu R ≤ hb.radius k x ∧
              (aMin * hd.mu R) / 2 ≤
                Geometry.Riemannian.expRadiusGp (I := I) (X.obj k).metric x := by
  obtain ⟨aq, aδ, aρ, haq, haδ, haρ, hall⟩ :=
    normalBrAccept (I := I) h hcomplete hconn
  let aMin : Real := min aρ (min (aq / 4) h.gpRatio)
  have haMin : 0 < aMin := by
    dsimp only [aMin]
    exact lt_min haρ (lt_min (div_pos haq (by norm_num)) h.gpRatio_pos)
  have haMinρ : aMin ≤ aρ := by
    dsimp only [aMin]
    exact min_le_left _ _
  have haMinq : aMin ≤ aq / 4 := by
    dsimp only [aMin]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have haMinGp : aMin ≤ h.gpRatio := by
    dsimp only [aMin]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨aq, aδ, aMin, haq, haδ, haMin, ?_⟩
  intro R hR
  obtain ⟨q, δ, hq, hδ, hqeq, hδlower, hqWide, hqAcc, herr, hinvErr,
      hfull⟩ := hall R hR
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hMinq : 2 * (aMin * hd.mu R) < (q : Real) := by
    calc
      2 * (aMin * hd.mu R) ≤ 2 * ((aq / 4) * hd.mu R) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right haMinq (hd.mu_nonneg R)) (by norm_num)
      _ = (q : Real) / 2 := by rw [hqeq]; ring
      _ < (q : Real) := half_lt_self hqReal
  refine ⟨q, δ, hq, hδ, hqeq, hδlower, hqWide, hqAcc, herr, hinvErr,
    hMinq, ?_⟩
  intro k x hx
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  have hρsmall : aMin * hd.mu R ≤ aρ * hd.mu R :=
    mul_le_mul_of_nonneg_right haMinρ (hd.mu_nonneg R)
  have hbranch : HasNormalBrFull (I := I) (X.obj k) (hcomplete.complete k)
      (hconn k) x q δ (aMin * hd.mu R) :=
    HasNormalBrFull.mono (I := I) (X.obj k) (hcomplete.complete k)
      (hconn k) x (hfull k x hx) hρsmall
  have hMinRatio : aMin ≤ h.ratio := haMinGp.trans h.gpRatio_le_ratio
  have hradius : aMin * hd.mu R ≤ hb.radius k x :=
    (mul_le_mul_of_nonneg_right hMinRatio (hd.mu_nonneg R)).trans
      (h.floor_le_radius hx)
  have hMinFloor : aMin * hd.mu R ≤ h.gpRatio * hd.mu R :=
    mul_le_mul_of_nonneg_right haMinGp (hd.mu_nonneg R)
  have hhalfFloor : (aMin * hd.mu R) / 2 ≤ h.gpRatio * hd.mu R := by
    calc
      (aMin * hd.mu R) / 2 ≤ aMin * hd.mu R := by
        nlinarith [mul_nonneg haMin.le (hd.mu_nonneg R)]
      _ ≤ h.gpRatio * hd.mu R := hMinFloor
  exact ⟨hbranch, hradius, hhalfFloor.trans (h.floor_le_expGp hx)⟩



theorem normalBrScale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ aq aδ aρ : Real,
      0 < aq ∧ 0 < aδ ∧ 0 < aρ ∧
      ∀ R, 0 ≤ R →
        ∃ (q : NNReal) (δ : Real),
          0 < q ∧ 0 < δ ∧
          (q : Real) = aq * hd.mu R ∧
          aδ * hd.mu R ≤ δ ∧
          6 * (q : Real) < h.phaseRadius R ∧
          ∀ k (x : (X.obj k).M),
            hd.dist k x (X.obj k).basepoint ≤ R →
            HasNormalBranchDom (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x q δ (aρ * hd.mu R) := by
  obtain ⟨aq, aδ, aρ, haq, haδ, haρ, hall⟩ :=
    normalBrAccept (I := I) h hcomplete hconn
  refine ⟨aq, aδ, aρ, haq, haδ, haρ, ?_⟩
  intro R hR
  obtain ⟨q, δ, hq, hδ, hqeq, hδlower, hqWide, _hqAcc, _herr, _hinvErr,
      hfull⟩ := hall R hR
  refine ⟨q, δ, hq, hδ, hqeq, hδlower, hqWide, ?_⟩
  intro k x hx
  exact HasNormalBrFull.toDom (I := I) (X.obj k) (hcomplete.complete k)
    (hconn k) x (hfull k x hx)

end HCGCompactness
end DifferentialGeometry
