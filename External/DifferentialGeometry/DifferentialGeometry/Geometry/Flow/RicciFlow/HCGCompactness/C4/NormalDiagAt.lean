import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhaseEndpoint








noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]





theorem normalDiagAtFull
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (q : NNReal) (hq : 0 < q)
    (hqWide : 6 * (q : Real) < r)
    (hqAccel : 3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    (herr : PhaseFlow.phaseErr (normalPhaseK h (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ (δ : Real) (e : OpenPartialHomeomorph (E × E) (E × E)),
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK h (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e ∧
      NormalDiagFence (I := I) (X.obj k) x q e ∧
      ApproximatesLinearOn
        (e.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        e.target
        (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
              (E × E) →L[Real] (E × E))‖₊⁻¹ -
            PhaseFlow.phaseErr (normalPhaseK h (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (normalPhaseK h (2 * q))) := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  obtain ⟨Φ, hΦ0, hΦcont, hΦwithin, _hΦat, hΦbox, hΦzero,
      happrox, hΦsmooth⟩ :=
    exists_normal_biflow (I := I) h k x hrMetric hrQuarter q hq
      hqWide hqAccel
  obtain ⟨e, δ, hδ, hsource, hcoe, htarget, hδeq, hinvApprox⟩ :=
    PhaseFlow.exists_quant_inv_bi hq happrox herr
  have heSmooth : ContDiffOn Real ∞ (e : E × E → E × E) e.source := by
    rw [hsource, hcoe]
    exact hΦsmooth
  have heZero : e 0 = 0 := by
    rw [hcoe]
    simp only [Prod.fst_zero, hΦzero]
    rfl
  have htargetE : Metric.closedBall (e 0) δ ⊆ e.target := by
    simpa only [hcoe] using htarget
  have htarget' : Metric.closedBall (0 : E × E) δ ⊆ e.target := by
    simpa only [heZero] using htargetE
  have happroxOpen : ApproximatesLinearOn
      (fun z ↦ (z.1, (Φ z 1).1))
      (PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[Real] (E × E))
      (Metric.ball (0 : E × E) q)
      (PhaseFlow.phaseErr (normalPhaseK h (2 * q))) := by
    simpa only [PhaseFlow.freeDiagCLE_coe] using
      happrox.mono_set Metric.ball_subset_closedBall
  have hinvSmooth : ContDiffOn Real ∞ e.symm e.target :=
    PhaseFlow.inv_smooth_of_approx happroxOpen (Or.inr herr)
      Metric.isOpen_ball hΦsmooth e hsource hcoe
  have hdiag : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj k) x (e z) =
        diagExp (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k))
          (normalTangent (I := I) (X.obj k) x z) := by
    intro z hz
    have hzdiag := normal_end_eq_diag (I := I) (X.obj k)
      hcomplete hconn x hrQuarter
      (hΦcont z hz) (hΦwithin z hz) (hΦbox z hz)
    rw [hcoe]
    simpa only [hΦ0 z hz] using hzdiag
  refine ⟨δ, e, hδ, hδeq, ?_, ?_, hinvApprox⟩
  · change e.source = Metric.ball (0 : E × E) q ∧
      e 0 = 0 ∧
      ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
      Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
      ContDiffOn Real ∞ e.symm e.target ∧
      ∀ z ∈ Metric.closedBall (0 : E × E) q,
        normalPair (I := I) (X.obj k) x (e z) =
          diagExp (I := I) (X.obj k).metric
            (normal_enorm (I := I) (X.obj k))
            (normalTangent (I := I) (X.obj k) x z)
    exact ⟨hsource, heZero, heSmooth, htarget', hinvSmooth, hdiag⟩
  · intro z hz
    have hzNorm : ‖z‖ ≤ (q : Real) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hqr : (q : Real) < r := by nlinarith [hqWide]
    have hzFirst : z.1 ∈ Metric.ball (0 : E) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_fst_le z).trans_lt (hzNorm.trans_lt hqr)
    have htime : (1 : Real) ∈ Set.Icc (-1) 1 := by norm_num
    have hzEnd : (Φ z 1).1 ∈ Metric.ball (0 : E) r :=
      (hΦbox z hz 1 htime).1
    have hExpPos := expMapC2Radius_pos (I := I) (X.obj k).metric x
    have hrNormal : Metric.ball (0 : E) r ⊆ normalBall (I := I) (X.obj k) x := by
      intro v hv
      have hvQuarter := hrQuarter hv
      change v ∈ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x)
      exact Metric.ball_subset_ball (by nlinarith) hvQuarter
    have hzFirst' := hrNormal hzFirst
    have hzEnd' := hrNormal hzEnd
    rw [hcoe]
    exact ⟨hzFirst', hzFirst', hzEnd'⟩


theorem normalDiagAt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (q : NNReal) (hq : 0 < q)
    (hqWide : 6 * (q : Real) < r)
    (hqAccel : 3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    (herr : PhaseFlow.phaseErr (normalPhaseK h (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ (δ : Real) (e : OpenPartialHomeomorph (E × E) (E × E)),
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK h (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e := by
  obtain ⟨δ, e, hδ, hδeq, he, _hfence, _hinvApprox⟩ :=
    normalDiagAtFull (I := I) h k x hcomplete hconn hrMetric hrQuarter
      q hq hqWide hqAccel herr
  exact ⟨δ, e, hδ, hδeq, he⟩

end HCGCompactness
end DifferentialGeometry
