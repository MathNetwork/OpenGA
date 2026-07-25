import DifferentialGeometry.Analysis.ODE.PhaseFlowExistence
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricGeodesicSpray
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalMetricExtend

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set
open scoped Manifold ContDiff NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



noncomputable def normalAccel
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E) : E := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact -((Integral.Connection.leviCivitaConnectionOfMetric (I := 𝓘(Real, E))
    (normalTotal (I := I) Y x) (fun _ : E ↦ z.2) z.1) z.2)


@[simp] theorem normalAccel_zero
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    normalAccel (I := I) Y x (0 : E × E) = 0 := by
  unfold normalAccel
  change -((Integral.Connection.leviCivitaConnectionOfMetric (I := 𝓘(Real, E))
    (normalTotal (I := I) Y x) (fun _ : E ↦ (0 : E)) (0 : E)) (0 : E)) = 0
  rw [Integral.Connection.leviCivitaConnectionOfMetric_apply]
  have hz :
      Integral.Connection.leviCivitaConnectionCandidateAt (I := 𝓘(Real, E))
        (normalTotal (I := I) Y x) (fun _ : E ↦ (0 : E)) (0 : E) (0 : E) = 0 :=
    ContinuousLinearMap.map_zero _
  rw [hz, neg_zero]


def normalPhaseBox (r : Real) (R : ℝ≥0) : Set (E × E) :=
  {z | z.1 ∈ Metric.ball (0 : E) r ∧ ‖z.2‖ ≤ (R : Real)}



def normalPhaseK
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) (R : ℝ≥0) : ℝ≥0 where
  val := (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) * (R : Real) ^ 2 +
    6 * h.metricC 1 * (R : Real)
  property := by
    have hA : 0 ≤ 6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2 :=
      add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (h.metricC 1)))
        (mul_nonneg (by norm_num) (h.metricC_nonneg 2))
    exact add_nonneg
      (mul_nonneg hA (sq_nonneg (R : Real)))
      (mul_nonneg (mul_nonneg (by norm_num) (h.metricC_nonneg 1)) R.coe_nonneg)



omit [NeZero (Module.finrank ℝ E)] in
theorem normalPhaseK_mono
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    {R S : ℝ≥0} (hRS : R ≤ S) : normalPhaseK h R ≤ normalPhaseK h S := by
  apply NNReal.coe_le_coe.mp
  have hRS' : (R : ℝ) ≤ (S : ℝ) := by exact_mod_cast hRS
  have hsq : (R : ℝ) ^ 2 ≤ (S : ℝ) ^ 2 := by
    nlinarith [R.coe_nonneg, S.coe_nonneg]
  have hA : 0 ≤ 6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2 :=
    add_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg (h.metricC 1)))
      (mul_nonneg (by norm_num) (h.metricC_nonneg 2))
  have hB : 0 ≤ 6 * h.metricC 1 :=
    mul_nonneg (by norm_num) (h.metricC_nonneg 1)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hsq hA)
    (mul_le_mul_of_nonneg_left hRS' hB)



theorem normalAccel_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E × E), z.1 ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x / 4) →
    ∀ hco : IsCoercive (normalCoordMetric (I := I) Y x z.1),
      normalAccel (I := I) Y x z =
        -MetricKoszul.koszulVec hco
          (fderiv Real (normalCoordMetric (I := I) Y x) z.1) z.2 z.2 := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz hco
  unfold normalAccel
  rw [normal_cov_eq (I := I) Y x z.1 hz hco z.2 z.2]
  rfl



theorem normalPhase_eq_spray
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (z : E × E),
      z.1 ∈ Metric.ball (0 : E)
        (expMapC2Radius (I := I) Y.metric x / 4) →
      ∀ _hco : IsCoercive (normalCoordMetric (I := I) Y x z.1),
        PhaseFlow.phaseField (normalAccel (I := I) Y x) z =
          MetricKoszul.metricSpray (normalCoordMetric (I := I) Y x) z := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hz hco
  rw [MetricKoszul.metricSpray_eq _ _ hco]
  change (z.2, normalAccel (I := I) Y x z) = _
  rw [normalAccel_eq (I := I) Y x z hz hco]


theorem normalAccel_norm
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (R : ℝ≥0) (z : E × E) (hz : z ∈ normalPhaseBox r R) :
    ‖normalAccel (I := I) (X.obj k) x z‖ ≤
      3 * h.metricC 1 * (R : Real) ^ 2 := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  rw [normalAccel_eq (I := I) (X.obj k) x z (hrQuarter hz.1)
    ((h.metric_equiv k x).coercive (hrMetric hz.1)), norm_neg]
  calc
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hz.1))
        (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z.1) z.2 z.2‖ ≤
        3 * h.metricC 1 * ‖z.2‖ * ‖z.2‖ :=
      h.koszulVec_norm_le k x (hrMetric hz.1) z.2 z.2
    _ ≤ 3 * h.metricC 1 * (R : Real) * (R : Real) := by
      have hC : 0 ≤ 3 * h.metricC 1 :=
        mul_nonneg (by norm_num) (h.metricC_nonneg 1)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_self_le_mul_self (norm_nonneg z.2) hz.2) hC
    _ = 3 * h.metricC 1 * (R : Real) ^ 2 := by ring




theorem normalAccel_lip
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (R : ℝ≥0) :
    LipschitzOnWith (normalPhaseK h R)
      (normalAccel (I := I) (X.obj k) x) (normalPhaseBox r R) := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  have hquarter : Metric.ball (0 : E)
      (expMapC2Radius (I := I) (X.obj k).metric x / 4) ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj k).metric x) := by
    simpa only [normalBall] using normalInner_sub (I := I) (X.obj k) x
  have hrExp : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj k).metric x) :=
    hrQuarter.trans hquarter
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz y hy
  have hraw := h.koszulAccel_lip_on k x hrMetric hrExp R.coe_nonneg
    hz.1 hy.1 hz.2 hy.2
  rw [normalAccel_eq (I := I) (X.obj k) x z (hrQuarter hz.1)
      ((h.metric_equiv k x).coercive (hrMetric hz.1)),
    normalAccel_eq (I := I) (X.obj k) x y (hrQuarter hy.1)
      ((h.metric_equiv k x).coercive (hrMetric hy.1))]
  simp only [dist_eq_norm, neg_sub_neg]
  rw [norm_sub_rev]
  simpa only [normalPhaseK, NNReal.coe_mk] using hraw




theorem normalDiag_approx
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (R : ℝ≥0) {u : Set (E × E)} {Φ : (E × E) → Real → E × E}
    (hinit : ∀ z ∈ u, Φ z 0 = z)
    (hcont : ∀ z ∈ u, ContinuousOn (Φ z) (Icc 0 1))
    (hderiv : ∀ z ∈ u, ∀ t ∈ Ico 0 1,
      HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) (Ici t) t)
    (hmem : ∀ z ∈ u, ∀ t ∈ Ico 0 1, Φ z t ∈ normalPhaseBox r R) :
    ApproximatesLinearOn (fun z ↦ (z.1, (Φ z 1).1))
      PhaseFlow.freeDiag u (PhaseFlow.phaseErr (normalPhaseK h R)) := by
  exact PhaseFlow.phase_diag_approx
    (normalAccel_lip (I := I) h k x hrMetric hrQuarter R)
    hinit hcont hderiv hmem





theorem exists_normalFlow
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (q : NNReal) (hq : 0 < q)
    (hqPos : 4 * (q : Real) < r)
    (hqAcc : 3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real)) :
    ∃ Φ : (E × E) → Real → E × E,
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ContinuousOn (Φ z) (Icc 0 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ico 0 1,
        HasDerivWithinAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
          (Ici t) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc 0 1,
        Φ z t ∈ normalPhaseBox r (2 * q)) ∧
      ApproximatesLinearOn (fun z ↦ (z.1, (Φ z 1).1)) PhaseFlow.freeDiag
        (Metric.closedBall (0 : E × E) q)
        (PhaseFlow.phaseErr (normalPhaseK h (2 * q))) := by
  let P : NNReal := 4 * q
  let V : NNReal := 2 * q
  let half : NNReal := 1 / 2
  let A : NNReal :=
    ⟨3 * h.metricC 1 * (V : Real) ^ 2,
      mul_nonneg (mul_nonneg (by norm_num) (h.metricC_nonneg 1)) (sq_nonneg _)⟩
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hV : 0 < V := by
    dsimp only [V]
    positivity
  have hbox : PhaseFlow.phaseBox (E := E) P V ⊆ normalPhaseBox r V := by
    intro z hz
    refine ⟨?_, hz.2⟩
    rw [mem_ball_zero_iff]
    exact hz.1.trans_lt (by simpa only [P, NNReal.coe_mul, NNReal.coe_natCast] using hqPos)
  have haLip : LipschitzOnWith (normalPhaseK h V)
      (normalAccel (I := I) (X.obj k) x) (PhaseFlow.phaseBox P V) :=
    (normalAccel_lip (I := I) h k x hrMetric hrQuarter V).mono hbox
  have haNorm : ∀ z ∈ PhaseFlow.phaseBox (E := E) P V,
      ‖normalAccel (I := I) (X.obj k) x z‖ ≤ (A : Real) := by
    intro z hz
    simpa only [A, NNReal.coe_mk] using
      normalAccel_norm (I := I) h k x hrMetric hrQuarter V z (hbox hz)
  have hVP : V ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (2 : Real) * (q : Real) ≤ (1 / 2 : Real) * (4 * (q : Real))
    nlinarith
  have hAV : A ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change 3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (1 / 2 : Real) * (2 * (q : Real))
    simpa using hqAcc
  have hhalf : (half : Real) ≤ 1 - (half : Real) := by
    norm_num [half]
  obtain ⟨Φ, hΦ⟩ := PhaseFlow.exists_fenced (E := E) hP hV haLip haNorm hVP hAV hhalf
  have hqP : q ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (4 * (q : Real))
    nlinarith [q.coe_nonneg]
  have hqV : q ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (2 * (q : Real))
    nlinarith
  have hscale := PhaseFlow.scale_maps_ball (E := E) hP hV hqP hqV
  have hspec : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      Φ z 0 = z ∧
      ContinuousOn (Φ z) (Icc 0 1) ∧
      (∀ t ∈ Ico 0 1,
        HasDerivWithinAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
          (Ici t) t) ∧
      ∀ t ∈ Icc 0 1, Φ z t ∈ normalPhaseBox r V := by
    intro z hz
    have hs := hΦ z (hscale hz)
    exact ⟨hs.1, hs.2.1, hs.2.2.1, fun t ht ↦ hbox (hs.2.2.2 t ht)⟩
  have hinit : ∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z :=
    fun z hz ↦ (hspec z hz).1
  have hcont : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (Φ z) (Icc 0 1) := fun z hz ↦ (hspec z hz).2.1
  have hderiv : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ico 0 1,
      HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
        (Ici t) t := fun z hz ↦ (hspec z hz).2.2.1
  have hmem : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc 0 1,
      Φ z t ∈ normalPhaseBox r V := fun z hz ↦ (hspec z hz).2.2.2
  have happ := normalDiag_approx (I := I) h k x hrMetric hrQuarter V
    hinit hcont hderiv (fun z hz t ht ↦ hmem z hz t ⟨ht.1, ht.2.le⟩)
  simpa only [V] using ⟨Φ, hinit, hcont, hderiv, hmem, happ⟩

end HCGCompactness
end DifferentialGeometry
