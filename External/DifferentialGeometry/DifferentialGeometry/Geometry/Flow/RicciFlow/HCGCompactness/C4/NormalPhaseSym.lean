import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhaseRealization

set_option autoImplicit false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Metric
open scoped Manifold ContDiff NNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]





theorem exists_normal_biflow
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (q : NNReal) (hq : 0 < q)
    (hqPos : 6 * (q : Real) < r)
    (hqAcc : 3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real)) :
    ∃ Φ : (E × E) → Real → E × E,
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ContinuousOn (Φ z) (Icc (-1) 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        HasDerivWithinAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
          (Icc (-1) 1) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ioo (-1) 1,
        HasDerivAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        Φ z t ∈ normalPhaseBox r (2 * q)) ∧
      Φ 0 1 = 0 ∧
      ApproximatesLinearOn (fun z ↦ (z.1, (Φ z 1).1)) PhaseFlow.freeDiag
        (Metric.closedBall (0 : E × E) q)
        (PhaseFlow.phaseErr (normalPhaseK h (2 * q))) ∧
      ContDiffOn Real ∞ (fun z ↦ (z.1, (Φ z 1).1))
        (Metric.ball (0 : E × E) q) := by
  let P : NNReal := 6 * q
  let V : NNReal := 2 * q
  let half : NNReal := 1 / 2
  let speed : NNReal := 1 / 3
  let T : Real := 3 / 2
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
    exact hz.1.trans_lt
      (by simpa only [P, NNReal.coe_mul, NNReal.coe_natCast] using hqPos)
  have haLip : LipschitzOnWith (normalPhaseK h V)
      (normalAccel (I := I) (X.obj k) x) (PhaseFlow.phaseBox P V) :=
    (normalAccel_lip (I := I) h k x hrMetric hrQuarter V).mono hbox
  have haNorm : ∀ z ∈ PhaseFlow.phaseBox (E := E) P V,
      ‖normalAccel (I := I) (X.obj k) x z‖ ≤ (A : Real) := by
    intro z hz
    simpa only [A, NNReal.coe_mk] using
      normalAccel_norm (I := I) h k x hrMetric hrQuarter V z (hbox hz)
  have hVP : V ≤ speed * P := by
    rw [← NNReal.coe_le_coe]
    change (2 : Real) * (q : Real) ≤ (1 / 3 : Real) * (6 * (q : Real))
    nlinarith
  have hAV : A ≤ speed * V := by
    rw [← NNReal.coe_le_coe]
    change 3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (1 / 3 : Real) * (2 * (q : Real))
    nlinarith [hqAcc]
  have hfence : (speed : Real) * T ≤ 1 - (half : Real) := by
    norm_num [speed, T, half]
  obtain ⟨Φ, hΦ⟩ := PhaseFlow.exists_fenced_on (E := E)
    (T := T) (by positivity) hP hV haLip haNorm hVP hAV hfence
  have hqP : q ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (6 * (q : Real))
    nlinarith [q.coe_nonneg]
  have hqV : q ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (2 * (q : Real))
    nlinarith
  have hscale := PhaseFlow.scale_maps_ball (E := E) hP hV hqP hqV
  have hspecWide : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      Φ z 0 = z ∧
      ContinuousOn (Φ z) (Icc (-T) T) ∧
      (∀ t ∈ Icc (-T) T, HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
        (Icc (-T) T) t) ∧
      (∀ t ∈ Ioo (-T) T, HasDerivAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) t) ∧
      ∀ t ∈ Icc (-T) T, Φ z t ∈ normalPhaseBox r V := by
    intro z hz
    obtain ⟨hΦ0, hΦcont, hΦwithin, hΦat, hΦmem⟩ := hΦ z (hscale hz)
    exact ⟨hΦ0, hΦcont, hΦwithin, hΦat, fun t ht ↦ hbox (hΦmem t ht)⟩
  have hsmallIcc : Icc (-1 : Real) 1 ⊆ Icc (-T) T := by
    intro t ht
    constructor <;> dsimp only [T] <;> linarith [ht.1, ht.2]
  have hsmallIoo : Ioo (-1 : Real) 1 ⊆ Ioo (-T) T := by
    intro t ht
    constructor <;> dsimp only [T] <;> linarith [ht.1, ht.2]
  have hspec : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      Φ z 0 = z ∧
      ContinuousOn (Φ z) (Icc (-1) 1) ∧
      (∀ t ∈ Icc (-1) 1, HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
        (Icc (-1) 1) t) ∧
      (∀ t ∈ Ioo (-1) 1, HasDerivAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) t) ∧
      ∀ t ∈ Icc (-1) 1, Φ z t ∈ normalPhaseBox r V := by
    intro z hz
    obtain ⟨hΦ0, hΦcont, hΦwithin, hΦat, hΦmem⟩ := hspecWide z hz
    refine ⟨hΦ0, hΦcont.mono hsmallIcc, ?_, ?_, fun t ht ↦ hΦmem t (hsmallIcc ht)⟩
    · intro t ht
      exact (hΦwithin t (hsmallIcc ht)).mono hsmallIcc
    · intro t ht
      exact hΦat t (hsmallIoo ht)
  have hinit : ∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z :=
    fun z hz ↦ (hspec z hz).1
  have hcont : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (Φ z) (Icc (-1) 1) := fun z hz ↦ (hspec z hz).2.1
  have hwithin : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
      HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
        (Icc (-1) 1) t := fun z hz ↦ (hspec z hz).2.2.1
  have hderiv : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ioo (-1) 1,
      HasDerivAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) t :=
    fun z hz ↦ (hspec z hz).2.2.2.1
  have hmem : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
      Φ z t ∈ normalPhaseBox r V := fun z hz ↦ (hspec z hz).2.2.2.2
  have hcont01 : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (Φ z) (Icc 0 1) := by
    intro z hz
    exact (hcont z hz).mono (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  have hderiv01 : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ico 0 1,
      HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
        (Ici t) t := by
    intro z hz t ht
    exact (hderiv z hz t ⟨by linarith [ht.1], ht.2⟩).hasDerivWithinAt
  have hzeroMem : (0 : E × E) ∈ Metric.closedBall (0 : E × E) q := by
    simp
  have hzeroDeriv : ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun _ : Real ↦ (0 : E × E))
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) 0) t := by
    intro t _ht
    simpa [PhaseFlow.phaseField] using
      (hasDerivAt_const (x := t) (c := (0 : E × E)))
  have hzeroEq : EqOn (Φ 0) (fun _ : Real ↦ (0 : E × E)) (Ioo (-T) T) :=
    Analysis.ODE.Flow.orbit_unique_smooth
      (v := PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x))
      ((normalPhase_contDiff (I := I) (X.obj k) x).of_le (by simp))
      (a := -T) (b := T) (t₀ := 0)
      (by dsimp only [T]; norm_num)
      (fun t ht ↦ (hspecWide 0 hzeroMem).2.2.2.1 t ht)
      hzeroDeriv
      (by simpa using (hspecWide 0 hzeroMem).1)
  have hzeroEnd : Φ 0 1 = 0 := by
    simpa using hzeroEq (by dsimp only [T]; norm_num)
  have happ := normalDiag_approx (I := I) h k x hrMetric hrQuarter V
    hinit hcont01 hderiv01
      (fun z hz t ht ↦ hmem z hz t ⟨by linarith [ht.1], ht.2.le⟩)
  have hslice : ContDiffOn Real ∞ (fun z ↦ Φ z 1)
      (Metric.ball (0 : E × E) q) := by
    apply Analysis.ODE.Flow.flow_slice_smooth
      (v := PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x))
      (D := Metric.ball (0 : E × E) q) (a := -T) (b := T) (t₀ := 0)
      (F := Φ)
    · exact normalPhase_contDiff (I := I) (X.obj k) x
    · exact Metric.isOpen_ball
    · dsimp only [T]
      norm_num
    · intro z hz
      exact (hspecWide z (Metric.ball_subset_closedBall hz)).1
    · intro z hz
      exact (hspecWide z (Metric.ball_subset_closedBall hz)).2.1
    · intro z hz t ht
      exact (hspecWide z (Metric.ball_subset_closedBall hz)).2.2.2.1 t ht
    · dsimp only [T]
      norm_num
  have hendSmooth : ContDiffOn Real ∞ (fun z ↦ (z.1, (Φ z 1).1))
      (Metric.ball (0 : E × E) q) :=
    (contDiff_fst.contDiffOn : ContDiffOn Real ∞ (fun z : E × E ↦ z.1) _).prodMk
      hslice.fst
  simpa only [V] using
    ⟨Φ, hinit, hcont, hwithin, hderiv, hmem, hzeroEnd, happ, hendSmooth⟩

end HCGCompactness
end DifferentialGeometry
