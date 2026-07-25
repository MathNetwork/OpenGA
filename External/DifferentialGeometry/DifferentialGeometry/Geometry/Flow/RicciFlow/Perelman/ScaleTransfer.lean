import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ParabolicRescaling
import DifferentialGeometry.Analysis.Integration.Measure.Scaling
import DifferentialGeometry.Geometry.Metric.DistanceScaling

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]


def paraFlowTime
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime) : D.FlowTime :=
  ⟨paraTime tau R (s : Real), s.2⟩

@[simp] theorem paraFlowTime_coe
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime) :
    (paraFlowTime tau R hR htau s : Real) = paraTime tau R (s : Real) := by
  rfl

namespace Perelman

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}


def paraBall
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s)) :
    FlowMetricBall (paraSolution (I := I) S tau R hR htau) s where
  center := B.center
  radius := Real.sqrt R * B.radius
  radius_pos := mul_pos (Real.sqrt_pos.2 hR) B.radius_pos



omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem paraBall_setAt
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s))
    (q : Real) :
    (paraBall S tau R hR htau s B).setAt q =
      B.setAt (paraTime tau R q) := by
  simpa only [FlowMetricBall.setAt, paraBall, paraSolution_metric] using
    (_root_.DifferentialGeometry.edistBall_scale (I := I) R hR
      (S.base.metric (paraTime tau R q)) B.center B.radius)



omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem paraBall_set
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s)) :
    (paraBall S tau R hR htau s B).set = B.set := by
  unfold FlowMetricBall.set
  simpa only [paraFlowTime_coe] using
    paraBall_setAt (I := I) S tau R hR htau s B (s : Real)


omit [CompleteSpace E] in
theorem paraBall_volume
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s)) :
    (paraBall S tau R hR htau s B).volume =
      ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E * B.volume := by
  change
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M)
        (scaleMetric (I := I) R hR
          (S.base.metric (paraTime tau R (s : Real))))
        (paraBall S tau R hR htau s B).set =
      ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          (I := I) (M := M)
          (S.base.metric (paraTime tau R (s : Real))) B.set
  rw [paraBall_set (I := I) S tau R hR htau s B]
  exact DifferentialGeometry.Integral.Measure.volume_scale_apply
    (I := I) (M := M) R hR
      (S.base.metric (paraTime tau R (s : Real))) B.set



omit [CompleteSpace E] in
theorem paraBall_kappa
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s))
    (kappa : Real) (hB : B.IsKappaNoncollapsed kappa) :
    (paraBall S tau R hR htau s B).IsKappaNoncollapsed kappa := by
  refine ⟨hB.1, ?_⟩
  change
    ENNReal.ofReal kappa *
        ENNReal.ofReal (Real.sqrt R * B.radius) ^ Module.finrank Real E ≤
      (paraBall S tau R hR htau s B).volume
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg R), mul_pow]
  rw [paraBall_volume (I := I) S tau R hR htau s B]
  calc
    ENNReal.ofReal kappa *
          (ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E *
            ENNReal.ofReal B.radius ^ Module.finrank Real E) =
        ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E *
          (ENNReal.ofReal kappa *
            ENNReal.ofReal B.radius ^ Module.finrank Real E) := by
      ac_rfl
    _ ≤ ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E * B.volume :=
      mul_le_mul_right hB.2 _

private theorem paraWindow
    (tau R : Real) (hR : 0 < R) (s q r : Real)
    (hq : q ∈ Set.Icc (s - (Real.sqrt R * r) ^ 2) s) :
    paraTime tau R q ∈
      Set.Icc (paraTime tau R s - r ^ 2) (paraTime tau R s) := by
  have hrad : (Real.sqrt R * r) ^ 2 = R * r ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR.le]
  have hlo : s - R * r ^ 2 ≤ q := by
    simpa only [hrad] using hq.1
  have hlo_div : (s - R * r ^ 2) / R ≤ q / R :=
    (div_le_div_iff_of_pos_right hR).2 hlo
  have hsplit : (s - R * r ^ 2) / R = s / R - r ^ 2 := by
    field_simp [ne_of_gt hR]
  rw [hsplit] at hlo_div
  have hhi_div : q / R ≤ s / R :=
    (div_le_div_iff_of_pos_right hR).2 hq.2
  unfold paraTime
  constructor <;> linarith


omit [SigmaCompactSpace M] in
theorem paraBall_rm
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s))
    (hB : B.IsRmControlled) :
    (paraBall S tau R hR htau s B).IsRmControlled := by
  rcases hB with ⟨hwindow, hcurv⟩
  constructor
  · intro q hq
    have hq_old := paraWindow tau R hR (s : Real) q B.radius hq
    exact hwindow hq_old
  · intro q hq x hx
    have hq_old := paraWindow tau R hR (s : Real) q B.radius hq
    have hx_old : x ∈ B.setAt (paraTime tau R q) := by
      rw [← paraBall_setAt (I := I) S tau R hR htau s B q]
      exact hx
    have hold := hcurv (paraTime tau R q) hq_old x hx_old
    unfold FlowMetricBall.rmNormSq
    rw [paraRmNormSq]
    have hscale :
        (Real.sqrt R * B.radius) ^ 4 * R⁻¹ ^ 2 = B.radius ^ 4 := by
      rw [mul_pow]
      calc
        Real.sqrt R ^ 4 * B.radius ^ 4 * R⁻¹ ^ 2 =
            (Real.sqrt R ^ 2) ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by ring
        _ = R ^ 2 * B.radius ^ 4 * R⁻¹ ^ 2 := by
          rw [Real.sq_sqrt hR.le]
        _ = B.radius ^ 4 := by field_simp [ne_of_gt hR]
    calc
      (Real.sqrt R * B.radius) ^ 4 *
          (R⁻¹ ^ 2 *
            Tensor0SBundle.normSq0S (I := I)
              (S.base.metric (paraTime tau R q)) x 4
              (S.base.rm04 (paraTime tau R q) x)) =
          ((Real.sqrt R * B.radius) ^ 4 * R⁻¹ ^ 2) *
            Tensor0SBundle.normSq0S (I := I)
              (S.base.metric (paraTime tau R q)) x 4
              (S.base.rm04 (paraTime tau R q) x) := by ring
      _ = B.radius ^ 4 *
            Tensor0SBundle.normSq0S (I := I)
              (S.base.metric (paraTime tau R q)) x 4
              (S.base.rm04 (paraTime tau R q) x) := by rw [hscale]
      _ ≤ 1 := hold



def backBall
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall (paraSolution (I := I) S tau R hR htau) s) :
    FlowMetricBall S (paraFlowTime tau R hR htau s) where
  center := B.center
  radius := B.radius / Real.sqrt R
  radius_pos := div_pos B.radius_pos (Real.sqrt_pos.2 hR)


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem paraBall_back
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall (paraSolution (I := I) S tau R hR htau) s) :
    paraBall S tau R hR htau s (backBall S tau R hR htau s B) = B := by
  cases B with
  | mk center radius radius_pos =>
      simp only [paraBall, backBall]
      congr
      field_simp [ne_of_gt (Real.sqrt_pos.2 hR)]



omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem backBall_setAt
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall (paraSolution (I := I) S tau R hR htau) s)
    (q : Real) :
    (backBall S tau R hR htau s B).setAt (paraTime tau R q) =
      B.setAt q := by
  have h := paraBall_setAt (I := I) S tau R hR htau s
    (backBall S tau R hR htau s B) q
  rw [paraBall_back (I := I) S tau R hR htau s B] at h
  exact h.symm



omit [CompleteSpace E] in
theorem backBall_volume
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall (paraSolution (I := I) S tau R hR htau) s) :
    B.volume = ENNReal.ofReal (Real.sqrt R) ^ Module.finrank Real E *
      (backBall S tau R hR htau s B).volume := by
  have h := paraBall_volume (I := I) S tau R hR htau s
    (backBall S tau R hR htau s B)
  rw [paraBall_back (I := I) S tau R hR htau s B] at h
  exact h



omit [CompleteSpace E] in
theorem backBall_kappa
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall (paraSolution (I := I) S tau R hR htau) s)
    (kappa : Real) (hB : B.IsKappaNoncollapsed kappa) :
    (backBall S tau R hR htau s B).IsKappaNoncollapsed kappa := by
  refine ⟨hB.1, ?_⟩
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt R)
  let n : Nat := Module.finrank Real E
  have ha0 : a ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hR))
  have hatop : a ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hfac0 : a ^ n ≠ 0 := pow_ne_zero n ha0
  have hfactop : a ^ n ≠ (∞ : ℝ≥0∞) := ENNReal.pow_ne_top hatop
  have hradius :
      B.radius = Real.sqrt R * (backBall S tau R hR htau s B).radius := by
    dsimp [backBall]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hR)]
  have hscaled := hB.2
  rw [hradius, ENNReal.ofReal_mul (Real.sqrt_nonneg R), mul_pow,
    backBall_volume (I := I) S tau R hR htau s B] at hscaled
  have hscaled' :
      a ^ n *
          (ENNReal.ofReal kappa *
            ENNReal.ofReal (backBall S tau R hR htau s B).radius ^ n) ≤
        a ^ n * (backBall S tau R hR htau s B).volume := by
    simpa only [a, n, mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact (ENNReal.mul_le_mul_iff_right hfac0 hfactop).mp hscaled'

private theorem backWindow
    (tau R : Real) (hR : 0 < R) (s q r : Real)
    (hq : q ∈ Set.Icc
      (paraTime tau R s - (r / Real.sqrt R) ^ 2) (paraTime tau R s)) :
    paraBack tau R q ∈ Set.Icc (s - r ^ 2) s := by
  have hrad : (r / Real.sqrt R) ^ 2 = r ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hR.le]
  have hlo0 := hq.1
  rw [hrad] at hlo0
  unfold paraTime at hlo0
  have hlo_div : (s - r ^ 2) / R ≤ q - tau := by
    rw [sub_div]
    linarith
  have hlo := (div_le_iff₀ hR).1 hlo_div
  have hhi0 := hq.2
  unfold paraTime at hhi0
  have hhi_div : q - tau ≤ s / R := by linarith
  have hhi := (le_div_iff₀ hR).1 hhi_div
  constructor
  · simpa [paraBack, mul_comm] using hlo
  · simpa [paraBack, mul_comm] using hhi



omit [SigmaCompactSpace M] in
theorem backBall_rm
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall (paraSolution (I := I) S tau R hR htau) s)
    (hB : B.IsRmControlled) :
    (backBall S tau R hR htau s B).IsRmControlled := by
  rcases hB with ⟨hwindow, hcurv⟩
  constructor
  · intro q hq
    let q' : Real := paraBack tau R q
    have hq_new : q' ∈ Set.Icc (s - B.radius ^ 2) (s : Real) :=
      backWindow tau R hR (s : Real) q B.radius hq
    have hmem := hwindow hq_new
    change paraTime tau R q' ∈ D.carrier at hmem
    simpa only [q', paraTime_back (ne_of_gt hR)] using hmem
  · intro q hq x hx
    let q' : Real := paraBack tau R q
    have hq_new : q' ∈ Set.Icc (s - B.radius ^ 2) (s : Real) :=
      backWindow tau R hR (s : Real) q B.radius hq
    have hset := backBall_setAt (I := I) S tau R hR htau s B q'
    rw [paraTime_back (ne_of_gt hR)] at hset
    have hx_new : x ∈ B.setAt q' := by
      rw [← hset]
      exact hx
    have hold := hcurv q' hq_new x hx_new
    unfold FlowMetricBall.rmNormSq at hold ⊢
    rw [paraRmNormSq, paraTime_back (ne_of_gt hR)] at hold
    change (B.radius / Real.sqrt R) ^ 4 *
      Tensor0SBundle.normSq0S (I := I) (S.base.metric q) x 4
        (S.base.rm04 q x) ≤ 1
    have hscale :
        (B.radius / Real.sqrt R) ^ 4 = B.radius ^ 4 * R⁻¹ ^ 2 := by
      rw [div_pow]
      have hsqrt : Real.sqrt R ^ 4 = R ^ 2 := by
        calc
          Real.sqrt R ^ 4 = (Real.sqrt R ^ 2) ^ 2 := by ring
          _ = R ^ 2 := by rw [Real.sq_sqrt hR.le]
      rw [hsqrt, div_eq_mul_inv, inv_pow]
    rw [hscale]
    simpa only [mul_assoc] using hold



omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] in
theorem backBall_para
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s)) :
    backBall S tau R hR htau s (paraBall S tau R hR htau s B) = B := by
  cases B with
  | mk center radius radius_pos =>
      simp only [paraBall, backBall]
      congr
      field_simp [ne_of_gt (Real.sqrt_pos.2 hR)]


omit [SigmaCompactSpace M] in
theorem paraBall_rm_iff
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s)) :
    (paraBall S tau R hR htau s B).IsRmControlled ↔ B.IsRmControlled := by
  constructor
  · intro h
    have hback := backBall_rm (I := I) S tau R hR htau s
      (paraBall S tau R hR htau s B) h
    rw [backBall_para (I := I) S tau R hR htau s B] at hback
    exact hback
  · exact paraBall_rm (I := I) S tau R hR htau s B



omit [CompleteSpace E] in
theorem paraBall_kappa_iff
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (s : (paraInterval D tau R hR htau).FlowTime)
    (B : FlowMetricBall S (paraFlowTime tau R hR htau s))
    (kappa : Real) :
    (paraBall S tau R hR htau s B).IsKappaNoncollapsed kappa ↔
      B.IsKappaNoncollapsed kappa := by
  constructor
  · intro h
    have hback := backBall_kappa (I := I) S tau R hR htau s
      (paraBall S tau R hR htau s B) kappa h
    rw [backBall_para (I := I) S tau R hR htau s B] at hback
    exact hback
  · exact paraBall_kappa (I := I) S tau R hR htau s B kappa



theorem para_noncollapse
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (kappa rho : Real)
    (hS : KappaNoncollapsedBelowScale S kappa rho) :
    KappaNoncollapsedBelowScale
      (paraSolution (I := I) S tau R hR htau) kappa
      (Real.sqrt R * rho) := by
  refine ⟨mul_pos (Real.sqrt_pos.2 hR) hS.1, ?_⟩
  intro s B hscale hRm
  let B₀ := backBall S tau R hR htau s B
  have hradius : B₀.radius ≤ rho := by
    dsimp [B₀, backBall]
    apply (div_le_iff₀ (Real.sqrt_pos.2 hR)).2
    simpa only [mul_comm] using hscale
  have hRm₀ : B₀.IsRmControlled :=
    backBall_rm (I := I) S tau R hR htau s B hRm
  have hk₀ := hS.2 (paraFlowTime tau R hR htau s) B₀ hradius hRm₀
  have hk := paraBall_kappa (I := I) S tau R hR htau s B₀ kappa hk₀
  rw [paraBall_back (I := I) S tau R hR htau s B] at hk
  exact hk



theorem para_no_local
    (S : SolutionOn (I := I) (M := M) D)
    (tau R : Real) (hR : 0 < R) (htau : tau ∈ D.carrier)
    (rho : Real) (hS : NoLocalCollapsing S rho) :
    NoLocalCollapsing (paraSolution (I := I) S tau R hR htau)
      (Real.sqrt R * rho) := by
  rcases hS with ⟨kappa, hkappa, hbelow⟩
  exact ⟨kappa, hkappa,
    para_noncollapse (I := I) S tau R hR htau kappa rho hbelow⟩

end Perelman

end DifferentialGeometry.PDE.RicciFlow

end
