import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SubcriticalSmallTime
import DifferentialGeometry.Analysis.Calculus.BallRetraction

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

section Recentre

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

noncomputable def recenteredBallRetraction (c : X) (R : ℝ) (v : X) : X :=
  c + ballRetraction R (v - c)

theorem recenteredBallRetraction_lipschitzWith {R : ℝ} (hR : 0 ≤ R) (c : X) :
    LipschitzWith 1 (recenteredBallRetraction c R) := by
  have hshift : LipschitzWith 1 (fun v : X => v - c) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [NNReal.coe_one, one_mul, dist_sub_right]
  have hadd : LipschitzWith 1 (fun w : X => c + w) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [NNReal.coe_one, one_mul, dist_add_left]
  have hcomp :
      LipschitzWith (1 * (1 * 1))
        (fun v : X => c + ballRetraction R (v - c)) :=
    hadd.comp ((lipschitzWith_ballRetraction (X := X) hR).comp hshift)
  simpa [recenteredBallRetraction] using hcomp

theorem recenteredBallRetraction_mapsTo {R : ℝ} (hR : 0 ≤ R) (c : X) :
    Set.MapsTo (recenteredBallRetraction c R) Set.univ (Metric.closedBall c R) := by
  intro v _
  rw [Metric.mem_closedBall, dist_eq_norm, recenteredBallRetraction,
    add_comm c _, add_sub_cancel_right]
  exact ballRetraction_mem_closedBall hR (v - c)

theorem recenteredBallRetraction_eq_self_of_mem {R : ℝ} {c v : X}
    (hv : v ∈ Metric.closedBall c R) :
    recenteredBallRetraction c R v = v := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hv
  rw [recenteredBallRetraction, ballRetraction_eq_self_of_mem hv, add_sub_cancel]

end Recentre

section Truncation

variable {N : tensorHs (I := I) (M := M) g r s (a + 1) →
    tensorHs (I := I) (M := M) g r s a}

def truncatedNonlin (N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a)
    (u₀' : tensorHs (I := I) (M := M) g r s (a + 1)) (R : ℝ) :
    tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a :=
  fun v => N (recenteredBallRetraction u₀' R v)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem truncatedNonlin_eq_of_mem
    {u₀' : tensorHs (I := I) (M := M) g r s (a + 1)} {R : ℝ}
    {v : tensorHs (I := I) (M := M) g r s (a + 1)}
    (hv : v ∈ Metric.closedBall u₀' R) :
    truncatedNonlin (I := I) (M := M) N u₀' R v = N v := by
  rw [truncatedNonlin, recenteredBallRetraction_eq_self_of_mem hv]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem truncatedNonlin_lipschitzWith {L_R : ℝ≥0}
    {u₀' : tensorHs (I := I) (M := M) g r s (a + 1)} {R : ℝ} (hR : 0 ≤ R)
    (hN : LipschitzOnWith L_R N (Metric.closedBall u₀' R)) :
    LipschitzWith L_R (truncatedNonlin (I := I) (M := M) N u₀' R) := by
  have hρ : LipschitzOnWith 1 (recenteredBallRetraction u₀' R) Set.univ :=
    lipschitzOnWith_univ.mpr
      (recenteredBallRetraction_lipschitzWith (X := _) hR u₀')
  have hmaps := recenteredBallRetraction_mapsTo (X := _) hR u₀'
  have hcomp : LipschitzOnWith (L_R * 1)
      (N ∘ recenteredBallRetraction u₀' R) Set.univ :=
    hN.comp hρ hmaps
  rw [mul_one] at hcomp
  have : LipschitzWith L_R (N ∘ recenteredBallRetraction u₀' R) :=
    lipschitzOnWith_univ.mp hcomp
  exact this

end Truncation

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinear_strong_existence_truncated_smallTime_ofCompact
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T_R : ℝ, 0 < T_R ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTR : T ≤ T_R) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce = nemytskiiHa1 (I := I) (M := M)
              (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀
                  gforce) :=
  quasilinear_strong_existence_smallTime (I := I) (M := M)
    (h_compact := h_compact) u₀
    (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_truncated_eqOn_ball
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    {u₀' : tensorHs (I := I) (M := M) g r s (a + 1)}
    (hN : LipschitzOnWith L_R N (Metric.closedBall u₀' R))
    (field : timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T)
    (hball : ∀ᵐ t ∂(timeMeasure T), field t ∈ Metric.closedBall u₀' R) :
    nemytskiiHa1 (I := I) (M := M)
        (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN) field =ᵐ[timeMeasure T]
      fun t => N (field t) := by
  have hcoe := nemytskiiHa1_coeFn (I := I) (M := M)
    (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN) field
  filter_upwards [hcoe, hball] with t ht htmem
  rw [ht, truncatedNonlin_eq_of_mem (I := I) (M := M) htmem]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T_R : ℝ, 0 < T_R ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTR : T ≤ T_R) (hT1 : T ≤ 1)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
        (_hfix : gforce = nemytskiiHa1 (I := I) (M := M)
            (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce))
        (_hstay : ∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce t ∈
              Metric.closedBall
                (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                  (show (a + 1) ≤ a + 2 by linarith) u₀) R),
      ∃ u : MaxRegSolutionSpace (I := I) (M := M) a T,
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => N (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              a hT hT1 u₀ gforce t)) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀
                  gforce) := by
  refine ⟨smallTimeHorizon L_R, smallTimeHorizon_pos L_R, ?_⟩
  intro T hT hTR hT1 gforce hfix hstay
  refine ⟨maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce, rfl, ?_, ?_, ?_⟩
  · conv_lhs => rw [hfix]
    exact nemytskiiHa1_truncated_eqOn_ball (I := I) (M := M) hR hN
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) hstay
  · exact maxRegDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT hT1 u₀ gforce
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T) hT hT1 u₀ gforce]
    exact congrArg₂ (· + ·) rfl hfix

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
