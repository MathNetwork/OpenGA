import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ForcingFixedPoint

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

section Nemytskii

variable {L : ℝ≥0}
  {N : tensorHs (I := I) (M := M) g r s (a + 1) →
    tensorHs (I := I) (M := M) g r s a}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem memLp_comp_nemytskiiHa1 (hN : LipschitzWith L N)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T) :
    MemLp (fun t => N (f t)) 2 (timeMeasure T) := by
  have hshift : LipschitzWith L (fun x => N x - N 0) := by
    have hsubL := hN.sub (LipschitzWith.const (N 0))
    rwa [add_zero] at hsubL
  have hshift0 : (fun x => N x - N 0) (0 : tensorHs (I := I) (M := M) g r s
      (a + 1)) = 0 := by simp
  have hcomp : MemLp ((fun x => N x - N 0) ∘ fun t => f t) 2 (timeMeasure T) :=
    hshift.comp_memLp hshift0 (Lp.memLp f)
  have hconst : MemLp (fun _ : ℝ => N 0) 2 (timeMeasure T) :=
    memLp_const (N 0)
  have hsum : MemLp (fun t => (N (f t) - N 0) + N 0) 2 (timeMeasure T) :=
    hcomp.add hconst
  have hfun : (fun t => N (f t)) =
      fun t => (N (f t) - N 0) + N 0 := by
    funext t; abel
  rw [hfun]
  exact hsum

def nemytskiiHa1 (hN : LipschitzWith L N) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun f => (memLp_comp_nemytskiiHa1 (I := I) (M := M) hN f).toLp (fun t => N (f t))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_coeFn (hN : LipschitzWith L N)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T) :
    nemytskiiHa1 (I := I) (M := M) hN f =ᵐ[timeMeasure T] fun t => N (f t) :=
  (memLp_comp_nemytskiiHa1 (I := I) (M := M) hN f).coeFn_toLp

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_dist_sq_le (hN : LipschitzWith L N)
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T) :
    ‖nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f'‖ ^ 2 ≤
      (L : ℝ) ^ 2 * ‖f - f'‖ ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral, TimeSobolev.norm_sq_eq_integral,
    ← MeasureTheory.integral_const_mul]
  have hdiff : ⇑(nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f') =ᵐ[timeMeasure T]
      fun t => N (f t) - N (f' t) := by
    have hsub := Lp.coeFn_sub (nemytskiiHa1 (I := I) (M := M) hN f)
      (nemytskiiHa1 (I := I) (M := M) hN f')
    have hf := nemytskiiHa1_coeFn (I := I) (M := M) hN f
    have hf' := nemytskiiHa1_coeFn (I := I) (M := M) hN f'
    filter_upwards [hsub, hf, hf'] with t ht htf htf'
    rw [ht, Pi.sub_apply, htf, htf']
  have hfdiff : ⇑(f - f') =ᵐ[timeMeasure T] fun t => f t - f' t :=
    Lp.coeFn_sub f f'
  have hint_fdiff : Integrable (fun t => ‖(f - f') t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (f - f'))).mp (Lp.memLp (f - f'))
  refine integral_mono_ae ?_ ?_ ?_
  · exact (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f'))).mp
      (Lp.memLp (nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f'))
  · exact hint_fdiff.const_mul ((L : ℝ) ^ 2)
  · filter_upwards [hdiff, hfdiff] with t ht htf
    rw [ht]
    have hlip : ‖N (f t) - N (f' t)‖ ≤ (L : ℝ) * ‖f t - f' t‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hN.dist_le_mul (f t) (f' t)
    have hnn : 0 ≤ ‖N (f t) - N (f' t)‖ := norm_nonneg _
    have hsq : ‖N (f t) - N (f' t)‖ ^ 2 ≤ ((L : ℝ) * ‖f t - f' t‖) ^ 2 := by
      have hrhs_nn : 0 ≤ (L : ℝ) * ‖f t - f' t‖ :=
        mul_nonneg L.coe_nonneg (norm_nonneg _)
      nlinarith [hlip, hnn, hrhs_nn]
    calc ‖N (f t) - N (f' t)‖ ^ 2
        ≤ ((L : ℝ) * ‖f t - f' t‖) ^ 2 := hsq
      _ = (L : ℝ) ^ 2 * ‖(f - f') t‖ ^ 2 := by rw [htf, mul_pow]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_lipschitzWith (hN : LipschitzWith L N) :
    LipschitzWith L (nemytskiiHa1 (I := I) (M := M) (T := T) hN) := by
  refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hsq := nemytskiiHa1_dist_sq_le (I := I) (M := M) hN f f'
  have hrhs_nn : 0 ≤ (L : ℝ) * ‖f - f'‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
  have hsq' : ‖nemytskiiHa1 (I := I) (M := M) hN f -
        nemytskiiHa1 (I := I) (M := M) hN f'‖ ^ 2 ≤
      ((L : ℝ) * ‖f - f'‖) ^ 2 := by
    rw [mul_pow]; exact hsq
  have h := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hrhs_nn] at h

end Nemytskii

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelSolFieldHa1_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce -
        maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce' =
      maximalRegularitySolFieldHa1 (I := I) (M := M) a hT hT1
        (gforce - gforce') := by
  rw [maximalRegularitySolFieldHa1_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 gforce gforce']
  rw [maxRegDuhamelSolFieldHa1, maxRegDuhamelSolFieldHa1]
  abel

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maxRegDuhamelSolFieldHa1_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce -
        maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce'‖ ≤
      2 * Real.sqrt T * ‖gforce - gforce'‖ := by
  rw [maxRegDuhamelSolFieldHa1_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 u₀ gforce gforce']
  exact maximalRegularitySolFieldHa1_norm_le (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 (gforce - gforce')

section FixedPoint

def quasilinearDuhamelMapHa1 (a : ℝ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun gforce => nemytskiiHa1 (I := I) (M := M) hN
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem quasilinearDuhamelMapHa1_apply (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    quasilinearDuhamelMapHa1 (I := I) (M := M) a hT hT1 u₀ hN gforce =
      nemytskiiHa1 (I := I) (M := M) hN
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) :=
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinearDuhamelMapHa1_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    dist (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT hT1 u₀ hN gforce)
        (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT hT1 u₀ hN gforce') ≤
      (L : ℝ) * (2 * Real.sqrt T) * dist gforce gforce' := by
  have hnem := (nemytskiiHa1_lipschitzWith (I := I) (M := M) hN).dist_le_mul
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce)
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce')
  have hfield : dist
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce)
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce') ≤
        (2 * Real.sqrt T) * dist gforce gforce' := by
    rw [dist_eq_norm, dist_eq_norm]
    exact maxRegDuhamelSolFieldHa1_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 u₀ gforce gforce'
  calc dist
        (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT hT1 u₀ hN gforce)
        (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT hT1 u₀ hN gforce')
      ≤ (L : ℝ) * dist
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce)
          (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀
            gforce') := hnem
    _ ≤ (L : ℝ) * ((2 * Real.sqrt T) * dist gforce gforce') :=
        mul_le_mul_of_nonneg_left hfield L.coe_nonneg
    _ = (L : ℝ) * (2 * Real.sqrt T) * dist gforce gforce' := by ring

def smallTimeHorizon (L : ℝ≥0) : ℝ :=
  min 1 (1 / (4 * ((L : ℝ) + 1) ^ 2))

theorem smallTimeHorizon_pos (L : ℝ≥0) : 0 < smallTimeHorizon L := by
  refine lt_min one_pos ?_
  have hpos : (0 : ℝ) < 4 * ((L : ℝ) + 1) ^ 2 := by positivity
  positivity

theorem smallTimeHorizon_le_one (L : ℝ≥0) : smallTimeHorizon L ≤ 1 :=
  min_le_left _ _

theorem smallTime_contraction_const_lt_one {L : ℝ≥0} {T : ℝ}
    (_hT : 0 < T) (hTL : T ≤ smallTimeHorizon L) :
    (L : ℝ) * (2 * Real.sqrt T) < 1 := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hLp1_pos : (0 : ℝ) < (L : ℝ) + 1 := by linarith
  have hTbd : T ≤ 1 / (4 * ((L : ℝ) + 1) ^ 2) :=
    le_trans hTL (min_le_right _ _)
  have hden_pos : (0 : ℝ) < 2 * ((L : ℝ) + 1) := by linarith
  have hsqrtT_le : Real.sqrt T ≤ 1 / (2 * ((L : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (2 * ((L : ℝ) + 1)) =
      Real.sqrt ((1 / (2 * ((L : ℝ) + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hTbd ?_)
    have heq : (1 : ℝ) / (4 * ((L : ℝ) + 1) ^ 2) =
        (1 / (2 * ((L : ℝ) + 1))) ^ 2 := by
      rw [div_pow, one_pow, mul_pow]
      norm_num
    rw [heq]
  have hsqrtT_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  calc (L : ℝ) * (2 * Real.sqrt T)
      = 2 * (L : ℝ) * Real.sqrt T := by ring
    _ ≤ 2 * (L : ℝ) * (1 / (2 * ((L : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left hsqrtT_le (by positivity)
    _ = (L : ℝ) / ((L : ℝ) + 1) := by
        rw [mul_one_div, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    _ < 1 := by
        rw [div_lt_one hLp1_pos]; linarith

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinearDuhamelMapHa1_contracting (hT : 0 < T)
    {L : ℝ≥0} (hTL : T ≤ smallTimeHorizon L)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) :
    ContractingWith
      ⟨(L : ℝ) * (2 * Real.sqrt T),
        mul_nonneg L.coe_nonneg (by positivity)⟩
      (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT
        (le_trans hTL (smallTimeHorizon_le_one L)) u₀ hN) := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using smallTime_contraction_const_lt_one (L := L) (T := T) hT hTL
  · refine LipschitzWith.of_dist_le_mul (fun gforce gforce' => ?_)
    have h := quasilinearDuhamelMapHa1_dist_le (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT
      (le_trans hTL (smallTimeHorizon_le_one L)) u₀ hN gforce gforce'
    simpa only [NNReal.coe_mk] using h

end FixedPoint

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinear_strong_existence_smallTime {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) :
    ∃ T_L : ℝ, 0 < T_L ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTL : T ≤ T_L) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce = nemytskiiHa1 (I := I) (M := M) hN
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M) hN
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀
                  gforce) := by
  refine ⟨smallTimeHorizon L, smallTimeHorizon_pos L, ?_⟩
  intro T hT hTL hT1
  have hcontr := quasilinearDuhamelMapHa1_contracting (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hTL u₀ hN
  set gStar := ContractingWith.fixedPoint
    (quasilinearDuhamelMapHa1 (I := I) (M := M) a hT hT1 u₀ hN) hcontr
    with hgStar_def
  have hgStar_fix :
      quasilinearDuhamelMapHa1 (I := I) (M := M) a hT hT1 u₀ hN gStar =
        gStar :=
    ContractingWith.fixedPoint_isFixedPt hcontr
  have hgStar_eq : gStar = nemytskiiHa1 (I := I) (M := M) hN
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gStar) := by
    rw [← quasilinearDuhamelMapHa1_apply (I := I) (M := M) (a := a) hT hT1 u₀ hN
      gStar, hgStar_fix]
  refine ⟨maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gStar,
    gStar, rfl, hgStar_eq, ?_, ?_⟩
  · exact maxRegDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT hT1 u₀ gStar
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T) hT hT1 u₀ gStar]
    exact congrArg₂ (· + ·) rfl hgStar_eq

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
