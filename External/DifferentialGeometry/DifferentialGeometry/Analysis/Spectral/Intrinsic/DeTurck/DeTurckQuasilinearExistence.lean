import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SubcriticalSmallTime
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FieldHa1TimeSupTrace


noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem timeL2_norm_le_of_ae_mixed_bound
    {T : ℝ} {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
    (h : timeL2 X T) (p : timeL2 Y T) (q : timeL2 Z T) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖h t‖ ≤ A * ‖p t‖ + B * ‖q t‖) :
    ‖h‖ ≤ A * ‖p‖ + B * ‖q‖ := by

  set Pf : ℝ → ℝ := fun t => ‖(p : ℝ → Y) t‖ with hPf
  set Qf : ℝ → ℝ := fun t => ‖(q : ℝ → Z) t‖ with hQf
  have hPm : AEStronglyMeasurable Pf (timeMeasure T) :=
    (Lp.aestronglyMeasurable p).norm
  have hQm : AEStronglyMeasurable Qf (timeMeasure T) :=
    (Lp.aestronglyMeasurable q).norm
  have hAPm : AEStronglyMeasurable (A • Pf) (timeMeasure T) := hPm.const_smul A
  have hBQm : AEStronglyMeasurable (B • Qf) (timeMeasure T) := hQm.const_smul B

  have hmono : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hbound] with t ht
    have happ : (A • Pf + B • Qf) t = A * ‖p t‖ + B * ‖q t‖ := by
      simp [hPf, hQf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hge : 0 ≤ (A • Pf + B • Qf) t := by
      rw [happ]; exact add_nonneg (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hge, happ]
    exact ht

  have htri : eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T) :=
    eLpNorm_add_le hAPm hBQm (by norm_num)
  have hscaleP : eLpNorm (A • Pf) 2 (timeMeasure T) =
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA]
  have hscaleQ : eLpNorm (B • Qf) 2 (timeMeasure T) =
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hB]

  have hfinal : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    calc eLpNorm (h : ℝ → X) 2 (timeMeasure T)
        ≤ eLpNorm (A • Pf) 2 (timeMeasure T) + eLpNorm (B • Qf) 2 (timeMeasure T) :=
          hmono.trans htri
      _ = _ := by rw [hscaleP, hscaleQ]
  have hp_top : eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp p).2.ne
  have hq_top : eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp q).2.ne
  have hnormh : ‖h‖ = (eLpNorm (h : ℝ → X) 2 (timeMeasure T)).toReal := rfl
  have hnormp : ‖p‖ = (eLpNorm (p : ℝ → Y) 2 (timeMeasure T)).toReal := rfl
  have hnormq : ‖q‖ = (eLpNorm (q : ℝ → Z) 2 (timeMeasure T)).toReal := rfl
  have hrhs_ne : ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top⟩
  rw [hnormh, hnormp, hnormq]
  refine le_trans (ENNReal.toReal_mono hrhs_ne hfinal) ?_
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    ENNReal.toReal_ofReal hB]

variable {g₀ g_bg : SmoothRiemannianMetric I M}

omit [BoundarylessManifold I M] in
theorem timeL2Inclusion_maxRegDuhamelSolField {a : ℝ} {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (T := T) a hT hT1 u₀ gforce) =
      maxRegDuhamelSolFieldHa1 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (T := T) a hT hT1 u₀ gforce := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)]

  rw [maxRegDuhamelSolField, maxRegDuhamelSolFieldHa1,
    timeModeCoeff_add (I := I) (M := M), timeModeCoeff_add (I := I) (M := M),
    maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT.le u₀ i,
    maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT.le u₀ i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le gforce i,
    maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce i]

def deTurckLipConst (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ≥0 :=
  (deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose

theorem deTurckSobolevNHa2_lipschitzWith_lipConst (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    LipschitzWith (deTurckLipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
      (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a) :=
  (deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose_spec

def deTurckTimeNemytskii (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (a := (a : ℝ)) (T := T)
    (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super)

def deTurckLipConstSymm (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ≥0 :=
  (deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose

theorem deTurckSobolevNHa2Symm_lipschitzWith_lipConst (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    LipschitzWith (deTurckLipConstSymm (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a) :=
  (deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose_spec

theorem deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ C₁ C₂ : ℝ≥0, ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a u -
          deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖ :=
  deTurckSobolevNonlinearitySymm_mixed_lipschitz_pointwise (I := I) (M := M) g₀ g_bg a ha_super

omit [BoundarylessManifold I M] in
theorem norm_maxRegDuhamelSolField_zero_le {a : ℝ} {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T) :
    ‖maxRegDuhamelSolField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (T := T) a hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2)) F‖ ≤ (1 + T) * ‖F‖ := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  rw [maxRegDuhamelSolField]
  refine le_trans (norm_add_le _ _) ?_
  have hhom : ‖maxRegHomogeneousSolField (I := I) (M := M) a T
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2))‖ ≤ Real.sqrt T * ‖(0 : tensorHs
        (I := I) (M := M) g₀ 0 2 (a + 2))‖ :=
    maxRegHomogeneousSolField_norm_le (I := I) (M := M) (h_compact := h_compact) _ hT.le
  rw [norm_zero, mul_zero] at hhom
  have hreg : ‖maximalRegularitySolField (I := I) (M := M) a hT.le F‖ ≤ (1 + T) * ‖F‖ :=
    maximalRegularitySolField_norm_le (I := I) (M := M) (h_compact := h_compact) hT.le F
  have hhom0 : ‖maxRegHomogeneousSolField (I := I) (M := M) a T
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2))‖ = 0 :=
    le_antisymm hhom (norm_nonneg _)
  rw [hhom0, zero_add]
  exact hreg

omit [BoundarylessManifold I M] in
theorem maxRegDuhamelSolField_zero_zero {a : ℝ} {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    maxRegDuhamelSolField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (T := T) a hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 (a + 2))
        (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T) = 0 := by
  have h := norm_maxRegDuhamelSolField_zero_le (I := I) (M := M) (g₀ := g₀)
    hT hT1 (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 a) T)
  rw [norm_zero, mul_zero] at h
  exact norm_le_zero_iff.mp h

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskii_time_mixed_bound (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    {T : ℝ} (R : ℝ) (hR : 0 ≤ R)
    (f f' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    (hfR : ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) f) t‖ ≤ R)
    (hf'R : ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) f') t‖ ≤ R) :
    ‖nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip f -
      nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip f'‖ ≤
      (C₁ : ℝ) * R * ‖f - f'‖ +
        (C₂ : ℝ) *
          ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')‖ := by
  have hNf := nemytskii_coeFn (I := I) (M := M) hLip f
  have hNf' := nemytskii_coeFn (I := I) (M := M) hLip f'
  have hsub := Lp.coeFn_sub
    (nemytskii (I := I) (M := M) hLip f) (nemytskii (I := I) (M := M) hLip f')
  have hsubff' := Lp.coeFn_sub f f'
  have hinclf :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) f) =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) f
  have hinclf' :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) f') =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) f'
  have hincldiff :
      ⇑(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((f - f') t) :=
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)).coeFn_compLpL
      (p := 2) (μ := timeMeasure T) (f - f')
  have hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖(nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) (T := T) hLip f -
        nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) (T := T) hLip f') t‖ ≤
        (C₁ : ℝ) * R * ‖(f - f') t‖ +
          (C₂ : ℝ) *
            ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) t‖ := by
    filter_upwards [hsub, hNf, hNf', hsubff', hfR, hf'R, hinclf, hinclf', hincldiff]
      with t ht htf htf' htsubff' htfR htf'R htinclf htinclf' htincldiff
    rw [ht, Pi.sub_apply, htf, htf']
    have hsg := hsingle (f t) (f' t)
    have hmax_le :
        max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖
               ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖ ≤ R := by
      refine max_le ?_ ?_
      · rw [← htinclf]; exact htfR
      · rw [← htinclf']; exact htf'R
    have hstep1 :
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖
            * ‖(f t) - (f' t)‖ ≤ (C₁ : ℝ) * R * ‖(f t) - (f' t)‖ := by
      have hnn : (0 : ℝ) ≤ ‖(f t) - (f' t)‖ := norm_nonneg _
      have hmul : (C₁ : ℝ) * max _ _ ≤ (C₁ : ℝ) * R :=
        mul_le_mul_of_nonneg_left hmax_le C₁.coe_nonneg
      exact mul_le_mul_of_nonneg_right hmul hnn
    have hff'eq : ‖(f t) - (f' t)‖ = ‖(f - f') t‖ := by
      rw [htsubff', Pi.sub_apply]
    have hstep2 :
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((f t) - (f' t))‖
          = (C₂ : ℝ) * ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) t‖ := by
      rw [htincldiff, htsubff', Pi.sub_apply]
    calc ‖Nfun (f t) - Nfun (f' t)‖
        ≤ (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f t)‖
                         ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                            (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f' t)‖
            * ‖(f t) - (f' t)‖ +
          (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                        (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) ((f t) - (f' t))‖ := hsg
      _ ≤ (C₁ : ℝ) * R * ‖(f - f') t‖ +
            (C₂ : ℝ) * ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f')) t‖ := by
          refine add_le_add ?_ (le_of_eq hstep2)
          rw [← hff'eq]
          exact hstep1
  exact timeL2_norm_le_of_ae_mixed_bound (T := T)
    (nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip f -
      nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip f')
    (f - f')
    (timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (f - f'))
    (mul_nonneg C₁.coe_nonneg hR) C₂.coe_nonneg hbound

def nemytskiiMixedForcingMap (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  fun F => nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (a := (a : ℝ)) (T := T) hLip
    (maxRegDuhamelSolField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (T := T) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F)

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem nemytskiiMixedForcingMap_apply (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (F : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T) :
    nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 F =
      nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (a := (a : ℝ)) (T := T) hLip
        (maxRegDuhamelSolField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (T := T) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) F) :=
  rfl

omit [BoundarylessManifold I M] in
theorem nemytskiiMixedForcingMap_dist_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (F F' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hF : ‖F‖ ≤ ρ) (hF' : ‖F'‖ ≤ ρ) :
    ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 F -
        nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 F'‖ ≤
      ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖F - F'‖ := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set z : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) := 0 with hz
  set fF := maxRegDuhamelSolField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (T := T) (a : ℝ) hT hT1 z F with hfF
  set fF' := maxRegDuhamelSolField (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (T := T) (a : ℝ) hT hT1 z F' with hfF'
  set R := Real.sqrt (1 + T) * ρ with hR
  have hT_pos : (0 : ℝ) < 1 + T := by linarith
  have hsqrtnn : 0 ≤ Real.sqrt (1 + T) := Real.sqrt_nonneg _
  have hRnn : 0 ≤ R := mul_nonneg hsqrtnn hρ
  have hfR : ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) fF) t‖ ≤ R := by
    filter_upwards [maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le
      (I := I) (M := M) (g₀ := g₀) hT hT1 F] with t ht
    refine le_trans ht ?_
    rw [hR]
    exact mul_le_mul_of_nonneg_left hF hsqrtnn
  have hf'R : ∀ᵐ t ∂(timeMeasure T),
      ‖(timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) fF') t‖ ≤ R := by
    filter_upwards [maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le
      (I := I) (M := M) (g₀ := g₀) hT hT1 F'] with t ht
    refine le_trans ht ?_
    rw [hR]
    exact mul_le_mul_of_nonneg_left hF' hsqrtnn
  have hfield_dist : ‖fF - fF'‖ ≤ (1 + T) * ‖F - F'‖ :=
    maxRegDuhamelSolField_dist_le (I := I) (M := M) (h_compact := h_compact) (a := (a : ℝ))
      hT hT1 z F F'
  have hincl_dist :
      ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (fF - fF')‖ ≤
        2 * Real.sqrt T * ‖F - F'‖ := by
    rw [map_sub, timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1 z F,
      timeL2Inclusion_maxRegDuhamelSolField (I := I) (M := M) hT hT1 z F']
    exact maxRegDuhamelSolFieldHa1_dist_le (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) hT hT1 z F F'
  have hmain := nemytskii_time_mixed_bound (I := I) (M := M) g₀ a hLip hsingle R hRnn fF fF'
    hfR hf'R
  calc ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 F -
          nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1 F'‖
      = ‖nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (a := (a : ℝ)) (T := T) hLip fF -
          nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (a := (a : ℝ)) (T := T) hLip fF'‖ := by
        rw [nemytskiiMixedForcingMap_apply, nemytskiiMixedForcingMap_apply]
    _ ≤ (C₁ : ℝ) * R * ‖fF - fF'‖ +
          (C₂ : ℝ) * ‖timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (fF - fF')‖ := hmain
    _ ≤ (C₁ : ℝ) * R * ((1 + T) * ‖F - F'‖) +
          (C₂ : ℝ) * (2 * Real.sqrt T * ‖F - F'‖) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hfield_dist (mul_nonneg C₁.coe_nonneg hRnn)
        · exact mul_le_mul_of_nonneg_left hincl_dist C₂.coe_nonneg
    _ = ((C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T)) * ‖F - F'‖ := by
        rw [hR]; ring

omit [BoundarylessManifold I M] in
private theorem norm_nemytskiiMixedForcingMap_zero_le (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    {L : ℝ≥0}
    {Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
        (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)‖ ≤
      Real.sqrt T * ‖Nfun (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
  rw [nemytskiiMixedForcingMap_apply,
    maxRegDuhamelSolField_zero_zero (I := I) (M := M) (g₀ := g₀) hT hT1]
  refine timeL2_norm_le_of_ae_bound _ (norm_nonneg _) ?_
  have hcoe := nemytskii_coeFn (I := I) (M := M) hLip
    (0 : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
  have hzero := Lp.coeFn_zero (E := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (p := 2) (μ := timeMeasure T)
  filter_upwards [hcoe, hzero] with t ht htz
  rw [ht, htz, Pi.zero_apply]

def deTurckForceBallRadiusSymm (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ :=
  1 / (16 * (((deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M)
    (g₀ := g₀) (g_bg := g_bg) a ha_super).choose : ℝ) + 1))

omit [BoundarylessManifold I M] in
theorem nemytskii_sol_const
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    (Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hLip : LipschitzWith L Nfun)
    (C₁ C₂ : ℝ≥0) (D : ℝ) (hD : 0 ≤ D)
    (hzero : ‖Nfun (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ ≤ D)
    (hsingle : ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖) :
    ∃ T₀ : ℝ,
      T₀ = min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
        ((1 / (16 * ((C₁ : ℝ) + 1)) / (2 * (D + 1))) ^ 2)) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => Nfun (maxRegDuhamelSolField (I := I) (M := M)
                (g := g₀) (r := 0) (s := 2) (T := T) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (T := T) (a : ℝ)
                (maxRegDuhamelSolField (I := I) (M := M)
                  (g := g₀) (r := 0) (s := 2) (T := T) (a : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce) + gforce ∧
          ‖gforce‖ ≤ 1 / (16 * ((C₁ : ℝ) + 1)) := by
  classical
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  set M₀ := ‖Nfun (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ with hM₀def
  have hM₀ : 0 ≤ M₀ := norm_nonneg _
  have hM₀D : M₀ ≤ D := by simpa only [hM₀def] using hzero
  have hD1pos : 0 < D + 1 := by linarith

  set ρ : ℝ := 1 / (16 * ((C₁ : ℝ) + 1)) with hρdef
  have hC₁p : (0 : ℝ) < 16 * ((C₁ : ℝ) + 1) := by positivity
  have hρpos : 0 < ρ := by rw [hρdef]; positivity

  set T₀ : ℝ := min 1 (min (1 / (64 * ((C₂ : ℝ) + 1) ^ 2))
    ((ρ / (2 * (D + 1))) ^ 2)) with hT₀def
  have hT₀pos : 0 < T₀ := by
    refine lt_min one_pos (lt_min ?_ ?_)
    · positivity
    · have : 0 < ρ / (2 * (D + 1)) := by positivity
      positivity
  refine ⟨T₀, ?_, hT₀pos, ?_⟩
  · rw [hT₀def, hρdef]
  intro T hT hTT₀ hT1

  have hT_le1 : T ≤ 1 := hT1
  have hT_lo : T ≤ 1 / (64 * ((C₂ : ℝ) + 1) ^ 2) :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hT_stay : T ≤ (ρ / (2 * (D + 1))) ^ 2 :=
    le_trans hTT₀ (le_trans (min_le_right _ _) (min_le_right _ _))

  set Λ : ℝ := (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) + (C₂ : ℝ) * (2 * Real.sqrt T) with hΛdef
  have hΛnn : 0 ≤ Λ := by
    rw [hΛdef]; have : (0:ℝ) ≤ 1 + T := by linarith
    positivity

  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  have hsqrt1T_le : Real.sqrt (1 + T) ≤ 1 + T := by
    have h1le : (1 : ℝ) ≤ 1 + T := by linarith
    calc Real.sqrt (1 + T) ≤ Real.sqrt ((1 + T) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 + T)])
      _ = 1 + T := Real.sqrt_sq (by linarith)
  have harm1 : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) ≤ 1 / 4 := by
    have hle : (C₁ : ℝ) * (Real.sqrt (1 + T)) * ρ * (1 + T) ≤ (C₁ : ℝ) * 2 * ρ * 2 := by
      have hc1 : (0:ℝ) ≤ (C₁:ℝ) := C₁.coe_nonneg
      have h0 : (0:ℝ) ≤ 1 + T := by linarith
      have hsqrt2 : Real.sqrt (1 + T) ≤ 2 := le_trans hsqrt1T_le h1T
      gcongr
    refine le_trans hle ?_
    rw [hρdef]
    rw [show (C₁ : ℝ) * 2 * (1 / (16 * ((C₁ : ℝ) + 1))) * 2 =
        (C₁ : ℝ) / ((C₁ : ℝ) + 1) * (4 / 16) by field_simp; ring]
    have hfrac : (C₁ : ℝ) / ((C₁ : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [C₁.coe_nonneg]
    nlinarith [hfrac, div_nonneg C₁.coe_nonneg (by positivity : (0:ℝ) ≤ (C₁:ℝ)+1)]

  have hsqrtT : Real.sqrt T ≤ 1 / (8 * ((C₂ : ℝ) + 1)) := by
    rw [show (1 : ℝ) / (8 * ((C₂ : ℝ) + 1)) =
        Real.sqrt ((1 / (8 * ((C₂ : ℝ) + 1))) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt (le_trans hT_lo ?_)
    rw [div_pow, one_pow, mul_pow]; norm_num
  have harm2 : (C₂ : ℝ) * (2 * Real.sqrt T) ≤ 1 / 4 := by
    have hc2 : (0:ℝ) ≤ (C₂:ℝ) := C₂.coe_nonneg
    calc (C₂ : ℝ) * (2 * Real.sqrt T)
        = 2 * (C₂ : ℝ) * Real.sqrt T := by ring
      _ ≤ 2 * (C₂ : ℝ) * (1 / (8 * ((C₂ : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left hsqrtT (by positivity)
      _ = (C₂ : ℝ) / ((C₂ : ℝ) + 1) * (1 / 4) := by
          have hne : ((C₂ : ℝ) + 1) ≠ 0 := by positivity
          field_simp
          ring
      _ ≤ 1 / 4 := by
          have hfrac : (C₂ : ℝ) / ((C₂ : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [hfrac, div_nonneg hc2 (by positivity : (0:ℝ) ≤ (C₂:ℝ)+1)]
  have hΛ_le : Λ ≤ 1 / 2 := by rw [hΛdef]; linarith
  have hΛ_lt : Λ < 1 := by linarith

  set Ψ := nemytskiiMixedForcingMap (I := I) (M := M) g₀ a hLip hT hT1
    with hΨdef
  set z₀ : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T := 0 with hz₀
  set ρt := recenteredBallRetraction (z₀) ρ with hρtdef
  set Ψ' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T →
      timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T := fun F => Ψ (ρt F) with hΨ'def

  have hΨ_ball : ∀ (F F' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
      ‖F‖ ≤ ρ → ‖F'‖ ≤ ρ → ‖Ψ F - Ψ F'‖ ≤ Λ * ‖F - F'‖ := by
    intro F F' hF hF'
    have h := nemytskiiMixedForcingMap_dist_le (I := I) (M := M) g₀ a hLip hsingle
      hT hT1 hρpos.le F F' hF hF'
    rw [hΛdef]
    exact h

  have hρt_mem : ∀ F, ρt F ∈ Metric.closedBall z₀ ρ := fun F =>
    recenteredBallRetraction_mapsTo (X := _) hρpos.le z₀ (Set.mem_univ F)
  have hρt_norm : ∀ F, ‖ρt F‖ ≤ ρ := by
    intro F
    have := hρt_mem F
    rw [Metric.mem_closedBall, hz₀, dist_zero_right] at this
    exact this
  have hρt_lip : LipschitzWith 1 ρt := recenteredBallRetraction_lipschitzWith hρpos.le z₀

  have hΨ'_lip : ∀ (F F' : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
      ‖Ψ' F - Ψ' F'‖ ≤ Λ * ‖F - F'‖ := by
    intro F F'
    have hbase := hΨ_ball (ρt F) (ρt F') (hρt_norm F) (hρt_norm F')
    refine le_trans hbase ?_
    have hretr : ‖ρt F - ρt F'‖ ≤ ‖F - F'‖ := by
      have := hρt_lip.dist_le_mul F F'
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at this
      exact this
    exact mul_le_mul_of_nonneg_left hretr hΛnn

  have hcontr : ContractingWith Λ.toNNReal Ψ' := by
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hΛnn]
      simpa using hΛ_lt
    · refine LipschitzWith.of_dist_le_mul (fun F F' => ?_)
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hΛnn]
      exact hΨ'_lip F F'

  set Fstar := ContractingWith.fixedPoint Ψ' hcontr with hFstar_def
  have hFstar_fix : Ψ' Fstar = Fstar := ContractingWith.fixedPoint_isFixedPt hcontr

  have hΨ0 : ‖Ψ z₀‖ ≤ Real.sqrt T * M₀ := by
    rw [hΨdef, hz₀, hM₀def]
    exact norm_nemytskiiMixedForcingMap_zero_le (I := I) (M := M) g₀ a hLip hT hT1
  have hsqrtTM : Real.sqrt T * M₀ ≤ ρ / 2 := by
    have hsqrtT_le : Real.sqrt T ≤ ρ / (2 * (D + 1)) := by
      rw [show ρ / (2 * (D + 1)) = Real.sqrt ((ρ / (2 * (D + 1))) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hT_stay
    calc Real.sqrt T * M₀ ≤ (ρ / (2 * (D + 1))) * M₀ :=
          mul_le_mul_of_nonneg_right hsqrtT_le hM₀
      _ ≤ (ρ / (2 * (D + 1))) * (D + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ρ / 2 := by
          have hne : (D + 1) ≠ 0 := ne_of_gt hD1pos
          field_simp
  have hz₀norm : ‖z₀‖ = 0 := by rw [hz₀, norm_zero]

  have hΨ_stay : ∀ G, ‖G‖ ≤ ρ → ‖Ψ G‖ ≤ ρ := by
    intro G hG
    have hball := hΨ_ball G z₀ hG (by rw [hz₀norm]; exact hρpos.le)
    have hGz : ‖G - z₀‖ = ‖G‖ := by rw [hz₀, sub_zero]
    rw [hGz] at hball
    calc ‖Ψ G‖ = ‖(Ψ G - Ψ z₀) + Ψ z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖Ψ G - Ψ z₀‖ + ‖Ψ z₀‖ := norm_add_le _ _
      _ ≤ Λ * ‖G‖ + Real.sqrt T * M₀ := add_le_add hball hΨ0
      _ ≤ (1 / 2) * ρ + ρ / 2 := by
          refine add_le_add ?_ hsqrtTM
          calc Λ * ‖G‖ ≤ Λ * ρ := mul_le_mul_of_nonneg_left hG hΛnn
            _ ≤ (1 / 2) * ρ := mul_le_mul_of_nonneg_right hΛ_le hρpos.le
      _ = ρ := by ring

  have hFstar_mem : ‖Fstar‖ ≤ ρ := by
    have heq : Fstar = Ψ (ρt Fstar) := hFstar_fix.symm
    rw [heq]
    exact hΨ_stay (ρt Fstar) (hρt_norm Fstar)

  have hρt_Fstar : ρt Fstar = Fstar :=
    recenteredBallRetraction_eq_self_of_mem (by
      rw [Metric.mem_closedBall, hz₀, dist_zero_right]; exact hFstar_mem)
  have hΨFstar : Ψ Fstar = Fstar := by
    have hstep : Ψ' Fstar = Ψ Fstar := by simp only [hΨ'def, hρt_Fstar]
    rw [← hstep]; exact hFstar_fix

  set field := maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
    (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar with hfielddef
  have hforce_eq : Fstar = nemytskii (I := I) (M := M) hLip field := by
    rw [← hΨFstar, hΨdef, nemytskiiMixedForcingMap_apply]

  refine ⟨maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar, Fstar, rfl, ?_, ?_, ?_, ?_⟩
  · have hcoe := nemytskii_coeFn (I := I) (M := M) hLip field
    have hforce_ae : ⇑Fstar =ᵐ[timeMeasure T]
        ⇑(nemytskii (I := I) (M := M) hLip field) := by
      rw [hforce_eq]
    refine hforce_ae.trans ?_
    exact hcoe
  · rw [maxRegDuhamelMap_trace0 (I := I) (M := M) (a := (a : ℝ)) (T := T) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar, map_zero]
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M) (h_compact := h_compact)
      (a := (a : ℝ)) (T := T) hT hT1 (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) Fstar]
  · exact hFstar_mem

omit [BoundarylessManifold I M] in
theorem quasilinear_maxreg_solution_of_nemytskii
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    (Nfun : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ))
    (hLip : LipschitzWith L Nfun)
    (hmix : ∃ C₁ C₂ : ℝ≥0, ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖) :
    ∃ T₀ : ℝ,
      T₀ = min 1 (min (1 / (64 * ((hmix.choose_spec.choose : ℝ) + 1) ^ 2))
        ((1 / (16 * ((hmix.choose : ℝ) + 1)) /
            (2 * (‖Nfun (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ + 1))) ^ 2)) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T),
        u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => Nfun (maxRegDuhamelSolField (I := I) (M := M)
                (g := g₀) (r := 0) (s := 2) (T := T) (a : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (T := T) (a : ℝ)
                (maxRegDuhamelSolField (I := I) (M := M)
                  (g := g₀) (r := 0) (s := 2) (T := T) (a : ℝ) hT hT1
                  (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce) + gforce ∧
          ‖gforce‖ ≤ 1 / (16 * ((hmix.choose : ℝ) + 1)) := by
  exact nemytskii_sol_const (I := I) (M := M) g₀ a Nfun hLip
    hmix.choose hmix.choose_spec.choose
    ‖Nfun (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖
    (norm_nonneg _) le_rfl hmix.choose_spec.choose_spec

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
