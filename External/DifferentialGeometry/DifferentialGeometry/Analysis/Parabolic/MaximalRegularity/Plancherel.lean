import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace MaximalRegularity

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma countable_tensorEigenIdx
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Countable (TensorEigenIdx (I := I) (M := M) g r s) := by
  haveI : Countable (TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :=
    TensorNonzeroResolventEigenvalue.countable_ofCompact
      (I := I) (M := M) g r s h_compact
  infer_instance

lemma ae_all_coeff_eq {ι : Type*} [Countable ι] {μ : Measure ℝ}
    {gfam f : ι → ℝ → ℝ} (h : ∀ i, gfam i =ᵐ[μ] f i) :
    ∀ᵐ t ∂μ, ∀ i, gfam i t = f i t :=
  (MeasureTheory.ae_all_iff).2 h

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorHsWeightMulCoeffSqLeNormSq {a : ℝ}
    (T : tensorHs (I := I) (M := M) g r s a)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i a * (T.coeff i) ^ 2 ≤ ‖T‖ ^ 2 := by
  rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M) T]
  refine Summable.le_tsum T.weighted_summable i (fun j _ => ?_)
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) j a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) j a
  positivity

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorHsAbsCoeffLe {a : ℝ}
    (T : tensorHs (I := I) (M := M) g r s a)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    |T.coeff i| ≤
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹ * ‖T‖ := by
  have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_pos (I := I) (M := M) i a
  have hsqrt_pos :
      0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) :=
    Real.sqrt_pos.mpr hw_pos
  have hbound := tensorHsWeightMulCoeffSqLeNormSq (I := I) (M := M) T i
  have hsq : (T.coeff i) ^ 2 ≤
      ((Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹ * ‖T‖) ^ 2 := by
    have hsqrt_sq :
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) ^ 2 =
          tensorSobolevWeight (I := I) (M := M) i a :=
      sq_sqrt_tensorSobolevWeight (I := I) (M := M) i a
    rw [mul_pow, inv_pow, hsqrt_sq, inv_mul_eq_div, le_div_iff₀ hw_pos, mul_comm]
    exact hbound
  have hrhs_nonneg :
      0 ≤ (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹ * ‖T‖ :=
    mul_nonneg (le_of_lt (inv_pos.mpr hsqrt_pos)) (norm_nonneg T)
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hrhs_nonneg] at h

def tensorHsCoeffL {a : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorHs (I := I) (M := M) g r s a →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun T => T.coeff i
      map_add' := fun S T => by
        simp only [tensorHs.add_coeff]
      map_smul' := fun c T => by
        simp only [tensorHs.smul_coeff, smul_eq_mul, RingHom.id_apply] }
    (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹
    (fun T => by
      change ‖T.coeff i‖ ≤
        (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹ * ‖T‖
      rw [Real.norm_eq_abs]
      exact tensorHsAbsCoeffLe (I := I) (M := M) T i)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorHsCoeffL_apply {a : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (T : tensorHs (I := I) (M := M) g r s a) :
    tensorHsCoeffL (I := I) (M := M) i T = T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorHsCoeffL_opNorm_le {a : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorHsCoeffL (I := I) (M := M) (a := a) i‖ ≤
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹ :=
  LinearMap.mkContinuous_norm_le _
    (le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr
      (tensorSobolevWeight_pos (I := I) (M := M) i a)))) _

def timeModeCoeff {a : ℝ} {T : ℝ}
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeL2 ℝ T :=
  (tensorHsCoeffL (I := I) (M := M) i).compLpL 2 (timeMeasure T) f

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_coeFn {a : ℝ} {T : ℝ}
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M) f i =ᵐ[timeMeasure T]
      fun t => (f t).coeff i := by
  have h := (tensorHsCoeffL (I := I) (M := M) i).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) f
  exact h.trans
    (Eventually.of_forall fun t => tensorHsCoeffL_apply (I := I) (M := M) i (f t))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_add {a : ℝ} {T : ℝ}
    (f₁ f₂ : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M) (f₁ + f₂) i =
      timeModeCoeff (I := I) (M := M) f₁ i +
        timeModeCoeff (I := I) (M := M) f₂ i := by
  unfold timeModeCoeff
  rw [map_add]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_smul {a : ℝ} {T : ℝ} (c : ℝ)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M) (c • f) i =
      c • timeModeCoeff (I := I) (M := M) f i := by
  unfold timeModeCoeff
  rw [map_smul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_timeModeCoeff_le {a : ℝ} {T : ℝ}
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖timeModeCoeff (I := I) (M := M) f i‖ ≤
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a))⁻¹ * ‖f‖ := by
  refine le_trans
    (((tensorHsCoeffL (I := I) (M := M) i).compLpL 2
      (timeMeasure T)).le_opNorm f) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
  exact le_trans
    (ContinuousLinearMap.norm_compLpL_le
      (tensorHsCoeffL (I := I) (M := M) i))
    (tensorHsCoeffL_opNorm_le (I := I) (M := M) i)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem integrable_timeModeCoeff_sq {a : ℝ} {T : ℝ}
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Integrable (fun t => (timeModeCoeff (I := I) (M := M) f i t) ^ 2)
      (timeMeasure T) :=
  (Lp.memLp (timeModeCoeff (I := I) (M := M) f i)).integrable_sq

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_timeModeCoeff_sq_eq_integral {a : ℝ} {T : ℝ}
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 =
      ∫ t in Set.Icc (0 : ℝ) T,
        (timeModeCoeff (I := I) (M := M) f i t) ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral (timeModeCoeff (I := I) (M := M) f i)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem integrable_weight_mul_coeff_sq {a : ℝ} {T : ℝ}
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Integrable (fun t => tensorSobolevWeight (I := I) (M := M) i a *
      ((f t).coeff i) ^ 2) (timeMeasure T) := by
  refine ((integrable_timeModeCoeff_sq (I := I) (M := M) f i).const_mul
    (tensorSobolevWeight (I := I) (M := M) i a)).congr ?_
  filter_upwards [timeModeCoeff_coeFn (I := I) (M := M) f i] with t ht
  rw [ht]

section PlancherelFubini

variable {a : ℝ} {T : ℝ}
  (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)

private def planIntegrand (i : TensorEigenIdx (I := I) (M := M) g r s)
    (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (tensorSobolevWeight (I := I) (M := M) i a * ((f t).coeff i) ^ 2)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem aemeasurable_planIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    AEMeasurable (planIntegrand (I := I) (M := M) f i) (timeMeasure T) := by
  letI : MeasurableSpace ℝ := borel ℝ
  haveI : BorelSpace ℝ := ⟨rfl⟩
  have hmeas : AEMeasurable (fun t => (f t).coeff i) (timeMeasure T) := by
    refine AEMeasurable.congr
      (Lp.aestronglyMeasurable
        (timeModeCoeff (I := I) (M := M) f i)).aemeasurable ?_
    exact timeModeCoeff_coeFn (I := I) (M := M) f i
  exact (((hmeas.pow_const 2).const_mul
    (tensorSobolevWeight (I := I) (M := M) i a))).ennreal_ofReal

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lintegral_planIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∫⁻ t, planIntegrand (I := I) (M := M) f i t ∂(timeMeasure T) =
      ENNReal.ofReal (tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
  have hw_nonneg : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hint : Integrable
      (fun t => tensorSobolevWeight (I := I) (M := M) i a *
        ((f t).coeff i) ^ 2) (timeMeasure T) :=
    integrable_weight_mul_coeff_sq (I := I) (M := M) f i
  have hnn : 0 ≤ᵐ[timeMeasure T]
      fun t => tensorSobolevWeight (I := I) (M := M) i a *
        ((f t).coeff i) ^ 2 :=
    Eventually.of_forall fun t => mul_nonneg hw_nonneg (sq_nonneg _)
  have hofReal :
      (∫⁻ t, planIntegrand (I := I) (M := M) f i t ∂(timeMeasure T))
        = ENNReal.ofReal (∫ t, tensorSobolevWeight (I := I) (M := M) i a *
            ((f t).coeff i) ^ 2 ∂(timeMeasure T)) :=
    (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  rw [hofReal]
  congr 1
  rw [integral_const_mul]
  congr 1
  rw [norm_timeModeCoeff_sq_eq_integral (I := I) (M := M) f i,
    show (∫ t in Set.Icc (0 : ℝ) T,
        (timeModeCoeff (I := I) (M := M) f i t) ^ 2)
      = ∫ t, (timeModeCoeff (I := I) (M := M) f i t) ^ 2 ∂(timeMeasure T)
      from rfl]
  refine integral_congr_ae ?_
  filter_upwards [timeModeCoeff_coeFn (I := I) (M := M) f i] with t ht
  rw [ht]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem ennreal_tsum_weight_mul_norm_sq_ne_top
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    (∑' i, ENNReal.ofReal (tensorSobolevWeight (I := I) (M := M) i a *
      ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)) ≠ (⊤ : ℝ≥0∞) := by
  haveI := countable_tensorEigenIdx
    (I := I) (M := M) (g := g) (r := r) (s := s) h_compact
  have hpoint : ∀ t : ℝ,
      ENNReal.ofReal (‖f t‖ ^ 2) =
        ∑' i, planIntegrand (I := I) (M := M) f i t := by
    intro t
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M) (f t)]
    have hnn : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        0 ≤ tensorSobolevWeight (I := I) (M := M) i a *
          ((f t).coeff i) ^ 2 :=
      fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a)
        (sq_nonneg _)
    rw [ENNReal.ofReal_tsum_of_nonneg hnn (f t).weighted_summable]
    rfl
  have hlintegral_eq :
      ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T) =
        ∑' i, ∫⁻ t, planIntegrand (I := I) (M := M) f i t
          ∂(timeMeasure T) := by
    rw [show (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T))
          = ∫⁻ t, (∑' i, planIntegrand (I := I) (M := M) f i t)
              ∂(timeMeasure T)
        from lintegral_congr (fun t => hpoint t)]
    exact lintegral_tsum
      (fun i => aemeasurable_planIntegrand (I := I) (M := M) f i)
  have hf_norm_sq_int : Integrable (fun t => ‖f t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)
  have hf_nn : 0 ≤ᵐ[timeMeasure T] fun t => ‖f t‖ ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  rw [← tsum_congr (fun i => lintegral_planIntegrand (I := I) (M := M) f i),
    ← hlintegral_eq, ← ofReal_integral_eq_lintegral_ofReal hf_norm_sq_int hf_nn]
  exact ENNReal.ofReal_ne_top

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem weight_mul_norm_timeModeCoeff_sq_nonneg
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ tensorSobolevWeight (I := I) (M := M) i a *
      ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 :=
  mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a) (sq_nonneg _)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem summable_weight_mul_norm_timeModeCoeff_sq
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i a *
      ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2) := by
  refine (ENNReal.summable_toReal
    (ennreal_tsum_weight_mul_norm_sq_ne_top
      (I := I) (M := M) h_compact (f := f))).congr
    (fun i => ?_)
  exact ENNReal.toReal_ofReal
    (weight_mul_norm_timeModeCoeff_sq_nonneg (I := I) (M := M) f i)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_sq_eq_tsum_timeModeCoeff
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    ‖f‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i a *
        ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 := by
  haveI := countable_tensorEigenIdx
    (I := I) (M := M) (g := g) (r := r) (s := s) h_compact
  have hpoint : ∀ t : ℝ,
      ENNReal.ofReal (‖f t‖ ^ 2) =
        ∑' i, planIntegrand (I := I) (M := M) f i t := by
    intro t
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M) (f t)]
    have hnn : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        0 ≤ tensorSobolevWeight (I := I) (M := M) i a *
          ((f t).coeff i) ^ 2 :=
      fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a)
        (sq_nonneg _)
    rw [ENNReal.ofReal_tsum_of_nonneg hnn (f t).weighted_summable]
    rfl
  have hlintegral_eq :
      ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T) =
        ∑' i, ∫⁻ t, planIntegrand (I := I) (M := M) f i t
          ∂(timeMeasure T) := by
    rw [show (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T))
          = ∫⁻ t, (∑' i, planIntegrand (I := I) (M := M) f i t)
              ∂(timeMeasure T)
        from lintegral_congr (fun t => hpoint t)]
    exact lintegral_tsum
      (fun i => aemeasurable_planIntegrand (I := I) (M := M) f i)
  have hf_norm_sq_int : Integrable (fun t => ‖f t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)
  have hf_nn : 0 ≤ᵐ[timeMeasure T] fun t => ‖f t‖ ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  calc ‖f‖ ^ 2
      = ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 :=
        TimeSobolev.norm_sq_eq_integral f
    _ = (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(timeMeasure T)).toReal := by
        rw [show (∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2)
              = ∫ t, ‖f t‖ ^ 2 ∂(timeMeasure T) from rfl]
        exact integral_eq_lintegral_of_nonneg_ae hf_nn
          ((Lp.aestronglyMeasurable f).norm.pow 2)
    _ = (∑' i, ∫⁻ t, planIntegrand (I := I) (M := M) f i t
            ∂(timeMeasure T)).toReal := by rw [hlintegral_eq]
    _ = (∑' i, ENNReal.ofReal (tensorSobolevWeight (I := I) (M := M) i a *
            ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)).toReal := by
        rw [tsum_congr (fun i => lintegral_planIntegrand (I := I) (M := M) f i)]
    _ = ∑' i, (ENNReal.ofReal (tensorSobolevWeight (I := I) (M := M) i a *
            ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2)).toReal := by
        rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
    _ = ∑' i, tensorSobolevWeight (I := I) (M := M) i a *
            ‖timeModeCoeff (I := I) (M := M) f i‖ ^ 2 := by
        refine tsum_congr (fun i => ?_)
        rw [ENNReal.toReal_ofReal
          (weight_mul_norm_timeModeCoeff_sq_nonneg (I := I) (M := M) f i)]

end PlancherelFubini

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_sq_le_of_weighted_perMode_le {a b : ℝ} {T : ℝ} {C : ℝ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (gT : timeL2 (tensorHs (I := I) (M := M) g r s b) T)
    (fT : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (hbound : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i b *
          ‖timeModeCoeff (I := I) (M := M) gT i‖ ^ 2 ≤
        C ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) fT i‖ ^ 2)) :
    ‖gT‖ ^ 2 ≤ C ^ 2 * ‖fT‖ ^ 2 := by
  have hg := norm_sq_eq_tsum_timeModeCoeff
    (I := I) (M := M) h_compact (f := gT)
  have hf := norm_sq_eq_tsum_timeModeCoeff
    (I := I) (M := M) h_compact (f := fT)
  have hg_summ :=
    summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := gT)
  have hf_summ :=
    summable_weight_mul_norm_timeModeCoeff_sq
      (I := I) (M := M) h_compact (f := fT)
  rw [hg, hf, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hbound hg_summ (hf_summ.mul_left _)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_le_of_weighted_perMode_le {a b : ℝ} {T : ℝ} {C : ℝ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (hC : 0 ≤ C)
    (gT : timeL2 (tensorHs (I := I) (M := M) g r s b) T)
    (fT : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    (hbound : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i b *
          ‖timeModeCoeff (I := I) (M := M) gT i‖ ^ 2 ≤
        C ^ 2 * (tensorSobolevWeight (I := I) (M := M) i a *
          ‖timeModeCoeff (I := I) (M := M) fT i‖ ^ 2)) :
    ‖gT‖ ≤ C * ‖fT‖ := by
  have hsq : ‖gT‖ ^ 2 ≤ (C * ‖fT‖) ^ 2 := by
    rw [mul_pow]
    exact norm_sq_le_of_weighted_perMode_le
      (I := I) (M := M) h_compact gT fT hbound
  have hrhs_nonneg : 0 ≤ C * ‖fT‖ := mul_nonneg hC (norm_nonneg fT)
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg gT), Real.sqrt_sq hrhs_nonneg] at h

def timeModeSynthesisPointwise {b : ℝ}
    (cFam : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (hsum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i b *
      (cFam i) ^ 2)) :
    tensorHs (I := I) (M := M) g r s b where
  coeff := cFam
  weighted_summable := hsum

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma timeModeSynthesisPointwise_coeff {b : ℝ}
    (cFam : TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    (hsum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i b *
      (cFam i) ^ 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (timeModeSynthesisPointwise (I := I) (M := M) cFam hsum).coeff i =
      cFam i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_injective {b : ℝ} {T : ℝ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    {f₁ f₂ : timeL2 (tensorHs (I := I) (M := M) g r s b) T}
    (h : ∀ i, timeModeCoeff (I := I) (M := M) f₁ i =
      timeModeCoeff (I := I) (M := M) f₂ i) :
    f₁ = f₂ := by
  haveI := countable_tensorEigenIdx
    (I := I) (M := M) (g := g) (r := r) (s := s) h_compact
  refine MeasureTheory.Lp.ext ?_
  have hcoord : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      (fun t => (f₁ t).coeff i) =ᵐ[timeMeasure T]
        fun t => (f₂ t).coeff i := by
    intro i
    have h1 := timeModeCoeff_coeFn (I := I) (M := M) f₁ i
    have h2 := timeModeCoeff_coeFn (I := I) (M := M) f₂ i
    have heq : timeModeCoeff (I := I) (M := M) f₁ i =ᵐ[timeMeasure T]
        timeModeCoeff (I := I) (M := M) f₂ i := by rw [h i]
    exact (h1.symm.trans heq).trans h2
  filter_upwards [ae_all_iff.mpr hcoord] with t ht
  exact tensorHs.ext (funext ht)

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
