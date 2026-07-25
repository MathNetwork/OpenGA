import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel

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
theorem norm_tensorHsBasisVec {σ : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) := by
  classical
  rw [tensorHs.norm_eq_sqrt_tsum]
  congr 1
  have hfun : (fun j => tensorSobolevWeight (I := I) (M := M) j σ *
        ((tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i).coeff j) ^ 2)
      = fun j => if j = i then tensorSobolevWeight (I := I) (M := M) j σ else 0 := by
    funext j
    rw [tensorHsBasisVec_coeff]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj, one_pow, mul_one]
    · rw [if_neg hj, if_neg hj, zero_pow (by norm_num), mul_zero]
  rw [hfun, tsum_ite_eq i (fun j => tensorSobolevWeight (I := I) (M := M) j σ)]

def singleModeCLM {σ : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ℝ →L[ℝ] tensorHs (I := I) (M := M) g r s σ :=
  LinearMap.mkContinuous
    { toFun := fun c => c • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i
      map_add' := fun c d => by rw [add_smul]
      map_smul' := fun a c => by rw [smul_smul]; rfl }
    (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))
    (fun c => by
      change ‖c • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i‖ ≤ _
      rw [norm_smul, norm_tensorHsBasisVec (I := I) (M := M) i, Real.norm_eq_abs]
      exact le_of_eq (mul_comm _ _))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem singleModeCLM_apply {σ : ℝ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) (c : ℝ) :
    singleModeCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i c =
      c • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i := rfl

open scoped Classical in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem singleModeCLM_coeff {σ : ℝ}
    (i j : TensorEigenIdx (I := I) (M := M) g r s) (c : ℝ) :
    (singleModeCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i c).coeff j =
      (if j = i then c else 0) := by
  classical
  rw [singleModeCLM_apply]
  simp only [tensorHs.smul_coeff, tensorHsBasisVec_coeff]
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj, mul_one]
  · rw [if_neg hj, if_neg hj, mul_zero]

variable {σ : ℝ} {T : ℝ}

def singleModeTimeL2 {σ : ℝ}
    {T : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeL2 ℝ T →L[ℝ] timeL2 (tensorHs (I := I) (M := M) g r s σ) T :=
  (singleModeCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i).compLpL 2 (timeMeasure T)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem singleModeTimeL2_coeFn (i : TensorEigenIdx (I := I) (M := M) g r s)
    (gf : timeL2 ℝ T) :
    singleModeTimeL2 (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i gf =ᵐ[timeMeasure T]
      fun t => (gf t) • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i := by
  have h := (singleModeCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) gf
  exact h.trans (Eventually.of_forall fun t => singleModeCLM_apply (I := I) (M := M) i (gf t))

open scoped Classical in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeModeCoeff_singleModeTimeL2
    (i j : TensorEigenIdx (I := I) (M := M) g r s) (gf : timeL2 ℝ T) :
    timeModeCoeff (I := I) (M := M)
        (singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf) j =
      (if j = i then gf else 0) := by
  classical
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn (I := I) (M := M)
    (singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf) j
  have hsm := singleModeTimeL2_coeFn (I := I) (M := M)
    (σ := σ) i gf
  have hcoord : ∀ t,
      (((gf t) • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i).coeff j)
        = (if j = i then gf t else 0) := by
    intro t
    simp only [tensorHs.smul_coeff, tensorHsBasisVec_coeff]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj, mul_one]
    · rw [if_neg hj, if_neg hj, mul_zero]
  by_cases hj : j = i
  · filter_upwards [hlhs, hsm] with t ht hsmt
    rw [ht, hsmt, hcoord t, if_pos hj, if_pos hj]
  · have hzero := Lp.coeFn_zero (E := ℝ) (p := 2) (μ := timeMeasure T)
    filter_upwards [hlhs, hsm, hzero] with t ht hsmt hzt
    rw [ht, hsmt, hcoord t, if_neg hj, if_neg hj, hzt]
    rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_singleModeTimeL2_sq (i : TensorEigenIdx (I := I) (M := M) g r s)
    (gf : timeL2 ℝ T) :
    ‖singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf‖ ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * ‖gf‖ ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral, TimeSobolev.norm_sq_eq_integral,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [singleModeTimeL2_coeFn (I := I) (M := M)
    (σ := σ) i gf] with t ht
  rw [ht, norm_smul, mul_pow, norm_tensorHsBasisVec (I := I) (M := M) i,
    Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ),
    Real.norm_eq_abs, sq_abs, mul_comm]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_singleModeTimeL2 (i : TensorEigenIdx (I := I) (M := M) g r s)
    (gf : timeL2 ℝ T) :
    ‖singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * ‖gf‖ := by
  have hsq := norm_singleModeTimeL2_sq (I := I) (M := M)
    (σ := σ) i gf
  have hrhs_nonneg : 0 ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * ‖gf‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h := Real.sqrt_le_sqrt (le_of_eq hsq)
  have h' := Real.sqrt_le_sqrt (le_of_eq hsq.symm)
  have hsqrt : ‖singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ * ‖gf‖ ^ 2) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt, Real.sqrt_mul (tensorSobolevWeight_nonneg (I := I) (M := M) i σ),
    Real.sqrt_sq (norm_nonneg _)]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem inner_tensorHsBasisVec_eq_zero {i j : TensorEigenIdx (I := I) (M := M) g r s}
    (hij : i ≠ j) :
    (inner ℝ (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i)
      (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ j) : ℝ) = 0 := by
  classical
  rw [tensorHs.inner_def]
  have hterm : (fun k => tensorSobolevWeight (I := I) (M := M) k σ *
        ((tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i).coeff k *
          (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ j).coeff k))
      = fun _ => (0 : ℝ) := by
    funext k
    rw [tensorHsBasisVec_coeff, tensorHsBasisVec_coeff]
    by_cases hki : k = i
    · rw [if_pos hki, if_neg (by rw [hki]; exact hij), mul_zero, mul_zero]
    · rw [if_neg hki, zero_mul, mul_zero]
  rw [hterm, tsum_zero]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem inner_singleModeTimeL2_eq_zero
    {i j : TensorEigenIdx (I := I) (M := M) g r s} (hij : i ≠ j)
    (gf hf : timeL2 ℝ T) :
    (inner ℝ (singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf)
      (singleModeTimeL2 (I := I) (M := M) (σ := σ) j hf) : ℝ) = 0 := by
  rw [TimeSobolev.inner_def]
  rw [show (∫ t in Set.Icc (0 : ℝ) T,
        inner ℝ (singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf t)
          (singleModeTimeL2 (I := I) (M := M) (σ := σ) j hf t))
      = ∫ t in Set.Icc (0 : ℝ) T, (0 : ℝ) from ?_, integral_zero]
  refine integral_congr_ae ?_
  filter_upwards [singleModeTimeL2_coeFn (I := I) (M := M)
      (σ := σ) i gf,
    singleModeTimeL2_coeFn (I := I) (M := M)
      (σ := σ) j hf] with t hit hjt
  rw [hit, hjt, inner_smul_left, inner_smul_right,
    inner_tensorHsBasisVec_eq_zero (I := I) (M := M) hij, mul_zero, mul_zero]

def singleModeScaledCLM {σ : ℝ}
    {T : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeL2 ℝ T →L[ℝ]
      timeL2 (tensorHs (I := I) (M := M) g r s σ) T :=
  (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ •
    singleModeTimeL2 (I := I) (M := M) (σ := σ) (T := T) i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem singleModeScaledCLM_apply
    (i : TensorEigenIdx (I := I) (M := M) g r s) (gf : timeL2 ℝ T) :
    singleModeScaledCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i gf =
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ •
        singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf := by
  rw [singleModeScaledCLM, ContinuousLinearMap.smul_apply]

def singleModeIsometry {σ : ℝ}
    {T : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    timeL2 ℝ T →ₗᵢ[ℝ]
      timeL2 (tensorHs (I := I) (M := M) g r s σ) T :=
  { (singleModeScaledCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i).toLinearMap with
    norm_map' := fun gf => by
      have hsqrt_pos : 0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
        Real.sqrt_pos.mpr (tensorSobolevWeight_pos (I := I) (M := M) i σ)
      have hval : ((singleModeScaledCLM (I := I) (M := M) (g := g) (r := r) (s := s)
            (σ := σ) i).toLinearMap gf) =
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ •
              singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf :=
        singleModeScaledCLM_apply (I := I) (M := M) i gf
      rw [hval, norm_smul, norm_singleModeTimeL2 (I := I) (M := M) i, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hsqrt_pos), ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_mul] }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem singleModeIsometry_apply
    (i : TensorEigenIdx (I := I) (M := M) g r s) (gf : timeL2 ℝ T) :
    singleModeIsometry (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i gf =
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ •
        singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf :=
  singleModeScaledCLM_apply (I := I) (M := M) i gf

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem orthogonalFamily_singleModeIsometry {σ : ℝ} {T : ℝ} :
    OrthogonalFamily ℝ (fun _ : TensorEigenIdx (I := I) (M := M) g r s => timeL2 ℝ T)
      (fun i => singleModeIsometry (I := I) (M := M) (g := g) (r := r) (s := s)
        (σ := σ) (T := T) i) := by
  intro i j hij gf hf
  rw [singleModeIsometry_apply, singleModeIsometry_apply, inner_smul_left,
    inner_smul_right, inner_singleModeTimeL2_eq_zero (I := I) (M := M) hij,
    mul_zero, mul_zero]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem singleModeTimeL2_eq_isometry (i : TensorEigenIdx (I := I) (M := M) g r s)
    (gf : timeL2 ℝ T) :
    singleModeTimeL2 (I := I) (M := M) (σ := σ) i gf =
      singleModeIsometry (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i
        ((Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)) • gf) := by
  have hsqrt_pos : 0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
    Real.sqrt_pos.mpr (tensorSobolevWeight_pos (I := I) (M := M) i σ)
  rw [singleModeIsometry_apply, map_smul, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_smul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem summable_singleModeTimeL2
    (gFam : TensorEigenIdx (I := I) (M := M) g r s → timeL2 ℝ T)
    (hsum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
      ‖gFam i‖ ^ 2)) :
    Summable (fun i => singleModeTimeL2 (I := I) (M := M) (σ := σ) i
      (gFam i)) := by
  have hrw : (fun i => singleModeTimeL2 (I := I) (M := M) (σ := σ) i
        (gFam i))
      = fun i => singleModeIsometry (I := I) (M := M) (g := g) (r := r) (s := s)
          (σ := σ) i
          ((Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)) • gFam i) := by
    funext i
    exact singleModeTimeL2_eq_isometry (I := I) (M := M) i (gFam i)
  rw [hrw]
  rw [(orthogonalFamily_singleModeIsometry (I := I) (M := M)
    (g := g) (r := r) (s := s) (σ := σ) (T := T)).summable_iff_norm_sq_summable]
  refine hsum.congr (fun i => ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)]

def timeL2OfModes
    (gFam : TensorEigenIdx (I := I) (M := M) g r s → timeL2 ℝ T) :
    timeL2 (tensorHs (I := I) (M := M) g r s σ) T :=
  ∑' i, singleModeTimeL2 (I := I) (M := M) (σ := σ) i (gFam i)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem timeL2OfModes_timeModeCoeff
    (gFam : TensorEigenIdx (I := I) (M := M) g r s → timeL2 ℝ T)
    (hsum : Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
      ‖gFam i‖ ^ 2))
    (j : TensorEigenIdx (I := I) (M := M) g r s) :
    timeModeCoeff (I := I) (M := M)
        (timeL2OfModes (I := I) (M := M) (σ := σ) gFam) j =
      gFam j := by
  classical
  have hsumm := summable_singleModeTimeL2 (I := I) (M := M) gFam hsum
  have hcomm : timeModeCoeff (I := I) (M := M)
        (timeL2OfModes (I := I) (M := M) (σ := σ) gFam) j =
      ∑' i, timeModeCoeff (I := I) (M := M)
        (singleModeTimeL2 (I := I) (M := M) (σ := σ) i (gFam i)) j := by
    rw [timeL2OfModes]
    exact ContinuousLinearMap.map_tsum
      ((tensorHsCoeffL (I := I) (M := M) j).compLpL 2 (timeMeasure T))
      hsumm
  rw [hcomm]
  have hterm : (fun i => timeModeCoeff (I := I) (M := M)
        (singleModeTimeL2 (I := I) (M := M) (σ := σ) i (gFam i)) j)
      = fun i => if i = j then gFam i else 0 := by
    funext i
    rw [timeModeCoeff_singleModeTimeL2 (I := I) (M := M) i j (gFam i)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij h.symm)]
  rw [hterm, tsum_ite_eq j gFam]

end MaximalRegularity
end Parabolic
end Analysis
end DifferentialGeometry
