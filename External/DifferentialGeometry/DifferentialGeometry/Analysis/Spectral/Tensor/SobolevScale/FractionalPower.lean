import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

def cast {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHs (I := I) (M := M) g r s τ where
  coeff := T.coeff
  weighted_summable := by
    subst h; exact T.weighted_summable

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cast_coeff {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (cast (I := I) (M := M) h T).coeff i = T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cast_coeff_fun {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    (cast (I := I) (M := M) h T).coeff = T.coeff := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cast_rfl {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s σ) :
    cast (I := I) (M := M) (rfl : σ = σ) T = T := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cast_add {σ τ : ℝ} (h : σ = τ)
    (S T : tensorHs (I := I) (M := M) g r s σ) :
    cast (I := I) (M := M) h (S + T) =
      cast (I := I) (M := M) h S + cast (I := I) (M := M) h T := by
  ext i
  simp only [cast_coeff, add_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cast_smul {σ τ : ℝ} (h : σ = τ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    cast (I := I) (M := M) h (c • T) =
      c • cast (I := I) (M := M) h T := by
  ext i
  simp only [cast_coeff, smul_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_cast {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖cast (I := I) (M := M) h T‖ = ‖T‖ := by
  subst h; rfl

def castEquiv {σ τ : ℝ} (h : σ = τ) :
    tensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s τ where
  toFun := cast (I := I) (M := M) h
  invFun := cast (I := I) (M := M) h.symm
  map_add' := cast_add (I := I) (M := M) h
  map_smul' := cast_smul (I := I) (M := M) h
  left_inv T := by ext i; simp only [cast_coeff]
  right_inv T := by ext i; simp only [cast_coeff]
  norm_map' := norm_cast (I := I) (M := M) h

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma castEquiv_coeff {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (castEquiv (I := I) (M := M) h T).coeff i = T.coeff i := rfl

end tensorHs

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_add (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ τ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ + τ) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        tensorSobolevWeight (I := I) (M := M) i τ := by
  unfold tensorSobolevWeight
  exact Real.rpow_add
    (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)) σ τ

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_neg (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (-σ) =
      (tensorSobolevWeight (I := I) (M := M) i σ)⁻¹ := by
  unfold tensorSobolevWeight
  exact Real.rpow_neg
    (le_trans zero_le_one (one_le_one_add_lambda (I := I) (M := M) i)) σ

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_sub (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ τ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ - τ) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorSobolevWeight (I := I) (M := M) i τ)⁻¹ := by
  rw [sub_eq_add_neg, tensorSobolevWeight_add (I := I) (M := M),
    tensorSobolevWeight_neg (I := I) (M := M)]

end tensorHs

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma fractionalPower_weight_term (i : TensorEigenIdx (I := I) (M := M) g r s)
    (θ σ : ℝ) (c : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * c) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * c ^ 2 := by
  have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
    tensorSobolevWeight_pos (I := I) (M := M) i θ
  have hsum : (σ - 2 * θ) + (θ + θ) = σ := by ring
  calc
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * c) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            (tensorSobolevWeight (I := I) (M := M) i θ *
              tensorSobolevWeight (I := I) (M := M) i θ) * c ^ 2 := by
          ring
    _ = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            tensorSobolevWeight (I := I) (M := M) i (θ + θ) * c ^ 2 := by
          rw [tensorSobolevWeight_add (I := I) (M := M) i θ θ]
    _ = tensorSobolevWeight (I := I) (M := M) i
            ((σ - 2 * θ) + (θ + θ)) * c ^ 2 := by
          rw [tensorSobolevWeight_add (I := I) (M := M) i (σ - 2 * θ)
            (θ + θ)]
    _ = tensorSobolevWeight (I := I) (M := M) i σ * c ^ 2 := by
          rw [hsum]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma fractionalPower_weighted_summable {σ : ℝ} (θ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2) := by
  have h_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2) =
      (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2) := by
    funext i
    exact fractionalPower_weight_term (I := I) (M := M) i θ σ (T.coeff i)
  rw [h_eq]
  exact T.weighted_summable

def fractionalPowerFun {σ : ℝ} (θ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHs (I := I) (M := M) g r s (σ - 2 * θ) where
  coeff i := tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i
  weighted_summable := fractionalPower_weighted_summable (I := I) (M := M) θ T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma fractionalPowerFun_coeff {σ : ℝ} (θ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fractionalPowerFun (I := I) (M := M) θ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma fractionalPowerFun_add {σ : ℝ} (θ : ℝ)
    (S T : tensorHs (I := I) (M := M) g r s σ) :
    fractionalPowerFun (I := I) (M := M) θ (S + T) =
      fractionalPowerFun (I := I) (M := M) θ S +
        fractionalPowerFun (I := I) (M := M) θ T := by
  ext i
  simp only [fractionalPowerFun_coeff, add_coeff]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma fractionalPowerFun_smul {σ : ℝ} (θ : ℝ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    fractionalPowerFun (I := I) (M := M) θ (c • T) =
      c • fractionalPowerFun (I := I) (M := M) θ T := by
  ext i
  simp only [fractionalPowerFun_coeff, smul_coeff]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_fractionalPowerFun {σ : ℝ} (θ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖fractionalPowerFun (I := I) (M := M) θ T‖ = ‖T‖ := by
  have h_target_sq : ‖fractionalPowerFun (I := I) (M := M) θ T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (fractionalPowerFun (I := I) (M := M) θ T)
    simpa only [fractionalPowerFun_coeff] using h
  have h_source_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    fun i => fractionalPower_weight_term (I := I) (M := M) i θ σ (T.coeff i)
  have h_sq_eq : ‖fractionalPowerFun (I := I) (M := M) θ T‖ ^ 2 =
      ‖T‖ ^ 2 := by
    rw [h_target_sq, h_source_sq]
    exact tsum_congr h_terms
  have h1 : 0 ≤ ‖fractionalPowerFun (I := I) (M := M) θ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  have := congrArg Real.sqrt h_sq_eq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

end tensorHs

def tensorFractionalPower {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ : ℝ) {σ : ℝ} :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s (σ - 2 * θ) :=
  LinearMap.mkContinuous
    { toFun := tensorHs.fractionalPowerFun (I := I) (M := M) θ
      map_add' := tensorHs.fractionalPowerFun_add (I := I) (M := M) θ
      map_smul' := fun c T =>
        tensorHs.fractionalPowerFun_smul (I := I) (M := M) θ c T }
    1
    (fun T => by
      change ‖tensorHs.fractionalPowerFun (I := I) (M := M) θ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact le_of_eq (tensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorFractionalPower_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T =
      tensorHs.fractionalPowerFun (I := I) (M := M) θ T := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorFractionalPower_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) :
    ‖tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) θ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T‖ = ‖T‖ :=
  tensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_inner {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ : ℝ) (S T : tensorHs (I := I) (M := M) g r s σ) :
    (inner ℝ (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ S)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T) : ℝ) =
      inner ℝ S T := by
  rw [tensorHs.inner_def, tensorHs.inner_def]
  refine tsum_congr (fun i => ?_)
  simp only [tensorFractionalPower_coeff]
  have hsum : (σ - 2 * θ) + (θ + θ) = σ := by ring
  calc
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * S.coeff i *
            (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i))
        = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            (tensorSobolevWeight (I := I) (M := M) i θ *
              tensorSobolevWeight (I := I) (M := M) i θ) *
            (S.coeff i * T.coeff i) := by ring
    _ = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            tensorSobolevWeight (I := I) (M := M) i (θ + θ) *
            (S.coeff i * T.coeff i) := by
          rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i θ θ]
    _ = tensorSobolevWeight (I := I) (M := M) i
            ((σ - 2 * θ) + (θ + θ)) * (S.coeff i * T.coeff i) := by
          rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M)
            i (σ - 2 * θ) (θ + θ)]
    _ = tensorSobolevWeight (I := I) (M := M) i σ *
          (S.coeff i * T.coeff i) := by rw [hsum]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorFractionalPower_zero_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (0 : ℝ) T).coeff i =
      T.coeff i := by
  rw [tensorFractionalPower_coeff, tensorSobolevWeight_zero, one_mul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_zero
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (0 : ℝ) T =
      tensorHs.cast (I := I) (M := M)
        (by ring : σ = σ - 2 * 0) T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_zero_coeff, tensorHs.cast_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_add_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (θ φ : ℝ) (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) φ T) =
      (tensorHs.cast (I := I) (M := M)
        (by ring :
          σ - 2 * (θ + φ) = (σ - 2 * φ) - 2 * θ))
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (θ + φ) T) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_coeff, tensorFractionalPower_coeff,
    tensorHs.cast_coeff, tensorFractionalPower_coeff,
    tensorHs.tensorSobolevWeight_add (I := I) (M := M) i θ φ]
  ring

def tensorFractionalPowerEquiv {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ) :
    tensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s (σ - 2 * θ) where
  toFun := tensorHs.fractionalPowerFun (I := I) (M := M) θ
  invFun T :=
    tensorHs.cast (I := I) (M := M)
      (by ring : σ - 2 * θ - 2 * (-θ) = σ)
      (tensorHs.fractionalPowerFun (I := I) (M := M) (-θ) T)
  map_add' := tensorHs.fractionalPowerFun_add (I := I) (M := M) θ
  map_smul' := fun c T =>
    tensorHs.fractionalPowerFun_smul (I := I) (M := M) θ c T
  left_inv T := by
    refine tensorHs.ext ?_
    funext i
    simp only [tensorHs.cast_coeff, tensorHs.fractionalPowerFun_coeff,
      tensorHs.tensorSobolevWeight_neg (I := I) (M := M) i θ]
    have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
      tensorSobolevWeight_pos (I := I) (M := M) i θ
    rw [← mul_assoc, inv_mul_cancel₀ hw_pos.ne', one_mul]
  right_inv T := by
    refine tensorHs.ext ?_
    funext i
    simp only [tensorHs.fractionalPowerFun_coeff, tensorHs.cast_coeff,
      tensorHs.tensorSobolevWeight_neg (I := I) (M := M) i θ]
    have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
      tensorSobolevWeight_pos (I := I) (M := M) i θ
    rw [← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
  norm_map' T := tensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorFractionalPowerEquiv_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ T =
      tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorFractionalPowerEquiv_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPowerEquiv_toContinuousLinearMap
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ) :
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s)
        θ σ).toContinuousLinearEquiv.toContinuousLinearMap =
      tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) θ := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPowerEquiv_symm {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    (θ σ : ℝ) (T : tensorHs (I := I) (M := M) g r s (σ - 2 * θ)) :
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ).symm T =
      tensorHs.cast (I := I) (M := M)
        (by ring : σ - 2 * θ - 2 * (-θ) = σ)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (-θ) T) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPowerEquiv_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    (θ σ : ℝ) (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ T‖ = ‖T‖ :=
  tensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lambdaPower_weighted_summable {σ : ℝ} (sh : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
        (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
          T.coeff i) ^ 2) := by
  have h := fractionalPower_weighted_summable (I := I) (M := M)
    (σ := σ) (sh / 2) T
  have heq : σ - 2 * (sh / 2) = σ - sh := by ring
  rwa [heq] at h

def lambdaPowerFun {σ : ℝ} (sh : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHs (I := I) (M := M) g r s (σ - sh) where
  coeff i := tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i
  weighted_summable := lambdaPower_weighted_summable (I := I) (M := M) sh T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma lambdaPowerFun_coeff {σ : ℝ} (sh : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (lambdaPowerFun (I := I) (M := M) sh T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lambdaPowerFun_add {σ : ℝ} (sh : ℝ)
    (S T : tensorHs (I := I) (M := M) g r s σ) :
    lambdaPowerFun (I := I) (M := M) sh (S + T) =
      lambdaPowerFun (I := I) (M := M) sh S +
        lambdaPowerFun (I := I) (M := M) sh T := by
  ext i
  simp only [lambdaPowerFun_coeff, add_coeff]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lambdaPowerFun_smul {σ : ℝ} (sh : ℝ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    lambdaPowerFun (I := I) (M := M) sh (c • T) =
      c • lambdaPowerFun (I := I) (M := M) sh T := by
  ext i
  simp only [lambdaPowerFun_coeff, smul_coeff]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_lambdaPowerFun {σ : ℝ} (sh : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖lambdaPowerFun (I := I) (M := M) sh T‖ = ‖T‖ := by
  have h_target_sq : ‖lambdaPowerFun (I := I) (M := M) sh T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
        (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (lambdaPowerFun (I := I) (M := M) sh T)
    simpa only [lambdaPowerFun_coeff] using h
  have h_source_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
          (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
            T.coeff i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    have h := fractionalPower_weight_term (I := I) (M := M)
      i (sh / 2) σ (T.coeff i)
    have heq : σ - 2 * (sh / 2) = σ - sh := by ring
    rwa [heq] at h
  have h_sq_eq : ‖lambdaPowerFun (I := I) (M := M) sh T‖ ^ 2 = ‖T‖ ^ 2 := by
    rw [h_target_sq, h_source_sq]
    exact tsum_congr h_terms
  have h1 : 0 ≤ ‖lambdaPowerFun (I := I) (M := M) sh T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  have := congrArg Real.sqrt h_sq_eq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

end tensorHs

def tensorLambdaPower {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (sh : ℝ) {σ : ℝ} :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s (σ - sh) :=
  LinearMap.mkContinuous
    { toFun := tensorHs.lambdaPowerFun (I := I) (M := M) sh
      map_add' := tensorHs.lambdaPowerFun_add (I := I) (M := M) sh
      map_smul' := fun c T =>
        tensorHs.lambdaPowerFun_smul (I := I) (M := M) sh c T }
    1
    (fun T => by
      change ‖tensorHs.lambdaPowerFun (I := I) (M := M) sh T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact le_of_eq (tensorHs.norm_lambdaPowerFun (I := I) (M := M) sh T))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorLambdaPower_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (sh : ℝ) (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) sh T =
      tensorHs.lambdaPowerFun (I := I) (M := M) sh T := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorLambdaPower_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (sh : ℝ) (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) sh T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorLambdaPower_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (sh : ℝ) (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) sh T‖ = ‖T‖ :=
  tensorHs.norm_lambdaPowerFun (I := I) (M := M) sh T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorLambdaPower_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ}
    (sh : ℝ) :
    ‖tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) sh‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorLambdaPower_eq_fractionalPower
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ}
    (sh : ℝ) (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) sh T =
      tensorHs.cast (I := I) (M := M)
        (by ring : σ - 2 * (sh / 2) = σ - sh)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (sh / 2) T) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorLambdaPower_coeff, tensorHs.cast_coeff,
    tensorFractionalPower_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorLambdaPower_zero_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) (0 : ℝ) T).coeff i =
      T.coeff i := by
  rw [tensorLambdaPower_coeff, zero_div, tensorSobolevWeight_zero, one_mul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_tensorHsInclusion
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {τ σ : ℝ}
    (θ : ℝ) (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (sub_le_sub_right hτσ (2 * θ))
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ T) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_coeff, tensorHsInclusion_coeff_apply,
    tensorHsInclusion_coeff_apply, tensorFractionalPower_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorFractionalPower_comp_tensorHsInclusion
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {τ σ : ℝ}
    (θ : ℝ) (hτσ : τ ≤ σ) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (sub_le_sub_right hτσ (2 * θ))).comp
        (tensorFractionalPower (I := I) (M := M) (σ := σ)
          θ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact tensorFractionalPower_tensorHsInclusion (I := I) (M := M) θ hτσ T

def tensorHsEquivOfFractionalPower {g : SmoothRiemannianMetric I M}
    {r s : ℕ}
    (σ τ : ℝ) :
    tensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s τ :=
  (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s)
    ((σ - τ) / 2) σ).trans
    (tensorHs.castEquiv (I := I) (M := M)
      (by ring : σ - 2 * ((σ - τ) / 2) = τ))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsEquivOfFractionalPower_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (σ τ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsEquivOfFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) σ τ T).coeff
        i =
      tensorSobolevWeight (I := I) (M := M) i ((σ - τ) / 2) * T.coeff i := by
  unfold tensorHsEquivOfFractionalPower
  rw [LinearIsometryEquiv.trans_apply]
  change (tensorHs.castEquiv (I := I) (M := M) _
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s)
      ((σ - τ) / 2) σ T)).coeff i = _
  rw [tensorHs.castEquiv_coeff, tensorFractionalPowerEquiv_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsEquivOfFractionalPower_norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (σ τ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖tensorHsEquivOfFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) σ τ T‖ =
      ‖T‖ :=
  (tensorHsEquivOfFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s)
    σ τ).norm_map T

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ : ℝ) {σ : ℝ} :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s (σ - 2 * θ) :=
  tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) θ

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (θ σ : ℝ) :
    tensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s (σ - 2 * θ) :=
  tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s) θ σ

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (σ τ : ℝ) :
    tensorHs (I := I) (M := M) g r s σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s τ :=
  tensorHsEquivOfFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) σ τ

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
