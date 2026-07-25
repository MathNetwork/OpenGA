import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs

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

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_eq_sqrt_succ_mul_sqrt_pred
    (i : TensorEigenIdx (I := I) (M := M) g r s) (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i σ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + 1)) *
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ - 1)) := by
  have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  set x := 1 + TensorEigenIdx.lambda (I := I) (M := M) i with hx
  unfold tensorSobolevWeight
  rw [← hx]
  have hsqrt_u : Real.sqrt (x ^ (σ + 1)) = x ^ ((σ + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1; ring
  have hsqrt_l : Real.sqrt (x ^ (σ - 1)) = x ^ ((σ - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1; ring
  rw [hsqrt_u, hsqrt_l, ← Real.rpow_add hbase]
  congr 1; ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sq_sum_crossScale_le
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i)) ^ 2 ≤
      (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2) *
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 := by
  set p : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ + 1)) * f i with hp_def
  set q : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (σ - 1)) * h i with hq_def
  have hsummand : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) = p i * q i := by
    intro i
    rw [hp_def, hq_def,
      tensorSobolevWeight_eq_sqrt_succ_mul_sqrt_pred (I := I) (M := M) i σ]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  have hCS : (∑ i ∈ S, p i * q i) ^ 2 ≤
      (∑ i ∈ S, (p i) ^ 2) * ∑ i ∈ S, (q i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S p q
  have hp_sq : ∀ i, (p i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2 := by
    intro i
    rw [hp_def, mul_pow,
      Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1))]
  have hq_sq : ∀ i, (q i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 := by
    intro i
    rw [hq_def, mul_pow,
      Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ - 1))]
  rw [Finset.sum_congr rfl (fun i _ => hp_sq i),
    Finset.sum_congr rfl (fun i _ => hq_sq i)] at hCS
  exact hCS

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem abs_sum_crossScale_le
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    |∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i)| ≤
      Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2) *
        Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2) := by
  have hhi_nonneg :
      0 ≤ ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
  have hlo_nonneg :
      0 ≤ ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ - 1)) (sq_nonneg _))
  have hsq := sq_sum_crossScale_le (I := I) (M := M) S σ f h
  have hprod_nonneg :
      0 ≤ Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2) *
        Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine abs_le_of_sq_le_sq ?_ hprod_nonneg
  rw [mul_pow, Real.sq_sqrt hhi_nonneg, Real.sq_sqrt hlo_nonneg]
  exact hsq

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem two_mul_sum_crossScale_le_eps
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) ≤
      ε * (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2) +
        ε⁻¹ * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 := by
  set A := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (f i) ^ 2 with hA
  set B := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (σ - 1) * (h i) ^ 2 with hB
  have hA_nonneg : 0 ≤ A :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ + 1)) (sq_nonneg _))
  have hB_nonneg : 0 ≤ B :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (σ - 1)) (sq_nonneg _))
  have habs := abs_sum_crossScale_le (I := I) (M := M) S σ f h
  rw [← hA, ← hB] at habs
  have hle :
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) ≤
        Real.sqrt A * Real.sqrt B :=
    le_trans (le_abs_self _) habs
  have hyoung : 2 * (Real.sqrt A * Real.sqrt B) ≤ ε * A + ε⁻¹ * B := by
    set sA := Real.sqrt A with hsA_def
    set sB := Real.sqrt B with hsB_def
    set sε := Real.sqrt ε with hsε_def
    set sεinv := Real.sqrt ε⁻¹ with hsεinv_def
    have hsqA : sA ^ 2 = A := Real.sq_sqrt hA_nonneg
    have hsqB : sB ^ 2 = B := Real.sq_sqrt hB_nonneg
    have hsqε : sε ^ 2 = ε := Real.sq_sqrt hε.le
    have hsqεinv : sεinv ^ 2 = ε⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hε.le)
    have hmix : sε * sεinv = 1 := by
      rw [hsε_def, hsεinv_def, ← Real.sqrt_mul hε.le, mul_inv_cancel₀ hε.ne', Real.sqrt_one]
    have hkey : 0 ≤ (sε * sA - sεinv * sB) ^ 2 := sq_nonneg _
    have hcross : (sε * sA) * (sεinv * sB) = sA * sB := by
      calc (sε * sA) * (sεinv * sB) = (sε * sεinv) * (sA * sB) := by ring
        _ = sA * sB := by rw [hmix, one_mul]
    nlinarith [hkey, hsqA, hsqB, hsqε, hsqεinv, hcross]
  nlinarith [hle, hyoung]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sq_sum_sameScale_le
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) :
    (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i)) ^ 2 ≤
      (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i) ^ 2) *
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (h i) ^ 2 := by
  set p : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * f i with hp_def
  set q : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * h i with hq_def
  have hsummand : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) = p i * q i := by
    intro i
    simp only [hp_def, hq_def]
    have hsq : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) =
        tensorSobolevWeight (I := I) (M := M) i σ :=
      Real.mul_self_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    rw [show Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * f i *
          (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * h i) =
        (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ)) * (f i * h i) by ring,
      hsq]
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  have hCS : (∑ i ∈ S, p i * q i) ^ 2 ≤
      (∑ i ∈ S, (p i) ^ 2) * ∑ i ∈ S, (q i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S p q
  have hp_sq : ∀ i, (p i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * (f i) ^ 2 := by
    intro i
    rw [hp_def, mul_pow,
      Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)]
  have hq_sq : ∀ i, (q i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * (h i) ^ 2 := by
    intro i
    rw [hq_def, mul_pow,
      Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)]
  rw [Finset.sum_congr rfl (fun i _ => hp_sq i),
    Finset.sum_congr rfl (fun i _ => hq_sq i)] at hCS
  exact hCS

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem two_mul_sum_sameScale_le_sqrt
    (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) (σ : ℝ)
    (f h : TensorEigenIdx (I := I) (M := M) g r s → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hh : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (h i) ^ 2 ≤ c ^ 2) :
    2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) ≤
      2 * c * Real.sqrt (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i) ^ 2) := by
  set A := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i) ^ 2 with hA
  set B := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (h i) ^ 2 with hB
  have hA_nonneg : 0 ≤ A :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _))
  have hB_nonneg : 0 ≤ B :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _))
  have hsq := sq_sum_sameScale_le (I := I) (M := M) S σ f h
  rw [← hA, ← hB] at hsq
  set P := ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (f i * h i) with hP
  have hP_sq : P ^ 2 ≤ A * B := hsq
  have hP_le_sqrtAB : P ≤ Real.sqrt (A * B) := by
    have h1 : P ≤ |P| := le_abs_self _
    have h2 : |P| ≤ Real.sqrt (A * B) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hP_sq
    exact le_trans h1 h2
  have hsqrtAB : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA_nonneg B
  have hsqrtB_le : Real.sqrt B ≤ c := by
    have := Real.sqrt_le_sqrt hh
    rwa [Real.sqrt_sq hc] at this
  have hmono : Real.sqrt A * Real.sqrt B ≤ Real.sqrt A * c :=
    mul_le_mul_of_nonneg_left hsqrtB_le (Real.sqrt_nonneg A)
  have hP_le : P ≤ Real.sqrt A * Real.sqrt B := by rw [← hsqrtAB]; exact hP_le_sqrtAB
  calc 2 * P ≤ 2 * (Real.sqrt A * Real.sqrt B) := by linarith [hP_le]
    _ ≤ 2 * (Real.sqrt A * c) := by linarith [hmono]
    _ = 2 * c * Real.sqrt A := by ring

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
