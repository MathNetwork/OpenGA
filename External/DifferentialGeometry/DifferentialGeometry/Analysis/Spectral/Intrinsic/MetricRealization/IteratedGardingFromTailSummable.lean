import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralSmoothRepresentative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralChartRegularityAnyOrder
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting





















































noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma resolvent_pow_eq_weight
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    (i.fst.val)⁻¹ ^ (2 * k + 1) =
      tensorSobolevWeight (I := I) (M := M) i ((2 * k + 1 : ℕ) : ℝ) := by
  rw [resolvent_eigenvalue_inv_eq_one_add_lambda (I := I) (M := M) g r s i]
  unfold tensorSobolevWeight
  rw [Real.rpow_natCast]










omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma garding_l1_sum_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    {p : ℝ}
    (h_tail_summable :
      Summable (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (-p)))
    {σ : ℝ} (hσ_def : σ = 2 * (2 * k + 1 : ℕ) + p)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (hT_fs : (Function.support T.coeff).Finite) :
    (∑ i ∈ hT_fs.toFinset,
        |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1)) ≤
      Real.sqrt (∑' i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s,
        tensorSobolevWeight (I := I) (M := M) i (-p)) * ‖T‖ := by
  classical
  set S := hT_fs.toFinset with hS_def
  set f : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i|
    with hf_def
  set d : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-p))
    with hd_def
  have hsummand : ∀ i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s,
      |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1) = f i * d i := by
    intro i
    rw [resolvent_pow_eq_weight (I := I) (M := M) g r s k i, hf_def, hd_def]
    have hweight_eq :
        tensorSobolevWeight (I := I) (M := M) i ((2 * k + 1 : ℕ) : ℝ) =
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
            Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-p)) := by
      rw [← Real.sqrt_mul (tensorSobolevWeight_nonneg (I := I) (M := M) i σ),
        ← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ (-p)]
      have hexp : σ + (-p) = ((2 * k + 1 : ℕ) : ℝ) + ((2 * k + 1 : ℕ) : ℝ) := by
        rw [hσ_def]; push_cast; ring
      rw [hexp, tensorHs.tensorSobolevWeight_add (I := I) (M := M) i
        ((2 * k + 1 : ℕ) : ℝ) ((2 * k + 1 : ℕ) : ℝ),
        Real.sqrt_mul_self (tensorSobolevWeight_nonneg (I := I) (M := M) i _)]
    rw [hweight_eq]; ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  have hCS : (∑ i ∈ S, f i * d i) ^ 2 ≤
      (∑ i ∈ S, (f i) ^ 2) * ∑ i ∈ S, (d i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S f d
  have hfsq : ∑ i ∈ S, (f i) ^ 2 ≤ ‖T‖ ^ 2 := by
    have heq : ∑ i ∈ S, (f i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hf_def, mul_pow,
        Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i σ), sq_abs]
    rw [heq, tensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) T.weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  have hdsq : ∑ i ∈ S, (d i) ^ 2 ≤
      ∑' i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s,
        tensorSobolevWeight (I := I) (M := M) i (-p) := by
    have heq : ∑ i ∈ S, (d i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (-p) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd_def, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (-p))]
    rw [heq]
    refine Summable.sum_le_tsum S (fun i _ => ?_) h_tail_summable
    exact tensorSobolevWeight_nonneg (I := I) (M := M) i (-p)
  set Stail : ℝ :=
    ∑' i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i (-p) with hStail_def
  have hStail_nonneg : 0 ≤ Stail := by
    rw [hStail_def]
    exact tsum_nonneg (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i (-p))
  have hsum_nonneg : 0 ≤ ∑ i ∈ S, f i * d i := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [hf_def, hd_def]
    have h1 : 0 ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (-p)) :=
      Real.sqrt_nonneg _
    positivity
  have hfsq_nn : 0 ≤ ∑ i ∈ S, (f i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hbound_sq : (∑ i ∈ S, f i * d i) ^ 2 ≤ ‖T‖ ^ 2 * Stail := by
    calc (∑ i ∈ S, f i * d i) ^ 2
        ≤ (∑ i ∈ S, (f i) ^ 2) * ∑ i ∈ S, (d i) ^ 2 := hCS
      _ ≤ ‖T‖ ^ 2 * Stail := by
          apply mul_le_mul hfsq hdsq (Finset.sum_nonneg (fun i _ => sq_nonneg _))
          exact sq_nonneg _
  have hrhs_eq : Real.sqrt (‖T‖ ^ 2 * Stail) = ‖T‖ * Real.sqrt Stail := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg T)]
  calc ∑ i ∈ S, f i * d i
      = Real.sqrt ((∑ i ∈ S, f i * d i) ^ 2) := (Real.sqrt_sq hsum_nonneg).symm
    _ ≤ Real.sqrt (‖T‖ ^ 2 * Stail) := Real.sqrt_le_sqrt hbound_sq
    _ = ‖T‖ * Real.sqrt Stail := hrhs_eq
    _ = Real.sqrt Stail * ‖T‖ := by ring


















theorem iteratedGardingExtensionBound_of_eigenvalueTailSummable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_tail : EigenvalueTailSummable (I := I) (M := M) g r s) :
    IteratedGardingExtensionBound (I := I) (M := M) g r s := by
  classical
  obtain ⟨p, hp_pos, h_tail_p⟩ := h_tail
  have h_tail_summable :
      Summable (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (-p)) := by
    have h_eq :
        (fun i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s =>
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p)) =
        (fun i => tensorSobolevWeight (I := I) (M := M) i (-p)) := by
      funext i; rfl
    rwa [h_eq] at h_tail_p
  set Stail : ℝ :=
    ∑' i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i (-p) with hStail_def
  have hStail_nonneg : 0 ≤ Stail :=
    tsum_nonneg (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i (-p))
  intro k
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    tensorHsSmoothRepr_wtwokTwoNorm_le_uniform
      (I := I) (M := M) g r s k
  refine ⟨2 * (2 * k + 1 : ℕ) + p, by positivity, C₀ * Real.sqrt Stail,
    mul_nonneg hC₀_nn (Real.sqrt_nonneg _), ?_⟩
  intro T hT_fs
  have h_mem : MemWtwokTwo (I := I) (M := M) g k
      (tensorHsSmoothRepr (I := I) (M := M) T hT_fs) :=
    tensorHsSmoothRepr_memWtwokTwo (I := I) (M := M) T hT_fs k
  have hbd := hC₀_bound T hT_fs
  have h_l1_nn : 0 ≤ ∑ i ∈ hT_fs.toFinset,
      |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1) := by
    refine Finset.sum_nonneg (fun i _ => ?_)
    have h_pow_nn : 0 ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) := by
      rw [resolvent_pow_eq_weight (I := I) (M := M) g r s k i]
      exact tensorSobolevWeight_nonneg (I := I) (M := M) i _
    exact mul_nonneg (abs_nonneg _) h_pow_nn
  have hrhs_ne_top :
      ENNReal.ofReal C₀ *
          ENNReal.ofReal (∑ i ∈ hT_fs.toFinset,
            |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top <;> exact ENNReal.ofReal_ne_top
  have htoReal :
      (wtwokTwoNorm (I := I) (M := M) g k
        (tensorHsSmoothRepr (I := I) (M := M) T hT_fs)).toReal ≤
      C₀ * (∑ i ∈ hT_fs.toFinset,
        |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    have h := ENNReal.toReal_mono hrhs_ne_top hbd
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀_nn,
      ENNReal.toReal_ofReal h_l1_nn] at h
  have hl1 := garding_l1_sum_le (I := I) (M := M) g r s k h_tail_summable
    (σ := 2 * (2 * k + 1 : ℕ) + p) rfl T hT_fs
  calc (wtwokTwoNorm (I := I) (M := M) g k
          (tensorHsSmoothRepr (I := I) (M := M) T hT_fs)).toReal
      ≤ C₀ * (∑ i ∈ hT_fs.toFinset,
          |T.coeff i| * (i.fst.val)⁻¹ ^ (2 * k + 1)) := htoReal
    _ ≤ C₀ * (Real.sqrt Stail * ‖T‖) :=
        mul_le_mul_of_nonneg_left hl1 hC₀_nn
    _ = C₀ * Real.sqrt Stail * ‖T‖ := by ring

















theorem iteratedGardingExtensionBound_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    IteratedGardingExtensionBound (I := I) (M := M) g r s :=
  iteratedGardingExtensionBound_of_eigenvalueTailSummable (I := I) (M := M) g r s
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g r s h)

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
