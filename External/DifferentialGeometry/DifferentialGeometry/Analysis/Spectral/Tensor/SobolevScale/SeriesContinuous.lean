import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Synthesis
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace DifferentialGeometry

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

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
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem tensorHs_continuousOn_of_coeff_of_higher_mass
    (g : SmoothRiemannianMetric I M) {σ σ' : ℝ}
    (hσσ' : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ)
    {s : Set ℝ} (W : ℝ → tensorHs (I := I) (M := M) g 0 2 σ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hcoeff : ∀ t ∈ s, ∀ i, (W t).coeff i = φ i t)
    (hφ_cont : ∀ i, ContinuousOn (φ i) s)
    {Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ} (hCmaj : Summable Cmaj)
    (hmass : ∀ i, ∀ t ∈ s,
      tensorSobolevWeight (I := I) (M := M) i σ' * (φ i t) ^ 2 ≤ Cmaj i) :
    ContinuousOn W s := by
  classical

  set negWeight : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) with hnegWeight
  have hnegWeight_sum : Summable negWeight :=
    tensorEigen_summable_negpow (I := I) (M := M) g (σ' - σ) hσσ'
  set U : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => (negWeight i + Cmaj i) / 2 with hU
  have hU_sum : Summable U :=
    ((hnegWeight_sum.add hCmaj).div_const 2)

  set f : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → tensorHs (I := I) (M := M) g 0 2 σ :=
    fun i t => φ i t •
      tensorHsBasisVec (I := I) (M := M) (g := g) (r := 0) (s := 2) σ i with hf

  have hf_cont : ∀ i, ContinuousOn (f i) s := by
    intro i
    exact (hφ_cont i).smul continuousOn_const

  have hf_bound : ∀ i, ∀ t ∈ s, ‖f i t‖ ≤ U i := by
    intro i t ht
    have hnorm : ‖f i t‖ =
        |φ i t| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) := by
      rw [hf, norm_smul, Real.norm_eq_abs, norm_tensorHsBasisVec]

    have hsq : ‖f i t‖ ^ 2 = tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 := by
      rw [hnorm, mul_pow, sq_abs, sq_sqrt_tensorSobolevWeight]
      ring

    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
        negWeight i * tensorSobolevWeight (I := I) (M := M) i σ' := by
      have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
      rw [hnegWeight]
      unfold tensorSobolevWeight
      rw [← Real.rpow_add hbase, show -(σ' - σ) + σ' = σ from by ring]

    have hsq_le : ‖f i t‖ ^ 2 ≤ negWeight i * Cmaj i := by
      rw [hsq, hsplit, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hmass i t ht)
        (by rw [hnegWeight]; exact tensorSobolevWeight_nonneg (I := I) (M := M) i _)

    have hnW_nonneg : 0 ≤ negWeight i := by
      rw [hnegWeight]; exact tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hC_nonneg : 0 ≤ Cmaj i :=
      le_trans (mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ') (sq_nonneg _))
        (hmass i t ht)
    have hnorm_nonneg : 0 ≤ ‖f i t‖ := norm_nonneg _
    have hsqrt : ‖f i t‖ ≤ Real.sqrt (negWeight i * Cmaj i) := by
      rw [show ‖f i t‖ = Real.sqrt (‖f i t‖ ^ 2) from (Real.sqrt_sq hnorm_nonneg).symm]
      exact Real.sqrt_le_sqrt hsq_le
    have hgeom : Real.sqrt (negWeight i * Cmaj i) ≤ U i := by
      rw [hU, Real.sqrt_mul hnW_nonneg]
      have h2 : 2 * Real.sqrt (negWeight i) * Real.sqrt (Cmaj i) ≤
          Real.sqrt (negWeight i) ^ 2 + Real.sqrt (Cmaj i) ^ 2 :=
        two_mul_le_add_sq _ _
      rw [Real.sq_sqrt hnW_nonneg, Real.sq_sqrt hC_nonneg] at h2
      linarith
    exact hsqrt.trans hgeom

  have hcont_tsum : ContinuousOn (fun t => ∑' i, f i t) s :=
    continuousOn_tsum hf_cont hU_sum (fun i t ht => hf_bound i t ht)

  refine hcont_tsum.congr ?_
  intro t ht
  have hsum : HasSum
      (fun i => (W t).coeff i •
        tensorHsBasisVec (I := I) (M := M) (g := g) (r := 0) (s := 2) σ i) (W t) :=
    tensorHs.hasSum_smul_basisVec (W t)
  have hsum' : HasSum (fun i => f i t) (W t) := by
    refine hsum.congr_fun ?_
    intro i
    rw [hf, hcoeff t ht i]
  exact (hsum'.tsum_eq).symm
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem mass_le_of_compact
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {σ σ' : ℝ}
    (hneg_sum : Summable (fun i : TensorEigenIdx
      (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ))))
    {K : Set ℝ}
    (hK : IsCompact K)
    (W : ℝ → tensorHs (I := I) (M := M) g r s σ')
    (hW : ContinuousOn W K)
    (φ : TensorEigenIdx (I := I) (M := M) g r s → ℝ → ℝ)
    (hcoeff : ∀ t ∈ K, ∀ i, (W t).coeff i = φ i t) :
    ∃ B : TensorEigenIdx (I := I) (M := M) g r s → ℝ,
      Summable B ∧
        ∀ i, ∀ t ∈ K,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (φ i t) ^ 2 ≤ B i := by
  classical
  have hnorm : ContinuousOn (fun t => ‖W t‖) K :=
    continuous_norm.comp_continuousOn hW
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := by
    exact le_max_right _ _
  let negWeight : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ))
  have hneg_sum' : Summable negWeight := by
    simpa only [negWeight] using hneg_sum
  let B : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => C0 ^ 2 * negWeight i
  have hB : Summable B := by
    exact hneg_sum'.mul_left (C0 ^ 2)
  refine ⟨B, hB, ?_⟩
  intro i t ht
  have hCt : ‖W t‖ ≤ C0 := by
    exact (hC ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hterm :
      tensorSobolevWeight (I := I) (M := M) i σ' *
          ((W t).coeff i) ^ 2 ≤ ‖W t‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    refine Summable.le_tsum (W t).weighted_summable i (fun j _ => ?_)
    exact mul_nonneg
      (tensorSobolevWeight_nonneg (I := I) (M := M) j σ')
      (sq_nonneg _)
  have htermC :
      tensorSobolevWeight (I := I) (M := M) i σ' *
          ((W t).coeff i) ^ 2 ≤ C0 ^ 2 := by
    exact hterm.trans ((sq_le_sq₀ (norm_nonneg _) hC0).2 hCt)
  have hneg : 0 ≤ negWeight i := by
    exact tensorSobolevWeight_nonneg (I := I) (M := M) i _
  have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  have hsplit :
      tensorSobolevWeight (I := I) (M := M) i σ =
        negWeight i * tensorSobolevWeight (I := I) (M := M) i σ' := by
    dsimp only [negWeight]
    unfold tensorSobolevWeight
    rw [← Real.rpow_add hbase,
      show -(σ' - σ) + σ' = σ from by ring]
  rw [← hcoeff t ht i, hsplit]
  calc
    (negWeight i *
          tensorSobolevWeight (I := I) (M := M) i σ') *
          ((W t).coeff i) ^ 2 =
        negWeight i *
          (tensorSobolevWeight (I := I) (M := M) i σ' *
            ((W t).coeff i) ^ 2) := by ring
    _ ≤ negWeight i * C0 ^ 2 :=
      mul_le_mul_of_nonneg_left htermC hneg
    _ = B i := by
      simp only [B]
      ring


end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry
