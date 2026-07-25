import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability

set_option maxHeartbeats 1600000

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private theorem weight_sum_high
    (g : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * Module.finrank ℝ E + 4 + (weylSobolevExp (E := E) + 1) ≤ a)
    (x : M) (v w : TangentSpace I x) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
        (eigenBilinScalar (I := I) g x v w i *
          (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) ^ 2) := by
  set m : ℕ := 2 * Module.finrank ℝ E + 4 with hm_def
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hm_le : 2 * Module.finrank ℝ E + 4 ≤ m := by rw [hm_def]
  have hmsW : m + sW ≤ a := by
    simpa [hm_def, hsW_def, add_assoc] using ha
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]
    push_cast
    linarith
  have hweyl : Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) :=
    tensorEigen_summable_negpow (I := I) (M := M) g (sW : ℝ) hsW_gt
  obtain ⟨C, hC_pos, hC⟩ :=
    abs_eigenBilinScalar_le (I := I) (M := M) g m hm_le x v w
  set K : ℝ := Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) with hK_def
  set D : ℝ := C * K with hD_def
  have hK_nn : 0 ≤ K := by
    rw [hK_def]
    positivity
  have hD_nn : 0 ≤ D := by
    rw [hD_def]
    exact mul_nonneg hC_pos.le hK_nn
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hweyl.mul_left (D ^ 2))
  · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
      (sq_nonneg _)
  · set wa := tensorSobolevWeight (I := I) (M := M) i (a : ℝ) with hwa_def
    set wm := tensorSobolevWeight (I := I) (M := M) i (m : ℝ) with hwm_def
    set e := eigenBilinScalar (I := I) g x v w i with he_def
    have hwa_pos : 0 < wa := by
      rw [hwa_def]
      exact tensorSobolevWeight_pos (I := I) (M := M) i (a : ℝ)
    have hwm_nn : 0 ≤ wm := by
      rw [hwm_def]
      exact tensorSobolevWeight_nonneg (I := I) (M := M) i (m : ℝ)
    have he_le : |e| ≤ D * Real.sqrt wm := by
      rw [he_def, hD_def, hK_def, hwm_def]
      calc
        |eigenBilinScalar (I := I) g x v w i|
            ≤ C * Real.sqrt
                (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) *
              (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) := hC i
        _ = (C * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w))) *
              Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) := by
              ring
    have hright_nn : 0 ≤ D * Real.sqrt wm :=
      mul_nonneg hD_nn (Real.sqrt_nonneg _)
    have hprod_nn :
        0 ≤ (D * Real.sqrt wm - |e|) * (D * Real.sqrt wm + |e|) :=
      mul_nonneg (sub_nonneg.mpr he_le)
        (add_nonneg hright_nn (abs_nonneg _))
    have he_sq : e ^ 2 ≤ D ^ 2 * wm := by
      have habs_sq : |e| ^ 2 ≤ (D * Real.sqrt wm) ^ 2 := by
        nlinarith
      calc
        e ^ 2 = |e| ^ 2 := (sq_abs e).symm
        _ ≤ (D * Real.sqrt wm) ^ 2 := habs_sq
        _ = D ^ 2 * wm := by rw [mul_pow, Real.sq_sqrt hwm_nn]
    have hexp : (m : ℝ) - (a : ℝ) ≤ -(sW : ℝ) := by
      have hmsW' : (m : ℝ) + (sW : ℝ) ≤ (a : ℝ) := by
        exact_mod_cast hmsW
      linarith
    have hweight_le :
        tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) - (a : ℝ)) ≤
          tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
      unfold tensorSobolevWeight
      exact Real.rpow_le_rpow_of_exponent_le
        (one_le_one_add_lambda (I := I) (M := M) i) hexp
    have hterm :
        wa * (e * wa⁻¹) ^ 2 = e ^ 2 * wa⁻¹ := by
      calc
        wa * (e * wa⁻¹) ^ 2 = e ^ 2 * (wa * wa⁻¹) * wa⁻¹ := by ring
        _ = e ^ 2 * wa⁻¹ := by rw [mul_inv_cancel₀ hwa_pos.ne']; ring
    rw [hterm]
    calc
      e ^ 2 * wa⁻¹ ≤ (D ^ 2 * wm) * wa⁻¹ :=
        mul_le_mul_of_nonneg_right he_sq (inv_nonneg.mpr hwa_pos.le)
      _ = D ^ 2 * (wm * wa⁻¹) := by ring
      _ = D ^ 2 *
          tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) - (a : ℝ)) := by
        rw [hwm_def, hwa_def,
          tensorHs.tensorSobolevWeight_sub (I := I) (M := M)]
      _ ≤ D ^ 2 * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) :=
        mul_le_mul_of_nonneg_left hweight_le (sq_nonneg D)

private theorem eval_hasSum_high
    (g : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * Module.finrank ℝ E + 4 + (weylSobolevExp (E := E) + 1) ≤ a)
    (T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    HasSum
      (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 T) i *
          eigenBilinScalar (I := I) g x v w i)
      (ccTensorBilinSymm (I := I) g T x v w) := by
  classical
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2
  let c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 T) i
  let e : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => eigenBilinScalar (I := I) g x v w i
  let wrep : tensorHs (I := I) (M := M) g 0 2 (a : ℝ) :=
    { coeff := fun i => e i *
          (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹
      weighted_summable :=
        weight_sum_high (I := I) (M := M) g a ha x v w }
  let zrep : tensorHs (I := I) (M := M) g 0 2 (a : ℝ) :=
    { coeff := c
      weighted_summable :=
        smoothCcTensor_tensorL2Coeff_weighted_summable
          (I := I) (M := M) g (a : ℝ) T hc }
  have hsum : Summable (fun i => c i * e i) := by
    have hprod := tensorHs.weightedProd_summable
      (I := I) (M := M) wrep zrep
    refine hprod.congr (fun i => ?_)
    change tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
        ((e i * (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) * c i) =
      c i * e i
    have hw_pos :=
      tensorSobolevWeight_pos (I := I) (M := M) i (a : ℝ)
    calc
      tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
          ((e i * (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) * c i) =
        (tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
          (tensorSobolevWeight (I := I) (M := M) i (a : ℝ))⁻¹) * (c i * e i) := by
            ring
      _ = c i * e i := by rw [mul_inv_cancel₀ hw_pos.ne', one_mul]
  have hmem : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hc hσ vH = SmoothCcTensor.toL2 T := by
    intro σ hσ
    refine allHs_of_weighted_summable_pub (I := I) (M := M) g
      (SmoothCcTensor.toL2 T) (fun τ _ => ?_) σ hσ
    exact smoothCcTensor_tensorL2Coeff_weighted_summable
      (I := I) (M := M) g τ T hc
  have heq := ccTensorBilinSymm_eigenSeries_eq (I := I) (M := M) g
    (SmoothCcTensor.toL2 T) hmem T (SmoothCcTensor.toL2_apply T) x v w
    (by simpa [c, e] using hsum)
  rw [heq]
  simpa [c, e] using hsum.hasSum

end DifferentialGeometry.PDE.RicciFlow
