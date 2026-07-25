import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Bound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem sqrt_finset_sum_sq_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∑ i ∈ s, f i ^ 2) ≤ ∑ i ∈ s, f i := by
  have hsum_nn : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hf
  have hsq : ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
    have hterm : ∀ i ∈ s, f i ^ 2 ≤ f i * ∑ j ∈ s, f j := by
      intro i hi
      have hle : f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum hf hi
      calc f i ^ 2 = f i * f i := sq (f i) ▸ rfl
        _ ≤ f i * ∑ j ∈ s, f j := mul_le_mul_of_nonneg_left hle (hf i hi)
    calc ∑ i ∈ s, f i ^ 2 ≤ ∑ i ∈ s, f i * ∑ j ∈ s, f j := Finset.sum_le_sum hterm
      _ = (∑ i ∈ s, f i) ^ 2 := by rw [← Finset.sum_mul, sq]
  calc Real.sqrt (∑ i ∈ s, f i ^ 2) ≤ Real.sqrt ((∑ i ∈ s, f i) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ∑ i ∈ s, f i := Real.sqrt_sq hsum_nn

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_appFullSec_iteratedCovGrad_l2_window_bound
    (g : SmoothRiemannianMetric I M) (r m c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r m c I) :
    ∃ cc : ℕ → ℝ, (∀ k, 0 ≤ cc k) ∧
      ∀ (W : SmoothCcTensor g r m) (k : ℕ),
        ‖iteratedCovGrad g r c k (homTensorRSFieldApply (I := I) (M := M) g r m c Q W)‖ ≤
          cc k * ∑ i ∈ Finset.range (k + 1), ‖iteratedCovGrad g r m i W‖ := by
  classical
  obtain ⟨cp, hcp_nn, hcp⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g r m c Q
  refine ⟨fun k => Real.sqrt (cp k), fun k => Real.sqrt_nonneg _, fun W k => ?_⟩
  set Z : SmoothCcTensor g r (c + k) :=
    iteratedCovGrad g r c k (homTensorRSFieldApply (I := I) (M := M) g r m c Q W) with hZ_def
  have hZsq : ‖Z‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (c + k) x (Z.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) Z]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
      g r (c + k) Z
  have hWi_sq : ∀ i : ℕ,
      ‖iteratedCovGrad g r m i W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (m + i) x
          ((iteratedCovGrad g r m i W).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro i
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad g r m i W)]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
      g r (m + i) (iteratedCovGrad g r m i W)
  have hint_rhs : MeasureTheory.Integrable
      (fun x => cp k * ∑ i ∈ Finset.range (k + 1),
        riemannianFiberNormSq (I := I) (M := M) g r (m + i) x
          ((iteratedCovGrad g r m i W).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.Integrable.const_mul ?_ (cp k)
    refine MeasureTheory.integrable_finset_sum _ (fun i _ => ?_)
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r (m + i)
      (iteratedCovGrad g r m i W)
  have hmono : ‖Z‖ ^ 2 ≤ cp k * ∑ i ∈ Finset.range (k + 1),
      ‖iteratedCovGrad g r m i W‖ ^ 2 := by
    rw [hZsq]
    have hle := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g r (c + k) x (Z.toSection x)))
      hint_rhs
      (Filter.Eventually.of_forall (fun x => hcp W k x))
    refine le_trans hle (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finset_sum]
    · exact Finset.sum_congr rfl (fun i _ => (hWi_sq i).symm)
    · intro i _
      exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r (m + i)
        (iteratedCovGrad g r m i W)
  have hZ_nn : 0 ≤ ‖Z‖ := norm_nonneg _
  have hstep : ‖Z‖ ≤ Real.sqrt (cp k * ∑ i ∈ Finset.range (k + 1),
      ‖iteratedCovGrad g r m i W‖ ^ 2) := by
    rw [← Real.sqrt_sq hZ_nn]
    exact Real.sqrt_le_sqrt hmono
  refine le_trans hstep ?_
  rw [Real.sqrt_mul (hcp_nn k)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  exact sqrt_finset_sum_sq_le_sum (Finset.range (k + 1))
    (fun i => ‖iteratedCovGrad g r m i W‖) (fun i _ => norm_nonneg _)

section NormedAppCc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem exists_appCcRS_l2_norm_le (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : SmoothCcTensor g 0 b,
      ‖ccOperatorFieldComp (I := I) (M := M) g 0 b c Φ V‖ ≤ C * ‖V‖ := by
  classical
  obtain ⟨Cop, hCop_nn, hCop⟩ :=
    exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g 0 b c Φ
  refine ⟨Real.sqrt Cop, Real.sqrt_nonneg _, fun V => ?_⟩
  set Z : SmoothCcTensor g 0 c := ccOperatorFieldComp (I := I) (M := M) g 0 b c Φ V with hZ_def
  have hZL2 : ‖Z‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Z.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) Z]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0 c Z
  have hVL2 : ‖V‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (V.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) V]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g 0 b V
  have hZsq_le : ‖Z‖ ^ 2 ≤ Cop * ‖V‖ ^ 2 := by
    rw [hZL2, hVL2]
    have hg_int : MeasureTheory.Integrable
        (fun x => Cop * riemannianFiberNormSq (I := I) (M := M) g 0 b x (V.toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 b V).const_mul Cop
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 c x (Z.toSection x)))
      hg_int
      (Filter.Eventually.of_forall (fun x => hCop V x))
    rw [MeasureTheory.integral_const_mul] at hmono
    linarith
  have hZnn : 0 ≤ ‖Z‖ := norm_nonneg _
  have hVnn : 0 ≤ ‖V‖ := norm_nonneg _
  rw [← Real.sqrt_sq hZnn]
  calc Real.sqrt (‖Z‖ ^ 2) ≤ Real.sqrt (Cop * ‖V‖ ^ 2) := Real.sqrt_le_sqrt hZsq_le
    _ = Real.sqrt Cop * ‖V‖ := by rw [Real.sqrt_mul hCop_nn, Real.sqrt_sq hVnn]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_appCc_iteratedCovGrad_l2_window_bound (g : SmoothRiemannianMetric I M)
    (b c : ℕ) (Φ : SmoothCcTensor g b c) :
    ∃ cc : ℕ → ℝ, (∀ k, 0 ≤ cc k) ∧
      ∀ (W : SmoothCcTensor g 0 b) (k : ℕ),
        ‖iteratedCovGrad g 0 c k (operatorFieldApply (I := I) (M := M) g b c Φ W)‖ ≤
          cc k * ∑ i ∈ Finset.range (k + 1), ‖iteratedCovGrad g 0 b i W‖ := by
  classical
  choose CC hCC_nn hCC using fun (k i : ℕ) =>
    exists_appCcRS_l2_norm_le (I := I) (M := M) g (b + i) (c + k)
      (appCcLeibnizPsi (I := I) (M := M) g b c Φ k i)
  refine ⟨fun k => ∑ i ∈ Finset.range (k + 1), CC k i,
    fun k => Finset.sum_nonneg (fun i _ => hCC_nn k i), fun W k => ?_⟩
  rw [iteratedCovGrad_operatorFieldApply_eq (I := I) (M := M) g b c Φ W k]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ‖ccOperatorFieldComp (I := I) (M := M) g 0 (b + i) (c + k)
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ k i)
          (iteratedCovGrad (I := I) g 0 b i W)‖ ≤
        CC k i * ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad g 0 b j W‖ := by
    intro i hi
    refine le_trans (hCC k i (iteratedCovGrad (I := I) g 0 b i W)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCC_nn k i)
    exact Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad g 0 b j W‖)
      (fun j _ => norm_nonneg _) hi
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

end NormedAppCc

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_appFullSec_norm_le (g : SmoothRiemannianMetric I M) (r m c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r m c I) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : SmoothCcTensor g r m,
        ‖homTensorRSFieldApply (I := I) (M := M) g r m c Q W‖ ≤ C * ‖W‖ := by
  classical
  obtain ⟨cc, hcc_nn, hcc⟩ :=
    exists_appFullSec_iteratedCovGrad_l2_window_bound (I := I) (M := M) g r m c Q
  refine ⟨cc 0, hcc_nn 0, fun W => ?_⟩
  have h := hcc W 0
  simpa only [zero_add, Finset.sum_range_one, iteratedCovGrad_zero] using h

end Connection
end Integral
end DifferentialGeometry

end
