import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmOrder1KoszulTameEnvelope
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder1TameEnvelope
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder0KernelJetGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]


theorem linearizedRicciConnDiffOrder1CoeffField_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨ΛΦ, KΦ, hΛΦ, hKΦ_nn, hΦfeed⟩ :=
    ricciCometricFourTraceCastG0_order0sup_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛW, KW, hΛW, hKW_nn, hWfeed⟩ :=
    linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 i).choose *
      (ΛW ^ 2 * ∑ n ∈ Finset.range (i + 1), KΦ n
        + ΛΦ ^ 2 * ∑ l ∈ Finset.range (i + 1), KW l),
    fun i => by
      refine mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
          (I := I) (M := M) g₀ 4 3 2 4 i).choose_spec.1) (add_nonneg ?_ ?_)
      · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun n _ => hKΦ_nn n))
      · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun l _ => hKW_nn l)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  obtain ⟨hΦsup, hΦtame⟩ := hΦfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hWsup, hWtame⟩ := hWfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hgrid_int, hgrid_bound⟩ :=
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 3 2 4 i).choose_spec.2
      (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)
      ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  rw [linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS (I := I) (M := M) g₀ g₁]
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (2 + i)
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 2
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)))
    (fun x => diagonalGridGrowthFactor (E := E) i *
      ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 4 2 n
              (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 4 l
                  (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)).toSection x))
    (hgrid_int.const_mul (diagonalGridGrowthFactor (E := E) i))
    (fun x => riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le (I := I) (M := M) g₀
      i 3 4 2 (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁) x)
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  have hAnn : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
  have hCnn : (0 : ℝ) ≤ (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 3 2 4 i).choose :=
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 3 2 4 i).choose_spec.1
  have hwin2_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSa : ∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 n
          (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
      (∑ n ∈ Finset.range (i + 1), KΦ n) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun n hn => ?_)
    refine le_trans (hΦtame n) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKΦ_nn n)
    have hsub : ∑ j ∈ Finset.range (n + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
      rw [Finset.mem_range] at hn
      omega
    linarith
  have hSc : ∑ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 4 l
          (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2 ≤
      (∑ l ∈ Finset.range (i + 1), KW l) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun l hl => ?_)
    refine le_trans (hWtame l) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKW_nn l)
    have hsub : ∑ j ∈ Finset.range (l + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
      rw [Finset.mem_range] at hl
      omega
    linarith
  calc diagonalGridGrowthFactor (E := E) i * ∫ x,
          (∑ n ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                ((iteratedCovGrad (I := I) g₀ 4 2 n
                  (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (i + 1 - n),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                    ((iteratedCovGrad (I := I) g₀ 3 4 l
                      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ diagonalGridGrowthFactor (E := E) i *
          ((exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 4 3 2 4 i).choose *
            (ΛW ^ 2 * ∑ n ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 n
                  (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 3 4 l
                  (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hgrid_bound hAnn
    _ ≤ diagonalGridGrowthFactor (E := E) i *
          ((exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 4 3 2 4 i).choose *
            ((ΛW ^ 2 * ∑ n ∈ Finset.range (i + 1), KΦ n
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (i + 1), KW l) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCnn) hAnn
        have h1 := mul_le_mul_of_nonneg_left hSa (sq_nonneg ΛW)
        have h2 := mul_le_mul_of_nonneg_left hSc (sq_nonneg ΛΦ)
        nlinarith [h1, h2]
    _ = diagonalGridGrowthFactor (E := E) i *
          (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 4 3 2 4 i).choose *
          (ΛW ^ 2 * ∑ n ∈ Finset.range (i + 1), KΦ n
            + ΛΦ ^ 2 * ∑ l ∈ Finset.range (i + 1), KW l) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring


theorem exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨KA, hKA_nn, hKA⟩ :=
    linearizedRicciConnDiffOrder1CoeffField_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KB, hKB_nn, hKB⟩ :=
    ricciArmOrder1KoszulCoeff_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * KA i + 2 * KB i,
    fun i => by linarith [hKA_nn i, hKB_nn i], ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hwin : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤
        (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
    nlinarith [mul_le_mul hnorm_le hnorm_le (norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  have hA : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
      KA i * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) :=
    hKA (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  have hB : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
      KB i * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) :=
    hKB (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  have hwinsum : ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_le_sum (fun j _ => hwin j)
  have hW_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hWP_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hA' : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
      KA i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
    refine le_trans hA (mul_le_mul_of_nonneg_left (by linarith [hwinsum]) (hKA_nn i))
  have hB' : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
      KB i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
    refine le_trans hB (mul_le_mul_of_nonneg_left (by linarith [hwinsum]) (hKB_nn i))
  rw [iteratedCovGrad_sub]
  have htri : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)‖ +
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ :=
    norm_sub_le _ _
  nlinarith [htri, hA', hB',
    norm_nonneg (iteratedCovGrad (I := I) g₀ 3 2 i
      (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 3 2 i
      (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)‖ -
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖)]

theorem corrArm0Combination_eq_order0_add_halfRiemann
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
        - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
        + (3 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) := by
  rw [show linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s =
      linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl,
    show linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s =
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl,
    show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num, add_smul, one_smul]
  abel

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_rfns_iteratedCovGrad_fixedCoeffField_bound
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 2 2) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i S).toSection x) ≤ c i := by
  have h : ∀ i : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i S).toSection x) ≤ c := fun i =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i S)
  choose c hc0 hcb using h
  exact ⟨c, hc0, hcb⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

private def pJetGridWindow (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k

private lemma pJetGridWindow_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) :
    0 ≤ pJetGridWindow b i :=
  Finset.sum_nonneg (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)

private lemma one_le_pJetGridWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) :
    1 ≤ pJetGridWindow b i := by
  rw [← Combinatorics.antidiagonalTupleGrid_zero b]
  exact Finset.single_le_sum
    (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
    (Finset.mem_range.mpr (by omega))

private lemma pJetGridWindow_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {i i' : ℕ} (h : i ≤ i') :
    pJetGridWindow b i ≤ pJetGridWindow b i' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (show i + 3 ≤ i' + 3 by omega)) ?_
  intro k _ _
  exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pJetGridWindow_eq_tripleSum (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (x : M) (i : ℕ) :
    pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i =
      ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := rfl


theorem riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
  classical
  obtain ⟨CF, hCF_nn, hCF⟩ :=
    rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CK, hCK_nn, hCK⟩ :=
    rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0KernelField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ n ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1 - n),
        CF n * CK l * Combinatorics.antidiagonalTupleGridWindowMulConst n (l + 2),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun l _ =>
        mul_nonneg (mul_nonneg (hCF_nn n) (hCK_nn l))
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg n (l + 2))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  have hwin_nn : ∀ w : ℕ, 0 ≤ Combinatorics.antidiagonalTupleGridWindow b w :=
    fun w => Combinatorics.antidiagonalTupleGridWindow_nonneg b hb w
  have hF : ∀ n : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
      ((iteratedCovGrad (I := I) g₀ 4 2 n
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
      CF n * Combinatorics.antidiagonalTupleGridWindow b (n + 1) :=
    fun n => hCF g₁ P htie hδ_le hδ0 hbound n x
  have hK : ∀ l : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 4 l
        (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) ≤
      CK l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) :=
    fun l => hCK g₁ P htie hδ_le hδ0 hbound l x
  rw [linearizedRicciConnDiffOrder0CoeffField_eq_ricciCometricFourTrace_comp_kernelField (I := I) (M := M) g₀ g₁]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 4 2 (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
    (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁) x) ?_
  have hterm : ∀ n ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 4 2 n
            (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 4 l
              (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) ≤
      (∑ l ∈ Finset.range (i + 1 - n),
        CF n * CK l * Combinatorics.antidiagonalTupleGridWindowMulConst n (l + 2)) *
        Combinatorics.antidiagonalTupleGridWindow b (i + 3) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have h2 : (∑ l ∈ Finset.range (i + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 4 l
            (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - n),
          CK l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) :=
      Finset.sum_le_sum (fun l _ => hK l)
    have hprod : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 4 2 n
            (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) *
        (∑ l ∈ Finset.range (i + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 4 l
              (linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x)) ≤
        (CF n * Combinatorics.antidiagonalTupleGridWindow b (n + 1)) *
          ∑ l ∈ Finset.range (i + 1 - n),
            CK l * Combinatorics.antidiagonalTupleGridWindow b (l + 3) :=
      mul_le_mul (hF n) h2
        (Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (4 + l) x _))
        (mul_nonneg (hCF_nn n) (hwin_nn (n + 1)))
    refine le_trans hprod ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun l hl => ?_)
    rw [Finset.mem_range] at hl
    have hww : Combinatorics.antidiagonalTupleGridWindow b (n + 1) *
        Combinatorics.antidiagonalTupleGridWindow b (l + 3) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst n (l + 2) *
          Combinatorics.antidiagonalTupleGridWindow b (n + l + 3) :=
      Combinatorics.antidiagonalTupleGridWindow_mul_le b hb n (l + 2)
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (n + l + 3) ≤
        Combinatorics.antidiagonalTupleGridWindow b (i + 3) :=
      Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hc_nn : (0 : ℝ) ≤ CF n * CK l := mul_nonneg (hCF_nn n) (hCK_nn l)
    calc (CF n * Combinatorics.antidiagonalTupleGridWindow b (n + 1)) *
            (CK l * Combinatorics.antidiagonalTupleGridWindow b (l + 3))
        = (CF n * CK l) * (Combinatorics.antidiagonalTupleGridWindow b (n + 1) *
            Combinatorics.antidiagonalTupleGridWindow b (l + 3)) := by ring
      _ ≤ (CF n * CK l) * (Combinatorics.antidiagonalTupleGridWindowMulConst n (l + 2) *
            Combinatorics.antidiagonalTupleGridWindow b (n + l + 3)) :=
          mul_le_mul_of_nonneg_left hww hc_nn
      _ ≤ (CF n * CK l) * (Combinatorics.antidiagonalTupleGridWindowMulConst n (l + 2) *
            Combinatorics.antidiagonalTupleGridWindow b (i + 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmono
              (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg n (l + 2)))
            hc_nn
      _ = CF n * CK l * Combinatorics.antidiagonalTupleGridWindowMulConst n (l + 2) *
            Combinatorics.antidiagonalTupleGridWindow b (i + 3) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul]
  rw [show (∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
      Combinatorics.antidiagonalTupleGridWindow b (i + 3) from rfl]
  exact le_of_eq (by ring)

set_option maxHeartbeats 3200000 in

theorem riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffFieldInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M)
                  g₀ g₁))).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  have hSW_ex : ∀ q : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 2 q
          (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤ c := fun q =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + q)
      (iteratedCovGrad (I := I) g₀ 2 2 q (ccInputSlotSwapField (I := I) (M := M) g₀))
  choose SW hSW_nn hSW using hSW_ex
  refine ⟨fun i => ((i : ℝ) + 3) * ((1 / 2 : ℝ) * CL i +
      (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CL i') *
        (∑ l ∈ Finset.range (i + 1), SW l))), ?_, ?_⟩
  · intro i
    have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), CL i' :=
      Finset.sum_nonneg fun i' _ => hCL_nn i'
    have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l :=
      Finset.sum_nonneg fun l _ => hSW_nn l
    have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
    have h1 : 0 ≤ CL i := hCL_nn i
    positivity
  · intro g₁ P htie δ hδ_le hδ0 hbound i x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
    have hb_nn : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    have hPJW_nn : 0 ≤ pJetGridWindow b i := pJetGridWindow_nonneg b hb_nn i
    have hL : ∀ n : ℕ, n ≤ i →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M)
              g₀ g₁)).toSection x) ≤
        CL n * pJetGridWindow b i := by
      intro n hn
      refine le_trans (hCL g₁ P htie hδ_le hδ0 hbound n x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCL_nn n)
      rw [← pJetGridWindow_eq_tripleSum (I := I) (M := M) g₀ P x n]
      exact pJetGridWindow_mono b hb_nn hn
    have hsubject : ccInputSlotSymm (I := I) (M := M) g₀
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁) =
        (1 / 2 : ℝ) • (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀)) := rfl
    rw [hsubject]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) • (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
        SmoothCcTensor.toSection_smul]
      rfl
    rw [hsm, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
    have hLi := hL i (le_refl i)
    have hApp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
        diagonalGridGrowthFactor (E := E) i * ((∑ i' ∈ Finset.range (i + 1), CL i') *
          ((∑ l ∈ Finset.range (i + 1), SW l) * pJetGridWindow b i)) := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
        (I := I) (M := M) g₀ i 2 2 2
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
        (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i' hi' => ?_
      rw [Finset.mem_range] at hi'
      have hswapsum : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), SW l := by
        refine le_trans (Finset.sum_le_sum fun l _ => hSW l x) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) ?_
        exact fun l _ _ => hSW_nn l
      have hLi' := hL i' (by omega)
      have hswap_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 2 2 i'
                (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M)
                  g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ (CL i' * pJetGridWindow b i) * (∑ l ∈ Finset.range (i + 1), SW l) :=
            mul_le_mul hLi' hswapsum hswap_nn (mul_nonneg (hCL_nn i') hPJW_nn)
        _ = CL i' * ((∑ l ∈ Finset.range (i + 1), SW l) * pJetGridWindow b i) := by ring
    have hconv : pJetGridWindow b i ≤
        ((i : ℝ) + 3) * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
      calc pJetGridWindow b i
          = ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k := rfl
        _ ≤ ∑ k ∈ Finset.range (i + 3),
              Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            rw [Finset.mem_range] at hk
            exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
              (by omega) (by omega)
        _ = ((i : ℝ) + 3) * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hmid : (1 / 4 : ℝ) * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M)
              g₀ g₁)).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
              (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x)) ≤
        ((1 / 2 : ℝ) * CL i +
          (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CL i') *
            (∑ l ∈ Finset.range (i + 1), SW l))) * pJetGridWindow b i := by
      nlinarith [hLi, hApp]
    refine le_trans hmid ?_
    have hC0_nn : 0 ≤ (1 / 2 : ℝ) * CL i +
        (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CL i') *
          (∑ l ∈ Finset.range (i + 1), SW l)) := by
      have h2 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), CL i' :=
        Finset.sum_nonneg fun i' _ => hCL_nn i'
      have h3 : 0 ≤ ∑ l ∈ Finset.range (i + 1), SW l :=
        Finset.sum_nonneg fun l _ => hSW_nn l
      have h4 : 0 ≤ diagonalGridGrowthFactor (E := E) i := appCcGdiag_nonneg (E := E) i
      have h1 : 0 ≤ CL i := hCL_nn i
      positivity
    calc ((1 / 2 : ℝ) * CL i +
          (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CL i') *
            (∑ l ∈ Finset.range (i + 1), SW l))) * pJetGridWindow b i
        ≤ ((1 / 2 : ℝ) * CL i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CL i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) *
            (((i : ℝ) + 3) * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3)) :=
          mul_le_mul_of_nonneg_left hconv hC0_nn
      _ = ((i : ℝ) + 3) * ((1 / 2 : ℝ) * CL i +
            (1 / 2 : ℝ) * (diagonalGridGrowthFactor (E := E) i * (∑ i' ∈ Finset.range (i + 1), CL i') *
              (∑ l ∈ Finset.range (i + 1), SW l))) *
            Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) := by ring

set_option maxHeartbeats 3200000 in

theorem riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfBackgroundDifferenceCombinationInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                  + (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
                      - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)))).toSection
              x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨CQ, hCQ_nn, hCQ⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0AACommCoeffFieldInputSymm_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    rfns_iteratedCovGrad_bgRDiffRefoldRemainderFieldInputSymm_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CL, hCL_nn, hCL⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffFieldInputSymm_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CK, hCK_nn, hCK⟩ :=
    rfns_iteratedCovGrad_refoldKernelContractionFieldInputSymm_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  let C : ℕ → ℝ := fun i => 8 * CQ i + 8 * CB i + 4 * CL i + 2 * CK i
  have hC : ∀ i, 0 ≤ C i := by
    intro i
    dsimp [C]
    have := hCQ_nn i
    have := hCB_nn i
    have := hCL_nn i
    have := hCK_nn i
    linarith
  apply Exists.intro C
  apply And.intro hC
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  let b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
  have hb_nn : ∀ l, 0 ≤ b l := fun l =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hPsymm' : ∀ (y : M) (v w : TangentSpace I y),
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w =
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y w v := by
    intro y v w
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P y v w,
      ccTensorBilin_symmS (I := I) (M := M) g₀ P y w v,
      ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
    ring
  have htie' : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w := by
    intro y v w
    rw [show ccTensorBilinSymm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w =
        (1 / 2 : ℝ) * (smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y v w
          + smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ P) y w v) from by
      rw [ccTensorBilinSymm_apply]]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P y v w,
      ccTensorBilin_symmS (I := I) (M := M) g₀ P y w v,
      ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, htie y v w,
      ccTensorBilinSymm_apply]
    ring
  rw [linearizedRicciConnDiffOrder0RiemannHalfBackgroundDifferenceCombinationInputSymm_eq_residualFieldSum
    (I := I) (M := M) g₀ g₁ (ccTensor02Symm (I := I) (M := M) g₀ P) htie' hPsymm']
  let Q : TensorRSSpace 2 (2 + i) I x :=
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ccInputSlotSymm (I := I) (M := M) g₀
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁))).toSection x
  let B : TensorRSSpace 2 (2 + i) I x :=
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ccInputSlotSymm (I := I) (M := M) g₀
        (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁))).toSection x
  let L : TensorRSSpace 2 (2 + i) I x :=
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ccInputSlotSymm (I := I) (M := M) g₀
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁))).toSection x
  let K : TensorRSSpace 2 (2 + i) I x :=
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ccInputSlotSymm (I := I) (M := M) g₀
        (refoldKernelContractionField (I := I) (M := M) g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1))).toSection x
  have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      (ccInputSlotSymm (I := I) (M := M) g₀
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)
        + ccInputSlotSymm (I := I) (M := M) g₀
            (refoldKernelContractionField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1))).toSection x =
      (((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccInputSlotSymm (I := I) (M := M) g₀
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁))).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccInputSlotSymm (I := I) (M := M) g₀
              (backgroundRicciCommutatorDiffRefoldRemainderField (I := I) (M := M) g₀ g₁))).toSection x)
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccInputSlotSymm (I := I) (M := M) g₀
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M)
                g₀ g₁))).toSection x)
        + (iteratedCovGrad (I := I) g₀ 2 2 i
            (ccInputSlotSymm (I := I) (M := M) g₀
              (refoldKernelContractionField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ P))
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1))).toSection x := by
    rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, iteratedCovGrad_add (I := I) g₀ 2 2 i _ _,
      iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  change riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (((Q + B) + L) + K) ≤
    C i *
      Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3)
  have p1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((Q + B) + L) K
  have p2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    (Q + B) L
  have p3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    Q B
  have hjets_mono : Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) ≤
      Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
    Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _)
  have hQ' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      Q ≤
      CQ i * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
    le_trans (hCQ g₁ P htie hδ_le hδ0 hbound i x)
      (mul_le_mul_of_nonneg_left hjets_mono (hCQ_nn i))
  have hB' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      B ≤
      CB i * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
    le_trans (hCB g₁ P htie hδ_le hδ0 hbound i x)
      (mul_le_mul_of_nonneg_left hjets_mono (hCB_nn i))
  have hL' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x L ≤
      CL i * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
    hCL g₁ P htie hδ_le hδ0 hbound i x
  have hK' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x K ≤
      CK i * Combinatorics.boundedFactorGridWindow b (i + 2) (i + 3) :=
    hCK g₁ P htie hδ_le hδ0 hbound i x
  linarith


theorem riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombinationInputSymm_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                  + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁))).toSection
              x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
  classical
  obtain ⟨C1, hC1_nn, hgrid1⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfBackgroundDifferenceCombinationInputSymm_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ :=
    exists_rfns_iteratedCovGrad_fixedCoeffField_bound (I := I) (M := M) g₀
      (ccInputSlotSymm (I := I) (M := M) g₀
        ((1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
  refine ⟨fun i => 2 * C1 i + 2 * cbg i,
    fun i => by have := hC1_nn i; have := hcbg_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  have hb_nn : ∀ l : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hW_ge1 : 1 ≤ Combinatorics.boundedFactorGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) :=
    Combinatorics.one_le_boundedFactorGridWindow _ hb_nn (by omega)
  have harg : linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
      + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ =
      (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
        + (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
            - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ := by
    rw [smul_sub]
    abel
  have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      (ccInputSlotSymm (I := I) (M := M) g₀
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁))).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccInputSlotSymm (I := I) (M := M) g₀
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
                - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)))).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 2 i
          (ccInputSlotSymm (I := I) (M := M) g₀
            ((1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))).toSection x := by
    rw [show ccInputSlotSymm (I := I) (M := M) g₀
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) =
        ccInputSlotSymm (I := I) (M := M) g₀
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + (1 / 2 : ℝ) • (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
                - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
        + ccInputSlotSymm (I := I) (M := M) g₀
            ((1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) from by
      rw [harg, ccInputSymm_add]]
    rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
  have h1 := hgrid1 g₁ P htie hδ_le hδ0 hbound i x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccInputSlotSymm (I := I) (M := M) g₀
          ((1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))).toSection x) ≤
      cbg i * Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) := by
    refine le_trans (hcbg i x) ?_
    nth_rewrite 1 [← mul_one (cbg i)]
    exact mul_le_mul_of_nonneg_left hW_ge1 (hcbg_nn i)
  rw [show (2 * C1 i + 2 * cbg i) * Combinatorics.boundedFactorGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3) =
      2 * (C1 i * Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3))
      + 2 * (cbg i * Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 3)) from by ring]
  linarith


theorem riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombinationInputAsymmRemainder_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              ((linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                  + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
                - ccInputSlotSymm (I := I) (M := M) g₀
                  (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                    + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁))).toSection
              x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
  classical
  obtain ⟨C0, hC0_nn, hC0⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ :=
    exists_rfns_iteratedCovGrad_fixedCoeffField_bound (I := I) (M := M) g₀
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨csw, hcsw_nn, hcsw⟩ :=
    exists_rfns_iteratedCovGrad_fixedCoeffField_bound (I := I) (M := M) g₀
      (ccInputSlotSwapField (I := I) (M := M) g₀)
  refine ⟨fun i => 1 / 2 * (2 * C0 i + CD i + cbg i)
      + 1 / 2 * (diagonalGridGrowthFactor (E := E) i *
        ((∑ n ∈ Finset.range (i + 1), (2 * C0 n + CD n + cbg n)) *
          ∑ l ∈ Finset.range (i + 1), csw l)),
    fun i => ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * C0 i + CD i + cbg i := by
      have := hC0_nn i; have := hCD_nn i; have := hcbg_nn i; linarith
    have h2 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i *
        ((∑ n ∈ Finset.range (i + 1), (2 * C0 n + CD n + cbg n)) *
          ∑ l ∈ Finset.range (i + 1), csw l) :=
      mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg
          (Finset.sum_nonneg (fun n _ => by
            have := hC0_nn n; have := hCD_nn n; have := hcbg_nn n; linarith))
          (Finset.sum_nonneg (fun l _ => hcsw_nn l)))
    linarith
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [← pJetGridWindow_eq_tripleSum (I := I) (M := M) g₀ P x i]
  have hW1 : 1 ≤ pJetGridWindow
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i :=
    one_le_pJetGridWindow _ hb i
  have hW_nn : 0 ≤ pJetGridWindow
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i :=
    le_trans zero_le_one hW1
  have hG : ∀ n : ℕ, n ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 2 2 n
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
              + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection
            x) ≤
        (2 * C0 n + CD n + cbg n) *
          pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i := by
    intro n hn
    have hWmono : pJetGridWindow
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) n ≤
        pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i :=
      pJetGridWindow_mono _ hb hn
    have hO0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)).toSection x) ≤
        C0 n * pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) n := by
      rw [pJetGridWindow_eq_tripleSum (I := I) (M := M) g₀ P x n]
      exact hC0 g₁ P htie hδ_le hδ0 hbound n x
    have hbgd : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
            - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
        CD n * pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) n := by
      rw [pJetGridWindow_eq_tripleSum (I := I) (M := M) g₀ P x n]
      exact hCD g₁ P htie hδ_le hδ0 hbound n x
    have hfix : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤ cbg n :=
      hcbg n x
    have hsec2 : (iteratedCovGrad (I := I) g₀ 2 2 n
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
            - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 n
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x := by
      conv_lhs => rw [show ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ =
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
        + ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ from by abel]
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 n _ _, SmoothCcTensor.toSection_add]
      rfl
    have hV : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
        2 * (CD n * pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0
            (2 + j) x ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) n)
          + 2 * cbg n := by
      rw [hsec2]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + n) x _ _) ?_
      linarith [hbgd, hfix]
    have hsm : (iteratedCovGrad (I := I) g₀ 2 2 n
        ((1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 n
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x) := by
      rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 n (1 / 2 : ℝ)
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁), SmoothCcTensor.toSection_smul]
      rfl
    have hsecG : (iteratedCovGrad (I := I) g₀ 2 2 n
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 n
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁)).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 n
            ((1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x := by
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 n _ _, SmoothCcTensor.toSection_add]
      rfl
    rw [hsecG, hsm]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + n) x _ _) ?_
    rw [riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + n) x (1 / 2 : ℝ) _,
      show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
    have e1 : C0 n * pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0
        (2 + j) x ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) n ≤
        C0 n * pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i :=
      mul_le_mul_of_nonneg_left hWmono (hC0_nn n)
    have e2 : CD n * pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0
        (2 + j) x ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) n ≤
        CD n * pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i :=
      mul_le_mul_of_nonneg_left hWmono (hCD_nn n)
    have e3 : cbg n ≤ cbg n * pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M)
        g₀ 0 (2 + j) x ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i :=
      le_mul_of_one_le_right (hcbg_nn n) hW1
    linarith [hO0, hV, e1, e2, e3]
  have hXb : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
          (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
      diagonalGridGrowthFactor (E := E) i *
        ((∑ n ∈ Finset.range (i + 1), (2 * C0 n + CD n + cbg n)) *
          ∑ l ∈ Finset.range (i + 1), csw l) *
        pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 2 2 2
      (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
        + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
      (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
    have hterm : ∀ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 2 2 n
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection
              x) *
          ∑ l ∈ Finset.range (i + 1 - n),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 2 l
                (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) ≤
        ((2 * C0 n + CD n + cbg n) * ∑ l ∈ Finset.range (i + 1), csw l) *
          pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i := by
      intro n hn
      rw [Finset.mem_range] at hn
      have h1 := hG n (by omega)
      have h2 : (∑ l ∈ Finset.range (i + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1), csw l := by
        refine le_trans (Finset.sum_le_sum (fun l _ => hcsw l x)) ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) ?_
        intro l _ _
        exact hcsw_nn l
      have hsw_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l
              (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x) :=
        Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _)
      have hKW_nn : 0 ≤ (2 * C0 n + CD n + cbg n) *
          pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i :=
        mul_nonneg (by have := hC0_nn n; have := hCD_nn n; have := hcbg_nn n; linarith) hW_nn
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 2 2 n
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection
              x) *
            ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l
                  (ccInputSlotSwapField (I := I) (M := M) g₀)).toSection x)
          ≤ ((2 * C0 n + CD n + cbg n) *
              pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i) *
              ∑ l ∈ Finset.range (i + 1), csw l :=
            mul_le_mul h1 h2 hsw_nn hKW_nn
        _ = ((2 * C0 n + CD n + cbg n) * ∑ l ∈ Finset.range (i + 1), csw l) *
              pJetGridWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) i := by
            ring
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
      (appCcGdiag_nonneg (E := E) i)) (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [sub_ccInputSymm_eq_half_smul_sub_appCcRS (I := I) (M := M) g₀
    (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
      + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)]
  have hmain : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) • (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
          (ccInputSlotSwapField (I := I) (M := M) g₀)))).toSection x =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
              + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) := by
    rw [iteratedCovGrad_smul_real (I := I) g₀ 2 2 i (1 / 2 : ℝ) _,
      SmoothCcTensor.toSection_smul]
    rfl
  rw [hmain, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2 : ℝ) _,
    show (1 / 2 : ℝ) ^ 2 = 1 / 4 from by norm_num]
  have hsub : (iteratedCovGrad (I := I) g₀ 2 2 i
      (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
          (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
              + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
            (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x := by
    rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_sub]
    rfl
  rw [hsub]
  refine le_trans (mul_le_mul_of_nonneg_left
    (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)) ?_
  have hGi := hG i le_rfl
  linarith [hGi, hXb]


theorem linearizedRicciConnDiffOrder0RiemannHalfCombination_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨CS, hCS_nn, hgridS⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombinationInputSymm_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CG, hCG_nn, hgridG⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombinationInputAsymmRemainder_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders
      (I := I) (M := M) g₀ a ha_super hR
  obtain ⟨Kt, hKt_nn, hKt⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => 2 * (CS i * ((1 + R ^ 2) * Kflat (i + 1)))
      + 2 * (CG i * ((1 + R ^ 2) * ∑ k ∈ Finset.range (i + 3), Kt k)),
    fun i => by
      have h1 : (0 : ℝ) ≤ CS i * ((1 + R ^ 2) * Kflat (i + 1)) :=
        mul_nonneg (hCS_nn i) (mul_nonneg (by positivity) (hKflat_nn (i + 1)))
      have h2 : (0 : ℝ) ≤ CG i * ((1 + R ^ 2) * ∑ k ∈ Finset.range (i + 3), Kt k) :=
        mul_nonneg (hCG_nn i) (mul_nonneg (by positivity)
          (Finset.sum_nonneg (fun k _ => hKt_nn k)))
      linarith, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨hWint₀, hWbound₀⟩ := hKflat P hPball (i + 1)
    have hWint : MeasureTheory.Integrable
        (fun x => Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 4))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := hWint₀
    have hWbound : (∫ x, Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 4)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kflat (i + 1) * (1 + ∑ j ∈ Finset.range (i + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := hWbound₀
    have hsplit : linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
        + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ =
        ccInputSlotSymm (I := I) (M := M) g₀
          (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
        + ((linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
            + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
          - ccInputSlotSymm (I := I) (M := M) g₀
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
              + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)) := by
      abel
    have hF_int : MeasureTheory.Integrable
        (fun x => 2 * (CS i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 4))
          + 2 * (CG i * ∑ k ∈ Finset.range (i + 3),
              ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      refine MeasureTheory.Integrable.add ?_ ?_
      · exact (hWint.const_mul (CS i)).const_mul 2
      · exact ((MeasureTheory.integrable_finset_sum _
          (fun k hk => (hKt P hPball k).1)).const_mul (CG i)).const_mul 2
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁))
      (fun x => 2 * (CS i * Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 4))
        + 2 * (CG i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
      hF_int
      (fun x => by
        have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
            (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
              + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x =
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ccInputSlotSymm (I := I) (M := M) g₀
                (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                  + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁))).toSection x
            + (iteratedCovGrad (I := I) g₀ 2 2 i
                ((linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                    + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
                  - ccInputSlotSymm (I := I) (M := M) g₀
                    (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                      + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                        g₁))).toSection x := by
          conv_lhs => rw [hsplit]
          rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
          rfl
        rw [hsec]
        refine le_trans
          (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
        have h1 := hgridS g₁ P htie hδ_le hδ0 hδ i x
        have hb_nn : ∀ l : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        have h1' := le_trans h1 (mul_le_mul_of_nonneg_left
          (Combinatorics.boundedFactorGridWindow_mono
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) hb_nn
            (le_refl (i + 2)) (by omega : i + 3 ≤ i + 4)) (hCS_nn i))
        have h2 := hgridG g₁ P htie hδ_le hδ0 hδ i x
        linarith)
    refine le_trans key ?_
    rw [MeasureTheory.integral_add ((hWint.const_mul (CS i)).const_mul 2)
        (((MeasureTheory.integrable_finset_sum _
          (fun k hk => (hKt P hPball k).1)).const_mul (CG i)).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKt P hPball k).1)]
    have htopP : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ≤ R :=
      hPball (i + 2) (by omega)
    have hlayer : ∀ k ∈ Finset.range (i + 3),
        (∫ x, ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * ((1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      refine le_trans (hKt P hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKt_nn k)
      have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
        omega
      have htail : ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 =
          (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
            + ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
        rw [Finset.sum_range_succ]
      have htop_sq : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ≤ R ^ 2 := by
        have := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)
        nlinarith [htopP]
      nlinarith [hwin_nn, htop_sq, hsub, htail, sq_nonneg R]
    have hsum_le : ∑ k ∈ Finset.range (i + 3),
        (∫ x, ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ k ∈ Finset.range (i + 3), Kt k) * ((1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hlayer
    have hS_le : CS i * ∫ x, Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 2) (i + 4)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) ≤
        CS i * (((1 + R ^ 2) * Kflat (i + 1)) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left (le_trans hWbound ?_) (hCS_nn i)
      have htail : ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 =
          (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
            + ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
        rw [Finset.sum_range_succ]
      have htop_sq : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ≤ R ^ 2 := by
        have := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)
        nlinarith [htopP]
      have habs : 1 + ∑ j ∈ Finset.range (i + 3),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          (1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        nlinarith [hwin_nn, htop_sq, htail, sq_nonneg R]
      calc Kflat (i + 1) * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          ≤ Kflat (i + 1) * ((1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left habs (hKflat_nn (i + 1))
        _ = ((1 + R ^ 2) * Kflat (i + 1)) * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
    have hG_le : CG i * ∑ k ∈ Finset.range (i + 3),
        (∫ x, ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        CG i * ((∑ k ∈ Finset.range (i + 3), Kt k) *
          ((1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left hsum_le (hCG_nn i)
    nlinarith [hS_le, hG_le]
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have h1 : (0 : ℝ) ≤ CS i * ((1 + R ^ 2) * Kflat (i + 1)) :=
      mul_nonneg (hCS_nn i) (mul_nonneg (by positivity) (hKflat_nn (i + 1)))
    have h2 : (0 : ℝ) ≤ CG i * ((1 + R ^ 2) * ∑ k ∈ Finset.range (i + 3), Kt k) :=
      mul_nonneg (hCG_nn i) (mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun k _ => hKt_nn k)))
    nlinarith [hwin_nn, h1, h2]


theorem exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
                + (3 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨K0, hK0_nn, hK0⟩ :=
    linearizedRicciConnDiffOrder0RiemannHalfCombination_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K0, hK0_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hwin : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
    intro j
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
        + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
      add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤
        (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
    nlinarith [mul_le_mul hnorm_le hnorm_le (norm_nonneg
        (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
      mul_nonneg (mul_nonneg hs0 h1ms)
        (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
      mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
      mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
  rw [corrArm0Combination_eq_order0_add_halfRiemann (I := I) (M := M) g₀ T T' hδ hδ' s]
  have hmain := hK0 (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i hi
  refine le_trans hmain ?_
  have hwinsum : ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_le_sum (fun j _ => hwin j)
  exact mul_le_mul_of_nonneg_left (by linarith [hwinsum]) (hK0_nn i)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
