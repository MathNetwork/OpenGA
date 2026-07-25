import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.IteratedFDerivTensorReprChartCompBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawTensorConnLapChartTargetSqBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapChartL2PouBridge
import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.FderivToWkpNormBridge
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.IteratedFderivToWkpNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartFderivBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem reprNormSq_le_sum_components_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (b : M) :
    ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ ^ 2 ≤
      ((Finset.univ : Finset
            ((Fin r → Fin (Module.finrank ℝ E)) ×
             (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  have h_lin := reprNorm_le_sum_components (I := I) (M := M) g r s T α b
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  have hprod : V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) :=
    Finset.univ_product_univ.symm
  have h_rhs_rewrite : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          |tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b| * Bnorm) =
      (∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) * Bnorm := by
    rw [Finset.sum_mul, hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b| * Bnorm)]
  rw [hBnorm_def.symm] at h_lin
  rw [h_rhs_rewrite] at h_lin
  have h_sum_nn : 0 ≤ (∑ p ∈ V,
      |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_rhs_nn : 0 ≤ (∑ p ∈ V,
      |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) * Bnorm :=
    mul_nonneg h_sum_nn hBnorm_nn
  have h_norm_sq : ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ ^ 2 ≤
      ((∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) *
        Bnorm) ^ 2 := by
    have := mul_le_mul h_lin h_lin (norm_nonneg _) h_rhs_nn
    simpa [sq] using this
  have hCS : (∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 ≤
      (V.card : ℝ) *
        ∑ p ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ))
      (fun p => |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|)
    simp only [one_mul, one_pow] at hbase
    have h_sum_one : (∑ _p ∈ V, (1 : ℝ)) = (V.card : ℝ) := by
      simp
    rw [show (∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b| ^ 2) =
        ∑ p ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2 from
      Finset.sum_congr rfl (fun _ _ => by rw [sq_abs]), h_sum_one] at hbase
    exact hbase
  set sumSq : ℝ := ∑ p ∈ V,
    (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2
  have h_sumSq_nn : 0 ≤ sumSq :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_combined : ‖tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) b‖ ^ 2 ≤
      (V.card : ℝ) * Bnorm ^ 2 * sumSq := by
    have h_sq_eq : ((∑ p ∈ V,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) *
        Bnorm) ^ 2 = (∑ p ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
        Bnorm ^ 2 := by ring
    rw [h_sq_eq] at h_norm_sq
    have h_mul := mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm)
    have h_bound : (∑ p ∈ V,
            |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
          Bnorm ^ 2 ≤ (V.card : ℝ) * sumSq * Bnorm ^ 2 := h_mul
    calc ‖tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) b‖ ^ 2
        ≤ (∑ p ∈ V,
            |tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b|) ^ 2 *
            Bnorm ^ 2 := h_norm_sq
      _ ≤ (V.card : ℝ) * sumSq * Bnorm ^ 2 := h_bound
      _ = (V.card : ℝ) * Bnorm ^ 2 * sumSq := by ring
  have h_sumSq_eq : sumSq = ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
    change (∑ p ∈ V, _) = _
    rw [hprod, Finset.sum_product
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2 b) ^ 2)]
  rw [h_sumSq_eq] at h_combined
  exact h_combined

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} {_ : MeasurableSpace α} (f : α → ℝ) (μ : Measure α) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  classical
  have h_rpow : eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
      (1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
  have h_two_toReal : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [h_rpow, h_two_toReal]
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ with hI_def
  have hI_eq : I = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr ?_
    intro x
    rw [show ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ ((2 : ℕ) : ℝ) from by norm_num,
      ENNReal.rpow_natCast]
  have h_step1 : (I ^ ((1 : ℝ) / 2)) ^ 2 = (I ^ ((1 : ℝ) / 2)) ^ ((2 : ℕ) : ℝ) := by
    rw [ENNReal.rpow_natCast]
  rw [h_step1]
  rw [← ENNReal.rpow_mul]
  have h_eq : ((1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [h_eq, ENNReal.rpow_one, hI_eq]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTargetPouWeightedL2NormSq_repr_le_sum_chartComp_L2NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ^ 2) *
              ENNReal.ofReal
                (‖tensorRSChartE_section_repr (I := I) r s α
                    (fun z : M => T.toSection z)
                    ((extChartAt I α).symm
                      ((toEuclidean (E := E)).symm y))‖ ^ 2)
            ∂(volume : Measure EuclN) ≤
          ENNReal.ofReal K *
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
                  (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
                  (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
  classical
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  set N : ℝ := (V.card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨N * Bnorm ^ 2, mul_nonneg hN_nn (sq_nonneg _), ?_⟩
  intro T
  set sym : EuclN → M := fun y : EuclN =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hsym_def
  set lhsIntegrand : EuclN → ℝ≥0∞ := fun y : EuclN =>
    ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ) (sym y)) ^ 2) *
      ENNReal.ofReal
        (‖tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => T.toSection z) (sym y)‖ ^ 2) with hlhs_def
  set rhsIntegrand : (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ≥0∞ :=
    fun Idx Jdx y =>
      ENNReal.ofReal
        ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2)
    with hrhs_def
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      lhsIntegrand y ≤ ENNReal.ofReal (N * Bnorm ^ 2) *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rhsIntegrand Idx Jdx y := by
    intro y _hy
    set b : M := sym y
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ) b
    set V_norm : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z) b‖
    have hρ_nn : 0 ≤ ρ :=
      (chartAtlasPOU I M).nonneg α b
    have hV_norm_nn : 0 ≤ V_norm := norm_nonneg _
    have h_sq := reprNormSq_le_sum_components_sq (I := I) (M := M) g r s T α b
    have h_scaled : ρ ^ 2 * V_norm ^ 2 ≤ ρ ^ 2 *
        (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) :=
      mul_le_mul_of_nonneg_left h_sq (sq_nonneg _)
    have h_distrib : ρ ^ 2 *
        (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
        N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 := by
      rw [show (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
          ρ ^ 2 * (∑ Idx, ∑ Jdx,
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [Finset.mul_sum]]
      ring
    rw [h_distrib] at h_scaled
    have hLHS_eq : lhsIntegrand y = ENNReal.ofReal (ρ ^ 2 * V_norm ^ 2) := by
      change ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (V_norm ^ 2) = _
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [hLHS_eq]
    have h_ennreal :
        ENNReal.ofReal (ρ ^ 2 * V_norm ^ 2) ≤
        ENNReal.ofReal (N * Bnorm ^ 2 *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) :=
      ENNReal.ofReal_le_ofReal h_scaled
    refine le_trans h_ennreal ?_
    rw [ENNReal.ofReal_mul (mul_nonneg hN_nn (sq_nonneg _))]
    have h_ofReal_double_sum :
        ENNReal.ofReal
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ρ ^ 2 *
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (ρ ^ 2 *
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Idx _ => Finset.sum_nonneg
          (fun Jdx _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun Jdx _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    rw [h_ofReal_double_sum]
    have h_sum_eq :
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (ρ ^ 2 *
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2)) =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y := by
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      change ENNReal.ofReal
          (ρ ^ 2 *
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
        ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2)
      have h_apply := tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx _hy
      rw [h_apply]
      have h_pou_eq : tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx b =
          ρ * tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
        unfold tensorChartComponentPou
        rfl
      rw [h_pou_eq]
      congr 1
      ring
    rw [h_sum_eq]
  have h_int_mono :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α, lhsIntegrand y
          ∂(volume : Measure EuclN) ≤
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal (N * Bnorm ^ 2) *
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  rhsIntegrand Idx Jdx y
            ∂(volume : Measure EuclN) :=
    setLIntegral_mono_ae' (chartTargetEuclid_measurableSet (I := I) (M := M) α)
      (Filter.Eventually.of_forall (fun y hy => h_pt y hy))
  rw [show (fun y : EuclN =>
      ENNReal.ofReal (N * Bnorm ^ 2) *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            rhsIntegrand Idx Jdx y) =
      (fun y : EuclN =>
        ENNReal.ofReal (N * Bnorm ^ 2) *
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y) from rfl] at h_int_mono
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h_int_mono
  have h_rhsIntegrand_meas : ∀ Idx Jdx,
      Measurable (fun y : EuclN => rhsIntegrand Idx Jdx y) := by
    intro Idx Jdx
    refine ENNReal.measurable_ofReal.comp ?_
    refine (continuous_pow 2).measurable.comp ?_
    exact (tensorChartComp_continuous (I := I) (M := M) g r s T α Idx Jdx).measurable
  have h_int_double_sum :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              rhsIntegrand Idx Jdx y) ∂(volume : Measure EuclN) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                rhsIntegrand Idx Jdx y ∂(volume : Measure EuclN) := by
    rw [MeasureTheory.lintegral_finset_sum _
      (fun Idx _ => by
        exact Finset.measurable_sum _ (fun Jdx _ => h_rhsIntegrand_meas Idx Jdx))]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    exact MeasureTheory.lintegral_finset_sum _
      (fun Jdx _ => h_rhsIntegrand_meas Idx Jdx)
  rw [h_int_double_sum] at h_int_mono
  have h_per_idx_jdx : ∀ Idx Jdx,
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          rhsIntegrand Idx Jdx y ∂(volume : Measure EuclN) ≤
        (iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) ^ 2 := by
    intro Idx Jdx
    have h_rhs_eq_enorm :
        (fun y : EuclN => rhsIntegrand Idx Jdx y) =
          (fun y : EuclN =>
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2) := by
      funext y
      change ENNReal.ofReal
          ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2) =
        ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
      rw [show ((tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) ^ 2) =
          ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
      rw [show ENNReal.ofReal
          (‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ ^ 2) =
            (ENNReal.ofReal
              ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖) ^ 2 from
        ENNReal.ofReal_pow (norm_nonneg _) 2]
      rw [ofReal_norm_eq_enorm]
    rw [h_rhs_eq_enorm]
    have h_sq_eLp :=
      sq_eLpNorm_two_eq_lintegral_enorm_sq
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
    rw [show ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
            ∂(volume : Measure EuclN) =
          ∫⁻ y,
            ‖tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y‖ₑ ^ 2
            ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) from rfl]
    rw [← h_sq_eLp]
    rw [show iteratedWeakSobolevNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) =
          eLpNorm (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) from
      wkpNorm_zero (d := Module.finrank ℝ E) 2 _ _]
  refine le_trans h_int_mono ?_
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  refine Finset.sum_le_sum (fun Idx _ => ?_)
  refine Finset.sum_le_sum (fun Jdx _ => ?_)
  exact h_per_idx_jdx Idx Jdx

end Connection
end Integral
end DifferentialGeometry

end
