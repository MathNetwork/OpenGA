import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.SlotChartSourceContMDiff
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.SlotUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartKernel
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberFromModelOpNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberToModelOpNorm
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.MeasureTheory.Integral.IntegrableOn
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponentGradientL2AtomsCovariantChartSource
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponentGradientL2AtomsMeasurability
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponentGradientL2AtomsCovariantRiemannian
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponentGradientL2AtomsChristoffelSlotNormBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

section RawAtoms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [CompactSpace M] in
private lemma scalarOnE_raw_eq_raw_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have hb_chart : b ∈ (chartAt H α).source := hb_base
  have hb_ext : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hb_chart
  exact scalarOnE_extChartAt (I := I) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hb_ext

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma scalarOnE_raw_sq_le_const_mul_tensorInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        {b : M}, b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          (scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
              (extChartAt I α b)) ^ 2 ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    tensorTrivProj_norm_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b hb
  rw [scalarOnE_raw_eq_raw_on_pouTsupport (I := I) (M := M) g r s α S Idx Jdx hb]
  unfold tensorChartComponentRaw
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx
  have h_proj_le : ‖P_IJ T‖ ≤ C_proj * ‖T‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
        (norm_nonneg _))
  have h_proj_sq_le : (P_IJ T) ^ 2 ≤ C_proj ^ 2 * ‖T‖ ^ 2 := by
    have h_abs : (P_IJ T) ^ 2 = ‖P_IJ T‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_abs]
    have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
    have h_rhs : (C_proj * ‖T‖) * (C_proj * ‖T‖) = C_proj ^ 2 * ‖T‖ ^ 2 := by
      ring
    have h_lhs : ‖P_IJ T‖ * ‖P_IJ T‖ = ‖P_IJ T‖ ^ 2 := by rw [sq]
    linarith [hsq, h_lhs.symm.le, h_rhs.symm.le, h_lhs.le, h_rhs.le]
  have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := h_norm S b hb
  have hC_proj_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
  have h_chain_sq : (P_IJ T) ^ 2 ≤
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) := by
    have h_mul := mul_le_mul_of_nonneg_left h_triv_sq_le hC_proj_sq_nn
    exact h_proj_sq_le.trans h_mul
  have h_reassoc :
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) =
        C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  linarith [h_chain_sq, h_reassoc.le, h_reassoc.symm.le]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma indicator_scalarOnE_raw_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
          ((tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
              (extChartAt I α b')) b) ^ 2 ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    scalarOnE_raw_sq_le_const_mul_tensorInner_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx b
  set ρSet : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  set F : M → ℝ := fun b' : M => scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (extChartAt I α b')
  by_cases hb : b ∈ ρSet
  · have h_ind_eq : ρSet.indicator F b = F b := Set.indicator_of_mem hb _
    rw [h_ind_eq]
    exact h_pt S Idx Jdx hb
  · have h_ind_eq : ρSet.indicator F b = 0 := Set.indicator_of_notMem hb _
    rw [h_ind_eq]
    have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) :=
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
    have h_RHS_nn : 0 ≤ C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := mul_nonneg hC_nn hQ_nn
    have hzero_sq : (0 : ℝ) ^ 2 = 0 := by ring
    rw [hzero_sq]
    exact h_RHS_nn

lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma sq_eLpNorm_indicator_raw_le_const_mul_tensorL2Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal (C *
            tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    indicator_scalarOnE_raw_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := fun b : M =>
    (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
      (fun b' : M => scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b')) b
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise (I := I) (M := M)
          g r s b (S.toFun b) (S.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt S Idx Jdx b)
  have h_inner_int := SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M) (g := g) (r := r) (s := s) S S
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
  have h_lint_le :
      ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
        ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards with b using h_pt_enn b
  have h_lint_eq :
      ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ =
        ENNReal.ofReal (∫ b, C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b) ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_C_smul_int h_C_smul_nn).symm
  rw [h_lint_eq] at h_lint_le
  have h_int_const_mul :
      ∫ b, C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) ∂μ =
        C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    rw [integral_const_mul]
  rw [h_int_const_mul] at h_lint_le
  exact h_lint_le

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem indicator_eLpNorm_raw_le_const_mul_tensorL2Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_sq⟩ :=
    sq_eLpNorm_indicator_raw_le_const_mul_tensorL2Inner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  have h_inner_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    refine integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have h_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
        (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 := by
    unfold tensorL2Norm
    rw [sq, Real.mul_self_sqrt h_inner_nn]
  set S_total : ℝ := C *
    tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun with hS_total_def
  have hS_total_nn : 0 ≤ S_total := mul_nonneg hC_nn h_inner_nn
  have h_eLpNorm_le :=
    eLpNorm_two_le_ofReal_sqrt hS_total_nn (h_sq S Idx Jdx)
  have h_sqrt_factor :
      Real.sqrt S_total = Real.sqrt C *
        tensorL2Norm (I := I) (M := M) g r s S.toFun := by
    rw [hS_total_def, h_norm_sq, Real.sqrt_mul hC_nn,
      show (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 =
        tensorL2Norm (I := I) (M := M) g r s S.toFun *
          tensorL2Norm (I := I) (M := M) g r s S.toFun from by ring,
      Real.sqrt_mul_self
        (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun)]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  exact h_eLpNorm_le

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorL2Norm_eq_norm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
      ‖S.toCcTensor‖ := by
  have h_sq := SmoothCcTensor.norm_sq_eq_inner_self
    (I := I) (M := M) (g := g) (r := r) (s := s) S.toCcTensor
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
        S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have h_norm_nn : 0 ≤ ‖S.toCcTensor‖ := norm_nonneg _
  have h_lhs :
      tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := rfl
  rw [h_lhs]
  have h_rhs :
      ‖S.toCcTensor‖ = Real.sqrt
        (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := by
    rw [← Real.sqrt_sq h_norm_nn, h_sq]
  rw [h_rhs]

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ofReal_tensorL2Norm_le_norm_ennreal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal
        (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
      (‖S‖₊ : ℝ≥0∞) := by
  rw [tensorL2Norm_eq_norm_toCcTensor (I := I) (M := M) g r s S]
  have h_l2_le_h1 :
      ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm S]
  exact ENNReal.ofReal_le_ofReal h_l2_le_h1

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
          (fun b : M => (tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M =>
              scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_smoothCc⟩ :=
    indicator_eLpNorm_raw_le_const_mul_tensorL2Norm
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  have h_smoothCc' :
      eLpNorm (fun b : M =>
          (tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)
              (extChartAt I α b')) b) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s
              S.toCcTensor.toFun) :=
    h_smoothCc S.toCcTensor Idx Jdx
  have h_rhs_le :
      ENNReal.ofReal C *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
        ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
    mul_le_mul_of_nonneg_left
      (ofReal_tensorL2Norm_le_norm_ennreal (I := I) (M := M) g r s S)
      (by exact zero_le _)
  exact h_smoothCc'.trans h_rhs_le

end RawAtoms

section ChristoffelAtomsRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Tensor.Tensor0SRiemannian

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompleteSpace E] in
theorem exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  ((∑ k : Fin r,
                      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
                    (∑ l : Fin s,
                      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨M_F_in, hM_F_in_nn, hM_F_in_le⟩ :=
    chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport_local
      (I := I) (M := M) g r s α
  obtain ⟨M_F_out, hM_F_out_nn, hM_F_out_le⟩ :=
    chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport_local
      (I := I) (M := M) g r s α
  set M_F : ℝ := max M_F_in M_F_out with hM_F_def
  have hM_F_nn : 0 ≤ M_F := le_max_of_le_left hM_F_in_nn
  have hM_F_input :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ≤
            M_F * ‖S.toSection b‖ := by
    intro S b hb k
    have h_orig := hM_F_in_le (fun b' => S.toSection b') (b := b) hb j k
    exact h_orig.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hM_F_output :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ≤
            M_F * ‖S.toSection b‖ := by
    intro S b hb l
    have h_orig := hM_F_out_le (fun b' => S.toSection b') (b := b) hb j l
    exact h_orig.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hK_S_bound :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖S.toSection b‖ ^ 2 ≤
          (1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
    intro S b _hb
    rw [one_mul]
    have h_inner : (⟪S.toSection b, S.toSection b⟫_ℝ : ℝ) =
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by
      change DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s b (S.toSection b) (S.toSection b) = _
      rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
      rfl
    rw [← h_inner, real_inner_self_eq_norm_sq]
  set C : ℝ := ((r : ℝ) + (s : ℝ)) * M_F ^ 2 with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
  have h_pt : ∀ (T : SmoothCcTensor g r s) {b : M},
      b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      ((∑ k : Fin r, ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
        (∑ l : Fin s, ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)) ≤
        C * tensorInnerPointwise (I := I) (M := M) g r s b
          (T.toFun b) (T.toFun b) := by
    intro T b hb
    have h_sec : ‖T.toSection b‖ ^ 2 ≤
        (1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s b
          (T.toFun b) (T.toFun b) := hK_S_bound T hb
    have h_in_each : ∀ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ^ 2 ≤
          M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
      intro k
      have hbnd := hM_F_input T hb k
      have hLHS_nn : 0 ≤ ‖chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ :=
        norm_nonneg _
      have := mul_self_le_mul_self hLHS_nn hbnd
      nlinarith [this, sq_nonneg M_F, norm_nonneg (T.toSection b)]
    have h_out_each : ∀ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ^ 2 ≤
          M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
      intro l
      have hbnd := hM_F_output T hb l
      have hLHS_nn : 0 ≤ ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
          (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ :=
        norm_nonneg _
      have := mul_self_le_mul_self hLHS_nn hbnd
      nlinarith [this, sq_nonneg M_F, norm_nonneg (T.toSection b)]
    have h_in_sum : (∑ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) ≤
        (r : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) := by
      have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
        (fun k _ => h_in_each k)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_le
      exact h_le
    have h_out_sum : (∑ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ^ 2) ≤
        (s : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) := by
      have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s)))
        (fun l _ => h_out_each l)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_le
      exact h_le
    have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (T.toFun b) (T.toFun b) :=
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
    have h_secSq : ‖T.toSection b‖ ^ 2 ≤
        tensorInnerPointwise (I := I) (M := M) g r s b (T.toFun b) (T.toFun b) := by
      rw [one_mul] at h_sec; exact h_sec
    have h_MF_sq_nn : 0 ≤ M_F ^ 2 := sq_nonneg _
    have h_rs_nn : 0 ≤ (r : ℝ) + (s : ℝ) := by positivity
    calc (∑ k : Fin r,
            ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
          (∑ l : Fin s,
            ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)
        ≤ (r : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) +
            (s : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) :=
          add_le_add h_in_sum h_out_sum
      _ = ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by ring
      _ ≤ ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
            tensorInnerPointwise (I := I) (M := M) g r s b (T.toFun b) (T.toFun b) :=
          mul_le_mul_of_nonneg_left h_secSq
            (mul_nonneg h_rs_nn h_MF_sq_nn)
      _ = C * tensorInnerPointwise (I := I) (M := M) g r s b
            (T.toFun b) (T.toFun b) := by rw [hC_def]
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set SumSq : M → ℝ := fun b : M =>
    (∑ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
      (∑ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α j) b l‖ ^ 2) with hSumSq_def
  set f : M → ℝ := fun b : M => ρ b * Real.sqrt (SumSq b) with hf_def
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  have hSumSq_nn : ∀ b : M, 0 ≤ SumSq b := by
    intro b
    rw [hSumSq_def]
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h_pt_sq : ∀ b : M, (f b) ^ 2 ≤
      C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) := by
    intro b
    by_cases hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    · have h_eq : (f b) ^ 2 = ρ b ^ 2 * SumSq b := by
        rw [hf_def, mul_pow,
          show Real.sqrt (SumSq b) ^ 2 = SumSq b from Real.sq_sqrt (hSumSq_nn b)]
      have h_rho_le_one : ρ b ≤ 1 := by
        rw [hρ_def]; exact (chartAtlasPOU I M).le_one α b
      have h_rho_nn : 0 ≤ ρ b := by rw [hρ_def]; exact (chartAtlasPOU I M).nonneg α b
      have h_rho_sq_le_one : ρ b ^ 2 ≤ 1 := by
        rw [sq]
        calc ρ b * ρ b ≤ 1 * 1 :=
              mul_le_mul h_rho_le_one h_rho_le_one h_rho_nn zero_le_one
          _ = 1 := by ring
      have h_sum_le : SumSq b ≤ C * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) := h_pt S.toCcTensor hb
      rw [h_eq]
      calc ρ b ^ 2 * SumSq b
          ≤ 1 * SumSq b :=
            mul_le_mul_of_nonneg_right h_rho_sq_le_one (hSumSq_nn b)
        _ = SumSq b := by ring
        _ ≤ C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) := h_sum_le
    · have h_rho_zero : ρ b = 0 := by
        rw [hρ_def]; by_contra hne; exact hb (subset_tsupport _ hne)
      have hzero : (f b) ^ 2 = 0 := by
        change (ρ b * Real.sqrt (SumSq b)) ^ 2 = 0
        rw [h_rho_zero]; ring
      rw [hzero]
      exact mul_nonneg hC_nn
        (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b
            (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt_sq b)
  have h_inner_int :
      Integrable (fun b : M => tensorInnerPointwise
        (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) μ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      S.toCcTensor S.toCcTensor
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) :=
    Filter.Eventually.of_forall fun b => mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  have h_int_le :
      ∫ b, tensorInnerPointwise
        (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ ≤
      ‖S‖ ^ 2 := by
    have h_l2_eq : ∫ b, tensorInnerPointwise
        (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ =
        ‖S.toCcTensor‖ ^ 2 := by
      rw [hμ_def]
      have h_eq : ∫ b,
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun := rfl
      rw [h_eq, ← SmoothCcTensor.norm_sq_eq_inner_self
        (I := I) (M := M) S.toCcTensor]
    rw [h_l2_eq]
    exact SmoothCcTensorH1.l2NormSq_le_h1NormSq S
  have h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal (C * ‖S‖ ^ 2) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
    calc ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ
        ≤ ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
            (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards with b using h_pt_enn b
      _ = ENNReal.ofReal (∫ b, C * tensorInnerPointwise
            (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            h_C_smul_int h_C_smul_nn).symm
      _ = ENNReal.ofReal (C *
            ∫ b, tensorInnerPointwise
              (I := I) (M := M) g r s b
                (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ) := by
          rw [integral_const_mul]
      _ ≤ ENNReal.ofReal (C * ‖S‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h_int_le hC_nn)
  set Tval : ℝ := C * ‖S‖ ^ 2 with hT_def
  have hT_nn : 0 ≤ Tval := mul_nonneg hC_nn (sq_nonneg _)
  have h_eLpNorm_le := eLpNorm_two_le_ofReal_sqrt hT_nn h_sq
  have hS_nn : 0 ≤ ‖S‖ := norm_nonneg _
  have h_sqrt_factor :
      Real.sqrt Tval = Real.sqrt C * ‖S‖ := by
    rw [hT_def, Real.sqrt_mul hC_nn,
      show ‖S‖ ^ 2 = ‖S‖ * ‖S‖ from by ring,
      Real.sqrt_mul_self hS_nn]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  rw [show ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞) from
    (coe_nnnorm_eq_ofReal_norm S).symm] at h_eLpNorm_le
  exact h_eLpNorm_le

end ChristoffelAtomsRiemannian

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
