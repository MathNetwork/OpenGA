import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.IntrinsicL2Bridge
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def tensorChartComponentSqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    M → ℝ :=
  fun b =>
    Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) *
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartComponentSqrtPou_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    tensorChartComponentSqrtPou (I := I) (M := M) g r s S α Idx Jdx b =
      Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComponentSqrtPou_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M) :
    (tensorChartComponentSqrtPou (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 := by
  have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
    (chartAtlasPOU I M).nonneg α b
  rw [tensorChartComponentSqrtPou_apply, mul_pow, Real.sq_sqrt hρ_nn]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tensorChartComponentSqrtPou_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
        (tensorChartComponentSqrtPou (I := I) (M := M)
            g r s S α Idx Jdx b) ^ 2 ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    tensorTrivProj_norm_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b with hT_def
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx with hP_def
  have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hsq_eq : (tensorChartComponentSqrtPou (I := I) (M := M)
      g r s S α Idx Jdx b) ^ 2 = ρ b * (P_IJ T) ^ 2 := by
    rw [tensorChartComponentSqrtPou_sq (I := I) (M := M) g r s S α Idx Jdx b]
    rfl
  by_cases hb : b ∈ tsupport ρ
  · have hρ_nn : 0 ≤ ρ b := (chartAtlasPOU I M).nonneg α b
    have hρ_le_one : ρ b ≤ 1 := (chartAtlasPOU I M).le_one α b
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
    have h_KQ_nn : 0 ≤
        K * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := mul_nonneg hK_nn hQ_nn
    have h_rhs_inner_nn : 0 ≤
        C_proj ^ 2 *
          (K * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b)) :=
      mul_nonneg hC_proj_sq_nn h_KQ_nn
    have h_factored : ρ b * (P_IJ T) ^ 2 ≤
        1 *
          (C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toFun b) (S.toFun b))) :=
      mul_le_mul hρ_le_one h_chain_sq (sq_nonneg _) (by norm_num)
    rw [hsq_eq]
    have h_rhs_rearr :
        1 *
          (C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toFun b) (S.toFun b))) =
          C_proj ^ 2 * K *
            tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by ring
    linarith [h_factored, h_rhs_rearr.le, h_rhs_rearr.symm.le]
  · have hρ_zero : ρ b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    rw [hsq_eq, hρ_zero, zero_mul]
    have hC_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
    have h_RHS_nn : 0 ≤ C_proj ^ 2 * K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by
      have heq : C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) =
          C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b)) := by ring
      have := mul_nonneg hC_sq_nn (mul_nonneg hK_nn hQ_nn)
      linarith [heq.le, heq.symm.le]
    exact h_RHS_nn

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) :
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

private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

private lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma eLpNorm_two_le_ofReal_sqrt
    {β : Type*} [MeasurableSpace β] {μ : Measure β} {f : β → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma sq_eLpNorm_tensorChartComponentSqrtPou_le_const_mul_tensorL2Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm (tensorChartComponentSqrtPou (I := I) (M := M)
              g r s S α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal (C *
            tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    tensorChartComponentSqrtPou_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := tensorChartComponentSqrtPou (I := I) (M := M)
    g r s S α Idx Jdx with hf_def
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
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
theorem eLpNorm_tensorChartComponentSqrtPou_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentSqrtPou (I := I) (M := M)
              g r s S α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_sq⟩ :=
    sq_eLpNorm_tensorChartComponentSqrtPou_le_const_mul_tensorL2Inner
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
private lemma support_sqrt_pou_eq
    (α : M) :
    Function.support
        (fun b : M => Real.sqrt
          (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)) =
      Function.support (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  ext b
  simp only [Function.mem_support, ne_eq, Real.sqrt_eq_zero']
  constructor
  · intro hb hcontra
    exact hb (by rw [hcontra])
  · intro hb hle
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartAtlasPOU I M).nonneg α b
    exact hb (le_antisymm hle hρ_nn)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tsupport_tensorChartComponentSqrtPou_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentSqrtPou (I := I) (M := M) g r s S α Idx Jdx) ⊆
      tsupport (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  have h_mul : tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
        g r s S α Idx Jdx) ⊆
      tsupport (fun b : M => Real.sqrt
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)) := by
    apply tsupport_mul_subset_left
      (f := fun b : M => Real.sqrt
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b))
      (g := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
  refine h_mul.trans ?_
  unfold tsupport
  rw [support_sqrt_pou_eq (I := I) (M := M) α]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma continuous_tensorChartComponentSqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous
      (tensorChartComponentSqrtPou (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  have hSqrt_cont : Continuous
      (fun y : M => Real.sqrt
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y)) :=
    Real.continuous_sqrt.comp
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_chart : x ∈ (chartAt H α).source
  · have hRaw_on := tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s S α Idx Jdx
    have hRaw_at : ContinuousAt
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) x :=
      ((hRaw_on.contMDiffAt
        (IsOpen.mem_nhds (chartAt H α).open_source hx_chart)).continuousAt)
    exact (hSqrt_cont.continuousAt).mul hRaw_at
  · have hsupp_sub :
        tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
            g r s S α Idx Jdx) ⊆ (chartAt H α).source :=
      (tsupport_tensorChartComponentSqrtPou_subset (I := I) (M := M)
        g r s S α Idx Jdx).trans
        (chartAtlasPOU_isSubordinate I M α)
    have hx_notin : x ∉ tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
        g r s S α Idx Jdx) := fun h => hx_chart (hsupp_sub h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    have hopen : IsOpen
        (tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
          g r s S α Idx Jdx))ᶜ :=
      isClosed_tsupport _ |>.isOpen_compl
    filter_upwards [hopen.mem_nhds hx_notin] with y hy
    have hy_notsupp : y ∉ Function.support
        (tensorChartComponentSqrtPou (I := I) (M := M)
          g r s S α Idx Jdx) := fun h_in => hy (subset_tsupport _ h_in)
    have hzero : tensorChartComponentSqrtPou (I := I) (M := M)
        g r s S α Idx Jdx y = 0 := by
      by_contra hne; exact hy_notsupp hne
    exact hzero.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma measurable_tensorChartComponentSqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (tensorChartComponentSqrtPou (I := I) (M := M) g r s S α Idx Jdx) :=
  (continuous_tensorChartComponentSqrtPou (I := I) (M := M)
    g r s S α Idx Jdx).measurable

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hsNorm_zero_integrand_eq_sq_eLpNorm_chartPushedRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (basisIdx : Fin 0 → Fin (Module.finrank ℝ E)) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ 0
                  (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      (eLpNorm
          (chartPushedRaw I α
            (tensorChartComponentSqrtPou (I := I) (M := M)
              g r s S α Idx Jdx)) 2
          ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α))) ^ 2 := by
  classical
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq]
  rw [← MeasureTheory.lintegral_indicator
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet,
      ← MeasureTheory.lintegral_indicator
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet]
  refine MeasureTheory.lintegral_congr (fun y => ?_)
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
    have hraw_eval :
        (iteratedFDeriv ℝ 0
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) =
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
      rw [iteratedFDeriv_zero_apply]; rfl
    have hpush :
        chartPushedRaw I α
            (tensorChartComponentSqrtPou (I := I) (M := M)
              g r s S α Idx Jdx) y =
          tensorChartComponentSqrtPou (I := I) (M := M) g r s S α Idx Jdx b :=
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy
    rw [hraw_eval, hpush]
    have hw_sq :
        (tensorChartComponentSqrtPou (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 :=
      tensorChartComponentSqrtPou_sq (I := I) (M := M) g r s S α Idx Jdx b
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2]
    congr 1
    rw [sq_abs, sq_abs, hw_sq]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_chartPushedRaw_sqrtPou_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (chartPushedRaw I α
              (tensorChartComponentSqrtPou (I := I) (M := M)
                g r s S α Idx Jdx)) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal B *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρ_def
  set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source := chartAtlasPOU_isSubordinate I M α
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by decide : (2 : ℝ≥0∞) ≠ ⊤)
  obtain ⟨D, hD_nn, hD_bound⟩ :=
    eLpNorm_tensorChartComponentSqrtPou_le_uniform
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C * D, mul_nonneg hC_pos.le hD_nn, ?_⟩
  intro S Idx Jdx
  set w : M → ℝ := tensorChartComponentSqrtPou (I := I) (M := M)
    g r s S α Idx Jdx with hw_def
  have hw_meas : Measurable w :=
    measurable_tensorChartComponentSqrtPou (I := I) (M := M) g r s S α Idx Jdx
  have hw_supp : tsupport w ⊆ Kα :=
    tsupport_tensorChartComponentSqrtPou_subset (I := I) (M := M)
      g r s S α Idx Jdx
  have h_bridge :=
    hC_bound (u := w) hw_meas hw_supp
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g
      from rfl] at h_bridge
  refine h_bridge.trans ?_
  have h_intrinsic := hD_bound S Idx Jdx
  calc ENNReal.ofReal C *
          eLpNorm w 2 (riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ENNReal.ofReal C *
          (ENNReal.ofReal D *
            ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toFun)) := by
        gcongr
    _ = ENNReal.ofReal (C * D) *
          ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
        rw [ENNReal.ofReal_mul hC_pos.le, mul_assoc]

private noncomputable def sqrtPouChartConst
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  (eLpNorm_chartPushedRaw_sqrtPou_le_uniform (I := I) (M := M) g r s α).choose

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma sqrtPouChartConst_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ sqrtPouChartConst (I := I) (M := M) g r s α :=
  (eLpNorm_chartPushedRaw_sqrtPou_le_uniform (I := I) (M := M)
    g r s α).choose_spec.1

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma sqrtPouChartConst_spec
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm
        (chartPushedRaw I α
          (tensorChartComponentSqrtPou (I := I) (M := M)
            g r s S α Idx Jdx)) 2
        ((volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal (sqrtPouChartConst (I := I) (M := M) g r s α) *
        ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
  (eLpNorm_chartPushedRaw_sqrtPou_le_uniform (I := I) (M := M)
    g r s α).choose_spec.2 S Idx Jdx

theorem tensorPouSobolevHsNorm_zero_le_tensorL2Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal ≤
          C * tensorL2Norm (I := I) (M := M) g r s S.toFun := by
  classical
  set N : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hN_def
  have hN_nn : 0 ≤ N := by positivity
  set Ksum : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      N * (sqrtPouChartConst (I := I) (M := M) g r s α) ^ 2 with hKsum_def
  have hKsum_nn : 0 ≤ Ksum := by
    refine Finset.sum_nonneg (fun α _ => ?_)
    exact mul_nonneg hN_nn (sq_nonneg _)
  refine ⟨Real.sqrt Ksum, Real.sqrt_nonneg _, ?_⟩
  intro S
  set L : ℝ := tensorL2Norm (I := I) (M := M) g r s S.toFun with hL_def
  have hL_nn : 0 ≤ L := tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun
  have h_sq_le :
      tensorPouSobolevHsNormSq (I := I) (M := M) g 0 S ≤
        ENNReal.ofReal (Ksum * L ^ 2) := by
    rw [tensorPouSobolevHsNormSq_eq_inner_sum]
    have h_tsum_eq :
        (∑' α : M,
          ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * 0 + 1),
              ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s S α
                                IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                  ∂(volume :
                    Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E))))) =
          ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range (2 * 0 + 1),
                ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                    ENNReal.ofReal
                      (((chartAtlasPOU I M α : M → ℝ)
                          ((extChartAt I α).symm
                            ((toEuclidean (E := E)).symm y))) *
                        |(iteratedFDeriv ℝ j
                              (tensorChartComponentRaw (I := I) (M := M) g r s S α
                                  IJ.1 IJ.2
                                ∘ (extChartAt I α).symm
                                ∘ (toEuclidean (E := E)).symm)
                              y)
                            (fun i => EuclideanSpace.basisFun
                              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                    ∂(volume :
                      Measure (EuclideanSpace ℝ
                        (Fin (Module.finrank ℝ E)))) := by
      refine tsum_eq_sum ?_
      intro α hα
      have hPOU_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
        fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
      refine Finset.sum_eq_zero ?_
      intro IJ _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro basisIdx _
      have h_integrand_zero :
          ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s S α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) = 0 := by
        intro y _
        rw [hPOU_zero, zero_mul, ENNReal.ofReal_zero]
      rw [MeasureTheory.setLIntegral_congr_fun
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
        h_integrand_zero]
      simp
    rw [h_tsum_eq]
    have h_termwise :
        ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * 0 + 1),
              ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s S α
                                IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                  ∂(volume :
                    Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E))))) ≤
            ENNReal.ofReal
              (N * (sqrtPouChartConst (I := I) (M := M) g r s α) ^ 2 * L ^ 2) := by
      intro α _
      have h_per_IJ :
          ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            (∑ j ∈ Finset.range (2 * 0 + 1),
              ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s S α
                                IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                  ∂(volume :
                    Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E))))) ≤
              ENNReal.ofReal
                ((sqrtPouChartConst (I := I) (M := M) g r s α) ^ 2 * L ^ 2) := by
        intro IJ
        rw [show (2 * 0 + 1) = 1 from rfl, Finset.sum_range_one]
        rw [Fintype.sum_subsingleton _ (default : Fin 0 → Fin (Module.finrank ℝ E))]
        rw [hsNorm_zero_integrand_eq_sq_eLpNorm_chartPushedRaw
          (I := I) (M := M) g r s S α IJ.1 IJ.2 default]
        have h_le := sqrtPouChartConst_spec (I := I) (M := M) g r s α S IJ.1 IJ.2
        calc (eLpNorm
                  (chartPushedRaw I α
                    (tensorChartComponentSqrtPou (I := I) (M := M)
                      g r s S α IJ.1 IJ.2)) 2
                  ((volume :
                      Measure (EuclideanSpace ℝ
                        (Fin (Module.finrank ℝ E)))).restrict
                    (chartTargetEuclid (I := I) (M := M) α))) ^ 2
            ≤ (ENNReal.ofReal (sqrtPouChartConst (I := I) (M := M) g r s α) *
                ENNReal.ofReal L) ^ 2 := by
              gcongr
          _ = ENNReal.ofReal
                ((sqrtPouChartConst (I := I) (M := M) g r s α) ^ 2 * L ^ 2) := by
              rw [← ENNReal.ofReal_mul (sqrtPouChartConst_nonneg
                  (I := I) (M := M) g r s α),
                ← ENNReal.ofReal_pow (mul_nonneg (sqrtPouChartConst_nonneg
                  (I := I) (M := M) g r s α) hL_nn)]
              rw [mul_pow]
      calc (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range (2 * 0 + 1),
                ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                    ENNReal.ofReal
                      (((chartAtlasPOU I M α : M → ℝ)
                          ((extChartAt I α).symm
                            ((toEuclidean (E := E)).symm y))) *
                        |(iteratedFDeriv ℝ j
                              (tensorChartComponentRaw (I := I) (M := M) g r s S α
                                  IJ.1 IJ.2
                                ∘ (extChartAt I α).symm
                                ∘ (toEuclidean (E := E)).symm)
                              y)
                            (fun i => EuclideanSpace.basisFun
                              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                    ∂(volume :
                      Measure (EuclideanSpace ℝ
                        (Fin (Module.finrank ℝ E)))))
          ≤ ∑ _IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ENNReal.ofReal
                ((sqrtPouChartConst (I := I) (M := M) g r s α) ^ 2 * L ^ 2) :=
            Finset.sum_le_sum (fun IJ _ => h_per_IJ IJ)
        _ = ENNReal.ofReal
              (N * (sqrtPouChartConst (I := I) (M := M) g r s α) ^ 2 * L ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hN_def]
            ring
    calc (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range (2 * 0 + 1),
                ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                    ENNReal.ofReal
                      (((chartAtlasPOU I M α : M → ℝ)
                          ((extChartAt I α).symm
                            ((toEuclidean (E := E)).symm y))) *
                        |(iteratedFDeriv ℝ j
                              (tensorChartComponentRaw (I := I) (M := M) g r s S α
                                  IJ.1 IJ.2
                                ∘ (extChartAt I α).symm
                                ∘ (toEuclidean (E := E)).symm)
                              y)
                            (fun i => EuclideanSpace.basisFun
                              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                    ∂(volume :
                      Measure (EuclideanSpace ℝ
                        (Fin (Module.finrank ℝ E)))))
        ≤ ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            ENNReal.ofReal
              (N * (sqrtPouChartConst (I := I) (M := M) g r s α) ^ 2 * L ^ 2) :=
          Finset.sum_le_sum h_termwise
      _ = ENNReal.ofReal (Ksum * L ^ 2) := by
          rw [← ENNReal.ofReal_sum_of_nonneg
            (fun α _ => by positivity)]
          congr 1
          rw [hKsum_def, Finset.sum_mul]
  have h_finite : tensorPouSobolevHsNormSq (I := I) (M := M) g 0 S ≠ ⊤ :=
    (tensorPouSobolevHsNormSq_lt_top (I := I) (M := M) g 0 S).ne
  have h_toReal_sq :
      (tensorPouSobolevHsNormSq (I := I) (M := M) g 0 S).toReal ≤ Ksum * L ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h_sq_le
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have h_norm_toReal :
      (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal =
        Real.sqrt ((tensorPouSobolevHsNormSq (I := I) (M := M) g 0 S).toReal) := by
    unfold tensorPouSobolevHsNormSq
    rw [ENNReal.toReal_pow, Real.sqrt_sq (ENNReal.toReal_nonneg)]
  rw [h_norm_toReal]
  calc Real.sqrt ((tensorPouSobolevHsNormSq (I := I) (M := M) g 0 S).toReal)
      ≤ Real.sqrt (Ksum * L ^ 2) := Real.sqrt_le_sqrt h_toReal_sq
    _ = Real.sqrt Ksum * L := by
        rw [Real.sqrt_mul hKsum_nn, Real.sqrt_sq hL_nn]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorL2Norm_toFun_eq_norm
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun = ‖S‖ := by
  have h_sq := SmoothCcTensor.norm_sq_eq_inner_self
    (I := I) (M := M) (g := g) (r := r) (s := s) S
  unfold tensorL2Norm
  rw [← h_sq, Real.sqrt_sq (norm_nonneg _)]

theorem tensorPouSobolevHsNorm_zero_toReal_le_norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal ≤ C * ‖T‖ := by
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    tensorPouSobolevHsNorm_zero_le_tensorL2Norm (I := I) (M := M) g r s
  refine ⟨C, hC_nn, fun T => ?_⟩
  have h := hC_bound T
  rwa [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g T] at h

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry

end
