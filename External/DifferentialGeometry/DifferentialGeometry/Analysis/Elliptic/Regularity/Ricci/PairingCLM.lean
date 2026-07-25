import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.Candidate
import DifferentialGeometry.Analysis.Elliptic.Regularity.Ricci.DualNorm
import Mathlib.Analysis.Normed.Operator.Extend


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace RicciPairingCLM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def ricciPairingSmooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothRicciPairingLp (I := I) (M := M) g φ v

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciPairingSmooth_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ricciPairingSmooth (I := I) (M := M) g φ v =
      smoothRicciPairingLp (I := I) (M := M) g φ v := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    (ricciPairingSmooth (I := I) (M := M) g φ v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun b : M =>
        ricciTensor (I := I) g b
          (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) :=
  smoothRicciPairingLp_coeFn (I := I) (M := M) g φ v

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciPairingSmooth_pt_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v w : SmoothScalar g) (b : M) :
    ricciTensor (I := I) g b (gradFun (I := I) g φ b)
        (gradFun (I := I) g (v + w).toFun b) =
      ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g v.toFun b) +
        ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g w.toFun b) := by
  have hgrad_add : gradFun (I := I) g (v + w).toFun b =
      gradFun (I := I) g v.toFun b + gradFun (I := I) g w.toFun b := by
    have hfun : (v + w).toFun = v.toFun + w.toFun := rfl
    rw [hfun]
    exact DifferentialGeometry.Integral.DivergenceTheorem.gradFun_add (I := I) g
      (v.smooth.mdifferentiable (by simp) b)
      (w.smooth.mdifferentiable (by simp) b)
  rw [hgrad_add, ContinuousLinearMap.map_add]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciPairingSmooth_pt_smul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) (b : M) :
    ricciTensor (I := I) g b (gradFun (I := I) g φ b)
        (gradFun (I := I) g (c • v).toFun b) =
      c * ricciTensor (I := I) g b (gradFun (I := I) g φ b)
        (gradFun (I := I) g v.toFun b) := by
  have hgrad_smul : gradFun (I := I) g (c • v).toFun b =
      c • gradFun (I := I) g v.toFun b := by
    have h := SmoothScalar.grad_g_smul_apply (I := I) (g := g) c v b
    rw [grad_g_apply, grad_g_apply] at h
    exact h
  rw [hgrad_smul]
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciPairingSmooth_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v w : SmoothScalar g) :
    ricciPairingSmooth (I := I) (M := M) g φ (v + w) =
      ricciPairingSmooth (I := I) (M := M) g φ v +
        ricciPairingSmooth (I := I) (M := M) g φ w := by
  apply MeasureTheory.Lp.ext
  have h_sum_coe := MeasureTheory.Lp.coeFn_add
    (ricciPairingSmooth (I := I) (M := M) g φ v)
    (ricciPairingSmooth (I := I) (M := M) g φ w)
  have h_lhs := ricciPairingSmooth_coeFn (I := I) (M := M) g φ (v + w)
  have h_v := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  have h_w := ricciPairingSmooth_coeFn (I := I) (M := M) g φ w
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_sum_coe, h_v, h_w] with b h_sum h_v_eq h_w_eq
  rw [h_sum, Pi.add_apply, h_v_eq, h_w_eq]
  exact (ricciPairingSmooth_pt_add (I := I) (M := M) g φ v w b).symm

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciPairingSmooth_smul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) :
    ricciPairingSmooth (I := I) (M := M) g φ (c • v) =
      c • ricciPairingSmooth (I := I) (M := M) g φ v := by
  apply MeasureTheory.Lp.ext
  have h_smul_coe := MeasureTheory.Lp.coeFn_smul c
    (ricciPairingSmooth (I := I) (M := M) g φ v)
  have h_lhs := ricciPairingSmooth_coeFn (I := I) (M := M) g φ (c • v)
  have h_v := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_smul_coe, h_v] with b h_smul h_v_eq
  rw [h_smul, Pi.smul_apply, h_v_eq, smul_eq_mul]
  exact (ricciPairingSmooth_pt_smul (I := I) (M := M) g φ c v b).symm

noncomputable def ricciPairingSmoothLin
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun v := ricciPairingSmooth (I := I) (M := M) g φ v
  map_add' v w := ricciPairingSmooth_add (I := I) (M := M) g φ v w
  map_smul' c v := ricciPairingSmooth_smul (I := I) (M := M) g φ c v

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciPairingSmoothLin_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ricciPairingSmoothLin (I := I) (M := M) g φ v =
      ricciPairingSmooth (I := I) (M := M) g φ v := rfl

noncomputable def ricciPairingCLMOnSmoothOfBound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (C : ℝ) (_hC_nn : 0 ≤ C)
    (hC_bound : ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖) :
    SmoothScalar g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (ricciPairingSmoothLin (I := I) (M := M) g φ).mkContinuous C hC_bound

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciPairingCLMOnSmoothOfBound_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (C : ℝ) (hC_nn : 0 ≤ C)
    (hC_bound : ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖)
    (v : SmoothScalar g) :
    ricciPairingCLMOnSmoothOfBound (I := I) (M := M) g φ C hC_nn hC_bound v =
      ricciPairingSmooth (I := I) (M := M) g φ v := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    DenseRange (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

noncomputable def ricciPairingCLMOfBound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (C : ℝ) (hC_nn : 0 ≤ C)
    (hC_bound : ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ContinuousLinearMap.extend
    (ricciPairingCLMOnSmoothOfBound (I := I) (M := M) g φ C hC_nn hC_bound)
    (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem ricciPairingCLMOfBound_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (C : ℝ) (hC_nn : 0 ≤ C)
    (hC_bound : ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖)
    (v : SmoothScalar g) :
    ricciPairingCLMOfBound (I := I) (M := M) g φ C hC_nn hC_bound
        (smoothToH1Compl (I := I) (M := M) g v) =
      ricciPairingSmooth (I := I) (M := M) g φ v := by
  unfold ricciPairingCLMOfBound
  exact ContinuousLinearMap.extend_eq
    (ricciPairingCLMOnSmoothOfBound (I := I) (M := M) g φ C hC_nn hC_bound)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) v

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_norm_nonneg
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    0 ≤ ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ :=
  norm_nonneg _

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma smoothRicciPairing_continuous
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    Continuous (fun b : M => ricciTensor (I := I) g b
      (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) :=
  (smoothRicciPairing_contMDiff (I := I) (M := M) g φ v).continuous

open DifferentialGeometry.Analysis.Laplacian.RicciDualNorm

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_norm_sq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ^ 2 =
      ∫ b, (ricciTensor (I := I) g b
              (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq
    (ricciPairingSmooth (I := I) (M := M) g φ v)
  rw [L2.inner_def (𝕜 := ℝ)] at h
  have hae_coe := ricciPairingSmooth_coeFn (I := I) (M := M) g φ v
  have hae : (fun a : M =>
        @inner ℝ _ _
          ((ricciPairingSmooth (I := I) (M := M) g φ v :
              Lp ℝ 2 _) a)
          ((ricciPairingSmooth (I := I) (M := M) g φ v :
              Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun a : M =>
        (ricciTensor (I := I) g a
          (gradFun (I := I) g φ a) (gradFun (I := I) g v.toFun a)) ^ 2) := by
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rw [show (ricciTensor (I := I) g a (gradFun (I := I) g φ a)
            (gradFun (I := I) g v.toFun a)) ^ 2 =
        (ricciTensor (I := I) g a (gradFun (I := I) g φ a)
            (gradFun (I := I) g v.toFun a)) *
        (ricciTensor (I := I) g a (gradFun (I := I) g φ a)
            (gradFun (I := I) g v.toFun a)) from sq _]
    rfl
  rw [integral_congr_ae hae] at h
  exact h.symm

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciPairing_sq_le_C_mul_grad
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {C : ℝ} (hC_bound : ∀ b : M,
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) ≤ C)
    (v : SmoothScalar g) (b : M) :
    (ricciTensor (I := I) g b
        (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) ^ 2 ≤
      C * g.inner b (gradFun (I := I) g v.toFun b) (gradFun (I := I) g v.toFun b) := by
  have h_cs := ricciPairing_cs_sq (I := I) g φ b (gradFun (I := I) g v.toFun b)
  have h_grad_nn : 0 ≤ g.inner b (gradFun (I := I) g v.toFun b)
      (gradFun (I := I) g v.toFun b) :=
    metric_inner_self_nonneg (I := I) (M := M) g b _
  calc (ricciTensor (I := I) g b
          (gradFun (I := I) g φ b) (gradFun (I := I) g v.toFun b)) ^ 2
      ≤ g.inner b (ricciSharp (I := I) g φ b)
            (ricciSharp (I := I) g φ b) *
          g.inner b (gradFun (I := I) g v.toFun b)
            (gradFun (I := I) g v.toFun b) := h_cs
    _ ≤ C * g.inner b (gradFun (I := I) g v.toFun b)
            (gradFun (I := I) g v.toFun b) :=
        mul_le_mul_of_nonneg_right (hC_bound b) h_grad_nn

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_norm_sq_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {C : ℝ} (hC_nn : 0 ≤ C) (hC_bound : ∀ b : M,
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) ≤ C)
    (v : SmoothScalar g) :
    ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ^ 2 ≤ C * ‖v‖ ^ 2 := by
  rw [ricciPairingSmooth_norm_sq (I := I) (M := M) g φ v]
  have h_pt : ∀ b : M,
      (ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g v.toFun b)) ^ 2 ≤
        C * g.inner b (gradFun (I := I) g v.toFun b)
            (gradFun (I := I) g v.toFun b) := fun b =>
    ricciPairing_sq_le_C_mul_grad (I := I) (M := M) g φ hC_bound v b
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hLHS_cont : Continuous (fun b : M =>
      (ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g v.toFun b)) ^ 2) :=
    (smoothRicciPairing_continuous (I := I) (M := M) g φ v).pow 2
  have hLHS_int : Integrable (fun b : M =>
      (ricciTensor (I := I) g b (gradFun (I := I) g φ b)
          (gradFun (I := I) g v.toFun b)) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hLHS_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgrad_cont : Continuous (fun b : M =>
      g.inner b (gradFun (I := I) g v.toFun b) (gradFun (I := I) g v.toFun b)) := by
    exact gradInnerSmooth_continuous (I := I) (M := M) g
      ⟨v.toFun, v.smooth⟩ v
  have hgrad_int : Integrable (fun b : M =>
      g.inner b (gradFun (I := I) g v.toFun b) (gradFun (I := I) g v.toFun b))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hgrad_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRHS_int : Integrable (fun b : M =>
      C * g.inner b (gradFun (I := I) g v.toFun b)
          (gradFun (I := I) g v.toFun b))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hgrad_int.const_mul _
  have h_int_le := integral_mono_ae hLHS_int hRHS_int
    (Filter.Eventually.of_forall h_pt)
  rw [integral_const_mul] at h_int_le
  have h_grad_int_le := integral_inner_grad_self_le_h1_norm_sq (g := g) v
  exact le_trans h_int_le (mul_le_mul_of_nonneg_left h_grad_int_le hC_nn)

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciPairingSmooth_norm_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {C : ℝ} (hC_nn : 0 ≤ C) (hC_bound : ∀ b : M,
      g.inner b (ricciSharp (I := I) g φ b) (ricciSharp (I := I) g φ b) ≤ C)
    (v : SmoothScalar g) :
    ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ Real.sqrt C * ‖v‖ := by
  have h_sq : ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ^ 2 ≤
      (Real.sqrt C * ‖v‖) ^ 2 := by
    have h := ricciPairingSmooth_norm_sq_le (I := I) (M := M) g φ hC_nn hC_bound v
    have hrhs : (Real.sqrt C * ‖v‖) ^ 2 = C * ‖v‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC_nn]
    rw [hrhs]
    exact h
  have h_lhs_nn : 0 ≤ ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ :=
    norm_nonneg _
  have h_rhs_nn : 0 ≤ Real.sqrt C * ‖v‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_ricciPairing_lipschitz_bound
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SmoothScalar g,
      ‖ricciPairingSmooth (I := I) (M := M) g φ v‖ ≤ C * ‖v‖ := by
  obtain ⟨C_sq, hC_sq_nn, hC_bound⟩ :=
    exists_global_ricci_dual_normSq_bound (I := I) (M := M) g φ
  refine ⟨Real.sqrt C_sq, Real.sqrt_nonneg _, ?_⟩
  intro v
  exact ricciPairingSmooth_norm_le (I := I) (M := M) g φ hC_sq_nn hC_bound v

noncomputable def ricciPairingCLMOnSmooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ricciPairingCLMOnSmoothOfBound (I := I) (M := M) g φ
    (Classical.choose (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ))
    (Classical.choose_spec
      (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ)).1
    (Classical.choose_spec
      (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ)).2

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricciPairingCLMOnSmooth_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ricciPairingCLMOnSmooth (I := I) (M := M) g φ v =
      ricciPairingSmooth (I := I) (M := M) g φ v := rfl

noncomputable def ricciPairingCLM
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ricciPairingCLMOfBound (I := I) (M := M) g φ
    (Classical.choose (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ))
    (Classical.choose_spec
      (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ)).1
    (Classical.choose_spec
      (exists_ricciPairing_lipschitz_bound (I := I) (M := M) g φ)).2

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem ricciPairingCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ricciPairingCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      ricciPairingSmooth (I := I) (M := M) g φ v := by
  unfold ricciPairingCLM
  exact ricciPairingCLMOfBound_smoothToH1Compl (I := I) (M := M) g φ _ _ _ v

end RicciPairingCLM
end Laplacian
end Analysis
end DifferentialGeometry

end
