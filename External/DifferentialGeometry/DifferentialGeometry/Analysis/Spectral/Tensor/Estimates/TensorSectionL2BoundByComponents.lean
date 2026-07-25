import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerPointwiseUpperBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2Bound
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic


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
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

abbrev MIdxC (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (r : ℕ) :=
  Fin r → Fin (Module.finrank ℝ E)

noncomputable def midxPairCard (r s : ℕ) : ℝ :=
  ((Finset.univ : Finset (MIdxC E r × MIdxC E s)).card : ℝ)

omit [NeZero (Module.finrank ℝ E)] in
lemma midxPairCard_nonneg (r s : ℕ) :
    0 ≤ midxPairCard (E := E) r s := Nat.cast_nonneg _

private noncomputable def sumScalarSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) : ℝ :=
  ∑ Idx : MIdxC E r, ∑ Jdx : MIdxC E s,
    (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx b) ^ 2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma sumScalarSq_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α b : M) :
    0 ≤ sumScalarSq g r s S α b :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorRSModel_norm_sq_le_sum_projection_sq (r s : ℕ)
    (T : TensorRSModel r s ℝ E) :
    ‖T‖ ^ 2 ≤
      midxPairCard (E := E) r s *
        (tensorChartBasisNormConstant (E := E) r s) ^ 2 *
        ∑ Idx : MIdxC E r, ∑ Jdx : MIdxC E s,
          (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2 := by
  classical
  set V : Finset ((MIdxC E r) × (MIdxC E s)) := Finset.univ
  set N : ℝ := (V.card : ℝ)
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s
  set P : (MIdxC E r) × (MIdxC E s) → ℝ := fun p =>
    tensorChartComponentProjection (E := E) r s p.1 p.2 T
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  have hprod : V = (Finset.univ : Finset (MIdxC E r)) ×ˢ
      (Finset.univ : Finset (MIdxC E s)) := Finset.univ_product_univ.symm
  have hrec_single : T = ∑ p ∈ V,
      tensorChartComponentProjection (E := E) r s p.1 p.2 T •
        tensorChartBasisElement (E := E) r s p.1 p.2 := by
    conv_lhs => rw [tensorRSModel_eq_sum_basis (E := E) r s T]
    rw [hprod, Finset.sum_product
      (f := fun p : (MIdxC E r) × (MIdxC E s) =>
        tensorChartComponentProjection (E := E) r s p.1 p.2 T •
          tensorChartBasisElement (E := E) r s p.1 p.2)]
  have h_norm_le : ‖T‖ ≤ (∑ p ∈ V, |P p|) * Bnorm := by
    rw [Finset.sum_mul]
    conv_lhs => rw [hrec_single]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (tensorChartBasisElement_norm_le (E := E) r s p.1 p.2) (abs_nonneg _)
  have hCS : (∑ p ∈ V, |P p|) ^ 2 ≤ N * ∑ p ∈ V, (P p) ^ 2 := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
      (fun _ : _ × _ => (1 : ℝ)) (fun p => |P p|)
    simp only [one_mul, one_pow] at hbase
    rw [show (∑ _p ∈ V, (1 : ℝ)) = N from by simp [N, V],
        show (∑ p ∈ V, |P p| ^ 2) = ∑ p ∈ V, (P p) ^ 2 from
          Finset.sum_congr rfl (fun _ _ => by rw [sq_abs])] at hbase
    exact hbase
  have h_sq : ‖T‖ ^ 2 ≤ N * Bnorm ^ 2 * ∑ p ∈ V, (P p) ^ 2 := by
    have h_norm_sq : ‖T‖ ^ 2 ≤ ((∑ p ∈ V, |P p|) * Bnorm) ^ 2 := by
      have := mul_le_mul h_norm_le h_norm_le (norm_nonneg _)
        (mul_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hBnorm_nn)
      simpa [sq] using this
    nlinarith [h_norm_sq, mul_le_mul_of_nonneg_right hCS (sq_nonneg Bnorm),
      sq_nonneg Bnorm, sq_nonneg (∑ p ∈ V, |P p|),
      Finset.sum_nonneg (s := V) (f := fun p => (P p) ^ 2)
        (fun _ _ => sq_nonneg _)]
  rw [show (∑ p ∈ V, (P p) ^ 2) =
      ∑ Idx : MIdxC E r, ∑ Jdx : MIdxC E s,
        (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2 from by
    rw [hprod, Finset.sum_product (f := fun p => (P p) ^ 2)]] at h_sq
  exact h_sq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pou_sq_tensorInner_le_sum_scalar_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) (b : M),
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b) ^ 2 *
            tensorInnerPointwise g r s b (S.toFun b) (S.toFun b) ≤
          C * sumScalarSq g r s S α b := by
  classical
  obtain ⟨K, hK_nn, h_C2b⟩ :=
    exists_tensorInnerPointwise_upper_bound_via_trivProj_norm_sq_on_pouTsupport
      g r s α
  set C₁ : ℝ := midxPairCard (E := E) r s *
    (tensorChartBasisNormConstant (E := E) r s) ^ 2
  have hC₁_nn : 0 ≤ C₁ :=
    mul_nonneg (midxPairCard_nonneg _ _) (sq_nonneg _)
  refine ⟨K * C₁, mul_nonneg hK_nn hC₁_nn, ?_⟩
  intro S b
  set ρ : ℝ := (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b with hρ_def
  set Q : ℝ := tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)
  set T : TensorRSModel r s ℝ E := tensorTrivProj g r s S α b with hT_def
  set sumProj : ℝ :=
    ∑ Idx : MIdxC E r, ∑ Jdx : MIdxC E s,
      (tensorChartComponentProjection (E := E) r s Idx Jdx T) ^ 2 with hsumProj_def
  have h_sum_nn := sumScalarSq_nonneg g r s S α b
  have hQ_nn : 0 ≤ Q := tensorInnerPointwise_nonneg g r s b _
  have h_pou_norm : ρ ^ 2 * ‖T‖ ^ 2 ≤ C₁ * sumScalarSq g r s S α b := by
    have h_alg : ‖T‖ ^ 2 ≤ C₁ * sumProj :=
      tensorRSModel_norm_sq_le_sum_projection_sq (E := E) r s T
    have h_mul : ρ ^ 2 * ‖T‖ ^ 2 ≤ ρ ^ 2 * (C₁ * sumProj) :=
      mul_le_mul_of_nonneg_left h_alg (sq_nonneg _)
    rw [show ρ ^ 2 * (C₁ * sumProj) = C₁ * sumScalarSq g r s S α b from by
      rw [show ρ ^ 2 * (C₁ * sumProj) = C₁ * (ρ ^ 2 * sumProj) by ring]
      congr 1
      unfold sumScalarSq
      rw [hsumProj_def, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun Jdx _ => by
        rw [show (tensorChartComponentScalar g r s S α Idx Jdx b) =
            ρ * tensorChartComponentProjection (E := E) r s Idx Jdx T from by
          change tensorChartComponentPou g r s S α Idx Jdx b = _
          unfold tensorChartComponentPou; rw [hρ_def, hT_def]; rfl]
        ring)] at h_mul
    exact h_mul
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · have h_scaled : ρ ^ 2 * Q ≤ ρ ^ 2 * (K * ‖T‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (h_C2b S b hb) (sq_nonneg _)
    nlinarith [h_scaled, h_pou_norm, hK_nn, hC₁_nn, h_sum_nn,
      sq_nonneg ‖T‖, sq_nonneg ρ]
  · have : ρ = 0 := by by_contra hne; exact hb (subset_tsupport _ hne)
    rw [show ρ ^ 2 * Q = 0 from by rw [this]; ring]
    exact mul_nonneg (mul_nonneg hK_nn hC₁_nn) h_sum_nn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorInner_le_const_mul_sum_scalar_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) (b : M),
        tensorInnerPointwise g r s b (S.toFun b) (S.toFun b) ≤
          C * ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            sumScalarSq g r s S α b := by
  classical
  set Sf : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  set N : ℝ := (Sf.card : ℝ)
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  choose Cα hCα_nn hCα_bound using fun α (_ : α ∈ Sf) =>
    pou_sq_tensorInner_le_sum_scalar_sq (E := E) g r s α
  set Cmax : ℝ := ∑ α ∈ Sf.attach, Cα α.val α.property
  have hCmax_nn : 0 ≤ Cmax :=
    Finset.sum_nonneg (fun α _ => hCα_nn α.val α.property)
  refine ⟨N * Cmax, mul_nonneg hN_nn hCmax_nn, ?_⟩
  intro S b
  set Q : ℝ := tensorInnerPointwise g r s b (S.toFun b) (S.toFun b)
  have hQ_nn : 0 ≤ Q := tensorInnerPointwise_nonneg g r s b _
  have h_CS : Q ≤ N * ∑ α ∈ Sf, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b) ^ 2 * Q := by
    have hbase := Finset.sum_mul_sq_le_sq_mul_sq Sf (fun _ : M => (1 : ℝ))
      (fun α : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b)
    have h_sum_one : ∑ α ∈ Sf, (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b = 1 :=
      chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) b
    have h_lhs : (∑ α ∈ Sf, (1 : ℝ) *
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b) ^ 2 = 1 := by
      rw [show (∑ α ∈ Sf, (1 : ℝ) * (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b) =
          ∑ α ∈ Sf, (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b from
        Finset.sum_congr rfl (fun α _ => by ring), h_sum_one]; ring
    have h_rhs1 : (∑ α ∈ Sf, (1 : ℝ) ^ 2) = N := by simp [N, Sf]
    rw [h_lhs, h_rhs1] at hbase
    have h_mul := mul_le_mul_of_nonneg_right hbase hQ_nn
    rw [show N * (∑ α ∈ Sf, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b) ^ 2) * Q =
        N * ∑ α ∈ Sf, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b) ^ 2 * Q from by
      rw [mul_assoc, Finset.sum_mul]] at h_mul
    simpa [one_mul] using h_mul
  set sumSS : ℝ := ∑ α ∈ Sf, sumScalarSq g r s S α b
  have h_per_α :
      (∑ α ∈ Sf, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b) ^ 2 * Q) ≤
        Cmax * sumSS := by
    rw [show (∑ α ∈ Sf, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b) ^ 2 * Q) =
        ∑ α ∈ Sf.attach,
          ((chartAtlasPOU I M α.val : C^∞⟮I, M; ℝ⟯) b) ^ 2 * Q from
      (Finset.sum_attach _ _).symm,
      show sumSS = ∑ α ∈ Sf.attach, sumScalarSq g r s S α.val b from
        (Finset.sum_attach _ _).symm,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun α _ => ?_
    have hCα_le : Cα α.val α.property ≤ Cmax := by
      change Cα α.val α.property ≤ ∑ β ∈ Sf.attach, Cα β.val β.property
      rw [← Finset.sum_erase_add _ _ (Finset.mem_attach Sf α), add_comm]
      linarith [Finset.sum_nonneg (s := (Sf.attach).erase α)
        (f := fun β => Cα β.val β.property)
        (fun β _ => hCα_nn β.val β.property)]
    exact (hCα_bound α.val α.property S b).trans
      (mul_le_mul_of_nonneg_right hCα_le (sumScalarSq_nonneg g r s S α.val b))
  have h_combined : Q ≤ N * (Cmax * sumSS) :=
    h_CS.trans (mul_le_mul_of_nonneg_left h_per_α hN_nn)
  linarith [h_combined, (show N * (Cmax * sumSS) = N * Cmax * sumSS by ring)]

section ScalarHelpers

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (S : SmoothCcTensor g r s) (α : M)
  (Idx : MIdxC E r) (Jdx : MIdxC E s)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponentScalar_memLp_two :
    MemLp (tensorChartComponentScalar g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (tensorChartComponentScalar_contMDiff (I := I) (M := M)
      g r s S α Idx Jdx).continuous.memLp_of_hasCompactSupport (p := 2)
    (tensorChartComponentScalar_hasCompactSupport g r s S α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponentScalar_sq_integrable :
    Integrable (fun b : M =>
      (tensorChartComponentScalar g r s S α Idx Jdx b) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact ((tensorChartComponentScalar_contMDiff (I := I) (M := M)
      g r s S α Idx Jdx).continuous.pow 2).integrable_of_hasCompactSupport
    ((tensorChartComponentScalar_hasCompactSupport g r s S α Idx Jdx).comp_left
      (g := fun y : ℝ => y ^ 2) (by simp))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorChartComponentScalar_integral_sq_eq_eLpNorm_toReal_sq :
    ∫ b, (tensorChartComponentScalar g r s S α Idx Jdx b) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ((eLpNorm (tensorChartComponentScalar g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)).toReal) ^ 2 := by
  classical
  set f : M → ℝ := tensorChartComponentScalar g r s S α Idx Jdx
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have h_eLp := (tensorChartComponentScalar_memLp_two (E := E) g r s S α Idx Jdx
    ).eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
  rw [show ((2 : ℝ≥0∞)).toReal = 2 from rfl] at h_eLp
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun b : M =>
    show (f b) ^ 2 = ‖f b‖ ^ (2 : ℝ) by
      rw [Real.norm_eq_abs, ← sq_abs, ← Real.rpow_natCast, Nat.cast_ofNat]))]
  have h_int_nn : 0 ≤ ∫ b, ‖f b‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [show (eLpNorm f 2 μ).toReal = (∫ b, ‖f b‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) from by
    rw [h_eLp]; exact ENNReal.toReal_ofReal (Real.rpow_nonneg h_int_nn _),
    ← Real.rpow_two, ← Real.rpow_mul h_int_nn]
  norm_num

end ScalarHelpers

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s),
        (tensorL2Norm g r s S.toFun) ^ 2 ≤
          C *
            ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
              ∑ Idx : MIdxC E r, ∑ Jdx : MIdxC E s,
                ((eLpNorm
                    (tensorChartComponentScalar (I := I) (M := M)
                      g r s S α Idx Jdx) 2
                    (riemannianVolumeMeasure (I := I) (M := M) g)).toReal) ^ 2 := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ := tensorInner_le_const_mul_sum_scalar_sq g r s
  refine ⟨C, hC_nn, ?_⟩
  intro S
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have h_inner_nn : 0 ≤ tensorL2Inner g r s S.toFun S.toFun :=
    integral_nonneg (fun b => tensorInnerPointwise_nonneg g r s b _)
  rw [show (tensorL2Norm g r s S.toFun) ^ 2 =
      tensorL2Inner g r s S.toFun S.toFun from by
    unfold tensorL2Norm; rw [sq, Real.mul_self_sqrt h_inner_nn]]
  have h_scalar_sq_int : ∀ α : M,
      Integrable (fun b : M => sumScalarSq g r s S α b) μ := fun α => by
    unfold sumScalarSq
    exact MeasureTheory.integrable_finset_sum _ (fun Idx _ =>
      MeasureTheory.integrable_finset_sum _ (fun Jdx _ =>
        tensorChartComponentScalar_sq_integrable g r s S α Idx Jdx))
  have h_int_mono :
      ∫ b, tensorInnerPointwise g r s b (S.toFun b) (S.toFun b) ∂μ ≤
      ∫ b, C *
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          sumScalarSq g r s S α b ∂μ :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun b => tensorInnerPointwise_nonneg g r s b _))
      ((MeasureTheory.integrable_finset_sum _ (fun α _ => h_scalar_sq_int α)).const_mul C)
      (Filter.Eventually.of_forall (fun b => h_pt S b))
  rw [integral_const_mul,
    MeasureTheory.integral_finset_sum _ (fun α _ => h_scalar_sq_int α)]
    at h_int_mono
  have h_int_sumScalarSq : ∀ α : M,
      ∫ b, sumScalarSq g r s S α b ∂μ =
        ∑ Idx : MIdxC E r, ∑ Jdx : MIdxC E s,
          ((eLpNorm (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) 2 μ).toReal) ^ 2 := fun α => by
    unfold sumScalarSq
    rw [MeasureTheory.integral_finset_sum _ (fun Idx _ =>
      MeasureTheory.integrable_finset_sum _ (fun Jdx _ =>
        tensorChartComponentScalar_sq_integrable g r s S α Idx Jdx))]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    rw [MeasureTheory.integral_finset_sum _ (fun Jdx _ =>
      tensorChartComponentScalar_sq_integrable g r s S α Idx Jdx)]
    exact Finset.sum_congr rfl (fun Jdx _ =>
      tensorChartComponentScalar_integral_sq_eq_eLpNorm_toReal_sq
        g r s S α Idx Jdx)
  rw [Finset.sum_congr rfl (fun α _ => h_int_sumScalarSq α)] at h_int_mono
  change tensorL2Inner g r s S.toFun S.toFun ≤ _
  unfold tensorL2Inner; exact h_int_mono

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
