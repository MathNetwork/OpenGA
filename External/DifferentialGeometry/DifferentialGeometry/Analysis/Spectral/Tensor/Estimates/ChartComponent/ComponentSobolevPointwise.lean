import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.FDerivDecompReal
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.ChristoffelDecomp
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma sq_add_le_two_mul_sq_add_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h : (a + b) ^ 2 + (a - b) ^ 2 = 2 * a ^ 2 + 2 * b ^ 2 := by ring
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  linarith

private lemma norm_add_sq_le_two_mul_sq_add_sq
    {F : Type*} [SeminormedAddCommGroup F] (u v : F) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have htri : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have hsum_nn : 0 ≤ ‖u‖ + ‖v‖ := by positivity
  have huv_nn : 0 ≤ ‖u + v‖ := norm_nonneg _
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    have := mul_self_le_mul_self huv_nn htri
    have h_lhs : ‖u + v‖ * ‖u + v‖ = ‖u + v‖ ^ 2 := by rw [sq]
    have h_rhs : (‖u‖ + ‖v‖) * (‖u‖ + ‖v‖) = (‖u‖ + ‖v‖) ^ 2 := by rw [sq]
    linarith [this, h_lhs.symm.le, h_lhs.le, h_rhs.symm.le, h_rhs.le]
  exact hsq.trans (sq_add_le_two_mul_sq_add_sq _ _)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem fderiv_tensorChartComponentRaw_pullback_norm_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E) :
    (fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w) ^ 2 ≤
      ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 *
        ‖fderiv ℝ
            (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ ^ 2 * ‖w‖ ^ 2 := by
  classical
  have hb_chart : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hchain := tensorChartComponentRaw_partial_decomp
    (I := I) (M := M) g r s α S hb_chart hb_int Idx Jdx w
  set P : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx with hP_def
  set F : E →L[ℝ] TensorRSModel r s ℝ E :=
    fderiv ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b) with hF_def
  have hchain' :
      fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
            (extChartAt I α).symm)
          (extChartAt I α b) w = P (F w) := hchain
  rw [hchain']
  have habs_sq : (P (F w)) ^ 2 = ‖P (F w)‖ ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [habs_sq]
  have hP_norm : ‖P (F w)‖ ≤ ‖P‖ * ‖F w‖ := P.le_opNorm (F w)
  have hF_norm : ‖F w‖ ≤ ‖F‖ * ‖w‖ := F.le_opNorm w
  have hP_nn : 0 ≤ ‖P‖ := norm_nonneg _
  have hF_nn : 0 ≤ ‖F‖ := norm_nonneg _
  have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
  have hPFw_nn : 0 ≤ ‖P (F w)‖ := norm_nonneg _
  have hcomb : ‖P (F w)‖ ≤ ‖P‖ * ‖F‖ * ‖w‖ := by
    have h1 : ‖P‖ * ‖F w‖ ≤ ‖P‖ * (‖F‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left hF_norm hP_nn
    have h2 : ‖P‖ * (‖F‖ * ‖w‖) = ‖P‖ * ‖F‖ * ‖w‖ := by ring
    linarith [hP_norm, h1, h2.le, h2.symm.le]
  have hrhs_nn : 0 ≤ ‖P‖ * ‖F‖ * ‖w‖ := by positivity
  have hsq := mul_self_le_mul_self hPFw_nn hcomb
  have hlhs_sq : ‖P (F w)‖ * ‖P (F w)‖ = ‖P (F w)‖ ^ 2 := by rw [sq]
  have hrhs_sq : (‖P‖ * ‖F‖ * ‖w‖) * (‖P‖ * ‖F‖ * ‖w‖) =
      ‖P‖ ^ 2 * ‖F‖ ^ 2 * ‖w‖ ^ 2 := by ring
  linarith [hsq, hlhs_sq.symm.le, hlhs_sq.le, hrhs_sq.symm.le, hrhs_sq.le]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem fderiv_tensorChartComponentRaw_pullback_norm_sq_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E) :
    (fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w) ^ 2 ≤
      (chartComponentProjectionUniformBound (E := E) r s) ^ 2 *
        ‖fderiv ℝ
            (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ ^ 2 * ‖w‖ ^ 2 := by
  classical
  have h := fderiv_tensorChartComponentRaw_pullback_norm_sq_le
    (I := I) (M := M) g r s α S Idx Jdx hb w
  set Pnorm : ℝ := ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖
  set Cproj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  set Fnorm : ℝ := ‖fderiv ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖
  have hP_le : Pnorm ≤ Cproj :=
    tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx
  have hP_nn : 0 ≤ Pnorm := norm_nonneg _
  have hCproj_nn : 0 ≤ Cproj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  have hPsq_le : Pnorm ^ 2 ≤ Cproj ^ 2 := by
    have := mul_self_le_mul_self hP_nn hP_le
    have h_lhs : Pnorm * Pnorm = Pnorm ^ 2 := by rw [sq]
    have h_rhs : Cproj * Cproj = Cproj ^ 2 := by rw [sq]
    linarith [this, h_lhs.symm.le, h_lhs.le, h_rhs.symm.le, h_rhs.le]
  have hFsq_nn : 0 ≤ Fnorm ^ 2 := sq_nonneg _
  have hwsq_nn : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have hrhs_le : Pnorm ^ 2 * Fnorm ^ 2 * ‖w‖ ^ 2 ≤
      Cproj ^ 2 * Fnorm ^ 2 * ‖w‖ ^ 2 := by
    have h1 : Pnorm ^ 2 * Fnorm ^ 2 ≤ Cproj ^ 2 * Fnorm ^ 2 :=
      mul_le_mul_of_nonneg_right hPsq_le hFsq_nn
    exact mul_le_mul_of_nonneg_right h1 hwsq_nn
  linarith

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem fderiv_tensorTrivProj_pullback_apply_norm_sq_two_term_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E)
    (hXb : X b = trivFromE (I := I) α b w) :
    ‖fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w‖ ^ 2 ≤
      2 * ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toSection b') X b)‖ ^ 2 +
        2 * ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (- (∑ k : Fin r,
                  chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toSection b') X b k)
                + (∑ l : Fin s,
                    chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => S.toSection b') X b l))‖ ^ 2 := by
  classical
  have hdec := fderiv_tensorTrivProj_pullback_apply_eq_chart_pushforward_cov
    (I := I) (M := M) g r s α S X hb w hXb
  rw [hdec]
  set A : TensorRSSpace r s I b :=
    chartTensorRSCovariantDerivative (I := I) r s g α
      (fun b' => S.toSection b') X b with hA_def
  set B : TensorRSSpace r s I b :=
    - (∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => S.toSection b') X b k)
      + (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b l) with hB_def
  have h_split : A - (∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => S.toSection b') X b k)
      + (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b l) = A + B := by
    rw [hB_def]
    abel
  rw [h_split]
  rw [((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).map_add]
  exact norm_add_sq_le_two_mul_sq_add_sq _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem fderiv_tensorChartComponentRaw_pullback_norm_sq_two_term_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E)
    (hXb : X b = trivFromE (I := I) α b w) :
    (fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w) ^ 2 ≤
      2 * ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 *
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toSection b') X b)‖ ^ 2 +
        2 * ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 *
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (- (∑ k : Fin r,
                chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun b' => S.toSection b') X b k)
              + (∑ l : Fin s,
                  chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toSection b') X b l))‖ ^ 2 := by
  classical
  have hb_chart : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hchain := tensorChartComponentRaw_partial_decomp
    (I := I) (M := M) g r s α S hb_chart hb_int Idx Jdx w
  set P : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx with hP_def
  set F : TensorRSModel r s ℝ E := fderiv ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b) w with hF_def
  have hchain' :
      fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
            (extChartAt I α).symm)
          (extChartAt I α b) w = P F := hchain
  rw [hchain']
  have habs_sq : (P F) ^ 2 = ‖P F‖ ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [habs_sq]
  have hPF_le : ‖P F‖ ≤ ‖P‖ * ‖F‖ := P.le_opNorm F
  have hP_nn : 0 ≤ ‖P‖ := norm_nonneg _
  have hF_nn : 0 ≤ ‖F‖ := norm_nonneg _
  have hPF_nn : 0 ≤ ‖P F‖ := norm_nonneg _
  have hsq_PF : ‖P F‖ ^ 2 ≤ ‖P‖ ^ 2 * ‖F‖ ^ 2 := by
    have h := mul_self_le_mul_self hPF_nn hPF_le
    have h_lhs : ‖P F‖ * ‖P F‖ = ‖P F‖ ^ 2 := by rw [sq]
    have h_rhs : (‖P‖ * ‖F‖) * (‖P‖ * ‖F‖) = ‖P‖ ^ 2 * ‖F‖ ^ 2 := by ring
    linarith [h, h_lhs.symm.le, h_lhs.le, h_rhs.symm.le, h_rhs.le]
  have hF_split := fderiv_tensorTrivProj_pullback_apply_norm_sq_two_term_split
    (I := I) (M := M) g r s α S X hb w hXb
  set Tcov : ℝ := ‖(trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSCovariantDerivative (I := I) r s g α
      (fun b' => S.toSection b') X b)‖ with hTcov_def
  set Tchr : ℝ := ‖(trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (- (∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => S.toSection b') X b k)
      + (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b') X b l))‖ with hTchr_def
  have hF_split' : ‖F‖ ^ 2 ≤ 2 * Tcov ^ 2 + 2 * Tchr ^ 2 := hF_split
  have hPsq_nn : 0 ≤ ‖P‖ ^ 2 := sq_nonneg _
  have h_mul : ‖P‖ ^ 2 * ‖F‖ ^ 2 ≤ ‖P‖ ^ 2 * (2 * Tcov ^ 2 + 2 * Tchr ^ 2) :=
    mul_le_mul_of_nonneg_left hF_split' hPsq_nn
  have h_chain : ‖P F‖ ^ 2 ≤ ‖P‖ ^ 2 * (2 * Tcov ^ 2 + 2 * Tchr ^ 2) :=
    hsq_PF.trans h_mul
  have h_rhs_eq : ‖P‖ ^ 2 * (2 * Tcov ^ 2 + 2 * Tchr ^ 2) =
      2 * ‖P‖ ^ 2 * Tcov ^ 2 + 2 * ‖P‖ ^ 2 * Tchr ^ 2 := by ring
  linarith [h_chain, h_rhs_eq.symm.le, h_rhs_eq.le]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem exists_const_fderiv_tensorChartComponentRaw_pullback_norm_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        {b : M} (_hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E),
        (fderiv ℝ
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
              (extChartAt I α).symm)
            (extChartAt I α b) w) ^ 2 ≤
          C * ‖fderiv ℝ
              (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
              (extChartAt I α b)‖ ^ 2 * ‖w‖ ^ 2 := by
  classical
  refine ⟨(chartComponentProjectionUniformBound (E := E) r s) ^ 2,
    sq_nonneg _, ?_⟩
  intro S Idx Jdx b hb w
  exact fderiv_tensorChartComponentRaw_pullback_norm_sq_le_uniform
    (I := I) (M := M) g r s α S Idx Jdx hb w

example (g : SmoothRiemannianMetric I M) (α : M) (S : SmoothCcTensor g 1 2)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (w : E) :
    (fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g 1 2 S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w) ^ 2 ≤
      ‖tensorChartComponentProjection (E := E) 1 2 Idx Jdx‖ ^ 2 *
        ‖fderiv ℝ
            (tensorTrivProj (I := I) (M := M) g 1 2 S α ∘ (extChartAt I α).symm)
            (extChartAt I α b)‖ ^ 2 * ‖w‖ ^ 2 :=
  fderiv_tensorChartComponentRaw_pullback_norm_sq_le
    (I := I) (M := M) g 1 2 α S Idx Jdx hb w

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
