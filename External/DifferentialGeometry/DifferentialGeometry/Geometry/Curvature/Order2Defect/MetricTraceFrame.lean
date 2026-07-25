import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Curvature.Order2Defect.FrameComponentBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CurvatureDefect
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.L2Bound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpDualFrameParseval


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section MetricTraceAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

noncomputable def metricTraceHessian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    tensorSecondCovDeriv (I := I) g r s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma metricTraceHessian_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTraceHessian (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) T x := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rawTensorConnLap_eq_metricTraceHessian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    rawTensorConnLap (I := I) g r s T x = metricTraceHessian (I := I) g r s T x := by
  rw [metricTraceHessian_def]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r s T x

noncomputable def firstSlotHessMap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x -
    (tensorCov (I := I) g r s).toFun T x ∘L (LeviCivita (I := I) g).toFun Y x

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma firstSlotHessMap_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M)
    (v : TangentSpace I x) :
    firstSlotHessMap (I := I) g r s Y T x v =
      (tensorCov (I := I) g r s).toFun (covApply (tensorCov (I := I) g r s) Y T) x v -
        (tensorCov (I := I) g r s).toFun T x ((LeviCivita (I := I) g).toFun Y x v) := by
  rw [firstSlotHessMap]
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorSecondCovDeriv_eq_firstSlotHessMap
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    tensorSecondCovDeriv (I := I) g r s X Y T x =
      firstSlotHessMap (I := I) g r s Y T x (X x) := by
  rw [tensorSecondCovDeriv_def, firstSlotHessMap_apply]

omit [CompactSpace M] [I.Boundaryless] in
theorem metricTraceHessian_eq_gWeighted_firstSlot
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x : M) :
    metricTraceHessian (I := I) g r s T x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        g.inner x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x) := by
  classical
  rw [metricTraceHessian_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_eq_firstSlotHessMap]
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        g.inner x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) •
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x)) =
      ∑ j : Fin (Module.finrank ℝ E),
        (if i = j then
          firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
            (smoothOrthoFrame (I := I) g x j x)
          else 0) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smoothOrthoFrame_orthonormal_at_center (I := I) g x i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, one_smul]
    · rw [if_neg hij, if_neg hij, zero_smul]]
  rw [Finset.sum_ite_eq (Finset.univ) i
    (fun j => firstSlotHessMap (I := I) g r s (smoothOrthoFrame (I := I) g x i) T x
      (smoothOrthoFrame (I := I) g x j x))]
  rw [if_pos (Finset.mem_univ i)]

omit [NeZero (Module.finrank ℝ E)] in
theorem thirdOrder_ricci_identity_firstSlot
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    firstSlotHessMap (I := I) g 0 3 Y
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x (X x) -
      firstSlotHessMap (I := I) g 0 3 X
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x (Y x) =
      riemannOp (tensorCov (I := I) g 0 3) x (X x) (Y x)
        ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  rw [← tensorSecondCovDeriv_eq_firstSlotHessMap, ← tensorSecondCovDeriv_eq_firstSlotHessMap]
  exact tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 3
    (T := fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
    hX hY (covGrad_contMDiff_mk' (I := I) (M := M) g T₀)

end MetricTraceAlgebra

theorem secondCovGrad_globalL2Bound_of_pointwise_curvatureBound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        C₀ ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x))) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun ^ 2 ≤
      (2 + 3 * C₀ + 2 * C₀ ^ 2) *
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun ^ 2) :=
  secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound (I := I) (M := M) g T₀ C₀ hC₀ hpt

section ChartInvGramBilinearTrace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

private noncomputable def coBchangeChartα (α : M) {b : M}
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i k => (chartModelBasis E).repr (trivToE (I := I) α b (B i)) k

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

private lemma decompose_in_chartBasisα (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b) (i : Fin (Module.finrank ℝ E)) :
    B i = ∑ k : Fin (Module.finrank ℝ E),
      coBchangeChartα (I := I) α B i k •
        chartBasisVecFiber (I := I) α k b := by
  classical
  have hrepr : trivToE (I := I) α b (B i) =
      ∑ k : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (trivToE (I := I) α b (B i)) k •
          ((chartModelBasis E) k : E) :=
    ((chartModelBasis E).sum_repr (trivToE (I := I) α b (B i))).symm
  calc B i = trivFromE (I := I) α b (trivToE (I := I) α b (B i)) :=
            (trivFromE_trivToE (I := I) α hb (B i)).symm
    _ = trivFromE (I := I) α b
          (∑ k : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr (trivToE (I := I) α b (B i)) k •
              ((chartModelBasis E) k : E)) := by rw [← hrepr]
    _ = ∑ k : Fin (Module.finrank ℝ E),
          coBchangeChartα (I := I) α B i k •
            chartBasisVecFiber (I := I) α k b := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_smul]
          rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

private lemma bilin_expand_chartBasisα {A : Type*} [AddCommGroup A] [Module ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Hb : TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] A)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b) (i j : Fin (Module.finrank ℝ E)) :
    Hb (B i) (B j) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (coBchangeChartα (I := I) α B i k *
            coBchangeChartα (I := I) α B j l) •
          Hb (chartBasisVecFiber (I := I) α k b)
            (chartBasisVecFiber (I := I) α l b) := by
  classical
  have hBi := decompose_in_chartBasisα (I := I) α hb B i
  have hBj := decompose_in_chartBasisα (I := I) α hb B j
  rw [show Hb (B i) = ∑ k : Fin (Module.finrank ℝ E),
        coBchangeChartα (I := I) α B i k •
          Hb (chartBasisVecFiber (I := I) α k b) from by
    rw [show Hb (B i) = Hb (∑ k : Fin (Module.finrank ℝ E),
          coBchangeChartα (I := I) α B i k •
            chartBasisVecFiber (I := I) α k b) from congrArg Hb hBi]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact Hb.map_smul _ _]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smul_apply]
  rw [show Hb (chartBasisVecFiber (I := I) α k b) (B j) =
        ∑ l : Fin (Module.finrank ℝ E),
          coBchangeChartα (I := I) α B j l •
            Hb (chartBasisVecFiber (I := I) α k b)
              (chartBasisVecFiber (I := I) α l b) from by
    rw [show Hb (chartBasisVecFiber (I := I) α k b) (B j) =
          Hb (chartBasisVecFiber (I := I) α k b)
            (∑ l : Fin (Module.finrank ℝ E),
              coBchangeChartα (I := I) α B j l •
                chartBasisVecFiber (I := I) α l b) from
      congrArg (Hb (chartBasisVecFiber (I := I) α k b)) hBj]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [(Hb (chartBasisVecFiber (I := I) α k b)).map_smul]]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [smul_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

private lemma orthonormal_matrix_form_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    coBchangeChartα (I := I) α B *
        chartGramMatrix (I := I) g α b *
          (coBchangeChartα (I := I) α B).transpose =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
  classical
  ext i j
  have hg : g.inner b (B i) (B j) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coBchangeChartα (I := I) α B i k *
          coBchangeChartα (I := I) α B j l *
            chartGramMatrix (I := I) g α b k l := by
    rw [bilin_expand_chartBasisα (I := I) α hb (g.inner b) B i j]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_eq_mul, ← chartGramMatrix_apply (I := I) g α b k l, mul_assoc]
  rw [hB i j] at hg
  rw [Matrix.mul_apply]
  rw [show (∑ k, (coBchangeChartα (I := I) α B *
        chartGramMatrix (I := I) g α b) i k *
      (coBchangeChartα (I := I) α B).transpose k j) =
    ∑ k, ∑ l,
      coBchangeChartα (I := I) α B i l *
          chartGramMatrix (I := I) g α b l k *
          coBchangeChartα (I := I) α B j k from
    Finset.sum_congr rfl (fun k _ => by
      rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul])]
  rw [show (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) i j = (if i = j then (1 : ℝ) else 0) from by
    rw [Matrix.one_apply]]
  rw [hg, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l₀ _ => ?_)
  refine Finset.sum_congr rfl (fun k₀ _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

private lemma sum_coBchangeChartα_eq_invGram
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (k l : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E),
      coBchangeChartα (I := I) α B i k *
        coBchangeChartα (I := I) α B i l =
      DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix (I := I) g α b k l := by
  classical
  set A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    coBchangeChartα (I := I) α B with hA_def
  set G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartGramMatrix (I := I) g α b with hG_def
  have hAGA : A * G * A.transpose = 1 := by
    rw [hA_def, hG_def]; exact orthonormal_matrix_form_chartα (I := I) g α hb B hB
  have hAGA_right : A * (G * A.transpose) = 1 := by rw [← Matrix.mul_assoc]; exact hAGA
  have hA_left_inv : (G * A.transpose) * A = 1 := (mul_eq_one_comm).mp hAGA_right
  rw [Matrix.mul_assoc] at hA_left_inv
  have hAtA_eq_Ginv : A.transpose * A = G⁻¹ := (Matrix.inv_eq_right_inv hA_left_inv).symm
  have hGinv_eq : G⁻¹ =
      DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix (I := I) g α b := by
    have hmul : DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix
        (I := I) g α b * G = 1 := by
      rw [hG_def]
      exact DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix_mul_chartGramMatrix
        (I := I) g α hb
    exact (Matrix.inv_eq_left_inv hmul).symm
  have heval : (A.transpose * A) k l = G⁻¹ k l := by rw [hAtA_eq_Ginv]
  rw [Matrix.mul_apply] at heval
  rw [show ∑ i, A.transpose k i * A i l = ∑ i, A i k * A i l from
    Finset.sum_congr rfl (fun i _ => by rw [Matrix.transpose_apply])] at heval
  rw [heval, hGinv_eq]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

theorem orthonormal_basis_bilin_trace_chartα {A : Type*} [AddCommGroup A] [Module ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Hb : TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] A)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix (I := I) g α b k l •
          Hb (chartBasisVecFiber (I := I) α k b)
            (chartBasisVecFiber (I := I) α l b) := by
  classical
  rw [show ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (coBchangeChartα (I := I) α B i k *
              coBchangeChartα (I := I) α B i l) •
            Hb (chartBasisVecFiber (I := I) α k b)
              (chartBasisVecFiber (I := I) α l b) from
    Finset.sum_congr rfl (fun i _ =>
      bilin_expand_chartBasisα (I := I) α hb Hb B i i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        (coBchangeChartα (I := I) α B i k *
            coBchangeChartα (I := I) α B i l) •
          Hb (chartBasisVecFiber (I := I) α k b)
            (chartBasisVecFiber (I := I) α l b)) =
      (∑ i : Fin (Module.finrank ℝ E),
        coBchangeChartα (I := I) α B i k *
          coBchangeChartα (I := I) α B i l) •
        Hb (chartBasisVecFiber (I := I) α k b)
          (chartBasisVecFiber (I := I) α l b) from by rw [← Finset.sum_smul]]
  rw [sum_coBchangeChartα_eq_invGram (I := I) g α hb B hB k l]

end ChartInvGramBilinearTrace

end Connection
end Integral
end DifferentialGeometry

end
