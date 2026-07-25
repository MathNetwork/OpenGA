import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.GradNormChartBoundPouWeighted
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberToModelOpNorm
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChristoffelCorrectionL2.ChristoffelSlotCorrectionFiberNormBridge


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartAtlasPOU_tsupport_isCompact (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartAtlasPOU_tsupport_subset_chartSource (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  chartAtlasPOU_isSubordinate (I := I) (M := M) α

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] in
theorem g_inner_gradFun_le_pou_weighted_fiber_norm_atoms_on_pouTsupport_h1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M),
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) b) ≤
          A * (scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) (extChartAt I α b)) ^ 2 +
          B * (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) ^ 2 *
              ((∑ k : Fin (Module.finrank ℝ E),
                  ‖chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b‖ ^ 2)
                + (∑ k : Fin (Module.finrank ℝ E),
                  ‖- (∑ i : Fin r,
                        chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b i)
                    + (∑ l : Fin s,
                        chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b l)‖ ^ 2)) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨A₀, B₀, hA₀_nn, hB₀_nn, hbound₀⟩ :=
    g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport_h1
      (I := I) (M := M) g r s α
  have hK_cpt :
      IsCompact (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    chartAtlasPOU_tsupport_isCompact (I := I) (M := M) α
  have hK_sub :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (chartAt H α).source :=
    chartAtlasPOU_tsupport_subset_chartSource (I := I) (M := M) α
  obtain ⟨Cop, hCop_pos, hCop_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  set A : ℝ := A₀ with hA_def
  set B : ℝ := B₀ * Cop ^ 2 with hB_def
  have hCop_nn : 0 ≤ Cop := le_of_lt hCop_pos
  have hCop_sq_nn : 0 ≤ Cop ^ 2 := sq_nonneg _
  have hA_nn : 0 ≤ A := hA₀_nn
  have hB_nn : 0 ≤ B := by rw [hB_def]; exact mul_nonneg hB₀_nn hCop_sq_nn
  refine ⟨A, B, hA_nn, hB_nn, ?_⟩
  intro S Idx Jdx b hb
  have h₀ := hbound₀ S Idx Jdx b hb
  set Tcov_triv : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    ‖(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toCcTensor.toSection b')
        (chartBasisVecFiber (I := I) α k) b)‖ ^ 2
    with hTcov_triv_def
  set Tchr_triv : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    ‖(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (- (∑ i : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b i)
        + (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2
    with hTchr_triv_def
  set Tcov_fib : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    ‖chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toCcTensor.toSection b')
        (chartBasisVecFiber (I := I) α k) b‖ ^ 2
    with hTcov_fib_def
  set Tchr_fib : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    ‖- (∑ i : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b i)
        + (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b l)‖ ^ 2
    with hTchr_fib_def
  set Tcov_sum_triv : ℝ := ∑ k : Fin (Module.finrank ℝ E), Tcov_triv k
    with hTcov_sum_triv_def
  set Tchr_sum_triv : ℝ := ∑ k : Fin (Module.finrank ℝ E), Tchr_triv k
    with hTchr_sum_triv_def
  set Tcov_sum_fib : ℝ := ∑ k : Fin (Module.finrank ℝ E), Tcov_fib k
    with hTcov_sum_fib_def
  set Tchr_sum_fib : ℝ := ∑ k : Fin (Module.finrank ℝ E), Tchr_fib k
    with hTchr_sum_fib_def
  have hTcov_triv_nn : ∀ k, 0 ≤ Tcov_triv k := fun k => by
    rw [hTcov_triv_def]; exact sq_nonneg _
  have hTchr_triv_nn : ∀ k, 0 ≤ Tchr_triv k := fun k => by
    rw [hTchr_triv_def]; exact sq_nonneg _
  have hTcov_fib_nn : ∀ k, 0 ≤ Tcov_fib k := fun k => by
    rw [hTcov_fib_def]; exact sq_nonneg _
  have hTchr_fib_nn : ∀ k, 0 ≤ Tchr_fib k := fun k => by
    rw [hTchr_fib_def]; exact sq_nonneg _
  have hTcov_sum_fib_nn : 0 ≤ Tcov_sum_fib :=
    Finset.sum_nonneg (fun k _ => hTcov_fib_nn k)
  have hTchr_sum_fib_nn : 0 ≤ Tchr_sum_fib :=
    Finset.sum_nonneg (fun k _ => hTchr_fib_nn k)
  have h_sum_fib_nn : 0 ≤ Tcov_sum_fib + Tchr_sum_fib := by
    exact add_nonneg hTcov_sum_fib_nn hTchr_sum_fib_nn
  have h_per_k_cov : ∀ k : Fin (Module.finrank ℝ E),
      Tcov_triv k ≤ Cop ^ 2 * Tcov_fib k := by
    intro k
    rw [hTcov_triv_def, hTcov_fib_def]
    set X : TensorRSSpace r s I b :=
      chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toCcTensor.toSection b')
        (chartBasisVecFiber (I := I) α k) b with hX_def
    have h_op : ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X :
            TensorRSModel r s ℝ E)‖ ≤ Cop * ‖X‖ :=
      hCop_bound b hb X
    have h_op_nn :
        0 ≤ ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X :
            TensorRSModel r s ℝ E)‖ := norm_nonneg _
    have h_rhs_nn : 0 ≤ Cop * ‖X‖ := mul_nonneg hCop_nn (norm_nonneg _)
    have h_sq := mul_self_le_mul_self h_op_nn h_op
    have h_lhs_eq :
        ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X :
            TensorRSModel r s ℝ E)‖ *
          ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X :
            TensorRSModel r s ℝ E)‖ =
        ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X :
            TensorRSModel r s ℝ E)‖ ^ 2 := by rw [sq]
    have h_rhs_eq : (Cop * ‖X‖) * (Cop * ‖X‖) = Cop ^ 2 * ‖X‖ ^ 2 := by ring
    linarith [h_sq, h_lhs_eq.le, h_lhs_eq.symm.le, h_rhs_eq.le, h_rhs_eq.symm.le]
  have h_per_k_chr : ∀ k : Fin (Module.finrank ℝ E),
      Tchr_triv k ≤ Cop ^ 2 * Tchr_fib k := by
    intro k
    rw [hTchr_triv_def, hTchr_fib_def]
    set Y : TensorRSSpace r s I b :=
      - (∑ i : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b i)
        + (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b l) with hY_def
    have h_op : ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y :
            TensorRSModel r s ℝ E)‖ ≤ Cop * ‖Y‖ :=
      hCop_bound b hb Y
    have h_op_nn :
        0 ≤ ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y :
            TensorRSModel r s ℝ E)‖ := norm_nonneg _
    have h_sq := mul_self_le_mul_self h_op_nn h_op
    have h_lhs_eq :
        ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y :
            TensorRSModel r s ℝ E)‖ *
          ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y :
            TensorRSModel r s ℝ E)‖ =
        ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y :
            TensorRSModel r s ℝ E)‖ ^ 2 := by rw [sq]
    have h_rhs_eq : (Cop * ‖Y‖) * (Cop * ‖Y‖) = Cop ^ 2 * ‖Y‖ ^ 2 := by ring
    linarith [h_sq, h_lhs_eq.le, h_lhs_eq.symm.le, h_rhs_eq.le, h_rhs_eq.symm.le]
  have h_Tcov_sum_le : Tcov_sum_triv ≤ Cop ^ 2 * Tcov_sum_fib := by
    rw [hTcov_sum_triv_def, hTcov_sum_fib_def]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => h_per_k_cov k)
  have h_Tchr_sum_le : Tchr_sum_triv ≤ Cop ^ 2 * Tchr_sum_fib := by
    rw [hTchr_sum_triv_def, hTchr_sum_fib_def]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => h_per_k_chr k)
  have h_atoms_sum_le :
      Tcov_sum_triv + Tchr_sum_triv ≤
        Cop ^ 2 * (Tcov_sum_fib + Tchr_sum_fib) := by
    have h_add := add_le_add h_Tcov_sum_le h_Tchr_sum_le
    have h_eq : Cop ^ 2 * Tcov_sum_fib + Cop ^ 2 * Tchr_sum_fib =
        Cop ^ 2 * (Tcov_sum_fib + Tchr_sum_fib) := by ring
    linarith
  set ρ_sq : ℝ := (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) ^ 2
    with hρ_sq_def
  have hρ_sq_nn : 0 ≤ ρ_sq := sq_nonneg _
  set raw_sq : ℝ := (scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx) (extChartAt I α b)) ^ 2
    with hraw_sq_def
  have hraw_sq_nn : 0 ≤ raw_sq := sq_nonneg _
  have h₀' :
      g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b) ≤
        A₀ * raw_sq + B₀ * ρ_sq * (Tcov_sum_triv + Tchr_sum_triv) := by
    rw [hraw_sq_def, hρ_sq_def, hTcov_sum_triv_def, hTchr_sum_triv_def,
        hTcov_triv_def, hTchr_triv_def]
    exact h₀
  have hB₀ρsq_nn : 0 ≤ B₀ * ρ_sq := mul_nonneg hB₀_nn hρ_sq_nn
  have h_triv_to_fib :
      B₀ * ρ_sq * (Tcov_sum_triv + Tchr_sum_triv) ≤
        B₀ * ρ_sq * (Cop ^ 2 * (Tcov_sum_fib + Tchr_sum_fib)) :=
    mul_le_mul_of_nonneg_left h_atoms_sum_le hB₀ρsq_nn
  have h_RHS_rearrange :
      B₀ * ρ_sq * (Cop ^ 2 * (Tcov_sum_fib + Tchr_sum_fib)) =
        B * ρ_sq * (Tcov_sum_fib + Tchr_sum_fib) := by
    rw [hB_def]; ring
  have h_final :
      g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b) ≤
        A * raw_sq + B * ρ_sq * (Tcov_sum_fib + Tchr_sum_fib) := by
    calc g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b)
        ≤ A₀ * raw_sq + B₀ * ρ_sq * (Tcov_sum_triv + Tchr_sum_triv) := h₀'
      _ ≤ A₀ * raw_sq + B₀ * ρ_sq * (Cop ^ 2 * (Tcov_sum_fib + Tchr_sum_fib)) := by
          have hA_eq : A₀ * raw_sq = A * raw_sq := by rw [hA_def]
          linarith [h_triv_to_fib]
      _ = A * raw_sq + B * ρ_sq * (Tcov_sum_fib + Tchr_sum_fib) := by
          rw [hA_def, h_RHS_rearrange]
  rw [hraw_sq_def, hρ_sq_def, hTcov_sum_fib_def, hTchr_sum_fib_def,
      hTcov_fib_def, hTchr_fib_def] at h_final
  exact h_final

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
