import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.GradNormChartBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

section PointwiseGradientBoundPouWeighted

variable [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)]

private lemma sq_add_le_two_mul_sq_add_sq_pou (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h : (a + b) ^ 2 + (a - b) ^ 2 = 2 * a ^ 2 + 2 * b ^ 2 := by ring
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (b : M),
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b) ≤
          A * (scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S α Idx Jdx) (extChartAt I α b)) ^ 2 +
          B * (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) ^ 2 *
              ((∑ k : Fin (Module.finrank ℝ E),
                  ‖(trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                        ℝ b
                    (chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toSection b')
                      (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)
                + (∑ k : Fin (Module.finrank ℝ E),
                  ‖(trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                        ℝ b
                    (- (∑ i : Fin r,
                        chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toSection b')
                          (chartBasisVecFiber (I := I) α k) b i)
                      + (∑ l : Fin s,
                          chartTensorRSOutputSlotCorrection (I := I) r s g α
                            (fun b' => S.toSection b')
                            (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2)) := by
  classical
  obtain ⟨M_Ginv, hM_Ginv_nn, hM_Ginv_le⟩ :=
    exists_chartInvGramMatrix_l1Sum_sup_on_pouTsupport (I := I) (M := M) g α
  obtain ⟨M_dρ, hM_dρ_nn, hM_dρ_le⟩ :=
    exists_sum_sq_partialDeriv_scalarOnE_chartAtlasPOU_sup (I := I) (M := M) α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
    with hC_proj_def
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  set A : ℝ := 2 * M_Ginv * M_dρ with hA_def
  set B : ℝ := 4 * M_Ginv * C_proj ^ 2 with hB_def
  have hA_nn : 0 ≤ A := by
    rw [hA_def]; positivity
  have hB_nn : 0 ≤ B := by
    rw [hB_def]; positivity
  refine ⟨A, B, hA_nn, hB_nn, ?_⟩
  intro S Idx Jdx b hb
  set z : E := extChartAt I α b with hz_def
  have hb_chart_src : b ∈ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α hb
  have hb_goodSet : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
        extChartAt_source_eq_chartAt_source (I := I)]
    exact hb_chart_src
  have hb_extSrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hb_chart_src
  have hu_mdiff_at : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b :=
    ((tensorChartComponentScalar_contMDiff (I := I) (M := M)
        g r s S α Idx Jdx).contMDiffAt).mdifferentiableAt (by simp)
  set Tcov : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    ‖(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b')
        (chartBasisVecFiber (I := I) α k) b)‖ ^ 2
    with hTcov_def
  set Tchr : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    ‖(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (- (∑ i : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toSection b')
            (chartBasisVecFiber (I := I) α k) b i)
        + (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b')
              (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2
    with hTchr_def
  set Tcov_sum : ℝ := ∑ k : Fin (Module.finrank ℝ E), Tcov k with hTcov_sum_def
  set Tchr_sum : ℝ := ∑ k : Fin (Module.finrank ℝ E), Tchr k with hTchr_sum_def
  have hTcov_nn : ∀ k, 0 ≤ Tcov k := fun k => by rw [hTcov_def]; exact sq_nonneg _
  have hTchr_nn : ∀ k, 0 ≤ Tchr k := fun k => by rw [hTchr_def]; exact sq_nonneg _
  have hTcov_sum_nn : 0 ≤ Tcov_sum :=
    Finset.sum_nonneg (fun k _ => hTcov_nn k)
  have hTchr_sum_nn : 0 ≤ Tchr_sum :=
    Finset.sum_nonneg (fun k _ => hTchr_nn k)
  set raw_z : ℝ := scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) z
    with hraw_z_def
  have hraw_sq_nn : 0 ≤ raw_z ^ 2 := sq_nonneg _
  set ρ_z : ℝ := scalarOnE (I := I) α
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) z
    with hρ_z_def
  have hρ_z_eq_b : ρ_z = ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b := by
    rw [hρ_z_def, hz_def]
    exact scalarOnE_extChartAt (I := I) α _ hb_extSrc
  have h_step_grad3 :
      g.inner b
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b) ≤
      chartInvGramMatrix_l1Sum (I := I) (M := M) g α b *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) ^ 2 := by
    have := g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials
      (I := I) (M := M) g α
      (f := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
      (x := b) hu_mdiff_at hb_chart_src
    rw [hz_def]
    exact this
  have h_l1Sum_le : chartInvGramMatrix_l1Sum (I := I) (M := M) g α b ≤ M_Ginv :=
    hM_Ginv_le b hb
  have h_leibniz : ∀ k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)) z =
        partialDeriv (E := E) k (scalarOnE (I := I) α
            (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z *
          raw_z +
        ρ_z *
          partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentRaw (I := I) (M := M)
              g r s S α Idx Jdx)) z := by
    intro k
    have h := partialDeriv_scalarOnE_tensorChartComponentScalar_leibniz
      (I := I) (M := M) g r s S α Idx Jdx hb_chart_src k
    rw [hraw_z_def, hρ_z_def, hz_def]
    exact h
  have h_sq_le : ∀ k : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
        2 * ((partialDeriv (E := E) k (scalarOnE (I := I) α
              (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z) ^ 2 *
            raw_z ^ 2) +
        2 * (ρ_z ^ 2 *
            (partialDeriv (E := E) k (scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α Idx Jdx)) z) ^ 2) := by
    intro k
    rw [h_leibniz k]
    have h_tri := sq_add_le_two_mul_sq_add_sq_pou
      (partialDeriv (E := E) k (scalarOnE (I := I) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z *
          raw_z)
      (ρ_z *
        partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z)
    have h_eq1 : (partialDeriv (E := E) k (scalarOnE (I := I) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z *
          raw_z) ^ 2 =
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z) ^ 2
        * raw_z ^ 2 := by ring
    have h_eq2 : (ρ_z *
        partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 =
        ρ_z ^ 2 *
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 := by ring
    linarith [h_tri, h_eq1.le, h_eq1.symm.le, h_eq2.le, h_eq2.symm.le]
  set Sρ : ℝ := ∑ k : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) k (scalarOnE (I := I) α
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z) ^ 2
    with hSρ_def
  set Sraw : ℝ := ∑ k : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) k (scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M)
        g r s S α Idx Jdx)) z) ^ 2
    with hSraw_def
  have hSρ_nn : 0 ≤ Sρ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSraw_nn : 0 ≤ Sraw := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSρ_le_M_dρ : Sρ ≤ M_dρ := by
    rw [hSρ_def, hz_def]
    exact hM_dρ_le b hb
  have h_sum_sq_le :
      ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
      2 * raw_z ^ 2 * Sρ + 2 * ρ_z ^ 2 * Sraw := by
    have hRHS_eq :
        2 * raw_z ^ 2 * Sρ + 2 * ρ_z ^ 2 * Sraw =
        ∑ k : Fin (Module.finrank ℝ E),
          (2 * ((partialDeriv (E := E) k (scalarOnE (I := I) α
                (fun x : M =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) z) ^ 2 *
              raw_z ^ 2) +
          2 * (ρ_z ^ 2 *
              (partialDeriv (E := E) k (scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S α Idx Jdx)) z) ^ 2)) := by
      rw [hSρ_def, hSraw_def]
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [hRHS_eq]
    exact Finset.sum_le_sum (fun k _ => h_sq_le k)
  have h_sum_sq_le' :
      ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
      2 * raw_z ^ 2 * M_dρ + 2 * ρ_z ^ 2 * Sraw := by
    have h1 : 2 * raw_z ^ 2 * Sρ ≤ 2 * raw_z ^ 2 * M_dρ := by
      have hcoef_nn : 0 ≤ 2 * raw_z ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hSρ_le_M_dρ hcoef_nn
    linarith
  have h_twoTerm_per_k : ∀ k : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
        2 * ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 *
          Tcov k +
        2 * ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 *
          Tchr k := by
    intro k
    have h_lhs_eq :
        partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx)) z =
        fderiv ℝ
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
            (extChartAt I α).symm) z
          ((chartModelBasis E) k) := rfl
    rw [h_lhs_eq]
    have hXb : chartBasisVecFiber (I := I) α k b =
        trivFromE (I := I) α b ((chartModelBasis E) k) := rfl
    have h_split :=
      fderiv_tensorChartComponentRaw_pullback_norm_sq_two_term_split
        (I := I) (M := M) g r s α S Idx Jdx
        (chartBasisVecFiber (I := I) α k) hb_goodSet
        ((chartModelBasis E) k) hXb
    rw [hz_def]
    rw [hTcov_def, hTchr_def]
    exact h_split
  set Pnorm_sq : ℝ := ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2
    with hPnorm_sq_def
  have hPnorm_sq_nn : 0 ≤ Pnorm_sq := sq_nonneg _
  have h_Sraw_le :
      Sraw ≤ 2 * Pnorm_sq * Tcov_sum + 2 * Pnorm_sq * Tchr_sum := by
    rw [hSraw_def, hTcov_sum_def, hTchr_sum_def]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [hPnorm_sq_def]
    exact h_twoTerm_per_k k
  have h_Pnorm_le_C_proj : Pnorm_sq ≤ C_proj ^ 2 := by
    rw [hPnorm_sq_def, hC_proj_def]
    have hP_nn : 0 ≤ ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ :=
      norm_nonneg _
    have hP_le : ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ≤
        chartComponentProjectionUniformBound (E := E) r s :=
      tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx
    have h := mul_self_le_mul_self hP_nn hP_le
    have h_lhs : ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ *
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ =
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ^ 2 := by rw [sq]
    have h_rhs : chartComponentProjectionUniformBound (E := E) r s *
        chartComponentProjectionUniformBound (E := E) r s =
        chartComponentProjectionUniformBound (E := E) r s ^ 2 := by rw [sq]
    linarith
  have h_Sraw_le' :
      Sraw ≤ 2 * C_proj ^ 2 * Tcov_sum + 2 * C_proj ^ 2 * Tchr_sum := by
    refine h_Sraw_le.trans ?_
    have h_2P_le : 2 * Pnorm_sq ≤ 2 * C_proj ^ 2 :=
      mul_le_mul_of_nonneg_left h_Pnorm_le_C_proj (by norm_num)
    have h1 : 2 * Pnorm_sq * Tcov_sum ≤ 2 * C_proj ^ 2 * Tcov_sum :=
      mul_le_mul_of_nonneg_right h_2P_le hTcov_sum_nn
    have h2 : 2 * Pnorm_sq * Tchr_sum ≤ 2 * C_proj ^ 2 * Tchr_sum :=
      mul_le_mul_of_nonneg_right h_2P_le hTchr_sum_nn
    linarith
  have hρ_z_sq_nn : 0 ≤ ρ_z ^ 2 := sq_nonneg _
  have h_2ρSraw_le :
      2 * ρ_z ^ 2 * Sraw ≤
        ρ_z ^ 2 * (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum) := by
    have h_2Sraw_le : 2 * Sraw ≤
        4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum := by
      have := mul_le_mul_of_nonneg_left h_Sraw_le' (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have h_step :=
      mul_le_mul_of_nonneg_left h_2Sraw_le hρ_z_sq_nn
    have h_arith :
        ρ_z ^ 2 * (2 * Sraw) = 2 * ρ_z ^ 2 * Sraw := by ring
    linarith [h_step, h_arith.le, h_arith.symm.le]
  have h_sum_sq_final :
      ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 ≤
      2 * raw_z ^ 2 * M_dρ +
        ρ_z ^ 2 * (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum) := by
    refine h_sum_sq_le'.trans ?_
    linarith
  have h_l1Sum_nn : 0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α b := by
    unfold chartInvGramMatrix_l1Sum
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_sum_sq_nn : 0 ≤ ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (scalarOnE (I := I) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) z) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_step_combined :
      g.inner b
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b) ≤
      M_Ginv * (2 * raw_z ^ 2 * M_dρ +
        ρ_z ^ 2 *
          (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum)) := by
    refine h_step_grad3.trans ?_
    have h1 : chartInvGramMatrix_l1Sum (I := I) (M := M) g α b *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) ^ 2 ≤
        M_Ginv *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) ^ 2 :=
      mul_le_mul_of_nonneg_right h_l1Sum_le h_sum_sq_nn
    have h2 : M_Ginv *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) ^ 2 ≤
        M_Ginv * (2 * raw_z ^ 2 * M_dρ +
          ρ_z ^ 2 *
            (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum)) :=
      mul_le_mul_of_nonneg_left h_sum_sq_final hM_Ginv_nn
    linarith
  have hρ_z_pow : ρ_z ^ 2 =
      (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) ^ 2 := by
    rw [hρ_z_eq_b]
  have h_RHS_eq :
      M_Ginv * (2 * raw_z ^ 2 * M_dρ +
        ρ_z ^ 2 *
          (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum)) =
      A * raw_z ^ 2 +
        B * (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) ^ 2 *
            (Tcov_sum + Tchr_sum) := by
    rw [hA_def, hB_def, ← hρ_z_pow]
    ring
  calc g.inner b
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
        (gradFun (I := I) g
          (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b)
      ≤ M_Ginv * (2 * raw_z ^ 2 * M_dρ +
          ρ_z ^ 2 *
            (4 * C_proj ^ 2 * Tcov_sum + 4 * C_proj ^ 2 * Tchr_sum)) :=
        h_step_combined
    _ = A * raw_z ^ 2 +
        B * (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) ^ 2 *
            (Tcov_sum + Tchr_sum) := h_RHS_eq

omit [NeZero (Module.finrank ℝ E)] in
theorem g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport_h1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
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
                  ‖(trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                        ℝ b
                    (chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)
                + (∑ k : Fin (Module.finrank ℝ E),
                  ‖(trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                        ℝ b
                    (- (∑ i : Fin r,
                        chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b i)
                      + (∑ l : Fin s,
                          chartTensorRSOutputSlotCorrection (I := I) r s g α
                            (fun b' => S.toCcTensor.toSection b')
                            (chartBasisVecFiber (I := I) α k) b l))‖ ^ 2)) := by
  obtain ⟨A, B, hA_nn, hB_nn, h⟩ :=
    g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport
      (I := I) (M := M) g r s α
  exact ⟨A, B, hA_nn, hB_nn, fun S Idx Jdx b hb => h S.toCcTensor Idx Jdx b hb⟩

end PointwiseGradientBoundPouWeighted

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
