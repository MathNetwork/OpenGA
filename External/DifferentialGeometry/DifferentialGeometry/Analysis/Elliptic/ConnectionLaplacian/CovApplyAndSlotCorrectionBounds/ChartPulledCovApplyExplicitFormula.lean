import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs


open DifferentialGeometry.Integral.L2 (SmoothCcTensor)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma good_set_mem_baseSet_rs
    (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    b ∈ (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
  classical
  change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
    ((trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet)
  refine ⟨?_, ?_⟩
  · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hb

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chart_pulled_covApply_explicit_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun T.toFun) b =
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α T.toFun ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (B.toFun b))
      + ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              T.toFun B.toFun b k)
      - ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              T.toFun B.toFun b l) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  have hb_baseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet :=
    good_set_mem_baseSet_rs (I := I) r s α hb
  have hb_baseT : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hAgree :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet (I := I) (M := M)
      g r s α T B (b := b) hb
  have hLHS_eq :
      tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun T.toFun) b =
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            T.toFun B.toFun b) := by
    change (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) B.toFun T.toFun) b) = _
    change (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)).toFun T.toFun b (B.toFun b)) = _
    rw [hAgree.symm]
  rw [hLHS_eq]
  rw [chartTensorRSCovariantDerivative_def (I := I) r s g α T.toFun B.toFun b]
  rw [map_sub, map_add]
  rw [show (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (∑ k : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b k) =
      ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b k) from
    map_sum ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) _ _]
  rw [show (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b l) =
      ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α
            T.toFun B.toFun b l) from
    map_sum ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) _ _]
  rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α T.toFun b (B.toFun b)]
  unfold tensorRSChartFiberFromModel
  rw [(trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt_symmL
      (R := ℝ) hb_baseRS]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chart_pulled_covApply_explicit_formula_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy_target : y ∈ (extChartAt I α).target)
    (hy_good : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α) :
    (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun T.toFun) ∘
          (extChartAt I α).symm) y =
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α T.toFun ∘
          (extChartAt I α).symm) y
        (trivToE (I := I) α ((extChartAt I α).symm y)
          (B.toFun ((extChartAt I α).symm y)))
      + ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              T.toFun B.toFun ((extChartAt I α).symm y) k)
      - ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              T.toFun B.toFun ((extChartAt I α).symm y) l) := by
  classical
  have h := chart_pulled_covApply_explicit_formula (I := I) (M := M)
    g r s α T B (b := (extChartAt I α).symm y) hy_good
  have hround : extChartAt I α ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy_target
  simp only [Function.comp_apply]
  rw [hround] at h
  exact h

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chart_pulled_covApply_explicit_formula_target_smoothCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : E} (hy_target : y ∈ (extChartAt I α).target)
    (hy_good : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α) :
    (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) B.toFun
          (fun b : M => T.toSection b)) ∘
          (extChartAt I α).symm) y =
      fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
          (fun b : M => T.toSection b) ∘
          (extChartAt I α).symm) y
        (trivToE (I := I) α ((extChartAt I α).symm y)
          (B.toFun ((extChartAt I α).symm y)))
      + ∑ k : Fin r,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b : M => T.toSection b) B.toFun
              ((extChartAt I α).symm y) k)
      - ∑ l : Fin s,
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt
            ℝ ((extChartAt I α).symm y)
            (chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b : M => T.toSection b) B.toFun
              ((extChartAt I α).symm y) l) :=
  chart_pulled_covApply_explicit_formula_target (I := I) (M := M)
    g r s α T.toSection B hy_target hy_good

end Connection
end Integral
end DifferentialGeometry

end
