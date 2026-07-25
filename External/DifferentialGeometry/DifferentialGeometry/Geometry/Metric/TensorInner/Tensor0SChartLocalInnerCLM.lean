import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SChartLocalInner
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure (chartGramMatrix
  chartGramMatrix_apply chartGramMatrix_isHermitian
  chartGramMatrix_posDef chartGramMatrix_det_pos
  chartGramMatrix_entry_contMDiffOn chartGramMatrix_det_contMDiffOn
  chartBasisVecFiber chartBasisVec)

variable {n : ℕ}

def chartTensorInnerPointwise_0sBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ]
      Tensor0SModel s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun S T => chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T)
    (fun S₁ S₂ T =>
      chartTensorInnerPointwise_0s_add_left (I := I) (M := M) g α b s S₁ S₂ T)
    (fun c S T =>
      chartTensorInnerPointwise_0s_smul_left (I := I) (M := M) g α b s c S T)
    (fun S T₁ T₂ =>
      chartTensorInnerPointwise_0s_add_right (I := I) (M := M) g α b s S T₁ T₂)
    (fun c S T =>
      chartTensorInnerPointwise_0s_smul_right (I := I) (M := M) g α b s c S T)

@[simp] lemma chartTensorInnerPointwise_0sBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M)
    (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0sBilin (I := I) (M := M) g s α b S T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := rfl

noncomputable def chartTensorInnerPointwise_0sCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ :=
  let bilin := chartTensorInnerPointwise_0sBilin (I := I) (M := M) g s α b
  LinearMap.toContinuousLinearMap
    { toFun := fun S => LinearMap.toContinuousLinearMap (bilin S)
      map_add' := fun S₁ S₂ => by
        refine ContinuousLinearMap.ext ?_
        intro T
        change chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (S₁ + S₂) T =
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₁ T +
            chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₂ T
        exact chartTensorInnerPointwise_0s_add_left
          (I := I) (M := M) g α b s S₁ S₂ T
      map_smul' := fun c S => by
        refine ContinuousLinearMap.ext ?_
        intro T
        change chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (c • S) T =
          c • chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T
        rw [chartTensorInnerPointwise_0s_smul_left]
        rfl }

@[simp] lemma chartTensorInnerPointwise_0sCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M)
    (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0sCLM (I := I) (M := M) g s α b S T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := rfl

noncomputable def curryLeftAtCLM (s : ℕ) (v : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ]
      Tensor0SModel s ℝ E :=
  LinearMap.mkContinuous
    { toFun := fun S => S.curryLeft v
      map_add' := fun S₁ S₂ => by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      map_smul' := fun c S => by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply] }
    ‖v‖
    (fun S => by
      change ‖S.curryLeft v‖ ≤ _

      refine (ContinuousMultilinearMap.opNorm_le_bound
        (M := ‖S‖ * ‖v‖) ?_ ?_).trans (by ring_nf; rfl)
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · intro m
        rw [ContinuousMultilinearMap.curryLeft_apply]
        have := S.norm_map_cons_le v m
        calc ‖S (Fin.cons v m)‖
            ≤ ‖S‖ * ‖v‖ * ∏ i, ‖m i‖ := this
          _ = ‖S‖ * ‖v‖ * ∏ i, ‖m i‖ := rfl)

lemma curryLeftAtCLM_apply (s : ℕ) (v : E)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    curryLeftAtCLM (E := E) s v S = S.curryLeft v := rfl

private noncomputable def composeCurryAtIJ (s : ℕ)
    (i j : Fin (Module.finrank ℝ E))
    (B : Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ] ℝ :=
  let CLi := curryLeftAtCLM (E := E) s ((chartModelBasis E) i)
  let CLj := curryLeftAtCLM (E := E) s ((chartModelBasis E) j)

  let postCompCLj :
      (Tensor0SModel s ℝ E →L[ℝ] ℝ) →L[ℝ]
        (ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
      (Tensor0SModel s ℝ E) ℝ).flip CLj
  postCompCLj.comp (B.comp CLi)

@[simp] private lemma composeCurryAtIJ_apply (s : ℕ)
    (i j : Fin (Module.finrank ℝ E))
    (B : Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    composeCurryAtIJ (E := E) s i j B S T =
      B (S.curryLeft ((chartModelBasis E) i))
        (T.curryLeft ((chartModelBasis E) j)) := by
  rfl

private lemma chartTensorInnerPointwise_0sCLM_succ_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    chartTensorInnerPointwise_0sCLM (I := I) (M := M) g (s + 1) α b
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (chartGramMatrix g α b)⁻¹ i j •
              composeCurryAtIJ (E := E) s i j
                (chartTensorInnerPointwise_0sCLM (I := I) (M := M) g s α b) := by
  refine ContinuousLinearMap.ext ?_
  intro S
  refine ContinuousLinearMap.ext ?_
  intro T
  rw [chartTensorInnerPointwise_0sCLM_apply, chartTensorInnerPointwise_0s_succ]

  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    composeCurryAtIJ_apply, smul_eq_mul,
    chartTensorInnerPointwise_0sCLM_apply]

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
