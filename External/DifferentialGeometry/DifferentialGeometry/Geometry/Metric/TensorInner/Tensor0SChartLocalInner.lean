import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
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

private lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix g α b).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical

  have hexp :
      (fun b : M => (chartGramMatrix g α b).adjugate i j)
        = (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)).det) := by
    funext b
    rw [Matrix.adjugate_apply]
  rw [hexp]

  have hexp2 :
      (fun b : M =>
          ((chartGramMatrix g α b).updateRow j (Pi.single i 1)).det)
        = (fun b : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k,
                  ((chartGramMatrix g α b).updateRow j (Pi.single i 1))
                    (σ k) k) := by
    funext b
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)

  by_cases hσkj : σ k = j
  · have heq :
        (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun _ : M => (Pi.single i 1 : Fin (Module.finrank ℝ E) → ℝ) k) := by
      funext b
      rw [hσkj, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq :
        (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun b : M => chartGramMatrix g α b (σ k) k) := by
      funext b
      rw [Matrix.updateRow_ne hσkj]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

lemma chartGramMatrix_inv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix g α b)⁻¹ i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by

  have hexp :
      (fun b : M => (chartGramMatrix g α b)⁻¹ i j)
        = (fun b : M => (chartGramMatrix g α b).det⁻¹ *
              (chartGramMatrix g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]

  intro b hb
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (chartGramMatrix g α b).det :=
    chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (chartGramMatrix g α b).det ≠ 0 := ne_of_gt hpos
  have hinv : ContMDiffWithinAt I 𝓘(ℝ) ∞
      (fun b' : M => (chartGramMatrix g α b').det⁻¹)
      (trivializationAt E (TangentSpace I) α).baseSet b :=
    ContMDiffWithinAt.inv₀ hdet hpos_ne
  exact hinv.mul hadj

noncomputable def chartTensorInnerPointwise_0s :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) → (b : M) →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _g, _α, _b, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, α, b, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise_0s s g α b
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))

lemma chartTensorInnerPointwise_0s_zero
    (g : SmoothRiemannianMetric I M) (α b : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

lemma chartTensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) := rfl

lemma chartTensorInnerPointwise_0s_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) (S T : Tensor0SModel s ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T)
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro S T

      have heq :
          (fun b : M =>
              chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b S T)
            = fun _ : M =>
              S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      exact contMDiffOn_const
  | succ s ih =>
      intro S T
      have heq :
          (fun b : M =>
              chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b S T)
            = fun b : M =>
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
                      (S.curryLeft ((chartModelBasis E) i))
                      (T.curryLeft ((chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · exact ih
          (S.curryLeft ((chartModelBasis E) i))
          (T.curryLeft ((chartModelBasis E) j))

lemma chartTensorInnerPointwise_0s_add_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S₁ S₂ T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (S₁ + S₂) T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₁ T +
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₂ T := by
  induction s with
  | zero =>
      change (S₁ + S₂) _ * T _ = S₁ _ * T _ + S₂ _ * T _
      rw [ContinuousMultilinearMap.add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (S₁ + S₂).curryLeft ((chartModelBasis E) i) =
            S₁.curryLeft ((chartModelBasis E) i) +
              S₂.curryLeft ((chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_smul_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (c • S) T =
      c * chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change (c • S) _ * T _ = c * (S _ * T _)
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • S).curryLeft ((chartModelBasis E) i) =
            c • S.curryLeft ((chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_add_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T₁ T₂ : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S (T₁ + T₂) =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T₁ +
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T₂ := by
  induction s with
  | zero =>
      change S _ * (T₁ + T₂) _ = S _ * T₁ _ + S _ * T₂ _
      rw [ContinuousMultilinearMap.add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (T₁ + T₂).curryLeft ((chartModelBasis E) j) =
            T₁.curryLeft ((chartModelBasis E) j) +
              T₂.curryLeft ((chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_smul_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S (c • T) =
      c * chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change S _ * (c • T) _ = c * (S _ * T _)
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • T).curryLeft ((chartModelBasis E) j) =
            c • T.curryLeft ((chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply]
      rw [hcurry, ih]
      ring

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
