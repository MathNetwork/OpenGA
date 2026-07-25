import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma chartGramBilin_eq_innerJinv
    (g : SmoothRiemannianMetric I M) (α b : M) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b u w =
      g.inner b
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b u)
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b w) := by
  classical
  rw [chartGramBilin_apply]
  have hrewrite :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix g α b j k *
            (chartModelBasis E).equivFun u j *
            (chartModelBasis E).equivFun w k)
        = ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (chartModelBasis E).equivFun u j *
                (chartModelBasis E).equivFun w k *
                g.inner b
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) k)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartGramMatrix_eq_innerJinv (I := I) (M := M) g α b j k]
    ring
  rw [hrewrite]
  have hcollapse_inner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ k : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun u j *
            (chartModelBasis E).equivFun w k *
            g.inner b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) k)))
        = (chartModelBasis E).equivFun u j *
            g.inner b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
              (∑ k : Fin (Module.finrank ℝ E),
                (chartModelBasis E).equivFun w k •
                  chartTrivializationLinearMapSymm (I := I) (M := M) α b
                    ((chartModelBasis E) k)) := by
    intro j
    have hRHS_unfold :
        ((g.inner b (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j)))
            (∑ k : Fin (Module.finrank ℝ E),
              (chartModelBasis E).equivFun w k •
                chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) k)))
          = ∑ k : Fin (Module.finrank ℝ E),
              (chartModelBasis E).equivFun w k *
                g.inner b
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [hRHS_unfold]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun u j *
            (chartModelBasis E).equivFun w k *
            g.inner b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) k)))
        = ∑ j : Fin (Module.finrank ℝ E),
            (chartModelBasis E).equivFun u j *
              g.inner b
                (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
                (∑ k : Fin (Module.finrank ℝ E),
                  (chartModelBasis E).equivFun w k •
                    chartTrivializationLinearMapSymm (I := I) (M := M) α b
                      ((chartModelBasis E) k)) from
      Finset.sum_congr rfl (fun j _ => hcollapse_inner j)]
  have hwsum :
      (∑ k : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun w k •
            chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) k)) =
        chartTrivializationLinearMapSymm (I := I) (M := M) α b w := by
    have hsum_eq :
        (∑ k : Fin (Module.finrank ℝ E),
            (chartModelBasis E).equivFun w k •
              chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) k))
          = chartTrivializationLinearMapSymm (I := I) (M := M) α b
              (∑ k : Fin (Module.finrank ℝ E),
                (chartModelBasis E).equivFun w k • (chartModelBasis E) k) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.map_smul]
    rw [hsum_eq, (chartModelBasis E).sum_equivFun w]
  rw [hwsum]
  have hcollapse_outer :
      (∑ j : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun u j *
            g.inner b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b w))
        = g.inner b
            (∑ j : Fin (Module.finrank ℝ E),
              (chartModelBasis E).equivFun u j •
                chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b w) := by
    rw [map_sum]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hcollapse_outer]
  have husum :
      (∑ j : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun u j •
            chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
        = chartTrivializationLinearMapSymm (I := I) (M := M) α b u := by
    have hsum_eq :
        (∑ j : Fin (Module.finrank ℝ E),
            (chartModelBasis E).equivFun u j •
              chartTrivializationLinearMapSymm (I := I) (M := M) α b ((chartModelBasis E) j))
          = chartTrivializationLinearMapSymm (I := I) (M := M) α b
              (∑ j : Fin (Module.finrank ℝ E),
                (chartModelBasis E).equivFun u j • (chartModelBasis E) j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ContinuousLinearMap.map_smul]
    rw [hsum_eq, (chartModelBasis E).sum_equivFun u]
  rw [husum]

lemma chartGramBilin_chartJ_chartJ
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b
        (chartTrivializationLinearMap (I := I) (M := M) α b u)
        (chartTrivializationLinearMap (I := I) (M := M) α b w) =
      g.inner b u w := by
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g α b]
  rw [chartJinv_chartJ_self (I := I) (M := M) α hb u]
  rw [chartJinv_chartJ_self (I := I) (M := M) α hb w]

lemma chartSeparableFormAt_chartJ_compose
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r : ℕ) (v_first : Fin r → E) :
    chartSeparableFormAt (I := I) (M := M) g α b r
        (fun k : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b (v_first k))
      = (separableFormAt (I := I) (M := M) g b r v_first).compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [chartSeparableFormAt_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g α b]
  rw [chartJinv_chartJ_self (I := I) (M := M) α hb (v_first k)]

theorem chartTensorInnerPointwise_0s_eq_tensorInnerPointwise_0s_chartJ
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (s : ℕ) (A B : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b A B =
      covariantTensorInnerPointwise (I := I) (M := M) s g b
        (A.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b))
        (B.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)) := by
  classical
  have hbridge :=
    tensorInnerPointwise_0s_bridge_identity (I := I) (M := M) g α s hb
      (A.compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b))
      (B.compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b))
  have hAcompose :
      (A.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b) = A := by
    refine ContinuousMultilinearMap.ext ?_
    intro m
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (m k)
  have hBcompose :
      (B.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b) = B := by
    refine ContinuousMultilinearMap.ext ?_
    intro m
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (m k)
  rw [hAcompose, hBcompose] at hbridge
  exact hbridge.symm

theorem chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise_0s_compChartJ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g b
        ((chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T₀).compContinuousLinearMap
          (fun _ : Fin (r + s) => chartTrivializationLinearMap (I := I) (M := M) α b))
        ((chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T₁).compContinuousLinearMap
          (fun _ : Fin (r + s) => chartTrivializationLinearMap (I := I) (M := M) α b)) := by
  rw [chartTensorInnerPointwise_rs_model_def]
  exact chartTensorInnerPointwise_0s_eq_tensorInnerPointwise_0s_chartJ
    (I := I) (M := M) g α hb (r + s) _ _

noncomputable def chartRSTwist
    (α : M) (b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    TensorRSModel r s ℝ E :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)).comp <|
    T.comp
      ((ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)))

@[simp]
lemma chartRSTwist_apply
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E)
    (α' : Tensor0SModel r ℝ E) :
    chartRSTwist (I := I) (M := M) α b r s T α' =
      (T (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b))).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b) := by
  rfl

lemma chartLowerAllUpperIndices_model_compChartJ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSModel r s ℝ E) :
    (chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T).compContinuousLinearMap
        (fun _ : Fin (r + s) => chartTrivializationLinearMap (I := I) (M := M) α b)
      = lowerAllUpperIndices (I := I) (M := M) g r s b
          (chartRSTwist (I := I) (M := M) α b r s T) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    chartLowerAllUpperIndices_model_apply]
  rw [lowerAllUpperIndices_apply]
  rw [chartRSTwist_apply]
  have hsep :
      chartSeparableFormAt (I := I) (M := M) g α b r
          (fun i : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b
            (v (Fin.castAdd s i)))
        = (separableFormAt (I := I) (M := M) g b r
            (fun i : Fin r => v (Fin.castAdd s i))).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
    have := chartSeparableFormAt_chartJ_compose (I := I) (M := M) g α hb r
      (fun i : Fin r => v (Fin.castAdd s i))
    exact this
  rw [hsep]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (chartRSTwist (I := I) (M := M) α b r s T₀)
        (chartRSTwist (I := I) (M := M) α b r s T₁) := by
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise_0s_compChartJ
    (I := I) (M := M) g r s α hb T₀ T₁]
  rw [chartLowerAllUpperIndices_model_compChartJ
    (I := I) (M := M) g r s α hb T₀]
  rw [chartLowerAllUpperIndices_model_compChartJ
    (I := I) (M := M) g r s α hb T₁]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
