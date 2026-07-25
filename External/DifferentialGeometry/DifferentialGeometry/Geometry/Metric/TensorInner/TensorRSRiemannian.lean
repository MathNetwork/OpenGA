import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace TensorRSRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def loweredCompose
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E) : Tensor0SModel (r + s) ℝ E :=
  (lowerAllUpperIndices (I := I) (M := M) g r s b T).compContinuousLinearMap
    (fun _ : Fin (r + s) =>
      DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
        (I := I) (M := M) α b)

@[simp] lemma loweredCompose_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    loweredCompose (I := I) (M := M) g r s α b T v =
      lowerAllUpperIndices (I := I) (M := M) g r s b T
        (fun i =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) α b (v i)) := by
  unfold loweredCompose
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

lemma loweredCompose_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T₁ T₂ : TensorRSModel r s ℝ E) :
    loweredCompose (I := I) (M := M) g r s α b (T₁ + T₂) =
      loweredCompose (I := I) (M := M) g r s α b T₁ +
        loweredCompose (I := I) (M := M) g r s α b T₂ := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_add]
  rfl

lemma loweredCompose_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (c : ℝ) (T : TensorRSModel r s ℝ E) :
    loweredCompose (I := I) (M := M) g r s α b (c • T) =
      c • loweredCompose (I := I) (M := M) g r s α b T := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_smul]
  rfl

lemma loweredCompose_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M) :
    loweredCompose (I := I) (M := M) g r s α b (0 : TensorRSModel r s ℝ E) =
      (0 : Tensor0SModel (r + s) ℝ E) := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_zero]
  rfl

noncomputable def chartTensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) : ℝ :=
  chartTensorInnerPointwise_0s (I := I) (M := M) (r + s) g α b
    (loweredCompose (I := I) (M := M) g r s α b T)
    (loweredCompose (I := I) (M := M) g r s α b S)

@[simp] lemma chartTensorInnerPointwise_apply
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T S =
      chartTensorInnerPointwise_0s (I := I) (M := M) (r + s) g α b
        (loweredCompose (I := I) (M := M) g r s α b T)
        (loweredCompose (I := I) (M := M) g r s α b S) := rfl

lemma chartTensorInnerPointwise_add_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T₁ T₂ S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b (T₁ + T₂) S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T₁ S +
        chartTensorInnerPointwise (I := I) (M := M) g α r s b T₂ S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    chartTensorInnerPointwise_apply, loweredCompose_add]
  exact chartTensorInnerPointwise_0s_add_left
    (I := I) (M := M) g α b (r + s) _ _ _

lemma chartTensorInnerPointwise_add_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S₁ S₂ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T (S₁ + S₂) =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T S₁ +
        chartTensorInnerPointwise (I := I) (M := M) g α r s b T S₂ := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    chartTensorInnerPointwise_apply, loweredCompose_add]
  exact chartTensorInnerPointwise_0s_add_right
    (I := I) (M := M) g α b (r + s) _ _ _

lemma chartTensorInnerPointwise_smul_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b (c • T) S =
      c * chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    loweredCompose_smul]
  exact chartTensorInnerPointwise_0s_smul_left
    (I := I) (M := M) g α b (r + s) c _ _

lemma chartTensorInnerPointwise_smul_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T (c • S) =
      c * chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    loweredCompose_smul]
  exact chartTensorInnerPointwise_0s_smul_right
    (I := I) (M := M) g α b (r + s) c _ _

lemma chartTensorInnerPointwise_zero_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b 0 S = 0 := by
  rw [chartTensorInnerPointwise_apply, loweredCompose_zero]

  have h := chartTensorInnerPointwise_0s_add_left
    (I := I) (M := M) g α b (r + s) (0 : Tensor0SModel (r + s) ℝ E) 0
    (loweredCompose (I := I) (M := M) g r s α b S)
  have h₀ : (0 : Tensor0SModel (r + s) ℝ E) + 0 = 0 := add_zero _
  rw [h₀] at h
  linarith

lemma chartTensorInnerPointwise_zero_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T 0 = 0 := by
  rw [chartTensorInnerPointwise_apply, loweredCompose_zero]
  have h := chartTensorInnerPointwise_0s_add_right
    (I := I) (M := M) g α b (r + s)
    (loweredCompose (I := I) (M := M) g r s α b T)
    (0 : Tensor0SModel (r + s) ℝ E) 0
  have h₀ : (0 : Tensor0SModel (r + s) ℝ E) + 0 = 0 := add_zero _
  rw [h₀] at h
  linarith

theorem tensorInnerPointwise_bridge_identity
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T S : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s b T S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  unfold tensorInnerPointwise chartTensorInnerPointwise loweredCompose
  exact tensorInnerPointwise_0s_bridge_identity
    (I := I) (M := M) g α (r + s) hb _ _

lemma chartTensorInnerPointwise_symm
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b S T := by
  rw [← tensorInnerPointwise_bridge_identity (I := I) (M := M) g α r s hb T S,
    ← tensorInnerPointwise_bridge_identity (I := I) (M := M) g α r s hb S T]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b T S

theorem chartTensorInnerPointwise_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (T S : M → TensorRSModel r s ℝ E)
    (hT : ContinuousOn (fun b : M => loweredCompose
        (I := I) (M := M) g r s α b (T b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS : ContinuousOn (fun b : M => loweredCompose
        (I := I) (M := M) g r s α b (S b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M => chartTensorInnerPointwise
        (I := I) (M := M) g α r s b (T b) (S b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hcont :
      ContinuousOn (fun b : M => chartTensorInnerPointwise_0s
        (I := I) (M := M) (r + s) g α b
          (loweredCompose (I := I) (M := M) g r s α b (T b))
          (loweredCompose (I := I) (M := M) g r s α b (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartTensorInnerPointwise_0s_continuousOn_smooth_args
      (I := I) (M := M) g α (r + s)
      (fun b => loweredCompose (I := I) (M := M) g r s α b (T b))
      (fun b => loweredCompose (I := I) (M := M) g r s α b (S b)) hT hS
  exact hcont

theorem chartLocal_continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y) (α : M)
    (hTα : ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            (T b))
          (TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by

  have hbridge : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)) =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)) := by
    intro b hb
    exact tensorInnerPointwise_bridge_identity
      (I := I) (M := M) g α r s hb _ _
  refine ContinuousOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_continuousOn
    (I := I) (M := M) g α r s
    (fun b : M => TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
        (T b))
    (fun b : M => TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
        (S b))
    hTα hSα

end TensorRSRiemannian
end Tensor
end DifferentialGeometry

namespace TensorRSBundle

open scoped Manifold Topology Bundle BigOperators
open Tensor0SBundle Bundle Set
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y)
    (hT_charts : ∀ α : M, ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    Continuous (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b))) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) b).baseSet :=
    (trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_continuous_inner_of_smooth_sections
      (I := I) (M := M) g r s T S b (hT_charts b) (hS_charts b)
  exact hLocal.continuousAt (hOpen.mem_nhds hb_base)

end TensorRSBundle
