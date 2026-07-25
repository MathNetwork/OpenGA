import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Analysis.Normed.Module.Multilinear.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace TensorRSRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance tensor0SModelNormedSpace_local {n : ℕ} :
    NormedSpace ℝ (Tensor0SModel n ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace n

private instance tensor0SModelNormedAddCommGroup_local {n : ℕ} :
    NormedAddCommGroup (Tensor0SModel n ℝ E) := inferInstance


omit [IsManifold I ∞ M] in
lemma contMDiffOn_eval_basisTuple_of_into_tensor0SModel
    {n : ℕ} {U : Set M} {Φ : M → Tensor0SModel n ℝ E}
    (hΦ : ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U := by

  set evalCLM :
      Tensor0SModel n ℝ E →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ
      (fun k : Fin n => (chartModelBasis E) (φ k)) with hevalCLM

  have heq : (fun b : M => Φ b (fun k : Fin n => (chartModelBasis E) (φ k)))
      = fun b : M => evalCLM (Φ b) := by
    funext b
    rfl
  rw [heq]
  exact evalCLM.contMDiff.comp_contMDiffOn hΦ


theorem chartTensorInnerPointwise_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (T S : M → TensorRSModel r s ℝ E)
    (hT : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b (T b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b (S b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => chartTensorInnerPointwise
        (I := I) (M := M) g α r s b (T b) (S b))
      (trivializationAt E (TangentSpace I) α).baseSet := by

  have hsmooth :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => chartTensorInnerPointwise_0s
          (I := I) (M := M) (r + s) g α b
            (loweredCompose (I := I) (M := M) g r s α b (T b))
            (loweredCompose (I := I) (M := M) g r s α b (S b)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartTensorInnerPointwise_0s_contMDiffOn_smooth_args
      (I := I) (M := M) g α (r + s)
      (fun b => loweredCompose (I := I) (M := M) g r s α b (T b))
      (fun b => loweredCompose (I := I) (M := M) g r s α b (S b))
      (fun φ => contMDiffOn_eval_basisTuple_of_into_tensor0SModel
        (I := I) (M := M) hT φ)
      (fun φ => contMDiffOn_eval_basisTuple_of_into_tensor0SModel
        (I := I) (M := M) hS φ)
  exact hsmooth


theorem chartLocal_contMDiff_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y) (α : M)
    (hTα : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I 𝓘(ℝ) ∞
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
  refine ContMDiffOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_contMDiffOn
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
open TensorMetricLowering
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance tensor0SModelNormedSpace_local {n : ℕ} :
    NormedSpace ℝ (Tensor0SModel n ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace n


theorem contMDiff_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y)
    (hT_charts : ∀ α : M, ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b))) := by
  intro b
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) b).baseSet :=
    (trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g r s T S b (hT_charts b) (hS_charts b)
  exact hLocal.contMDiffAt (hOpen.mem_nhds hb_base)

end TensorRSBundle

namespace DifferentialGeometry
namespace Tensor

open scoped Manifold Topology Bundle
open Tensor0SBundle Bundle Set
open TensorMetricLowering
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem tensorInnerPointwise_contMDiff_of_mdiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (T b))
        (TensorRSSpace.toModel (S b))) :=
  TensorRSBundle.contMDiff_inner_of_smooth_sections
    (I := I) (M := M) g r s
    (fun b : M => T b) (fun b : M => S b)
    (fun α : M =>
      TensorMetricLowering.contMDiffOn_loweredCompose
        (I := I) (M := M) g r s T α)
    (fun α : M =>
      TensorMetricLowering.contMDiffOn_loweredCompose
        (I := I) (M := M) g r s S α)


theorem tensorInnerPointwise_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (S.toSection b))
        (TensorRSSpace.toModel (T.toSection b))) :=
  tensorInnerPointwise_contMDiff_of_mdiff
    (I := I) (M := M) g r s S.toSection T.toSection

end Tensor
end DifferentialGeometry

end
