import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Tensor.Multilinear.Bundle
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

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
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_trivialization_continuousLinearMapAt_apply
    (α : M) {b : M} (r : ℕ)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : Tensor0SSpace r I b) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b T =
      (T : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
  have hbase : b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet := by
    change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  have hcoe := (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).coe_linearMapAt_of_mem (R := ℝ) hbase
  change ((trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).linearMapAt ℝ b) T = _
  rw [show ((trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).linearMapAt ℝ b) T =
        ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α) ⟨b, T⟩).2 from
      congrFun hcoe T]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_trivialization_symmL_apply
    (α : M) {b : M} (r : ℕ)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (V : Tensor0SModel r ℝ E) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b V =
      V.compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) := by
  have hbase : b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet := by
    change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  have h := _root_.Pretrivialization.continuousMultilinearMap_symm_apply'
    (𝕜 := ℝ) (s := r) (F := E) (E := (TangentSpace I : M → Type _))
    (e := trivializationAt E (TangentSpace I) α) (b := b) hb V
  change (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symm b V = _
  rw [show (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).symm b V =
        ((Pretrivialization.continuousMultilinearMap (𝕜 := ℝ) (s := r)
          (F := E) (E := (TangentSpace I : M → Type _))
          (trivializationAt E (TangentSpace I) α)).symm b V) from rfl]
  rw [h]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorTrivProj_eq_chartRSTwistInv_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    tensorTrivProj (I := I) (M := M) g r s S α b =
      chartRSTwistInv (I := I) (M := M) α b r s (S.toFun b) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  unfold tensorTrivProj
  have hbaseHom : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseHom
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b (S.toSection b)) α' = _
  have hval :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b (S.toSection b)) =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, S.toSection b⟩).2 :=
    congrFun hcoeRS (S.toSection b)
  rw [hval]
  have hHom :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, S.toSection b⟩
        = ⟨b, ((trivializationAt (Tensor0SModel s ℝ E)
            (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
            : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
              ((S.toSection b).comp
                ((trivializationAt (Tensor0SModel r ℝ E)
                  (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
                  : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))⟩ := rfl
  rw [hHom]
  change (((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
      ((S.toSection b).comp
        ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
          : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))) α' = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [tensor0S_trivialization_symmL_apply (I := I) (M := M) α r hb α']
  rw [tensor0S_trivialization_continuousLinearMapAt_apply (I := I) (M := M) α s hb
    ((S.toSection b) (α'.compContinuousLinearMap
      (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))]
  rw [chartRSTwistInv_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartRSTwist_tensorTrivProj_eq_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartRSTwist (I := I) (M := M) α b r s
        (tensorTrivProj (I := I) (M := M) g r s S α b) =
      S.toFun b := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  rw [tensorTrivProj_eq_chartRSTwistInv_toFun (I := I) (M := M) g r s α S hb]
  rw [chartRSTwist_apply, chartRSTwistInv_apply]
  have hinner :
      (α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) = α' := by
    refine ContinuousMultilinearMap.ext ?_
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJinv_chartJ_self (I := I) (M := M) α hb (v k)
  rw [hinner]
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext k
  exact chartJinv_chartJ_self (I := I) (M := M) α hb (w k)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source)
    (T : TensorRSSpace r s I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T =
      chartRSTwistInv (I := I) (M := M) α b r s (TensorRSSpace.toModel T) := by
  classical
  have hb' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  refine ContinuousLinearMap.ext ?_
  intro α'
  have hbaseHom : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb'
    · change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb'
  have hcoeRS := (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseHom
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b T) α' = _
  have hval :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b T) =
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, T⟩).2 :=
    congrFun hcoeRS T
  rw [hval]
  have hHom :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) ⟨b, T⟩
        = ⟨b, ((trivializationAt (Tensor0SModel s ℝ E)
            (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
            : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
              (T.comp
                ((trivializationAt (Tensor0SModel r ℝ E)
                  (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
                  : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))⟩ := rfl
  rw [hHom]
  change (((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        : Tensor0SSpace s I b →L[ℝ] Tensor0SModel s ℝ E).comp
      (T.comp
        ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b
          : Tensor0SModel r ℝ E →L[ℝ] Tensor0SSpace r I b))) α' = _
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [tensor0S_trivialization_symmL_apply (I := I) (M := M) α r hb' α']
  rw [tensor0S_trivialization_continuousLinearMapAt_apply (I := I) (M := M) α s hb'
    (T (α'.compContinuousLinearMap
      (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))]
  rw [chartRSTwistInv_apply]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
