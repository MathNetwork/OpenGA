import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality








noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotExtIter_apply (g : SmoothRiemannianMetric I M) (s w : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (A : Tensor0SSpace ((s + 1) + w) I x) :
    (show Tensor0SSpace ((s + 1) + w) I x →L[ℝ]
        Tensor0SSpace ((s + 1) + w) I x from
      (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) w
        (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) ((s + 1) + w) ⟨w, by omega⟩ x (Λ x) A := by
  induction w with
  | zero =>
      rfl
  | succ w ih =>
      change slotExtendPointwise (I := I) (M := M) g ((s + 1) + w) ((s + 1) + w) x
          (show Tensor0SSpace ((s + 1) + w) I x →L[ℝ]
              Tensor0SSpace ((s + 1) + w) I x from
            (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) w
              (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)).toSection x) A = _
      change _ =
        (slotInsertEndoFib (I := I) (M := M) (((s + 1) + w) + 1)
          (⟨w, by omega⟩ : Fin ((s + 1) + w)).succ x (Λ x)) A
      rw [slotInsertEndoFib_succ (I := I) (M := M) g ((s + 1) + w)
        ⟨w, by omega⟩ x (Λ x)]
      apply Tensor0SSpace.toModel_injective
      refine ContinuousMultilinearMap.ext (fun m => ?_)
      rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
      rw [slotExtendFib_apply_eval (I := I) (M := M) g ((s + 1) + w) ((s + 1) + w),
        slotExtendFib_apply_eval (I := I) (M := M) g ((s + 1) + w) ((s + 1) + w)]
      rw [ih]


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem app_slotExt_apply (g : SmoothRiemannianMetric I M) (s w : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (W : SmoothCcTensor g 0 ((s + 1) + w)) (x : M) (d : Tensor0SSpace 0 I x) :
    (ccOperatorFieldComp (I := I) (M := M) g 0 ((s + 1) + w) ((s + 1) + w)
      (slotExtendIter (I := I) (M := M) g (s + 1) (s + 1) w
        (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)) W).toSection x d =
      slotInsertEndoFib (I := I) (M := M) ((s + 1) + w) ⟨w, by omega⟩ x (Λ x)
        (W.toSection x d) := by
  rw [appCcRS_toSection, ContinuousLinearMap.comp_apply]
  exact slotExtIter_apply (I := I) (M := M) g s w Λ x (W.toSection x d)

end Connection
end Integral
end DifferentialGeometry
