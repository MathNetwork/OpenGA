import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Geometry.Connection.ParsevalFrameField










noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem trace_slot_flat (q h : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    cometricDoubleTraceFib (I := I) h 0 x D =
      cometricDoubleTraceFib (I := I) q 0 x
        (slotExtendPointwise (I := I) (M := M) q 1 1 x
          ((g0FlatCLM (I := I) q x).comp (inverseMetricSharpFib (I := I) h x)) D) := by
  classical
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  beta_reduce
  rw [cometricDoubleTraceFib_toModel (I := I) h 0 x D]
  rw [modelDoubleTrace_apply (E := E) 0 (cometricLmodel (I := I) h x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) h x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel D) mm]
  rw [cometricDoubleTraceFib_toModel (I := I) q 0 x]
  rw [modelDoubleTrace_apply (E := E) 0 (cometricLmodel (I := I) q x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) q x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel
      (slotExtendPointwise (I := I) (M := M) q 1 1 x
        ((g0FlatCLM (I := I) q x).comp (inverseMetricSharpFib (I := I) h x)) D)) mm]
  have hslot : ∀ a : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (slotExtendPointwise (I := I) (M := M) q 1 1 x
            ((g0FlatCLM (I := I) q x).comp (inverseMetricSharpFib (I := I) h x)) D)
          (Fin.cons ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E) mm)) =
        Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)
            (Fin.cons (show E from inverseMetricSharpFib (I := I) h x
              (g0FlatCLM (I := I) q x (smoothOrthoFrame (I := I) q x a x))) mm)) := by
    intro a
    rw [slotExtendFib_apply_eval]
    rw [ContinuousLinearMap.comp_apply, g0FlatCLM_apply]
    change q.inner x
        (inverseMetricSharpFib (I := I) h x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) D
            (smoothOrthoFrame (I := I) q x a x)))
        (smoothOrthoFrame (I := I) q x a x) = _
    rw [q.symm x]
    rw [← cotangentToDual_g0FlatCLM (I := I) q x
      (smoothOrthoFrame (I := I) q x a x)]
    rw [← cotangentToDualLinear_apply]
    rw [← inverseMetricSharpFib_inner (I := I) h x
      (g0FlatCLM (I := I) q x (smoothOrthoFrame (I := I) q x a x))]
    rw [h.symm x]
    rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_apply]
    rw [show (fun _ : Fin 1 =>
        (inverseMetricSharpFib (I := I) h x
          (g0FlatCLM (I := I) q x (smoothOrthoFrame (I := I) q x a x)) : E)) =
        Fin.cons
          (show E from inverseMetricSharpFib (I := I) h x
            (g0FlatCLM (I := I) q x (smoothOrthoFrame (I := I) q x a x))) mm from by
      funext j
      fin_cases j
      rfl]
    change Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) D
          (smoothOrthoFrame (I := I) q x a x))
        (Fin.cons
          (show E from inverseMetricSharpFib (I := I) h x
            (g0FlatCLM (I := I) q x (smoothOrthoFrame (I := I) q x a x))) mm) = _
    rw [TensorMultilinear.tensor0S_curry_apply_eval]
  rw [Finset.sum_congr rfl (fun a _ => hslot a)]
  have horthH : ∀ i j : Fin (Module.finrank ℝ E),
      h.inner x (smoothOrthoFrame (I := I) h x i x)
        (smoothOrthoFrame (I := I) h x j x) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) h x i j
  have hF : ∀ a : Fin (Module.finrank ℝ E),
      (show E from inverseMetricSharpFib (I := I) h x
        (g0FlatCLM (I := I) q x (smoothOrthoFrame (I := I) q x a x))) =
        ∑ c : Fin (Module.finrank ℝ E),
          q.inner x (smoothOrthoFrame (I := I) q x a x)
              (smoothOrthoFrame (I := I) h x c x) •
            ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E) := by
    intro a
    have hexp := orthonormal_tangent_expansion (I := I) (M := M) h x
      (fun c => smoothOrthoFrame (I := I) h x c x) horthH
      (inverseMetricSharpFib (I := I) h x
        (g0FlatCLM (I := I) q x (smoothOrthoFrame (I := I) q x a x)))
    rw [← hexp]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [h.symm x, inverseMetricSharpFib_inner, cotangentToDualLinear_apply,
      cotangentToDual_g0FlatCLM]
  have horthQ : ∀ i j : Fin (Module.finrank ℝ E),
      q.inner x (smoothOrthoFrame (I := I) q x i x)
        (smoothOrthoFrame (I := I) q x j x) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) q x i j
  have hQexp : ∀ c : Fin (Module.finrank ℝ E),
      (∑ a : Fin (Module.finrank ℝ E),
          q.inner x (smoothOrthoFrame (I := I) q x a x)
              (smoothOrthoFrame (I := I) h x c x) •
            ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)) =
        ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E) := by
    intro c
    exact orthonormal_tangent_expansion (I := I) (M := M) q x
      (fun a => smoothOrthoFrame (I := I) q x a x) horthQ
      (smoothOrthoFrame (I := I) h x c x)
  symm
  calc
    (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)
            (Fin.cons (show E from inverseMetricSharpFib (I := I) h x
              (g0FlatCLM (I := I) q x (smoothOrthoFrame (I := I) q x a x))) mm))) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
        q.inner x (smoothOrthoFrame (I := I) q x a x)
            (smoothOrthoFrame (I := I) h x c x) *
          Tensor0SSpace.toModel D
            (Fin.cons ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hF a]
        change (((Tensor0SSpace.toModel D).curryLeft
            ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)).curryLeft
              (∑ c : Fin (Module.finrank ℝ E),
                q.inner x (smoothOrthoFrame (I := I) q x a x)
                    (smoothOrthoFrame (I := I) h x c x) •
                  ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E))) mm = _
        rw [map_sum, ContinuousMultilinearMap.sum_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
        rfl
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        q.inner x (smoothOrthoFrame (I := I) q x a x)
            (smoothOrthoFrame (I := I) h x c x) *
          Tensor0SSpace.toModel D
            (Fin.cons ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E) mm)) :=
      Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hlin :
            Tensor0SSpace.toModel D
                (Fin.cons
                  (∑ a : Fin (Module.finrank ℝ E),
                    q.inner x (smoothOrthoFrame (I := I) q x a x)
                        (smoothOrthoFrame (I := I) h x c x) •
                      ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E))
                  (Fin.cons ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E) mm)) =
              ∑ a : Fin (Module.finrank ℝ E),
                q.inner x (smoothOrthoFrame (I := I) q x a x)
                    (smoothOrthoFrame (I := I) h x c x) *
                  Tensor0SSpace.toModel D
                    (Fin.cons ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)
                      (Fin.cons ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E) mm)) := by
          change ((Tensor0SSpace.toModel D).curryLeft
              (∑ a : Fin (Module.finrank ℝ E),
                q.inner x (smoothOrthoFrame (I := I) q x a x)
                    (smoothOrthoFrame (I := I) h x c x) •
                  ((smoothOrthoFrame (I := I) q x a x : TangentSpace I x) : E)))
              (Fin.cons ((smoothOrthoFrame (I := I) h x c x : TangentSpace I x) : E) mm) = _
          rw [map_sum, ContinuousMultilinearMap.sum_apply]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
          rfl
        rw [← hlin, hQexp c]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
