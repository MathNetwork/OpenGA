import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.Defs
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Adjoint


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

noncomputable def tensorResolventL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).comp
    (tensorResolvent (I := I) (M := M) g r s)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorResolventL2_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) :
    tensorResolventL2 (I := I) (M := M) g r s f =
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s f) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma inner_tensorResolventL2_eq_inner_tensorResolvent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f h : TensorL2 r s g) :
    ⟪tensorResolventL2 (I := I) (M := M) g r s f, h⟫_ℝ =
      ⟪tensorResolvent (I := I) (M := M) g r s f,
        tensorResolvent (I := I) (M := M) g r s h⟫_ℝ := by
  rw [tensorResolventL2_apply]
  have hvar := tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s h
    (tensorResolvent (I := I) (M := M) g r s f)
  rw [← hvar]
  exact real_inner_comm _ _

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventL2_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f h : TensorL2 r s g) :
    ⟪tensorResolventL2 (I := I) (M := M) g r s f, h⟫_ℝ =
      ⟪f, tensorResolventL2 (I := I) (M := M) g r s h⟫_ℝ := by
  rw [inner_tensorResolventL2_eq_inner_tensorResolvent (I := I) (M := M) g r s f h]
  rw [show ⟪f, tensorResolventL2 (I := I) (M := M) g r s h⟫_ℝ =
      ⟪tensorResolventL2 (I := I) (M := M) g r s h, f⟫_ℝ from real_inner_comm _ _]
  rw [inner_tensorResolventL2_eq_inner_tensorResolvent (I := I) (M := M) g r s h f]
  exact real_inner_comm _ _

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventL2_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  exact tensorResolventL2_symm (I := I) (M := M) g r s f h

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  tensorResolventL2 (I := I) (M := M) g r s

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
