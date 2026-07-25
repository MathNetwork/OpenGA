import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.Resolvent
import Mathlib.Analysis.Normed.Operator.Compact


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorResolventL2_eq_comp (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    tensorResolventL2 (I := I) (M := M) g r s =
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).comp
        (tensorResolvent (I := I) (M := M) g r s) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorResolventL2_apply_eq_comp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (f : TensorL2 r s g) :
    (tensorResolventL2 (I := I) (M := M) g r s) f =
      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)
        ((tensorResolvent (I := I) (M := M) g r s) f) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventL2_isCompactOperator_of_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_H1L2 :
      IsCompactOperator
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) := by
  have h_comp : IsCompactOperator
      ((fun v : TensorH1Compl g r s =>
          TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) ∘
        (fun f : TensorL2 r s g =>
          tensorResolvent (I := I) (M := M) g r s f)) :=
    h_H1L2.comp_clm (tensorResolvent (I := I) (M := M) g r s)
  exact h_comp

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventL2_isCompactOperator_and_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_H1L2 :
      IsCompactOperator
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) ∧
      IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) :=
  ⟨tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s h_H1L2,
   tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s⟩

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : IsCompactOperator (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s h

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
