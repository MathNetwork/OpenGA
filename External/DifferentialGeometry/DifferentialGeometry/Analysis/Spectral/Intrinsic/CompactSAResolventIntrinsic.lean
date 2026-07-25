import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CompactInclusionIntrinsic
import DifferentialGeometry.Analysis.Spectral.Tensor.Rellich.Tensor
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.Resolvent

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompleteSpace E] in
theorem tensorResolventL2_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator_of_isCompactOperator
    (I := I) (M := M) g r s
    (tensorH1ComplToTensorL2_isCompactOperator_intrinsic
      (I := I) (M := M) g r s)

omit [CompleteSpace E] in
theorem tensorResolventL2_isCompactOperator_isSelfAdjoint_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) ∧
      IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) :=
  ⟨tensorResolventL2_isCompactOperator (I := I) (M := M) g r s,
   tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s⟩

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) :=
  tensorResolventL2_isCompactOperator (I := I) (M := M) g r s

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
