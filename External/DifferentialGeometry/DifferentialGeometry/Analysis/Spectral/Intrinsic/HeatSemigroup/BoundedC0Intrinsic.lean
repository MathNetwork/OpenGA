import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Intrinsic
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.BoundedC0Semigroup

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

noncomputable def tensorBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    BoundedC0Semigroup (TensorL2 r s g) where
  toFun := fun t => tensorHeatSemigroup (I := I) (M := M) g r s t
  apply_zero :=
    tensorHeatSemigroup_intrinsic_apply_zero (I := I) (M := M) g r s
  apply_add := fun _ _ ht hs =>
    tensorHeatSemigroup_intrinsic_apply_add (I := I) (M := M) g r s ht hs
  opNorm_le_one := fun t _ =>
    tensorHeatSemigroup_intrinsic_opNorm_le_one (I := I) (M := M) g r s t
  continuousOn_apply := fun T =>
    tensorHeatSemigroup_intrinsic_continuousOn (I := I) (M := M) g r s T

@[simp]
theorem tensorBoundedC0Semigroup_intrinsic_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    tensorBoundedC0Semigroup (I := I) (M := M) g r s t =
      tensorHeatSemigroup (I := I) (M := M) g r s t :=
  rfl

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
