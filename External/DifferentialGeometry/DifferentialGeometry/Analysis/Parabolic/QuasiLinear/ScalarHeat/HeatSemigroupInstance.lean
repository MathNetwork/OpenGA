import DifferentialGeometry.Analysis.Sobolev.Hs.HeatSemigroupContinuity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.BoundedC0Semigroup

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def scalarHsBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    BoundedC0Semigroup (scalarHs (I := I) (M := M) g σ) where
  toFun := fun t => heatSemigroupHsExt (I := I) (M := M) g σ t
  apply_zero := heatSemigroupHsExt_zero (I := I) (M := M) g σ
  apply_add := fun _ _ ht hs =>
    heatSemigroupHsExt_add (I := I) (M := M) (g := g) (σ := σ) ht hs
  opNorm_le_one := fun _ ht =>
    heatSemigroupHsExt_opNorm_le_one (I := I) (M := M)
      (g := g) (σ := σ) ht
  continuousOn_apply := fun u =>
    heatSemigroupHsExt_continuousOn (I := I) (M := M) g σ u

omit [NeZero (Module.finrank ℝ E)] in
@[simp]
theorem scalarHsBoundedC0Semigroup_apply
    (g : SmoothRiemannianMetric I M) (σ : ℝ) (t : ℝ) :
    scalarHsBoundedC0Semigroup (I := I) (M := M) g σ t =
      heatSemigroupHsExt (I := I) (M := M) g σ t := rfl

abbrev hkScalarBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    BoundedC0Semigroup (HkScalar (I := I) (M := M) g k) :=
  scalarHsBoundedC0Semigroup (I := I) (M := M) g (k : ℝ)

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
