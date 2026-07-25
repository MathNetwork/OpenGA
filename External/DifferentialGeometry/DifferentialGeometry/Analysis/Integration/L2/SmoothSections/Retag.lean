import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace L2
namespace SmoothCcTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



def retagEquiv
    (g h : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s ≃ₗ[ℝ] SmoothCcTensor h r s where
  toFun S := ⟨S.toSection, S.hasCompactSupport⟩
  invFun S := ⟨S.toSection, S.hasCompactSupport⟩
  left_inv S := by
    ext
    rfl
  right_inv S := by
    ext
    rfl
  map_add' S T := by
    ext
    rfl
  map_smul' c S := by
    ext
    rfl


@[simp]
theorem retag_toSection
    (g h : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (retagEquiv g h r s S).toSection = S.toSection := rfl

end SmoothCcTensor
end L2
end Integral
end DifferentialGeometry
