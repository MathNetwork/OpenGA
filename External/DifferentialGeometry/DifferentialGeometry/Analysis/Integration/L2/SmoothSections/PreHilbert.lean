import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.VectorBundle.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section PreHilbert

variable [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}


noncomputable instance instPreInnerProductSpaceCore :
    PreInnerProductSpace.Core ℝ (SmoothCcTensor g r s) where
  inner S T := tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
  conj_inner_symm S T := by
    change (tensorL2Inner (I := I) (M := M) g r s T.toFun S.toFun : ℝ) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
    exact tensorL2Inner_symm (I := I) (M := M) g r s T.toFun S.toFun
  re_inner_nonneg S := by
    change (0 : ℝ) ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun
    exact tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun
  add_left S₁ S₂ T := by
    change tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂).toFun T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun +
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun S₂.toFun T.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)
  smul_left S T c := by
    change tensorL2Inner (I := I) (M := M) g r s (c • S).toFun T.toFun =
      c * tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun
    rw [SmoothCcTensor.toFun_smul]
    exact tensorL2Inner_smul_left (I := I) (M := M) g r s c S.toFun T.toFun


noncomputable instance instSeminormedAddCommGroup :
    SeminormedAddCommGroup (SmoothCcTensor g r s) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)


noncomputable instance instInnerProductSpace :
    InnerProductSpace ℝ (SmoothCcTensor g r s) :=
  InnerProductSpace.ofCore _


@[simp] theorem SmoothCcTensor.inner_def (S T : SmoothCcTensor g r s) :
    ⟪S, T⟫_ℝ = tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun := rfl


theorem SmoothCcTensor.norm_def (S : SmoothCcTensor g r s) :
    ‖S‖ = tensorL2Norm (I := I) (M := M) g r s S.toFun := rfl

end PreHilbert

section InstanceTests

variable [T2Space M] [SigmaCompactSpace M]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SeminormedAddCommGroup (SmoothCcTensor g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (SmoothCcTensor g r s) := inferInstance

end InstanceTests

end L2
end Integral
end DifferentialGeometry

end
