import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.ChartJacobianMatrixEntrySmoothness
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Bilinear


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
lemma chartJ_self (b : M) :
    (trivializationAt E (TangentSpace I) b).continuousLinearMapAt ℝ b =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b) (b := b) (mem_chart_source H b)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b) b
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H b) v

omit [Module.Finite ℝ E] in
lemma chartJinv_self (b : M) :
    (trivializationAt E (TangentSpace I) b).symmL ℝ b = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b) (b := b) (mem_chart_source H b)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b) b
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H b) v

omit [Module.Finite ℝ E] in
theorem chartJinv_wrapped_continuousAt
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContinuousAt
      (fun b : M =>
        ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b ∘L
          (trivializationAt E (TangentSpace I) α).symmL ℝ b
            : E →L[ℝ] E))
      b₀ :=
  (contMDiffAt_tangentTrivialization_coordChangeL_alpha_to_b0 (I := I) (M := M) α hb₀).continuousAt

omit [Module.Finite ℝ E] in
theorem chartJ_wrapped_continuousAt
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContinuousAt
      (fun b : M =>
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b ∘L
          (trivializationAt E (TangentSpace I) b₀).symmL ℝ b
            : E →L[ℝ] E))
      b₀ :=
  (contMDiffAt_tangentTrivialization_coordChangeL_b0_to_alpha (I := I) (M := M) α hb₀).continuousAt

omit [Module.Finite ℝ E] in
theorem chartJinv_wrapped_centre_eq
    (α : M) (b₀ : M) :
    ((trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b₀ ∘L
      (trivializationAt E (TangentSpace I) α).symmL ℝ b₀
        : E →L[ℝ] E) =
    chartTrivializationLinearMapSymm (I := I) (M := M) α b₀ := by
  rw [chartJ_self (I := I) (M := M) b₀]
  ext v
  rfl

omit [Module.Finite ℝ E] in
theorem chartJ_wrapped_centre_eq
    (α : M) (b₀ : M) :
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀ ∘L
      (trivializationAt E (TangentSpace I) b₀).symmL ℝ b₀
        : E →L[ℝ] E) =
    chartTrivializationLinearMap (I := I) (M := M) α b₀ := by
  rw [chartJinv_self (I := I) (M := M) b₀]
  ext v
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
