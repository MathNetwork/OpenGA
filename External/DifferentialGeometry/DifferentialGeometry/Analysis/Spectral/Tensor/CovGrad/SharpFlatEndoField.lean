import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower








noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem sharpFlatEndo_eval (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) w =
      cotangentToDual (I := I) om (metricComparisonEndo (I := I) g₀ g₁ x w) := by
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om =
      g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  have h₁ : ∀ v : TangentSpace I x,
      g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x w) v =
        g₀.inner x w v := by
    intro v
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_inner,
      cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) (x := x) om
        (metricComparisonEndo (I := I) g₀ g₁ x w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (metricComparisonEndo (I := I) g₀ g₁ x w) by
      rw [inverseMetricSharpFib_inner]
      rfl]
  rw [g₁.symm, h₁]
  exact g₀.symm x _ _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
