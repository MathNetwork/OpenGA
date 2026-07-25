import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PosDefPerturbation


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
theorem perturbedInner_self_upper_bound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ : metricCauchySchwarzBound g h δ)
    (x : M) (v : TangentSpace I x) :
    perturbedInner g h x v v ≤ (1 + δ) * g.inner x v v := by
  have hnn : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hbound := hδ x v v
  have hsq : Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) = g.inner x v v := by
    rw [← Real.sqrt_mul hnn, Real.sqrt_mul_self hnn]
  have hdiag : |h x v v| ≤ δ * g.inner x v v := by
    calc |h x v v|
        ≤ δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) := hbound
      _ = δ * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v)) := by ring
      _ = δ * g.inner x v v := by rw [hsq]
  have hle : h x v v ≤ δ * g.inner x v v := le_of_abs_le hdiag
  rw [perturbedInner_apply]
  nlinarith [hle]

omit [Module.Finite ℝ E] in
theorem gInner_self_le_of_gFibreOpBound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ : metricCauchySchwarzBound g h δ)
    (x : M) (v : TangentSpace I x) :
    g.inner x v v + h x v v ≤ (1 + δ) * g.inner x v v := by
  have h := perturbedInner_self_upper_bound (I := I) (M := M) g h hδ x v
  rwa [perturbedInner_apply] at h

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
