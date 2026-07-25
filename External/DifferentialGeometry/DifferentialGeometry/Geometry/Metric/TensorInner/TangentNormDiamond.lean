import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentContinuousRiemannianMetric
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Basic


noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem tensor0SBundle_enorm_eq_riemannianBundle_enorm
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) := by
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI _rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  have hinner : (inner ℝ v v : ℝ) = g.inner x v v := rfl
  rw [hinner]

end DifferentialGeometry.Geometry.Riemannian

end
