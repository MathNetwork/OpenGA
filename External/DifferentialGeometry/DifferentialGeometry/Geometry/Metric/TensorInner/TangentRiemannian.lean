import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricFiberData
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace DifferentialGeometry
namespace Tensor
namespace TangentRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [Module.Finite ℝ E] in
private lemma continuous_g_inner_aux
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x}
    (hv : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (v x)))
    (hw : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (w x))) :
    Continuous (fun b : M => g.inner b (v b) (w b)) := by

  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩

  have h := Continuous.inner_bundle (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun x => x) (v := v) (w := w) hv hw

  refine h.congr ?_
  intro b

  rfl

end TangentRiemannian
end Tensor
end DifferentialGeometry

namespace TangentBundle

open scoped Manifold Topology Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
theorem continuous_g_inner_of_smooth_sections
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (X b) (Y b)) := by

  have hX : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (X x)) :=
    X.contMDiff.continuous
  have hY : Continuous (fun x : M => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) x (Y x)) :=
    Y.contMDiff.continuous
  exact DifferentialGeometry.Tensor.TangentRiemannian.continuous_g_inner_aux
    (I := I) (M := M) g hX hY

end TangentBundle
