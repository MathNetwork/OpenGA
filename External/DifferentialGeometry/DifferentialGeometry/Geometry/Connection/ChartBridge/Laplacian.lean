import DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian


noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem connLaplacian_function_eq_chartLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = Δ_g (I := I) g hf x := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem traceFun_abstractHessian_eq_laplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      Δ_g (I := I) g hf x := by
  classical
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h1 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
    traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity
      (I := I) g f x hM
  have h2 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      chartHessTrace (I := I) g f x :=
    traceFun_hessFun_eq_chartHessTrace_of_orthonormal (I := I) g f x h_orth
  have h3 : chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x :=
    chartHessTrace_eq_laplacian_pointwise_of_boundaryless (I := I) g hf x
  rw [← h1, h2, h3]

omit [NeZero (Module.finrank ℝ E)] in
theorem traceFun_abstractHessian_eq_connLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      connLaplacian_function (I := I) g hf x := by
  rw [connLaplacian_function_eq_chartLaplacian (I := I) g hf x]
  exact traceFun_abstractHessian_eq_laplacian (I := I) g hf x h_orth

end Connection
end Integral
end DifferentialGeometry
