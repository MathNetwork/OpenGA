import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian

set_option autoImplicit false
set_option linter.style.longLine false














































noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]












omit [InnerProductSpace ℝ E] in
theorem cotangentSharp_gen_eq_metricSharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (β : Tensor0SSpace 1 I x) :
    cotangentSharp_gen (I := I) g x β =
      metricSharp (I := I) g x (cotangentToDual_gen (I := I) β) := by
  apply metricFlatLinear_injective (I := I) g x
  ext w
  change g.inner x (cotangentSharp_gen (I := I) g x β) w =
    g.inner x (metricSharp (I := I) g x (cotangentToDual_gen (I := I) β)) w
  rw [cotangentSharp_inner_gen (I := I) g x β w,
    inner_metricSharp (I := I) g x (cotangentToDual_gen (I := I) β) w]



omit [InnerProductSpace ℝ E] in
theorem cotangentToDual_gen_chartBasis_eval
    (α : M) (j : Fin (Module.finrank ℝ E))
    (β : Π b : M, Tensor0SSpace 1 I b) (b : M) :
    cotangentToDual_gen (I := I) (β b) (chartBasisVecFiber (I := I) α j b) =
      β b (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) :=
  cotangentToDual_apply_gen (I := I) (β b) (chartBasisVecFiber (I := I) α j b)











omit [InnerProductSpace ℝ E] in
theorem cotangentSharp_gen_contMDiff_total [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {β : Π b : M, Tensor0SSpace 1 I b}
    (hβ : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => β b (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        TotalSpace.mk' E b (cotangentSharp_gen (I := I) g b (β b))) := by

  set cv : Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun b => cotangentToDual_gen (I := I) (β b) with hcv

  have hcv_smooth : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => cv b (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have heq :
        (fun b : M => cv b (chartBasisVecFiber (I := I) α j b)) =
          fun b : M => β b (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) := by
      funext b
      exact cotangentToDual_gen_chartBasis_eval (I := I) α j β b
    rw [heq]
    exact hβ α j

  have hmetric :=
    metricSharp_contMDiff_total (I := I) g (cv := cv) hcv_smooth

  have hsection_eq :
      (fun b : M =>
          TotalSpace.mk' E b (cotangentSharp_gen (I := I) g b (β b))) =
        fun b : M =>
          TotalSpace.mk' E b (metricSharp (I := I) g b (cv b)) := by
    funext b
    change TotalSpace.mk' E b (cotangentSharp_gen (I := I) g b (β b)) =
      TotalSpace.mk' E b (metricSharp (I := I) g b (cotangentToDual_gen (I := I) (β b)))
    rw [cotangentSharp_gen_eq_metricSharp (I := I) g b (β b)]
  rw [hsection_eq]
  exact hmetric






omit [InnerProductSpace ℝ E] in
theorem cotangentSharp_gen_mdiffAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {β : Π b : M, Tensor0SSpace 1 I b}
    (hβ : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => β b (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source)
    (x : M) :
    MDiffAt (T% (fun y : M => cotangentSharp_gen (I := I) g y (β y))) x :=
  (cotangentSharp_gen_contMDiff_total (I := I) g hβ).contMDiffAt.mdifferentiableAt
    (by simp)

end DivergenceTheorem
end Integral
end DifferentialGeometry
