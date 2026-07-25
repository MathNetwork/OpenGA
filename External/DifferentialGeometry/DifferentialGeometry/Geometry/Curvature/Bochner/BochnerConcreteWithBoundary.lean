import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerConcrete
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Laplacian
import DifferentialGeometry.Geometry.Boundary.ModelBoundary
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs












































































noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry
namespace Integral
namespace Connection
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [HasSmoothBoundary E H I]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]


























omit [NeZero (Module.finrank ℝ E)] [HasSmoothBoundary E H I] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] in
theorem bochner_pointwise_concrete_metric_withBoundary
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (h_pointwise : ∀ x : M, x ∈ I.interior M →
      Δ_g_with_boundary (I := I) g hf hf_int x =
        2 * chartHessFrobeniusSq (I := I) g f x +
          2 * ricciFun (I := I) g x
                (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
          2 * g.inner x (gradFun (I := I) g f x)
              (gradFun (I := I) g (Δ_g_with_boundary (I := I) g hf hf_int) x))
    {x : M} (hx : x ∈ I.interior M) :
    Δ_g_with_boundary (I := I) g hf hf_int x =
      2 * chartHessFrobeniusSq (I := I) g f x +
        2 * ricciFun (I := I) g x
              (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
        2 * g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g (Δ_g_with_boundary (I := I) g hf hf_int) x) :=
  h_pointwise x hx





omit [NeZero (Module.finrank ℝ E)] [HasSmoothBoundary E H I] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] in
theorem bochner_pointwise_concrete_metric_withBoundary_eqOn
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (h_pointwise : ∀ x : M, x ∈ I.interior M →
      Δ_g_with_boundary (I := I) g hf hf_int x =
        2 * chartHessFrobeniusSq (I := I) g f x +
          2 * ricciFun (I := I) g x
                (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
          2 * g.inner x (gradFun (I := I) g f x)
              (gradFun (I := I) g (Δ_g_with_boundary (I := I) g hf hf_int) x)) :
    Set.EqOn (Δ_g_with_boundary (I := I) g hf hf_int)
      (fun x : M =>
        2 * chartHessFrobeniusSq (I := I) g f x +
          2 * ricciFun (I := I) g x
                (gradFun (I := I) g f x) (gradFun (I := I) g f x) +
          2 * g.inner x (gradFun (I := I) g f x)
              (gradFun (I := I) g (Δ_g_with_boundary (I := I) g hf hf_int) x))
      (I.interior M) := by
  intro x hx
  exact bochner_pointwise_concrete_metric_withBoundary
    (I := I) g hf hf_int h_pointwise hx

end WithBoundary
end Connection
end Integral
end DifferentialGeometry
