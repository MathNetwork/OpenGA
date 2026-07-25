import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Proper
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Analysis.Integration.Measure.Family


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_divergence_eq_zero_of_compact_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (t : ℝ) :
    ∫ x, divergence_g (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_eq_zero_of_compact (I := I) (g_fam t) X

theorem integral_divergence_eq_zero_of_hasCompactSupport_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, divergence_g (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_eq_zero_of_hasCompactSupport (I := I) (g_fam t) X hX

theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * divergence_g (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) (g_fam t) hf X hX

theorem integral_tangentSectionAction_mul_add_eq_neg_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) (t : ℝ) :
    ∫ x, (tangentSectionAction (I := I) X f x * h x +
            f x * tangentSectionAction (I := I) X h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * h x * divergence_g (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_mul_add_eq_neg
    (I := I) (g_fam t) hf hh X hX

theorem integral_inner_grad_eq_neg_integral_smul_laplacian_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_supp : HasCompactSupport h) (t : ℝ) :
    ∫ x, (g_fam t).inner x
            ((grad_g (I := I) (g_fam t) hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) (g_fam t) hh :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * Δ_g (I := I) (g_fam t) hh x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) (g_fam t) hf hh hh_supp

theorem integral_smul_laplacian_sub_eq_zero_family
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (t : ℝ) :
    ∫ x, (f x * Δ_g (I := I) (g_fam t) hh x -
            h x * Δ_g (I := I) (g_fam t) hf x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact green_second_integral_smul_laplacian_sub_eq_zero (I := I) (g_fam t) hf hh

theorem volumeVariation_hasDerivAt
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ :=
  first_variation_of_volume (I := I) (M := M) (g_fam := g_fam)
    (f := f) (t₀ := t₀) hg hf

end DivergenceTheorem
end Integral
end DifferentialGeometry
