import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.InteriorCompactSupport
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Green
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.Stokes
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.GreenWithBoundary
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Family
import DifferentialGeometry.Analysis.Integration.Measure.Family


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [InnerProductSpace ℝ E] in
theorem integral_divergence_with_boundary_eq_zero_of_compact_of_interior_support_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX_int : tsupport X ⊆ I.interior M) (t : ℝ) :
    ∫ x, divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_with_boundary_eq_zero_of_compact_of_interior_support
    (I := I) (g_fam t) X hX_int

omit [InnerProductSpace ℝ E] in
theorem integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support_family
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) (t : ℝ) :
    ∫ x, divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
    (I := I) (g_fam t) X hX hX_int

omit [InnerProductSpace ℝ E] in
theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary_family
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) (t : ℝ) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
    (I := I) (g_fam t) hf hf_int X hX hX_int

omit [InnerProductSpace ℝ E] in
theorem integral_tangentSectionAction_mul_add_eq_neg_with_boundary_family
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) (t : ℝ) :
    ∫ x, (tangentSectionAction (I := I) X f x * h x +
            f x * tangentSectionAction (I := I) X h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * h x * divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_tangentSectionAction_mul_add_eq_neg_with_boundary
    (I := I) (g_fam t) hf hh hf_int hh_int X hX hX_int

omit [InnerProductSpace ℝ E] in
theorem integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary_family
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (hh_supp : HasCompactSupport h) (t : ℝ) :
    ∫ x, (g_fam t).inner x (gradFun (I := I) (g_fam t) f x)
            (gradFun (I := I) (g_fam t) h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      -∫ x, f x * Δ_g_with_boundary (I := I) (g_fam t) hh hh_int x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) := by
  rw [riemannianMeasureFamily_def]
  exact integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
    (I := I) (g_fam t) hf hh hf_int hh_int hh_supp

omit [InnerProductSpace ℝ E] in
theorem integral_smul_laplacian_sub_eq_zero_with_boundary_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (t : ℝ) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) (g_fam t) hh hh_int x -
            h x * Δ_g_with_boundary (I := I) (g_fam t) hf hf_int x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) = 0 := by
  rw [riemannianMeasureFamily_def]
  exact integral_smul_laplacian_sub_eq_zero_with_boundary
    (I := I) (g_fam t) hf hh hf_int hh_int

section StokesGlobal

variable [hI : HasSmoothBoundary E H I]

omit [InnerProductSpace ℝ E] in
theorem stokes_compact_via_pou_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (t : ℝ) :
    ∫ x, divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        chartBoundaryFaceIntegral (I := I) (g_fam t) α X
          ((chartAtlasPOU I M) α) := by
  rw [riemannianMeasureFamily_def]
  exact stokes_compact_via_pou (I := I) (g_fam t) X

omit [InnerProductSpace ℝ E] in
theorem integral_divergence_with_boundary_eq_boundaryFaceSum_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (t : ℝ) :
    ∫ x, divergence_g_with_boundary (I := I) (g_fam t) X x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      boundaryFaceSum (I := I) (g_fam t) X := by
  rw [riemannianMeasureFamily_def]
  exact integral_divergence_with_boundary_eq_boundaryFaceSum (I := I) (g_fam t) X

omit [InnerProductSpace ℝ E] in
theorem green_first_with_boundary_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) (t : ℝ) :
    ∫ x, (g_fam t).inner x (gradFun (I := I) (g_fam t) f x)
            (gradFun (I := I) (g_fam t) h x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) +
      ∫ x, f x * Δ_g_with_boundary (I := I) (g_fam t) hh hh_int x
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      boundaryFaceSum (I := I) (g_fam t)
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) (g_fam t) hh hh_int)) := by
  simp only [riemannianMeasureFamily_def]
  exact green_first_with_boundary (I := I) (g_fam t) hf hh hh_int

omit [InnerProductSpace ℝ E] in
theorem green_second_with_boundary_family
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (t : ℝ) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) (g_fam t) hh hh_int x -
            h x * Δ_g_with_boundary (I := I) (g_fam t) hf hf_int x)
        ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t) =
      boundaryFaceSum (I := I) (g_fam t)
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) (g_fam t) hh hh_int)) -
      boundaryFaceSum (I := I) (g_fam t)
        (smoothSmul (I := I) h hh
          (grad_g_with_boundary_section (I := I) (g_fam t) hf hf_int)) := by
  rw [riemannianMeasureFamily_def]
  exact green_second_with_boundary (I := I) (g_fam t) hf hh hf_int hh_int

end StokesGlobal

omit [InnerProductSpace ℝ E] in
theorem volumeVariation_hasDerivAt_with_boundary
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

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
