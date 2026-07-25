import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Laplacian
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.InteriorCompactSupport
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

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
theorem integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (hh_supp : HasCompactSupport h) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hX_def
  have hX_cs : HasCompactSupport X :=
    hasCompactSupport_grad_g_with_boundary_section (I := I) g hh hh_int hh_supp
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have h_ibp :=
    integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
      (I := I) g hf hf_int X hX_cs hX_int
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g X x]
    change g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergence_g_with_boundary (I := I) g X x =
        f x * Δ_g_with_boundary (I := I) g hh hh_int x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

omit [InnerProductSpace ℝ E] in
private theorem integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary'
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M)
    (hf_supp : HasCompactSupport f) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hf hf_int with hX_def
  have hX_cs : HasCompactSupport X :=
    hasCompactSupport_grad_g_with_boundary_section (I := I) g hf hf_int hf_supp
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hf hf_int
  have h_ibp :=
    integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
      (I := I) g hh hh_int X hX_cs hX_int
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X h x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g X x]
    rfl
  have hRHS_eq : ∀ x : M,
      h x * divergence_g_with_boundary (I := I) g X x =
        h x * Δ_g_with_boundary (I := I) g hf hf_int x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X h x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, h x * divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

omit [InnerProductSpace ℝ E] in
theorem integral_smul_laplacian_sub_eq_zero_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) g hh hh_int x -
            h x * Δ_g_with_boundary (I := I) g hf hf_int x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  have hh_cs : HasCompactSupport h := HasCompactSupport.of_compactSpace _
  have h1 := integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary
    (I := I) g hf hh hf_int hh_int hh_cs
  have h2 := integral_inner_grad_eq_neg_integral_smul_laplacian_with_boundary'
    (I := I) g hf hh hf_int hh_int hf_cs
  have h_eq : ∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have : -∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          -∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [← h1, h2]
    linarith
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hΔh_cont : Continuous (Δ_g_with_boundary (I := I) g hh hh_int) :=
    Δ_g_with_boundary_continuous (I := I) g hh hh_int
  have hΔf_cont : Continuous (Δ_g_with_boundary (I := I) g hf hf_int) :=
    Δ_g_with_boundary_continuous (I := I) g hf hf_int
  have hf_cont : Continuous f := hf.continuous
  have hh_cont : Continuous h := hh.continuous
  have h_int_fΔh : Integrable (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x) :=
      hf_cont.mul hΔh_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_hΔf : Integrable (fun x : M => h x * Δ_g_with_boundary (I := I) g hf hf_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => h x * Δ_g_with_boundary (I := I) g hf hf_int x) :=
      hh_cont.mul hΔf_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub h_int_fΔh h_int_hΔf]
  rw [h_eq, sub_self]

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
