import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.Stokes
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Laplacian
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.POUReduction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Green
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.POUReduction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic


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

noncomputable def boundaryFaceSum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    chartBoundaryFaceIntegral (I := I) g α X
      ((chartAtlasPOU I M) α : M → ℝ)

omit [InnerProductSpace ℝ E] in
@[simp] lemma boundaryFaceSum_def
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    boundaryFaceSum (I := I) g X =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        chartBoundaryFaceIntegral (I := I) g α X
          ((chartAtlasPOU I M) α : M → ℝ) := rfl

section StokesGlobal

variable [hI : HasSmoothBoundary E H I]

omit [InnerProductSpace ℝ E] in
theorem integral_divergence_with_boundary_eq_boundaryFaceSum
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g X := by
  rw [boundaryFaceSum_def]
  exact stokes_compact_via_pou (I := I) g X

omit hI in
omit [InnerProductSpace ℝ E] in
private lemma inner_grad_grad_continuous_of_interior_support
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Continuous
      (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)) := by
  classical
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hY_def
  have hY_int : tsupport (Y : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have h_eq : ∀ x : M,
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) =
        tangentSectionAction (I := I) Y f x := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g Y x]
    change g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) =
      g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
    exact g.symm x _ _
  have hY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (Y x)) := Y.contMDiff
  have h_act_cont : Continuous (tangentSectionAction (I := I) Y f) := by
    classical
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx_supp : x ∈ tsupport (Y : ∀ x, TangentSpace I x)
    · have hx_int : x ∈ I.interior M := hY_int hx_supp
      have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
      have hx_target_int : extChartAt I x x ∈ interior (extChartAt I x).target :=
        extChartAt_mem_interior_target_of_isInteriorPoint
          (I := I) (M := M) x hx_chart hx_int
      have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) Y f)
          ((extChartAt I x).source ∩
            (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) :=
        tangentSectionAction_contMDiffOn (I := I) x Y hf
      have hxsrc : x ∈ (extChartAt I x).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_chart
      have hxU : x ∈ (extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target :=
        ⟨hxsrc, hx_target_int⟩
      have hUopen : IsOpen ((extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) := by
        have hcontOn := continuousOn_extChartAt (I := I) x
        exact hcontOn.isOpen_inter_preimage (isOpen_extChartAt_source (I := I) x)
          isOpen_interior
      exact ((hsmooth x hxU).continuousWithinAt.continuousAt) (hUopen.mem_nhds hxU)
    · have h_open : IsOpen (tsupport (Y : ∀ x, TangentSpace I x))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev_zero : tangentSectionAction (I := I) Y f =ᶠ[𝓝 x]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hx_supp] with y hy
        have hY_zero : (Y : ∀ z, TangentSpace I z) y = 0 := by
          by_contra hne
          exact hy (subset_tsupport _ hne)
        change mfderiv I 𝓘(ℝ) f y ((Y : ∀ z, TangentSpace I z) y) = 0
        rw [hY_zero]
        exact (mfderiv I 𝓘(ℝ, ℝ) f y).map_zero
      exact (continuous_const.continuousAt.congr hev_zero.symm)
  refine h_act_cont.congr ?_
  intro x
  exact (h_eq x).symm

omit hI in
omit [InnerProductSpace ℝ E] in
private lemma f_mul_Δ_continuous
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Continuous (fun x : M =>
      f x * Δ_g_with_boundary (I := I) g hh hh_int x) :=
  hf.continuous.mul (Δ_g_with_boundary_continuous (I := I) g hh hh_int)


omit hI in
omit [InnerProductSpace ℝ E] in
private lemma f_mul_Δ_hasCompactSupport
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    HasCompactSupport (fun x : M =>
      f x * Δ_g_with_boundary (I := I) g hh hh_int x) :=
  HasCompactSupport.of_compactSpace _

omit hI in
omit [InnerProductSpace ℝ E] in
private lemma f_mul_Δ_integrable
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (f_mul_Δ_continuous (I := I) g hf hh hh_int).integrable_of_hasCompactSupport
    (f_mul_Δ_hasCompactSupport (I := I) g hf hh hh_int)

omit hI in
omit [InnerProductSpace ℝ E] in
private lemma inner_grad_grad_integrable
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    Integrable
      (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (inner_grad_grad_continuous_of_interior_support
    (I := I) g hf hh hh_int).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [InnerProductSpace ℝ E] in
theorem green_first_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
      ∫ x, f x * Δ_g_with_boundary (I := I) g hh hh_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hX_def
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) f hf X with hY_def
  have hStokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I) g Y
  have h_leibniz : ∀ x : M,
      divergence_g_with_boundary (I := I) g Y x =
        f x * divergence_g_with_boundary (I := I) g X x +
          tangentSectionAction (I := I) X f x :=
    divergence_g_with_boundary_smoothSmul (I := I) g f hf X
  have h1 : ∀ x : M,
      f x * divergence_g_with_boundary (I := I) g X x =
        f x * Δ_g_with_boundary (I := I) g hh hh_int x := by
    intro x; rfl
  have h2 : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I) g X x]
    change g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
    exact g.symm x _ _
  have h_combined : ∀ x : M,
      divergence_g_with_boundary (I := I) g Y x =
        f x * Δ_g_with_boundary (I := I) g hh hh_int x +
          g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x
    rw [h_leibniz x, h1 x, h2 x]
  have h_int_eq :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (f x * Δ_g_with_boundary (I := I) g hh hh_int x +
                g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_combined x
  have h_int_fΔh : Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hf hh hh_int
  have h_int_inner : Integrable
      (fun x : M =>
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    inner_grad_grad_integrable (I := I) g hf hh hh_int
  rw [h_int_eq] at hStokes
  rw [integral_add h_int_fΔh h_int_inner] at hStokes
  linarith


omit [InnerProductSpace ℝ E] in
theorem green_first_with_boundary_face_sum_eq_zero_of_interior_support
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_int : tsupport h ⊆ I.interior M) :
    boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) = 0 := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hh hh_int with hX_def
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) f hf X with hY_def
  have hY_cs : HasCompactSupport Y := HasCompactSupport.of_compactSpace _
  have hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hh hh_int
  have hY_int : tsupport (Y : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_smoothSmul_subset_interior (I := I) hf X hX_int
  have h_div_Y_zero :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
    integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
      (I := I) g Y hY_cs hY_int
  have h_stokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I) g Y
  rw [h_div_Y_zero] at h_stokes
  exact h_stokes.symm

omit [InnerProductSpace ℝ E] in
private theorem green_first_with_boundary_swap
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) :
    ∫ x, g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
      ∫ x, h x * Δ_g_with_boundary (I := I) g hf hf_int x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) h hh
          (grad_g_with_boundary_section (I := I) g hf hf_int)) :=
  green_first_with_boundary (I := I) g hh hf hf_int

omit [InnerProductSpace ℝ E] in
theorem green_second_with_boundary
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M)
    (hh_int : tsupport h ⊆ I.interior M) :
    ∫ x, (f x * Δ_g_with_boundary (I := I) g hh hh_int x -
            h x * Δ_g_with_boundary (I := I) g hf hf_int x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) f hf
          (grad_g_with_boundary_section (I := I) g hh hh_int)) -
      boundaryFaceSum (I := I) g
        (smoothSmul (I := I) h hh
          (grad_g_with_boundary_section (I := I) g hf hf_int)) := by
  classical
  have h_main := green_first_with_boundary (I := I) g hf hh hh_int
  have h_swap := green_first_with_boundary_swap (I := I) g hf hh hf_int
  have h_inner_symm : ∀ x : M,
      g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x) =
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x) := by
    intro x; exact g.symm x _ _
  have h_inner_int_eq :
      ∫ x, g.inner x (gradFun (I := I) g h x) (gradFun (I := I) g f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall h_inner_symm)
  rw [h_inner_int_eq] at h_swap
  have h_int_fΔh : Integrable
      (fun x : M => f x * Δ_g_with_boundary (I := I) g hh hh_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hf hh hh_int
  have h_int_hΔf : Integrable
      (fun x : M => h x * Δ_g_with_boundary (I := I) g hf hf_int x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f_mul_Δ_integrable (I := I) g hh hf hf_int
  rw [integral_sub h_int_fΔh h_int_hΔf]
  linarith [h_main, h_swap]

end StokesGlobal

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
