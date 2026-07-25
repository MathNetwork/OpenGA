import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Intrinsic.Lp
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Intrinsic.Algebra
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Laplacian
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.InteriorCompactSupport
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary
namespace EquivalenceFull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp

private lemma exists_bound_continuous_compactSpace
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, |f x| ≤ C := by
  by_cases hM : Nonempty M
  · have hrange : IsCompact (Set.range f) := isCompact_range hf
    obtain ⟨C₁, hC₁⟩ := hrange.bddAbove
    have hrange_neg : IsCompact (Set.range (-f)) := isCompact_range hf.neg
    obtain ⟨C₂, hC₂⟩ := hrange_neg.bddAbove
    refine ⟨max (max C₁ C₂) 0, le_max_right _ _, ?_⟩
    intro x
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h_neg : -f x ≤ C₂ := hC₂ ⟨x, rfl⟩
      have hC₂_le : C₂ ≤ max (max C₁ C₂) 0 :=
        le_trans (le_max_right C₁ C₂) (le_max_left _ _)
      linarith
    · have h_pos : f x ≤ C₁ := hC₁ ⟨x, rfl⟩
      have hC₁_le : C₁ ≤ max (max C₁ C₂) 0 :=
        le_trans (le_max_left C₁ C₂) (le_max_left _ _)
      linarith
  · refine ⟨0, le_refl _, ?_⟩
    intro x
    exact (hM ⟨x⟩).elim

omit [InnerProductSpace ℝ E] in
private lemma continuous_memLp_of_compactSpace
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {f : M → ℝ} (hf : Continuous f) :
    MemLp f p (riemannianVolumeMeasure I M g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmeas : AEStronglyMeasurable f (riemannianVolumeMeasure I M g) :=
    hf.aestronglyMeasurable
  obtain ⟨C, _hC_nn, hC⟩ := exists_bound_continuous_compactSpace hf
  exact MemLp.of_bound hmeas C (Filter.Eventually.of_forall (fun x => hC x))

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

omit [InnerProductSpace ℝ E] in
private lemma tangentSectionAction_continuous_of_X_interior_support
    [T2Space M]
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M) :
    Continuous (tangentSectionAction (I := I) X u) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_supp : x ∈ tsupport (X : ∀ x, TangentSpace I x)
  · have hx_int : x ∈ I.interior M := hX_int hx_supp
    have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
    have hx_target_int : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_mem_interior_target_of_isInteriorPoint
        (I := I) (M := M) x hx_chart hx_int
    have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X u)
        ((extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) :=
      tangentSectionAction_contMDiffOn (I := I) x X hu
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
  · have h_open : IsOpen (tsupport (X : ∀ x, TangentSpace I x))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have hev_zero : tangentSectionAction (I := I) X u =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_supp] with y hy
      have hX_zero : (X : ∀ z, TangentSpace I z) y = 0 := by
        by_contra hne
        exact hy (subset_tsupport _ hne)
      change mfderiv I 𝓘(ℝ) u y ((X : ∀ z, TangentSpace I z) y) = 0
      rw [hX_zero]
      exact (mfderiv I 𝓘(ℝ, ℝ) u y).map_zero
    exact (continuous_const.continuousAt.congr hev_zero.symm)

omit [InnerProductSpace ℝ E] in
private theorem integral_tangentSectionAction_eq_neg_no_u_interior_support
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (X : ∀ x, TangentSpace I x))
    (hX_int : tsupport (X : ∀ x, TangentSpace I x) ⊆ I.interior M) :
    ∫ x, tangentSectionAction (I := I) X u x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, u x * divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) u hu X with hY_def
  have hY_cs : HasCompactSupport Y :=
    hasCompactSupport_smoothSmul (I := I) hu X hX
  have hY_int : tsupport (Y : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_smoothSmul_subset_interior (I := I) hu X hX_int
  have hY_div : ∀ x : M,
      divergence_g_with_boundary (I := I) g Y x =
        u x * divergence_g_with_boundary (I := I) g X x +
          tangentSectionAction (I := I) X u x :=
    divergence_g_with_boundary_smoothSmul (I := I) g u hu X
  have hu_cont : Continuous u := hu.continuous
  have hX_div_cont : Continuous (divergence_g_with_boundary (I := I) g X) := by
    have hdiv_supp : tsupport (divergence_g_with_boundary (I := I) g X) ⊆ tsupport X :=
      tsupport_divergence_g_with_boundary_subset_of_interior_support
        (I := I) g X hX_int
    have hdiv_supp_int :
        tsupport (divergence_g_with_boundary (I := I) g X) ⊆ I.interior M :=
      hdiv_supp.trans hX_int
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx_supp : x ∈ tsupport (divergence_g_with_boundary (I := I) g X)
    · have hx_int : x ∈ I.interior M := hdiv_supp_int hx_supp
      have hcont_int :
          ContinuousOn (divergence_g_with_boundary (I := I) g X) (I.interior M) :=
        divergence_g_with_boundary_continuousOn_interior (I := I) g X
      exact (hcont_int x hx_int).continuousAt (isOpen_interior_M.mem_nhds hx_int)
    · have h_open : IsOpen (tsupport (divergence_g_with_boundary (I := I) g X))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev_zero : (divergence_g_with_boundary (I := I) g X) =ᶠ[𝓝 x]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hx_supp] with y hy
        by_contra hne
        exact hy (subset_tsupport _ hne)
      exact (continuous_const.continuousAt.congr hev_zero.symm)
  have hAct_cont : Continuous (tangentSectionAction (I := I) X u) :=
    tangentSectionAction_continuous_of_X_interior_support
      (I := I) (M := M) hu X hX_int
  have hX_div_cs : HasCompactSupport (divergence_g_with_boundary (I := I) g X) :=
    hasCompactSupport_divergence_g_with_boundary (I := I) g hX hX_int
  have hAct_cs : HasCompactSupport (tangentSectionAction (I := I) X u) :=
    hasCompactSupport_tangentSectionAction (I := I) hX u
  have hMul_cont : Continuous (fun x : M =>
      u x * divergence_g_with_boundary (I := I) g X x) :=
    hu_cont.mul hX_div_cont
  have hMul_cs : HasCompactSupport (fun x : M =>
      u x * divergence_g_with_boundary (I := I) g X x) :=
    hX_div_cs.mul_left
  have h_div_Y_zero :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
    integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
      (I := I) g Y hY_cs hY_int
  have h_div_Y_split :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (u x * divergence_g_with_boundary (I := I) g X x +
                tangentSectionAction (I := I) X u x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact hY_div x
  have h_int_mul : Integrable (fun x : M =>
      u x * divergence_g_with_boundary (I := I) g X x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    WithBoundary.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hMul_cont hMul_cs
  have h_int_act : Integrable (tangentSectionAction (I := I) X u)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    WithBoundary.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hAct_cont hAct_cs
  have h_int_split :
      ∫ x, (u x * divergence_g_with_boundary (I := I) g X x +
              tangentSectionAction (I := I) X u x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, u x * divergence_g_with_boundary (I := I) g X x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
          ∫ x, tangentSectionAction (I := I) X u x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_add h_int_mul h_int_act
  have h_sum_zero :
      ∫ x, u x * divergence_g_with_boundary (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
        ∫ x, tangentSectionAction (I := I) X u x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    rw [← h_int_split, ← h_div_Y_split]; exact h_div_Y_zero
  linarith [h_sum_zero]

omit [InnerProductSpace ℝ E] in
private lemma memLp_g_norm_gradFun_interior_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_int : tsupport u ⊆ I.interior M) :
    MemLp (fun x : M => Real.sqrt
        (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) p
      (riemannianVolumeMeasure I M g) := by
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hu hu_int with hY_def
  have hY_inner_cont : Continuous (fun x : M => g.inner x (Y x) (Y x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g Y Y
  have hY_eq : ∀ x : M, g.inner x (Y x) (Y x) =
      g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) := by
    intro x
    have h := grad_g_with_boundary_section_apply (I := I) g hu hu_int x
    rw [h]
  have hgrad_inner_cont : Continuous (fun x : M =>
      g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x)) := by
    refine hY_inner_cont.congr ?_
    intro x
    exact hY_eq x
  have hG_cont : Continuous (fun x : M => Real.sqrt
      (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) :=
    Real.continuous_sqrt.comp hgrad_inner_cont
  exact continuous_memLp_of_compactSpace g p hG_cont

omit [InnerProductSpace ℝ E] in
private lemma hasWeakRiemannianGradLp_withBoundary_gradFun_interior
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_int : tsupport u ⊆ I.interior M) :
    HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u
      (fun x : M => (gradFun (I := I) g u x : E)) := by
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g_with_boundary_section (I := I) g hu hu_int with hY_def
  refine ⟨?_, ?_⟩
  · intro Z
    have h_eq : ∀ x : M, g.inner x (gradFun (I := I) g u x) (Z x) =
        g.inner x (Y x) (Z x) := by
      intro x
      have h := grad_g_with_boundary_section_apply (I := I) g hu hu_int x
      rw [h]
    have h_cont : Continuous (fun x : M => g.inner x (Y x) (Z x)) :=
      TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g Y Z
    have h_cont' : Continuous (fun x : M =>
        g.inner x (gradFun (I := I) g u x) (Z x)) := by
      refine h_cont.congr ?_
      intro x
      exact (h_eq x).symm
    exact h_cont'.aestronglyMeasurable
  · intro X hX hX_int
    have h_pt : ∀ x : M, g.inner x (gradFun (I := I) g u x) (X x) =
        tangentSectionAction (I := I) X u x := by
      intro x
      rw [g.symm x (gradFun (I := I) g u x) (X x)]
      rw [inner_gradFun_right (I := I) g u x ((X : ∀ z, TangentSpace I z) x)]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall h_pt)]
    exact integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
      (I := I) g hu hu_int X hX hX_int

theorem MemW1pIntrinsicLp_withBoundary_of_contMDiff_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_int : tsupport u ⊆ I.interior M) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.MemW1pIntrinsicLp_withBoundary
      (I := I) (M := M) g p u := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact
    ⟨continuous_memLp_of_compactSpace g p hu.continuous,
      (fun x : M => (gradFun (I := I) g u x : E)),
      hasWeakRiemannianGradLp_withBoundary_gradFun_interior
        (I := I) (M := M) g hu hu_int,
      memLp_g_norm_gradFun_interior_smooth
        (I := I) (M := M) g p hu hu_int⟩

theorem MemW1pIntrinsicLp_withBoundary_of_MemWkpChart_smooth_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_int : tsupport u ⊆ I.interior M) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.MemW1pIntrinsicLp_withBoundary
      (I := I) (M := M) g p u :=
  MemW1pIntrinsicLp_withBoundary_of_contMDiff_interior
    (I := I) (M := M) g p hu_smooth hu_int

omit [InnerProductSpace ℝ E] in
private lemma partialDerivWithin_scalarOnE_continuousOn_target
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α u))
      (extChartAt I α).target := by
  have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
    uniqueDiffOn_extChartAt_target (I := I) α
  have hbase : ContDiffOn ℝ ∞ (scalarOnE (I := I) α u)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hu
  have hpartial_target : ContDiffOn ℝ ∞
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α u))
      (extChartAt I α).target :=
    partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := j) hbase hUD
  exact hpartial_target.continuousOn

omit [InnerProductSpace ℝ E] in
private lemma partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y : M =>
        partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α u) (extChartAt I α y))
      (chartAt H α).source := by
  have hpartial : ContinuousOn
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α u))
      (extChartAt I α).target :=
    partialDerivWithin_scalarOnE_continuousOn_target (I := I) α hu j
  have hchart : ContinuousOn (extChartAt I α : M → E) (chartAt H α).source := by
    have h1 : ContinuousOn (extChartAt I α : M → E) (extChartAt I α).source :=
      continuousOn_extChartAt (I := I) α
    refine h1.mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hmaps : Set.MapsTo (extChartAt I α : M → E) (chartAt H α).source
      (extChartAt I α).target := by
    intro x hx
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
    exact (extChartAt I α).map_source hxsrc
  exact hpartial.comp hchart hmaps

omit [InnerProductSpace ℝ E] in
private lemma gradChartCoeffWithin_continuousOn_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (gradChartCoeffWithin (I := I) g α u i) (chartAt H α).source := by
  classical
  have heq : ∀ y ∈ (chartAt H α).source,
      gradChartCoeffWithin (I := I) g α u i y =
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α y i j *
            partialDerivWithin (E := E) (extChartAt I α).target j
              (scalarOnE (I := I) α u) (extChartAt I α y) := by
    intro y _; rfl
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => chartInvGramMatrix (I := I) g α y i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    have h2 : ContinuousOn
        (fun y => chartInvGramMatrix (I := I) g α y i j)
        (trivializationAt E (TangentSpace I) α).baseSet := h1.continuousOn
    refine h2.mono ?_
    intro y hy
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hy
  · exact partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
      (I := I) α hu j

omit [InnerProductSpace ℝ E] in
private lemma chartGramMatrix_entry_continuousOn_source
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun y : M => chartGramMatrix (I := I) g α y i j)
      (chartAt H α).source := by
  have h := chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hcont : ContinuousOn (fun y : M => chartGramMatrix (I := I) g α y i j)
      (trivializationAt E (TangentSpace I) α).baseSet := h.continuousOn
  refine hcont.mono ?_
  intro y hy
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hy

omit [InnerProductSpace ℝ E] in
private lemma g_inner_gradFun_gradFun_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContinuousOn
      (fun y : M => g.inner y (gradFun (I := I) g u y) (gradFun (I := I) g u y))
      (chartAt H α).source := by
  classical
  have h_rewrite : ∀ y ∈ (chartAt H α).source,
      g.inner y (gradFun (I := I) g u y) (gradFun (I := I) g u y) =
        g.inner y (gradChartLocalWithin (I := I) g α u y)
          (gradChartLocalWithin (I := I) g α u y) := by
    intro y hy
    rw [(gradChartLocalWithin_eq_gradFun (I := I) g α hu hy)]
  refine ContinuousOn.congr ?_ (fun y hy => h_rewrite y hy)
  have h_expand : ∀ y ∈ (chartAt H α).source,
      g.inner y (gradChartLocalWithin (I := I) g α u y)
          (gradChartLocalWithin (I := I) g α u y) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α u i y *
              gradChartCoeffWithin (I := I) g α u j y *
                chartGramMatrix (I := I) g α y i j := by
    intro y _hy
    unfold gradChartLocalWithin
    rw [show (g.inner y (∑ i : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α u i y •
                chartBasisVecFiber (I := I) α i y)
            (∑ j : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α u j y •
                chartBasisVecFiber (I := I) α j y))
        = ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α u i y *
                gradChartCoeffWithin (I := I) g α u j y *
                  g.inner y (chartBasisVecFiber (I := I) α i y)
                    (chartBasisVecFiber (I := I) α j y) from ?_]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rfl
    · rw [show (g.inner y (∑ i : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α u i y •
              chartBasisVecFiber (I := I) α i y))
          = ∑ i : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α u i y •
                g.inner y (chartBasisVecFiber (I := I) α i y) from ?_]
      · rw [ContinuousLinearMap.sum_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [show (g.inner y (chartBasisVecFiber (I := I) α i y))
              (∑ j : Fin (Module.finrank ℝ E),
                gradChartCoeffWithin (I := I) g α u j y •
                  chartBasisVecFiber (I := I) α j y) =
            ∑ j : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α u j y *
                g.inner y (chartBasisVecFiber (I := I) α i y)
                  (chartBasisVecFiber (I := I) α j y) from ?_]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
        · rw [map_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [map_smul]
          rfl
      · rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul]
  refine ContinuousOn.congr ?_ (fun y hy => h_expand y hy)
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact gradChartCoeffWithin_continuousOn_source (I := I) g α hu i
  · exact gradChartCoeffWithin_continuousOn_source (I := I) g α hu j
  · exact chartGramMatrix_entry_continuousOn_source (I := I) g α i j

omit [InnerProductSpace ℝ E] in
private lemma g_inner_gradFun_gradFun_continuous
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    Continuous (fun x : M =>
      g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
  have hcontOn :=
    g_inner_gradFun_gradFun_continuousOn_chart_source (I := I) g x hu
  exact (hcontOn x hx_chart).continuousAt (hopen.mem_nhds hx_chart)

omit [InnerProductSpace ℝ E] in
private lemma memLp_g_norm_gradFun_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemLp (fun x : M => Real.sqrt
        (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) p
      (riemannianVolumeMeasure I M g) := by
  have hcont := g_inner_gradFun_gradFun_continuous (I := I) (M := M) g hu
  exact continuous_memLp_of_compactSpace g p (Real.continuous_sqrt.comp hcont)

omit [InnerProductSpace ℝ E] in
private lemma tangentSectionAction_chartLocal_within
    (α : M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    tangentSectionAction (I := I) Y u x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α Y i x *
          partialDerivWithin (E := E) (extChartAt I α).target i
            (scalarOnE (I := I) α u) (extChartAt I α x) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hY_decomp : (Y : ∀ z, TangentSpace I z) x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α Y i x •
          chartBasisVecFiber (I := I) α i x :=
    chartCoeff_recompose (I := I) α Y hbase
  change mfderiv I 𝓘(ℝ) u x ((Y : ∀ z, TangentSpace I z) x) = _
  rw [hY_decomp, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show mfderiv I 𝓘(ℝ) u x (chartCoeff (I := I) α Y i x •
        chartBasisVecFiber (I := I) α i x) =
      chartCoeff (I := I) α Y i x •
        mfderiv I 𝓘(ℝ) u x (chartBasisVecFiber (I := I) α i x) from
    ContinuousLinearMap.map_smul (mfderiv I 𝓘(ℝ) u x)
      (chartCoeff (I := I) α Y i x) (chartBasisVecFiber (I := I) α i x)]
  rw [mfderiv_chartBasisVecFiber_within_of_smooth (I := I) α hu hx i]
  rfl

omit [InnerProductSpace ℝ E] in
private lemma chartCoeff_continuousOn_source
    (α : M) (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (chartCoeff (I := I) α Y i) (chartAt H α).source := by
  have h := chartCoeff_contMDiffOn (I := I) α Y i
  have hcont : ContinuousOn (chartCoeff (I := I) α Y i)
      (trivializationAt E (TangentSpace I) α).baseSet := h.continuousOn
  refine hcont.mono ?_
  intro y hy
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact hy

omit [InnerProductSpace ℝ E] in
private lemma tangentSectionAction_continuousOn_chart_source
    (α : M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContinuousOn (tangentSectionAction (I := I) Y u) (chartAt H α).source := by
  classical
  have h_eq : ∀ y ∈ (chartAt H α).source,
      tangentSectionAction (I := I) Y u y =
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α Y i y *
            partialDerivWithin (E := E) (extChartAt I α).target i
              (scalarOnE (I := I) α u) (extChartAt I α y) :=
    fun y hy => tangentSectionAction_chartLocal_within (I := I) α Y hu hy
  refine ContinuousOn.congr ?_ (fun y hy => h_eq y hy)
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · exact chartCoeff_continuousOn_source (I := I) α Y i
  · exact partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
      (I := I) α hu i

omit [InnerProductSpace ℝ E] in
private lemma tangentSectionAction_continuous
    [T2Space M]
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    Continuous (tangentSectionAction (I := I) Y u) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
  have hcontOn := tangentSectionAction_continuousOn_chart_source (I := I) x Y hu
  exact (hcontOn x hx_chart).continuousAt (hopen.mem_nhds hx_chart)

omit [InnerProductSpace ℝ E] in
private lemma continuous_g_inner_gradFun_section
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun x : M => g.inner x (gradFun (I := I) g u x) (Y x)) := by
  have h_eq : ∀ x : M, g.inner x (gradFun (I := I) g u x) (Y x) =
      tangentSectionAction (I := I) Y u x := by
    intro x
    rw [g.symm x (gradFun (I := I) g u x) ((Y : ∀ z, TangentSpace I z) x)]
    rw [inner_gradFun_right (I := I) g u x ((Y : ∀ z, TangentSpace I z) x)]
    rfl
  exact (tangentSectionAction_continuous (I := I) (M := M) Y hu).congr
    (fun x => (h_eq x).symm)

omit [InnerProductSpace ℝ E] in
private lemma hasWeakRiemannianGradLp_withBoundary_gradFun_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    HasWeakRiemannianGradLp_withBoundary (I := I) (M := M) g u
      (fun x : M => (gradFun (I := I) g u x : E)) := by
  refine ⟨?_, ?_⟩
  · intro Z
    have h := continuous_g_inner_gradFun_section (I := I) (M := M) g hu Z
    exact h.aestronglyMeasurable
  · intro X hX hX_int
    have h_pt : ∀ x : M, g.inner x (gradFun (I := I) g u x) (X x) =
        tangentSectionAction (I := I) X u x := by
      intro x
      rw [g.symm x (gradFun (I := I) g u x) ((X : ∀ z, TangentSpace I z) x)]
      rw [inner_gradFun_right (I := I) g u x ((X : ∀ z, TangentSpace I z) x)]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall h_pt)]
    exact integral_tangentSectionAction_eq_neg_no_u_interior_support
      (I := I) g hu X hX hX_int

theorem MemW1pIntrinsicLp_withBoundary_of_contMDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.MemW1pIntrinsicLp_withBoundary
      (I := I) (M := M) g p u := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact
    ⟨continuous_memLp_of_compactSpace g p hu.continuous,
      (fun x : M => (gradFun (I := I) g u x : E)),
      hasWeakRiemannianGradLp_withBoundary_gradFun_smooth
        (I := I) (M := M) g hu,
      memLp_g_norm_gradFun_smooth (I := I) (M := M) g p hu⟩

theorem MemW1pIntrinsicLp_withBoundary_of_MemWkpChart_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.MemW1pIntrinsicLp_withBoundary
      (I := I) (M := M) g p u :=
  MemW1pIntrinsicLp_withBoundary_of_contMDiff
    (I := I) (M := M) g p hu_smooth

theorem w1pNormIntrinsicLp_withBoundary_lt_top_of_contMDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
      (I := I) (M := M) g p u < ⊤ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hmem :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.MemW1pIntrinsicLp_withBoundary
      (I := I) (M := M) g p u :=
    MemW1pIntrinsicLp_withBoundary_of_contMDiff (I := I) (M := M) g p hu
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hmem
  unfold DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
  rw [ENNReal.add_lt_top]
  refine ⟨hu_p.2, ?_⟩
  refine lt_of_le_of_lt (iInf_le_of_le G (iInf_le _ hG_weak)) ?_
  exact hG_p.2

theorem w1pNormIntrinsicLp_withBoundary_lt_top_of_contMDiff_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_int : tsupport u ⊆ I.interior M) :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
      (I := I) (M := M) g p u < ⊤ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hmem :
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.MemW1pIntrinsicLp_withBoundary
      (I := I) (M := M) g p u :=
    MemW1pIntrinsicLp_withBoundary_of_contMDiff_interior
      (I := I) (M := M) g p hu hu_int
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hmem
  unfold DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
  rw [ENNReal.add_lt_top]
  refine ⟨hu_p.2, ?_⟩
  refine lt_of_le_of_lt (iInf_le_of_le G (iInf_le _ hG_weak)) ?_
  exact hG_p.2

omit [InnerProductSpace ℝ E] in
private lemma smooth_u_eq_zero_of_w1pNormIntrinsicLp_withBoundary_zero
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (h_zero : DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
      (I := I) (M := M) g p u = 0) :
    u = (fun _ => (0 : ℝ)) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_eLp_u_zero : eLpNorm u p (riemannianVolumeMeasure I M g) = 0 := by
    have h_le_sum :
        eLpNorm u p (riemannianVolumeMeasure I M g) ≤
        DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
          (I := I) (M := M) g p u := by
      unfold DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
      exact le_self_add
    rw [h_zero] at h_le_sum
    exact le_antisymm h_le_sum (zero_le _)
  have h_aestronglyMeasurable : AEStronglyMeasurable u
      (riemannianVolumeMeasure I M g) :=
    hu_smooth.continuous.aestronglyMeasurable
  have h_p_ne_zero : p ≠ 0 := by
    intro h
    rw [h] at hp_one
    exact absurd hp_one (by norm_num)
  have h_u_aeEq_zero :
      u =ᵐ[riemannianVolumeMeasure I M g] 0 :=
    (eLpNorm_eq_zero_iff h_aestronglyMeasurable h_p_ne_zero).mp h_eLp_u_zero
  have hu_cont : Continuous u := hu_smooth.continuous
  have h_zero_cont : Continuous (fun _ : M => (0 : ℝ)) := continuous_const
  have h_pos : (riemannianVolumeMeasure I M g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have h_u_aeEq_const :
      u =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : ℝ)) := h_u_aeEq_zero
  exact (hu_cont.ae_eq_iff_eq (riemannianVolumeMeasure I M g) h_zero_cont).mp
    h_u_aeEq_const

theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_withBoundary_smooth_finite
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {p : ℝ≥0∞} (_hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth :
      ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ u)
    (h_chart_lt_top :
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
        (n := n) (M := M) g 1 p u < ⊤)
    (h_intr_pos :
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
          (n := n) (M := M) g 1 p u ≤
        ENNReal.ofReal C *
          DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
            (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u := by
  classical
  have h_intr_lt_top :
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u < ⊤ :=
    w1pNormIntrinsicLp_withBoundary_lt_top_of_contMDiff
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p hu_smooth
  have h_chart_ne_top :
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
        (n := n) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
  have h_intr_ne_top :
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u ≠ ⊤ :=
    h_intr_lt_top.ne
  set a : ℝ :=
    (DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
      (n := n) (M := M) g 1 p u).toReal with ha_def
  set b : ℝ :=
    (DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u).toReal with hb_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  have hb_pos : 0 < b := by
    rw [hb_def]
    exact ENNReal.toReal_pos h_intr_pos h_intr_ne_top
  set C : ℝ := a / b + 1 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact add_nonneg (div_nonneg ha_nn (le_of_lt hb_pos)) (le_of_lt one_pos)
  refine ⟨C, hC_nn, ?_⟩
  rw [show DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
      (n := n) (M := M) g 1 p u = ENNReal.ofReal a from
    (ENNReal.ofReal_toReal h_chart_ne_top).symm]
  rw [show DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u = ENNReal.ofReal b from
    (ENNReal.ofReal_toReal h_intr_ne_top).symm]
  rw [← ENNReal.ofReal_mul hC_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hC_def]
  have h_eq : (a / b + 1) * b = a + b := by field_simp
  rw [h_eq]
  linarith

theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_withBoundary_smooth
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ {u : M → ℝ}, ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ u →
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.AllChartsInteriorSupport
        (n := n) (M := M) u →
      ∃ C : ℝ, 0 ≤ C ∧
        DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
            (n := n) (M := M) g 1 p u ≤
          ENNReal.ofReal C *
            DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u := by
  intro u hu_smooth h_int
  classical
  have h_mem_chart :
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart
        (n := n) (M := M) g 1 p u :=
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.MemWkpChart_of_contMDiff_AllChartsInteriorSupport
      (n := n) (M := M) g hp_one hu_smooth h_int
  have h_chart_lt_top :
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
        (n := n) (M := M) g 1 p u < ⊤ :=
    DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_lt_top_of_memWkpChart
      (n := n) (M := M) g hp_one h_mem_chart
  by_cases h_intr_zero :
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u = 0
  · refine ⟨0, le_refl _, ?_⟩
    have h_u_zero : u = (fun _ : M => (0 : ℝ)) :=
      smooth_u_eq_zero_of_w1pNormIntrinsicLp_withBoundary_zero
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g hp_one
        hu_smooth h_intr_zero
    rw [h_u_zero]
    rw [DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_zero_fun
      (n := n) (M := M) g hp_one]
    simp
  · obtain ⟨C, hC_nn, hC_bound⟩ :=
      wkpNormChart_le_const_mul_w1pNormIntrinsicLp_withBoundary_smooth_finite
        (n := n) (M := M) g hp_one hp_top hu_smooth h_chart_lt_top h_intr_zero
    exact ⟨C, hC_nn, hC_bound⟩

theorem wkpNormChart_le_const_mul_w1pNormIntrinsicLp_withBoundary_smooth_uniform_full
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ {u : M → ℝ}, ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ u →
      DifferentialGeometry.Analysis.Sobolev.WithBoundary.AllChartsInteriorSupport
        (n := n) (M := M) u →
      ∃ C : ℝ, 0 ≤ C ∧
        DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart
            (n := n) (M := M) g 1 p u ≤
          ENNReal.ofReal C *
            DifferentialGeometry.Analysis.Sobolev.WithBoundary.IntrinsicLp.w1pNormIntrinsicLp_withBoundary
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g p u :=
  wkpNormChart_le_const_mul_w1pNormIntrinsicLp_withBoundary_smooth
    (n := n) (M := M) g hp_one hp_top

end EquivalenceFull
end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry

end
