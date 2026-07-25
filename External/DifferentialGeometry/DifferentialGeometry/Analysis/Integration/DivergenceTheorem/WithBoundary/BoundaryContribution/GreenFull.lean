import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.GreenWithBoundary
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.GradientGlobalSection
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.SurfaceIntegralIdentification
import DifferentialGeometry.Geometry.Boundary.OutwardNormal
import DifferentialGeometry.Geometry.Boundary.SurfaceMeasure
import DifferentialGeometry.Geometry.Boundary.EuclideanHalfSpaceInstance
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.POUReduction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.Stokes
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Analysis.Integration.Measure.Family
import Mathlib.MeasureTheory.Integral.Bochner.Basic


noncomputable section

open Bundle Manifold Set MeasureTheory Function
open scoped Manifold Topology ContDiff Matrix ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

open DifferentialGeometry.Integral.Measure

private local instance instMeasurableSpaceM
    {M : Type*} [TopologicalSpace M] : MeasurableSpace M := borel M

private local instance instBorelSpaceM
    {M : Type*} [TopologicalSpace M] :
    @BorelSpace M _ (borel M) := letI : MeasurableSpace M := borel M; ⟨rfl⟩

section ClassicalLaplacian

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

noncomputable def Δ_g_classical
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {h : M → ℝ} (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    M → ℝ :=
  divergence_g_with_boundary
    (I := modelWithCornersEuclideanHalfSpace n) g
    (grad_g_full_section (M := M) (n := n) g hh)

@[simp] lemma Δ_g_classical_def
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {h : M → ℝ} (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h)
    (x : M) :
    Δ_g_classical (M := M) (n := n) g hh x =
      divergence_g_with_boundary
        (I := modelWithCornersEuclideanHalfSpace n) g
        (grad_g_full_section (M := M) (n := n) g hh) x := rfl

end ClassicalLaplacian

section IntegrabilityHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance instMeasurableSpaceE : MeasurableSpace E := borel E
private local instance instBorelSpaceE : @BorelSpace E _ (borel E) := ⟨rfl⟩

omit [InnerProductSpace ℝ E] in
private lemma integrable_divergence_g_with_boundary
    [hI : HasSmoothBoundary E H I]
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Integrable (divergence_g_with_boundary (I := I) g X)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set ρ : SmoothPartitionOfUnity M I M (univ : Set M) := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hρsub : ρ.IsSubordinate (fun α : M => (chartAt H α).source) :=
    chartAtlasPOU_isSubordinate I M
  have hsupp_each : ∀ α : M, tsupport ((ρ α : M → ℝ)) ⊆ (chartAt H α).source := by
    intro α; exact hρsub α
  have hsummand_cont : ∀ α : M,
      Continuous (fun x : M => localDivergenceWithin (I := I) g α X x *
        (ρ α : M → ℝ) x) := by
    intro α
    have hα_cont_on_source : ContinuousOn (localDivergenceWithin (I := I) g α X)
        (chartAt H α).source :=
      localDivergenceWithin_continuousOn (I := I) g α X
    have hρα_cont : Continuous ((ρ α : M → ℝ)) := (ρ α).contMDiff.continuous
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ (chartAt H α).source
    · have h_locDiv_at : ContinuousAt (localDivergenceWithin (I := I) g α X) x :=
        (hα_cont_on_source x hx).continuousAt
          ((chartAt H α).open_source.mem_nhds hx)
      exact h_locDiv_at.mul hρα_cont.continuousAt
    · have hx_nots : x ∉ tsupport ((ρ α : M → ℝ)) :=
        fun h => hx (hsupp_each α h)
      have h_open : IsOpen (tsupport ((ρ α : M → ℝ)))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev : (fun y : M => localDivergenceWithin (I := I) g α X y *
            (ρ α : M → ℝ) y) =ᶠ[nhds x] (fun _ : M => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hx_nots] with y hy
        have hρy : (ρ α : M → ℝ) y = 0 := by
          by_contra hne
          exact hy (subset_tsupport _ hne)
        change localDivergenceWithin (I := I) g α X y * (ρ α : M → ℝ) y = 0
        rw [hρy, mul_zero]
      exact (continuousAt_const (y := (0 : ℝ))).congr hev.symm
  have hsumm_supp : ∀ α : M,
      tsupport (fun x : M => localDivergenceWithin (I := I) g α X x *
        (ρ α : M → ℝ) x) ⊆ (chartAt H α).source := by
    intro α
    have htss : tsupport (fun x : M => localDivergenceWithin (I := I) g α X x *
          (ρ α : M → ℝ) x) ⊆ tsupport (ρ α : M → ℝ) := by
      apply closure_mono
      intro x hx
      rw [Function.mem_support] at hx
      have hρne : (ρ α : M → ℝ) x ≠ 0 := by
        intro h
        apply hx
        rw [h, mul_zero]
      exact hρne
    exact htss.trans (hsupp_each α)
  have hloc_int : ∀ α : M,
      Integrable
        (fun x : M => localDivergenceWithin (I := I) g α X x *
          (ρ α : M → ℝ) x) (chartLocalMeasure (I := I) g α) := by
    intro α
    have hsupp_compact : IsCompact (tsupport (fun x : M =>
        localDivergenceWithin (I := I) g α X x * (ρ α : M → ℝ) x)) :=
      .of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)
    have hμ_supp : chartLocalMeasure (I := I) g α
        (tsupport (fun x : M =>
          localDivergenceWithin (I := I) g α X x * (ρ α : M → ℝ) x)) < ⊤ :=
      chartLocalMeasure_compact_lt_top (I := I) g α hsupp_compact (hsumm_supp α)
    obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖localDivergenceWithin (I := I) g α X x *
          (ρ α : M → ℝ) x‖ ≤ C := by
      have hCpt := (isCompact_univ (X := M)).image (hsummand_cont α).norm
      obtain ⟨C, hCmem⟩ := hCpt.bddAbove
      exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
    have hbnd : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
        ENNReal.ofReal ‖localDivergenceWithin (I := I) g α X x *
            (ρ α : M → ℝ) x‖ ≤
          ENNReal.ofReal C *
            (tsupport (fun y : M => localDivergenceWithin (I := I) g α X y *
              (ρ α : M → ℝ) y)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ tsupport (fun y : M =>
          localDivergenceWithin (I := I) g α X y * (ρ α : M → ℝ) y)
      · rw [Set.indicator_of_mem hx, mul_one]
        exact ENNReal.ofReal_le_ofReal (hC x)
      · rw [Set.indicator_of_notMem hx, mul_zero]
        have hf_zero : localDivergenceWithin (I := I) g α X x *
            (ρ α : M → ℝ) x = 0 := by
          by_contra hne
          exact hx (subset_tsupport _ hne)
        rw [hf_zero]; simp
    refine ⟨(hsummand_cont α).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc ∫⁻ x, ENNReal.ofReal ‖localDivergenceWithin (I := I) g α X x *
              (ρ α : M → ℝ) x‖ ∂(chartLocalMeasure (I := I) g α)
        ≤ ∫⁻ x, ENNReal.ofReal C *
              (tsupport (fun y : M => localDivergenceWithin (I := I) g α X y *
                (ρ α : M → ℝ) y)).indicator (fun _ => (1 : ℝ≥0∞)) x
              ∂(chartLocalMeasure (I := I) g α) :=
          MeasureTheory.lintegral_mono_ae hbnd
      _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α
            (tsupport (fun y : M => localDivergenceWithin (I := I) g α X y *
              (ρ α : M → ℝ) y)) := by
            rw [MeasureTheory.lintegral_const_mul _ ((measurable_const).indicator
              (isClosed_tsupport _).measurableSet)]
            rw [MeasureTheory.lintegral_indicator (isClosed_tsupport _).measurableSet]
            simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_supp
  have hae_eq : ∀ α : M,
      (fun x : M => divergence_g_with_boundary (I := I) g X x * (ρ α : M → ℝ) x)
        =ᵐ[chartLocalMeasure (I := I) g α]
      (fun x : M => localDivergenceWithin (I := I) g α X x * (ρ α : M → ℝ) x) := by
    intro α
    have h_open : IsOpen (tsupport (ρ α : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    set bad : Set M := (chartAt H α).source ∩ I.boundary M with hbad_def
    have h_bad_measzero :
        chartLocalMeasure (I := I) g α bad = 0 :=
      chartLocalMeasure_chart_boundary_zero (I := I) g α
    refine MeasureTheory.ae_iff.mpr ?_
    apply MeasureTheory.measure_mono_null _ h_bad_measzero
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_cases hx_chart : x ∈ (chartAt H α).source
    · by_cases hx_int : x ∈ I.interior M
      · exfalso; apply hx
        have hd_eq : divergence_g_with_boundary (I := I) g X x =
            localDivergenceWithin (I := I) g α X x :=
          voss_weyl_divergence_with_boundary_formula (I := I) g α X hx_chart hx_int
        rw [hd_eq]
      · refine ⟨hx_chart, ?_⟩
        rw [← I.compl_interior]
        exact hx_int
    · exfalso; apply hx
      have hx_nots : x ∉ tsupport (ρ α : M → ℝ) :=
        fun h => hx_chart (hsupp_each α h)
      have hρ_zero : (ρ α : M → ℝ) x = 0 := by
        by_contra hne
        exact hx_nots (subset_tsupport _ hne)
      rw [hρ_zero, mul_zero, mul_zero]
  have hglob_int : ∀ α : M,
      Integrable
        (fun x : M => divergence_g_with_boundary (I := I) g X x *
          (ρ α : M → ℝ) x) (chartLocalMeasure (I := I) g α) :=
    fun α => (hloc_int α).congr (hae_eq α).symm
  have hVol_eq :=
    riemannianVolumeMeasure_eq_finset_sum (I := I) (M := M) g
  rw [hVol_eq]
  rw [integrable_finset_sum_measure]
  intro α _hα
  have hρα_meas : Measurable (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y)) :=
    ENNReal.measurable_ofReal.comp (ρ α).contMDiff.continuous.measurable
  have hρα_aemeas : AEMeasurable (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y))
      (chartLocalMeasure (I := I) g α) := hρα_meas.aemeasurable
  have hρα_lt_top : ∀ᵐ y ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ((ρ α : M → ℝ) y) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hρα_nonneg : ∀ x : M, 0 ≤ (ρ α : M → ℝ) x :=
    fun x => ρ.nonneg α x
  have hsmul_eq : (fun x : M => (ENNReal.ofReal ((ρ α : M → ℝ) x)).toReal •
              divergence_g_with_boundary (I := I) g X x)
        = fun x : M => divergence_g_with_boundary (I := I) g X x *
            (ρ α : M → ℝ) x := by
    funext x
    rw [ENNReal.toReal_ofReal (hρα_nonneg x), smul_eq_mul, mul_comm]
  refine (integrable_withDensity_iff_integrable_smul₀'
    hρα_aemeas hρα_lt_top
    (g := fun x : M => divergence_g_with_boundary (I := I) g X x)).mpr ?_
  rw [hsmul_eq]
  exact hglob_int α

end IntegrabilityHelpers

section GreenFull

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem green_first_eq_boundary_surface_integral
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h)
    (h_chart_iden : ∀ α ∈ chartAtlasPOU_finset
        (I := modelWithCornersEuclideanHalfSpace n) (M := M),
      chartFaceIntegralEqualsSurfaceIntegralOnChart (n := n) (M := M)
        g α (smoothSmul (I := modelWithCornersEuclideanHalfSpace n) f hf
              (grad_g_full_section (M := M) (n := n) g hh))
        ((chartAtlasPOU (modelWithCornersEuclideanHalfSpace n) M) α : M → ℝ))
    (h_int : Integrable
      (fun b : BoundaryManifold (modelWithCornersEuclideanHalfSpace n) M =>
        g.inner b.val
          (outwardNormal
              (I := modelWithCornersEuclideanHalfSpace n) (M := M) g b :
            TangentSpace _ b.val)
          ((smoothSmul (I := modelWithCornersEuclideanHalfSpace n) f hf
              (grad_g_full_section (M := M) (n := n) g hh)) b.val))
      (surfaceMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g)) :
    ∫ x, g.inner x
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)
        ∂(riemannianVolumeMeasure
          (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) +
      ∫ x, f x * Δ_g_classical (M := M) (n := n) g hh x
        ∂(riemannianVolumeMeasure
          (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) =
      ∫ x : (modelWithCornersEuclideanHalfSpace n).boundary M,
        f x.val *
          g.inner x.val
            (outwardNormal
                (I := modelWithCornersEuclideanHalfSpace n) (M := M) g x :
              TangentSpace _ x.val)
            (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x.val)
        ∂(surfaceMeasure
          (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  classical
  set I' : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
    modelWithCornersEuclideanHalfSpace n with hI'_def
  set X : Cₛ^∞⟮I'; EuclideanSpace ℝ (Fin n),
      (TangentSpace I' : M → Type _)⟯ :=
    grad_g_full_section (M := M) (n := n) g hh with hX_def
  set Y : Cₛ^∞⟮I'; EuclideanSpace ℝ (Fin n),
      (TangentSpace I' : M → Type _)⟯ :=
    smoothSmul (I := I') f hf X with hY_def
  have hStokes :=
    integral_divergence_with_boundary_eq_boundaryFaceSum (I := I') g Y
  have h_leibniz : ∀ x : M,
      divergence_g_with_boundary (I := I') g Y x =
        f x * divergence_g_with_boundary (I := I') g X x +
          tangentSectionAction (I := I') X f x :=
    divergence_g_with_boundary_smoothSmul (I := I') g f hf X
  have h1 : ∀ x : M,
      f x * divergence_g_with_boundary (I := I') g X x =
        f x * Δ_g_classical (M := M) (n := n) g hh x := by
    intro x; rfl
  have h2 : ∀ x : M,
      tangentSectionAction (I := I') X f x =
        g.inner x
          (gradFun (I := I') g f x)
          (gradFun (I := I') g h x) := by
    intro x
    rw [tangentSectionAction_grad_g_with_boundary_eq_inner (I := I') g X x]
    change g.inner x
        (gradFun (I := I') g h x)
        (gradFun (I := I') g f x) =
      g.inner x
        (gradFun (I := I') g f x)
        (gradFun (I := I') g h x)
    exact g.symm x _ _
  have h_combined : ∀ x : M,
      divergence_g_with_boundary (I := I') g Y x =
        f x * Δ_g_classical (M := M) (n := n) g hh x +
          g.inner x
            (gradFun (I := I') g f x)
            (gradFun (I := I') g h x) := by
    intro x
    rw [h_leibniz x, h1 x, h2 x]
  have h_int_eq :
      ∫ x, divergence_g_with_boundary (I := I') g Y x
          ∂(riemannianVolumeMeasure (I := I') (M := M) g) =
        ∫ x, (f x * Δ_g_classical (M := M) (n := n) g hh x +
                g.inner x
                  (gradFun (I := I') g f x)
                  (gradFun (I := I') g h x))
          ∂(riemannianVolumeMeasure (I := I') (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_combined x
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I') (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I') (M := M) g
  haveI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  have hgrad_f_smooth : ContMDiff I' (I'.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x : M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x
        (gradFun (I := I') g f x)) :=
    grad_g_smooth_section_full (M := M) (n := n) g hf
  set X_f : Cₛ^∞⟮I'; EuclideanSpace ℝ (Fin n),
      (TangentSpace I' : M → Type _)⟯ :=
    grad_g_full_section (M := M) (n := n) g hf with hX_f_def
  have h_inner_cont : Continuous (fun x : M =>
      g.inner x (X_f x) (X x)) :=
    (contMDiff_g_inner_of_smooth_sections (I := I') g X_f X).continuous
  have h_inner_cont' : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I') g f x)
        (gradFun (I := I') g h x)) := by
    refine h_inner_cont.congr ?_
    intro x
    rfl
  have h_inner_int : Integrable (fun x : M =>
      g.inner x
        (gradFun (I := I') g f x)
        (gradFun (I := I') g h x))
      (riemannianVolumeMeasure (I := I') (M := M) g) := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖g.inner x
        (gradFun (I := I') g f x)
        (gradFun (I := I') g h x)‖ ≤ C := by
      have hCpt := (isCompact_univ (X := M)).image h_inner_cont'.norm
      obtain ⟨C, hCmem⟩ := hCpt.bddAbove
      exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
    exact (integrable_const C).mono' h_inner_cont'.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have h_div_Y_int : Integrable (divergence_g_with_boundary (I := I') g Y)
      (riemannianVolumeMeasure (I := I') (M := M) g) :=
    integrable_divergence_g_with_boundary (I := I') g Y
  have h_div_Y_ae : (fun x : M => divergence_g_with_boundary (I := I') g Y x)
      =ᵐ[riemannianVolumeMeasure (I := I') (M := M) g]
      (fun x : M => f x * Δ_g_classical (M := M) (n := n) g hh x +
        g.inner x
          (gradFun (I := I') g f x)
          (gradFun (I := I') g h x)) :=
    Filter.Eventually.of_forall h_combined
  have h_sum_int : Integrable (fun x : M =>
      f x * Δ_g_classical (M := M) (n := n) g hh x +
        g.inner x
          (gradFun (I := I') g f x)
          (gradFun (I := I') g h x))
      (riemannianVolumeMeasure (I := I') (M := M) g) :=
    h_div_Y_int.congr h_div_Y_ae
  have h_fΔ_int : Integrable (fun x : M =>
      f x * Δ_g_classical (M := M) (n := n) g hh x)
      (riemannianVolumeMeasure (I := I') (M := M) g) := by
    have h_eq : (fun x : M => f x * Δ_g_classical (M := M) (n := n) g hh x) =
        (fun x : M => (f x * Δ_g_classical (M := M) (n := n) g hh x +
            g.inner x
              (gradFun (I := I') g f x)
              (gradFun (I := I') g h x)) -
          g.inner x
            (gradFun (I := I') g f x)
            (gradFun (I := I') g h x)) := by
      funext x; ring
    rw [h_eq]
    exact h_sum_int.sub h_inner_int
  rw [h_int_eq] at hStokes
  rw [integral_add h_fΔ_int h_inner_int] at hStokes
  have h_BFS_eq :
      boundaryFaceSum (I := I') g Y =
        ∫ x : I'.boundary M,
          g.inner x.val
            (outwardNormal (I := I') (M := M) g x :
              TangentSpace _ x.val)
            (Y x.val)
          ∂(surfaceMeasure (I := I') (M := M) g) :=
    boundaryFaceSum_eq_surface_integral_of_chartIdentification
      (n := n) (M := M) g Y h_chart_iden h_int
  rw [h_BFS_eq] at hStokes
  have h_Y_inner : ∀ b : I'.boundary M,
      g.inner b.val
        (outwardNormal (I := I') (M := M) g b :
          TangentSpace _ b.val)
        (Y b.val) =
      f b.val *
        g.inner b.val
          (outwardNormal (I := I') (M := M) g b :
            TangentSpace _ b.val)
          (gradFun (I := I') g h b.val) := by
    intro b
    have hY_b : (Y : ∀ x : M, TangentSpace I' x) b.val =
        f b.val • gradFun (I := I') g h b.val := by
      change f b.val • (X : ∀ x : M, TangentSpace I' x) b.val =
        f b.val • gradFun (I := I') g h b.val
      rfl
    rw [hY_b]
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  have h_surf_eq :
      ∫ x : I'.boundary M,
          g.inner x.val
            (outwardNormal (I := I') (M := M) g x :
              TangentSpace _ x.val)
            (Y x.val)
          ∂(surfaceMeasure (I := I') (M := M) g) =
        ∫ x : I'.boundary M,
          f x.val *
            g.inner x.val
              (outwardNormal (I := I') (M := M) g x :
                TangentSpace _ x.val)
              (gradFun (I := I') g h x.val)
          ∂(surfaceMeasure (I := I') (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall h_Y_inner)
  rw [h_surf_eq] at hStokes
  linarith

end GreenFull

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
