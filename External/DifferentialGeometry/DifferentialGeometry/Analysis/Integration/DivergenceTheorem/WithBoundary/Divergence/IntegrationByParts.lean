import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.InteriorCompactSupport
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.POUReduction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.POUReduction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Proper
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support


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

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

omit [InnerProductSpace ℝ E] in
lemma Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact hf.integrable_of_hasCompactSupport hcs

omit [InnerProductSpace ℝ E] in
lemma tangentSectionAction_continuous_of_interior_support
    [T2Space M]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Continuous (tangentSectionAction (I := I) X f) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_supp : x ∈ tsupport f
  · have hx_int : x ∈ I.interior M := hf_int hx_supp
    have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
    have hx_target_int : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_mem_interior_target_of_isInteriorPoint
        (I := I) (M := M) x hx_chart hx_int
    have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (tangentSectionAction (I := I) X f)
        ((extChartAt I x).source ∩
          (extChartAt I x : M → E) ⁻¹' interior (extChartAt I x).target) :=
      tangentSectionAction_contMDiffOn (I := I) x X hf
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
  · have h_open : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
    have hev : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_supp] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have hev_action : tangentSectionAction (I := I) X f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hev.eventually_nhds] with y hy
      have hmfderiv_zero : mfderiv I 𝓘(ℝ) f y = 0 := by
        rw [Filter.EventuallyEq.mfderiv_eq hy, mfderiv_const]
        rfl
      change mfderiv I 𝓘(ℝ) f y (X y) = 0
      rw [hmfderiv_zero]; rfl
    exact (continuous_const.continuousAt.congr hev_action.symm)

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
lemma support_smoothSmul_subset
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Function.support ((smoothSmul (I := I) f hf X) : ∀ x, TangentSpace I x) ⊆
      Function.support (X : ∀ x, TangentSpace I x) := by
  intro x hx
  by_contra hneX
  rw [Function.notMem_support] at hneX
  have hYx : (smoothSmul (I := I) f hf X : ∀ x, TangentSpace I x) x =
      (0 : TangentSpace I x) := by
    change f x • X x = (0 : TangentSpace I x)
    rw [hneX]; exact smul_zero _
  exact hx hYx

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
lemma tsupport_smoothSmul_subset
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    tsupport ((smoothSmul (I := I) f hf X) : ∀ x, TangentSpace I x) ⊆ tsupport X :=
  closure_minimal
    ((support_smoothSmul_subset (I := I) hf X).trans (subset_tsupport _))
    (isClosed_tsupport _)

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
lemma hasCompactSupport_smoothSmul
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) :
    HasCompactSupport (smoothSmul (I := I) f hf X) :=
  hX.mono' ((support_smoothSmul_subset (I := I) hf X).trans (subset_tsupport _))

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
lemma tsupport_smoothSmul_subset_interior
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX_int : tsupport X ⊆ I.interior M) :
    tsupport ((smoothSmul (I := I) f hf X) : ∀ x, TangentSpace I x) ⊆ I.interior M :=
  (tsupport_smoothSmul_subset (I := I) hf X).trans hX_int

omit [InnerProductSpace ℝ E] in
theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) f hf X with hY_def
  have hY_cs : HasCompactSupport Y :=
    hasCompactSupport_smoothSmul (I := I) hf X hX
  have hY_int : tsupport (Y : ∀ x, TangentSpace I x) ⊆ I.interior M :=
    tsupport_smoothSmul_subset_interior (I := I) hf X hX_int
  have hY_div : ∀ x : M,
      divergence_g_with_boundary (I := I) g Y x =
        f x * divergence_g_with_boundary (I := I) g X x +
          tangentSectionAction (I := I) X f x :=
    divergence_g_with_boundary_smoothSmul (I := I) g f hf X
  have hf_cont : Continuous f := hf.continuous
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
  have hAct_cont : Continuous (tangentSectionAction (I := I) X f) :=
    tangentSectionAction_continuous_of_interior_support (I := I) X hf hf_int
  have hX_div_cs : HasCompactSupport (divergence_g_with_boundary (I := I) g X) :=
    hasCompactSupport_divergence_g_with_boundary (I := I) g hX hX_int
  have hAct_cs : HasCompactSupport (tangentSectionAction (I := I) X f) :=
    hasCompactSupport_tangentSectionAction (I := I) hX f
  have hMul_cont : Continuous (fun x : M => f x * divergence_g_with_boundary (I := I) g X x) :=
    hf_cont.mul hX_div_cont
  have hMul_cs : HasCompactSupport (fun x : M => f x * divergence_g_with_boundary (I := I) g X x) :=
    hX_div_cs.mul_left
  have h_div_Y_zero :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
    integral_divergence_with_boundary_eq_zero_of_hasCompactSupport_of_interior_support
      (I := I) g Y hY_cs hY_int
  have h_eq_pointwise : ∀ x : M, divergence_g_with_boundary (I := I) g Y x =
      f x * divergence_g_with_boundary (I := I) g X x +
        tangentSectionAction (I := I) X f x := hY_div
  have h_div_Y_split :
      ∫ x, divergence_g_with_boundary (I := I) g Y x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (f x * divergence_g_with_boundary (I := I) g X x +
                tangentSectionAction (I := I) X f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_eq_pointwise x
  have h_int_mul : Integrable (fun x : M => f x * divergence_g_with_boundary (I := I) g X x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hMul_cont hMul_cs
  have h_int_act : Integrable (tangentSectionAction (I := I) X f)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hAct_cont hAct_cs
  have h_int_split :
      ∫ x, (f x * divergence_g_with_boundary (I := I) g X x +
              tangentSectionAction (I := I) X f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, f x * divergence_g_with_boundary (I := I) g X x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
          ∫ x, tangentSectionAction (I := I) X f x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_add h_int_mul h_int_act
  have h_sum_zero :
      ∫ x, f x * divergence_g_with_boundary (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
        ∫ x, tangentSectionAction (I := I) X f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    rw [← h_int_split, ← h_div_Y_split]; exact h_div_Y_zero
  linarith [h_sum_zero]

private lemma tsupport_mul_subset_left (f h : M → ℝ) :
    tsupport (fun x : M => f x * h x) ⊆ tsupport f := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hne
  have hf_zero : f x = 0 := by
    by_contra hne'
    exact hne (subset_tsupport _ hne')
  exact hx (by rw [hf_zero, zero_mul])


omit [InnerProductSpace ℝ E] in
theorem integral_tangentSectionAction_mul_add_eq_neg_with_boundary
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ) ∞ h)
    (hf_int : tsupport f ⊆ I.interior M) (_hh_int : tsupport h ⊆ I.interior M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X)
    (hX_int : tsupport X ⊆ I.interior M) :
    ∫ x, (tangentSectionAction (I := I) X f x * h x +
            f x * tangentSectionAction (I := I) X h x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * h x * divergence_g_with_boundary (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hfh : ContMDiff I 𝓘(ℝ) ∞ (f * h) := hf.mul hh
  have hfh_int : tsupport (f * h) ⊆ I.interior M := by
    have : tsupport (fun x : M => (f * h) x) ⊆ tsupport f := by
      change tsupport (fun x : M => f x * h x) ⊆ tsupport f
      exact tsupport_mul_subset_left (M := M) f h
    exact this.trans hf_int
  have h_a := integral_tangentSectionAction_eq_neg_integral_smul_divergence_with_boundary
    (I := I) g hfh hfh_int X hX hX_int
  have h_leibniz : ∀ x : M,
      tangentSectionAction (I := I) X (f * h) x =
        tangentSectionAction (I := I) X f x * h x +
          f x * tangentSectionAction (I := I) X h x := fun x =>
    tangentSectionAction_mul (I := I) X hf hh x
  have h_lhs_eq :
      ∫ x, tangentSectionAction (I := I) X (f * h) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (tangentSectionAction (I := I) X f x * h x +
                f x * tangentSectionAction (I := I) X h x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_leibniz x
  rw [← h_lhs_eq, h_a]
  rfl

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
