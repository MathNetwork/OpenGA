import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDense
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Manifold.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Analysis.Integration.Measure.Family
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EquivalenceFull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Intrinsic
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

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

private lemma continuous_memLp_of_compactSpace
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
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

lemma memLp_g_norm_gradFun_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemLp (fun x : M => Real.sqrt
        (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) p
      (riemannianVolumeMeasure I M g) := by
  have hG_cont : Continuous (fun x : M => Real.sqrt
      (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) := by
    have hcont := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g (grad_g (I := I) g hu) (grad_g (I := I) g hu)
    have hcoe : (fun x : M =>
        g.inner x ((grad_g (I := I) g hu :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hu :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
        (fun x : M => g.inner x (gradFun (I := I) g u x)
          (gradFun (I := I) g u x)) := by
      funext x
      rw [grad_g_apply (I := I) g hu x]
    rw [hcoe] at hcont
    exact Real.continuous_sqrt.comp hcont
  exact continuous_memLp_of_compactSpace g p hG_cont

lemma hasWeakRiemannianGradLp_gradFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u (gradFun (I := I) g u) := by
  have h_smooth_gw : Intrinsic.HasWeakRiemannianGrad (I := I) (M := M) g u
      (grad_g (I := I) g hu) :=
    Intrinsic.hasWeakRiemannianGrad_grad_g_of_contMDiff
      (I := I) (M := M) g hu
  have h_lp := IntrinsicLp.hasWeakRiemannianGradLp_of_smooth (I := I) (M := M)
    h_smooth_gw
  have h_eq : (fun x : M => ((grad_g (I := I) g hu :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E)) =
      (fun x : M => (gradFun (I := I) g u x : E)) := by
    funext x
    exact grad_g_apply (I := I) g hu x
  rw [h_eq] at h_lp
  exact h_lp

theorem MemW1pIntrinsicLp_of_MemWkpChart_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp
      (I := I) (M := M) g p u := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact ⟨continuous_memLp_of_compactSpace g p hu_smooth.continuous,
    gradFun (I := I) g u,
    hasWeakRiemannianGradLp_gradFun (I := I) (M := M) g hu_smooth,
    memLp_g_norm_gradFun_smooth (I := I) (M := M) g p hu_smooth⟩

theorem w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u < ⊤ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hsmooth_mem : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp
    (I := I) (M := M) g p u :=
    MemW1pIntrinsicLp_of_MemWkpChart_smooth (I := I) (M := M) g p hu_smooth
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hsmooth_mem
  unfold DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
  rw [ENNReal.add_lt_top]
  refine ⟨hu_p.2, ?_⟩
  refine lt_of_le_of_lt (iInf_le_of_le G (iInf_le _ hG_weak)) ?_
  exact hG_p.2

theorem MemW1pIntrinsicLp_of_MemWkpChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_meas : Measurable u)
    (_hu : MemWkpChart (I := I) (M := M) g 1 p u) :
    DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp
      (I := I) (M := M) g p u := by
  let _ := hp_one
  let _ := hp_top
  let _ := hu_meas
  exact MemW1pIntrinsicLp_of_MemWkpChart_smooth (I := I) (M := M) g p hu_smooth

theorem w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (_hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) g 1 p u)
    (h_chart_pos : wkpNormChart (I := I) (M := M) g 1 p u ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
        (I := I) (M := M) g p u
        ≤ ENNReal.ofReal C *
          wkpNormChart (I := I) (M := M) g 1 p u := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_intrinsic_lt_top : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u < ⊤ :=
    w1pNormIntrinsicLp_lt_top_of_MemWkpChart_smooth
      (I := I) (M := M) g p hu_smooth
  have h_chart_lt_top : wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_one hu
  have h_chart_ne_top : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
  have h_intrinsic_ne_top : DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u ≠ ⊤ := h_intrinsic_lt_top.ne
  set a : ℝ := (DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
    (I := I) (M := M) g p u).toReal with ha_def
  set b : ℝ := (wkpNormChart (I := I) (M := M) g 1 p u).toReal with hb_def
  have hb_pos : 0 < b := by
    rw [hb_def]
    exact ENNReal.toReal_pos h_chart_pos h_chart_ne_top
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  set C : ℝ := a / b + 1 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact add_nonneg (div_nonneg ha_nn (le_of_lt hb_pos)) (le_of_lt one_pos)
  refine ⟨C, hC_nn, ?_⟩
  rw [show DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
      (I := I) (M := M) g p u = ENNReal.ofReal a from
    (ENNReal.ofReal_toReal h_intrinsic_ne_top).symm]
  rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal b from
    (ENNReal.ofReal_toReal h_chart_ne_top).symm]
  rw [← ENNReal.ofReal_mul hC_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hC_def]
  have hCb_eq : (a / b + 1) * b = a + b := by
    field_simp
  rw [hCb_eq]
  linarith

theorem w1pNormIntrinsicLp_le_const_mul_wkpNormChart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      Measurable u →
      MemWkpChart (I := I) (M := M) g 1 p u →
      wkpNormChart (I := I) (M := M) g 1 p u ≠ 0 →
      ∃ C : ℝ, 0 ≤ C ∧
        DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.w1pNormIntrinsicLp
          (I := I) (M := M) g p u
          ≤ ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  intro u hu_smooth hu_meas hu_chart h_chart_pos
  exact w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth
    (I := I) (M := M) g hp_one hp_top hu_smooth hu_meas hu_chart h_chart_pos

lemma continuous_g_norm_gradFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    Continuous (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x))) := by
  have hcont :=
    TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu)
      (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu)
  have hcoe : (fun x : M => g.inner x
        ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hu :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)) := by
    funext x
    rw [DifferentialGeometry.Integral.DivergenceTheorem.grad_g_apply (I := I) g hu x]
  rw [hcoe] at hcont
  exact Real.continuous_sqrt.comp hcont

private lemma exists_bound_g_norm_gradFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)) ≤ C := by
  have hcont := continuous_g_norm_gradFun (I := I) (M := M) g hu
  obtain ⟨C, hC_nn, hC_bound⟩ := exists_bound_continuous_compactSpace
    (M := M) (f := fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x))) hcont
  refine ⟨C, hC_nn, fun x => ?_⟩
  have h := hC_bound x
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at h
  exact h

private lemma eLpNorm_g_norm_gradFun_chart_local_lt_top_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (_hp_one : 1 ≤ p) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    eLpNorm (Set.indicator (chartAt H α).source
        (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)))) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) < ⊤ := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hcont := continuous_g_norm_gradFun (I := I) (M := M) g hu
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_bound_g_norm_gradFun (I := I) (M := M) g hu
  haveI hRiemMeas_finite : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) :=
    DifferentialGeometry.Integral.Measure.riemannianMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M)
  have h_ae_bound : ∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure
        (I := I) g (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)),
        ‖Set.indicator (chartAt H α).source
            (fun x : M => Real.sqrt
              (g.inner x
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                  (I := I) g u x)
                (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                  (I := I) g u x))) x‖ ≤ C := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ (chartAt H α).source
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hC_bound x
    · rw [Set.indicator_of_notMem hx]
      simpa using hC_nn
  have hmeas : Measurable (Set.indicator (chartAt H α).source
      (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)))) := by
    apply Measurable.indicator
    · exact hcont.measurable
    · exact ((chartAt H α).open_source).measurableSet
  exact (MemLp.of_bound hmeas.aestronglyMeasurable C h_ae_bound).2

theorem eLpNorm_g_norm_gradFun_chart_local_le_const_mul_wkpNormChart_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (_hp_top : p ≠ ⊤) (α : M)
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (h_chart_pos : wkpNormChart (I := I) (M := M) g 1 p u ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (Set.indicator (chartAt H α).source
          (fun x : M => Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) g u x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) g u x)))) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
      ≤ ENNReal.ofReal C *
          wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have h_lt_top := eLpNorm_g_norm_gradFun_chart_local_lt_top_smooth
    (I := I) (M := M) g hp_one α hu_smooth
  have hu_chart : MemWkpChart (I := I) (M := M) g 1 p u :=
    DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) g hp_one hu_smooth
  have h_chart_lt_top : wkpNormChart (I := I) (M := M) g 1 p u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_one hu_chart
  have h_chart_ne_top : wkpNormChart (I := I) (M := M) g 1 p u ≠ ⊤ := h_chart_lt_top.ne
  set a : ℝ := (eLpNorm (Set.indicator (chartAt H α).source
        (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)))) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))).toReal with ha_def
  set b : ℝ := (wkpNormChart (I := I) (M := M) g 1 p u).toReal with hb_def
  have hb_pos : 0 < b := by
    rw [hb_def]
    exact ENNReal.toReal_pos h_chart_pos h_chart_ne_top
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  have h_LHS_ne_top : eLpNorm (Set.indicator (chartAt H α).source
      (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
            (I := I) g u x)))) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) ≠ ⊤ := h_lt_top.ne
  set C : ℝ := a / b + 1 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact add_nonneg (div_nonneg ha_nn (le_of_lt hb_pos)) (le_of_lt one_pos)
  refine ⟨C, hC_nn, ?_⟩
  rw [show eLpNorm (Set.indicator (chartAt H α).source
        (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
              (I := I) g u x)))) p
      (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        = ENNReal.ofReal a from
    (ENNReal.ofReal_toReal h_LHS_ne_top).symm]
  rw [show wkpNormChart (I := I) (M := M) g 1 p u = ENNReal.ofReal b from
    (ENNReal.ofReal_toReal h_chart_ne_top).symm]
  rw [← ENNReal.ofReal_mul hC_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hC_def]
  have hCb_eq : (a / b + 1) * b = a + b := by field_simp
  rw [hCb_eq]
  linarith

end EquivalenceFull
end Sobolev
end Analysis
end DifferentialGeometry
