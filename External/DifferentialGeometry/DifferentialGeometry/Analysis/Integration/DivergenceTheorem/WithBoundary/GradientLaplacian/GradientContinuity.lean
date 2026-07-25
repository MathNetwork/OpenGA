import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin
import DifferentialGeometry.Geometry.Boundary.EuclideanHalfSpaceInstance
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.ContinuousOn


noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix BigOperators ENNReal

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure


omit [InnerProductSpace ℝ E] in
private lemma partialDerivWithin_scalarOnE_continuousOn_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target := by
  have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
    uniqueDiffOn_extChartAt_target (I := I) α
  have hbase : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hpartial_target : ContDiffOn ℝ ∞
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target :=
    partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := j) hbase hUD
  exact hpartial_target.continuousOn


omit [InnerProductSpace ℝ E] in
private lemma partialDerivWithin_scalarOnE_extChartAt_continuousOn_source
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y : M =>
        partialDerivWithin (E := E) (extChartAt I α).target j
          (scalarOnE (I := I) α f) (extChartAt I α y))
      (chartAt H α).source := by
  have hpartial : ContinuousOn
      (partialDerivWithin (E := E) (extChartAt I α).target j
        (scalarOnE (I := I) α f))
      (extChartAt I α).target :=
    partialDerivWithin_scalarOnE_continuousOn_target (I := I) α hf j
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
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (gradChartCoeffWithin (I := I) g α f i) (chartAt H α).source := by
  classical
  have heq : ∀ y ∈ (chartAt H α).source,
      gradChartCoeffWithin (I := I) g α f i y =
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α y i j *
            partialDerivWithin (E := E) (extChartAt I α).target j
              (scalarOnE (I := I) α f) (extChartAt I α y) := by
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
      (I := I) α hf j


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
private lemma g_inner_gradChartLocalWithin_expand
    (g : SmoothRiemannianMetric I M) (α : M) (f h : M → ℝ) (y : M) :
    g.inner y (gradChartLocalWithin (I := I) g α f y)
        (gradChartLocalWithin (I := I) g α h y) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α f i y *
            gradChartCoeffWithin (I := I) g α h j y *
              chartGramMatrix (I := I) g α y i j := by
  classical
  unfold gradChartLocalWithin
  rw [show
        g.inner y (∑ i : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α f i y •
              chartBasisVecFiber (I := I) α i y)
          (∑ j : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α h j y •
              chartBasisVecFiber (I := I) α j y) =
        ∑ i : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α f i y *
            (g.inner y (chartBasisVecFiber (I := I) α i y))
              (∑ j : Fin (Module.finrank ℝ E),
                gradChartCoeffWithin (I := I) g α h j y •
                  chartBasisVecFiber (I := I) α j y) from ?_]
  swap
  · rw [show g.inner y (∑ i : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α f i y •
                chartBasisVecFiber (I := I) α i y) =
            ∑ i : Fin (Module.finrank ℝ E),
              gradChartCoeffWithin (I := I) g α f i y •
                g.inner y (chartBasisVecFiber (I := I) α i y) from ?_]
    · rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (g.inner y (chartBasisVecFiber (I := I) α i y))
          (∑ j : Fin (Module.finrank ℝ E),
            gradChartCoeffWithin (I := I) g α h j y •
              chartBasisVecFiber (I := I) α j y) =
        ∑ j : Fin (Module.finrank ℝ E),
          gradChartCoeffWithin (I := I) g α h j y *
            g.inner y (chartBasisVecFiber (I := I) α i y)
              (chartBasisVecFiber (I := I) α j y) from ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [chartGramMatrix_apply]
    ring
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul]
    rfl


omit [InnerProductSpace ℝ E] in
private lemma g_inner_gradFun_gradFun_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (α : M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ContinuousOn
      (fun y : M => g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g h y))
      (chartAt H α).source := by
  classical
  have h_rewrite : ∀ y ∈ (chartAt H α).source,
      g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g h y) =
        g.inner y (gradChartLocalWithin (I := I) g α f y)
          (gradChartLocalWithin (I := I) g α h y) := by
    intro y hy
    rw [(gradChartLocalWithin_eq_gradFun (I := I) g α hf hy)]
    rw [(gradChartLocalWithin_eq_gradFun (I := I) g α hh hy)]
  refine ContinuousOn.congr ?_ (fun y hy => h_rewrite y hy)
  refine ContinuousOn.congr (s := (chartAt H α).source) ?_
    (fun y _ => g_inner_gradChartLocalWithin_expand (I := I) g α f h y)
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact gradChartCoeffWithin_continuousOn_source (I := I) g α hf i
  · exact gradChartCoeffWithin_continuousOn_source (I := I) g α hh j
  · exact chartGramMatrix_entry_continuousOn_source (I := I) g α i j


omit [InnerProductSpace ℝ E] in
private lemma g_inner_gradFun_gradFun_continuous_general
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    Continuous (fun x : M => g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g h x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx_chart : x ∈ (chartAt H x).source := mem_chart_source H x
  have hopen : IsOpen (chartAt H x).source := (chartAt H x).open_source
  have hcontOn :=
    g_inner_gradFun_gradFun_continuousOn_chart_source
      (I := I) (M := M) g x hf hh
  exact (hcontOn x hx_chart).continuousAt (hopen.mem_nhds hx_chart)

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure

theorem continuous_g_inner_gradFun_gradFun
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
  g_inner_gradFun_gradFun_continuous_general
    (I := modelWithCornersEuclideanHalfSpace n) (M := M) g hf hh

theorem bddAbove_g_inner_gradFun_gradFun_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    BddAbove (Set.range (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x))) := by
  have hcont : Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
    continuous_g_inner_gradFun_gradFun (n := n) (M := M) g hf hh
  exact (isCompact_range hcont).bddAbove

private local instance instMeasurableSpaceM_gradContinuity :
    MeasurableSpace M := borel M
private local instance instBorelSpaceM_gradContinuity : BorelSpace M := ⟨rfl⟩

theorem integrable_g_inner_gradFun_gradFun
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace n) M)
    {f h : M → ℝ}
    (hf : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (modelWithCornersEuclideanHalfSpace n) 𝓘(ℝ, ℝ) ∞ h) :
    Integrable (fun x : M =>
        g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
          (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x))
      (riemannianVolumeMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) := by
  haveI : IsFiniteMeasure
      (riemannianVolumeMeasure
        (I := modelWithCornersEuclideanHalfSpace n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := modelWithCornersEuclideanHalfSpace n) (M := M) g
  have hcont : Continuous (fun x : M =>
      g.inner x (gradFun (I := modelWithCornersEuclideanHalfSpace n) g f x)
        (gradFun (I := modelWithCornersEuclideanHalfSpace n) g h x)) :=
    continuous_g_inner_gradFun_gradFun (n := n) (M := M) g hf hh
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry

end
