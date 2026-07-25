import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartMeasureEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in (extChartAt I α).target,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y)
        ∂(modelHaar (E := E)) := by
  classical
  have h_step1 :=
    integral_riemannianVolumeMeasure_eq_chartLocal_of_support_in_chart
      (I := I) (M := M) g α hf_cont hf_supp
  rw [h_step1]
  exact integral_chartLocalMeasure (I := I) (M := M) g α f hf_cont.measurable

theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) *
          Set.indicator (extChartAt I α).target (fun _ => (1 : ℝ)) y
        ∂(modelHaar (E := E)) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget
    (I := I) (M := M) g α hf_cont hf_supp]
  have htgt_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  rw [show
      (∫ y in (extChartAt I α).target,
          chartDensity g α ((extChartAt I α).symm y) *
            f ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) =
        ∫ y, (extChartAt I α).target.indicator
              (fun y' : E =>
                chartDensity g α ((extChartAt I α).symm y') *
                  f ((extChartAt I α).symm y')) y
            ∂(modelHaar (E := E)) from
        (MeasureTheory.integral_indicator htgt_meas).symm]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

private def toEuclideanMeasurableEquiv :
    E ≃ᵐ EuclN :=
  (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv

@[simp] private lemma toEuclideanMeasurableEquiv_apply (y : E) :
    toEuclideanMeasurableEquiv (E := E) y = toEuclidean y := rfl

@[simp] private lemma toEuclideanMeasurableEquiv_symm_apply (y : EuclN) :
    (toEuclideanMeasurableEquiv (E := E)).symm y = (toEuclidean (E := E)).symm y := rfl

omit [IsManifold I ∞ M] in

private lemma toEuclidean_mem_chartTargetEuclid_iff
    (α : M) (y : E) :
    toEuclidean (E := E) y ∈ chartTargetEuclid (I := I) (M := M) α ↔
      y ∈ (extChartAt I α).target := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rcases hy with ⟨z, hz_target, hz_eq⟩
    have hyz : y = z := ((toEuclidean (E := E)).injective hz_eq).symm
    rw [hyz]; exact hz_target
  · exact ⟨y, hy, rfl⟩

omit [IsManifold I ∞ M] in
private lemma chartTargetEuclid_measurableSet (α : M) :
    MeasurableSet (chartTargetEuclid (I := I) (M := M) α) := by
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  change MeasurableSet (toEuclidean '' (extChartAt I α).target)
  exact (toEuclideanMeasurableEquiv (E := E)).measurableEmbedding.measurableSet_image.mpr
    htarget_meas

theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget
    (I := I) (M := M) g α hf_cont hf_supp]
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  rw [show
      (∫ y in (extChartAt I α).target,
          chartDensity g α ((extChartAt I α).symm y) *
            f ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) =
        ∫ y, (extChartAt I α).target.indicator
              (fun y' : E =>
                chartDensity g α ((extChartAt I α).symm y') *
                  f ((extChartAt I α).symm y')) y
            ∂(modelHaar (E := E)) from
        (MeasureTheory.integral_indicator htarget_meas).symm]
  rw [show
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y',
            (chartTargetEuclid (I := I) (M := M) α).indicator
              (fun y'' : EuclN =>
                densityOnEuclid (I := I) g α y'' *
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y''))) y'
            ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
                (modelHaar (E := E))) from
        (MeasureTheory.integral_indicator hctE_meas).symm]
  rw [show
      (∫ y',
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y'' : EuclN =>
              densityOnEuclid (I := I) g α y'' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y''))) y'
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y,
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y'' : EuclN =>
              densityOnEuclid (I := I) g α y'' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'')))
            (toEuclideanMeasurableEquiv (E := E) y)
          ∂(modelHaar (E := E)) from ?_]
  · refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => ?_))
    simp only
    by_cases hy : y ∈ (extChartAt I α).target
    · have hctE_y : toEuclideanMeasurableEquiv (E := E) y ∈
          chartTargetEuclid (I := I) (M := M) α :=
        (toEuclidean_mem_chartTargetEuclid_iff (I := I) (M := M) α y).mpr hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hctE_y]
      have h_symm_apply :
          (toEuclidean (E := E)).symm (toEuclidean y) = y :=
        (toEuclidean (E := E)).symm_apply_apply y
      change chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) =
        densityOnEuclid (I := I) g α (toEuclidean y) *
          f ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm (toEuclidean y)))
      rw [h_symm_apply]
      change chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) =
        chartDensity g α ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm (toEuclidean y))) *
          f ((extChartAt I α).symm y)
      rw [h_symm_apply]
    · have hctE_off : toEuclideanMeasurableEquiv (E := E) y ∉
          chartTargetEuclid (I := I) (M := M) α := by
        intro hcontra
        exact hy ((toEuclidean_mem_chartTargetEuclid_iff (I := I) (M := M) α y).mp hcontra)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hctE_off]
  · exact MeasureTheory.integral_map_equiv
      (μ := modelHaar (E := E))
      (e := toEuclideanMeasurableEquiv (E := E))
      (f := fun y'' : EuclN =>
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun y''' : EuclN =>
            densityOnEuclid (I := I) g α y''' *
              f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'''))) y'')

theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_supp : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          Set.indicator (chartTargetEuclid (I := I) (M := M) α)
            (fun _ => (1 : ℝ)) y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α hf_cont hf_supp]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  rw [show
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y,
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y' : EuclN =>
              densityOnEuclid (I := I) g α y' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))) y
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E))) from
        (MeasureTheory.integral_indicator hctE_meas).symm]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

end ChartMeasureEquiv
end Laplacian
end Analysis
end DifferentialGeometry
