import DifferentialGeometry.Analysis.Integration.Measure.RealizedMetricForMeasure
import DifferentialGeometry.Integration.Volume.Family.Base
import DifferentialGeometry.Integration.Volume.Family.Variation

set_option autoImplicit false

namespace DifferentialGeometry.Integral.Measure

noncomputable section

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


abbrev metricFamilyForMeasure
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real) :
    Real → SmoothRiemannianMetric I M :=
  fun t => G.metric t


abbrev metricFamilyForMeasureOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D) :
    Real → SmoothRiemannianMetric I M :=
  fun t => G.metric t


abbrev volumeMeasureFamily [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real) :
    Real → MeasureTheory.Measure M :=
  riemannianMeasureFamily (I := I) (M := M) (metricFamilyForMeasure (I := I) (M := M) G)

@[simp]
theorem volumeMeasureFamily_eq [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real) (t : Real) :
    volumeMeasureFamily (I := I) (M := M) G t =
      Measure.volumeMeasureAt (I := I) (M := M) G t := rfl


abbrev volumeMeasureFamilyOn [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D) :
    Real → MeasureTheory.Measure M :=
  riemannianMeasureFamily (I := I) (M := M) (metricFamilyForMeasureOn (I := I) (M := M) G)

@[simp]
theorem volumeMeasureFamilyOn_eq [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D) (t : Real) :
    volumeMeasureFamilyOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M)
        (G.metric t) := rfl

@[simp]
theorem volumeMeasureFamilyOn_eq_volumeMeasureOn [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) :
    volumeMeasureFamilyOn (I := I) (M := M) G (t : Real) =
      Measure.volumeMeasureOn (I := I) (M := M) G t := rfl


abbrev traceTimeDerivMetricAt
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real) (t : Real) (x : M) :
    Real :=
  traceTimeDerivMetric (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t x

@[simp]
theorem traceTimeDerivMetricAt_eq
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real) (t : Real) (x : M) :
    traceTimeDerivMetricAt (I := I) G t x =
      traceTimeDerivMetric (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t x := rfl


abbrev traceTimeDerivMetricOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D) (t : Real) (x : M) :
    Real :=
  traceTimeDerivMetric (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t x

@[simp]
theorem traceTimeDerivMetricOn_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D) (t : Real) (x : M) :
    traceTimeDerivMetricOn (I := I) G t x =
      traceTimeDerivMetric (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t x := rfl

theorem volume_variation_formula_clean_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀
            + (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  simpa [volumeMeasureFamily, traceTimeDerivMetricAt] using
    (volume_variation_formula_clean (I := I) (M := M)
      (g_fam := metricFamilyForMeasure (I := I) (M := M) G)
      (f := f) (t₀ := t₀) hg hf)

theorem volume_variation_formula_clean_on
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn (I := I) (M := M) D)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamilyOn (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀
            + (1 / 2 : Real) * traceTimeDerivMetricOn (I := I) G t₀ x * f t₀ x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) G t₀))
      t₀ := by
  simpa [volumeMeasureFamilyOn, traceTimeDerivMetricOn] using
    (volume_variation_formula_clean (I := I) (M := M)
      (g_fam := metricFamilyForMeasureOn (I := I) (M := M) G)
      (f := f) (t₀ := t₀) hg hf)

end

end DifferentialGeometry.Integral.Measure
