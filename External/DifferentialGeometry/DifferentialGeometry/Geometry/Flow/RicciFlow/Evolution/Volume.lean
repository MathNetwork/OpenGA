import DifferentialGeometry.Analysis.Integration.Measure.VolumeVariation
import DifferentialGeometry.Geometry.Curvature.Realized.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Realized.RicciFlow

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow
namespace Evolution
namespace Volume

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Measure
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {A : Type*} [CommRing A] [Algebra Real A]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


abbrev volumeTraceFrame :
    Fin (Module.finrank Real E) → (x : M) → TangentSpace I x :=
  fun i x => chartBasisVecFiber (I := I) x i x


abbrev volumeTraceInvMetricComponents
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) :
    M → Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
  fun x i j => ((chartGramMatrix (I := I) g x x)⁻¹) i j



abbrev scalarCurvatureFromRicciInVolumeFrame
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real) :
    Real → M → Real :=
  fun t =>
    DifferentialGeometry.Integral.Connection.scalarCurvatureFromRicciTraceInFrame (I := I) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M))



theorem scalarCurvatureFromRicciInVolumeFrame_realizes
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real) (t : Real) :
    DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceInFrame (I := I)
      (scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t)
      (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)) :=
  DifferentialGeometry.Integral.Connection.scalarCurvatureFromRicciTraceInFrame_realizes
    (I := I) (M := M) (Ric t)
    (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
    (volumeTraceFrame (I := I) (M := M))






theorem traceTimeDerivMetricAt_eq_trace_metric_derivative
    (td : TimeDerivativeData Real A Real)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {t : Real} {x : M}
    (hdt : ∀ F : Real → Real, td.dt_apply F t = deriv F t) :
    traceTimeDerivMetricAt (I := I) G t x =
      Matrix.trace
        ((chartGramMatrix (I := I) (G.metric t) x x)⁻¹ *
          Matrix.of fun i j =>
            DifferentialGeometry.Integral.Connection.metricTimeDerivative td G t x
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x)) := by
  rw [traceTimeDerivMetricAt_eq, traceTimeDerivMetric_eq]
  congr 2
  ext i j
  have h := hdt
    (fun s : Real =>
      (G.metric s).inner x
        (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x))
  simpa [metricFamilyForMeasure, DifferentialGeometry.Integral.Connection.metricTimeDerivative, chartGramMatrix_apply]
    using h.symm


private theorem chartGramMatrix_inv_symm
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank Real E)) :
    ((chartGramMatrix (I := I) g x x)⁻¹) j i =
      ((chartGramMatrix (I := I) g x x)⁻¹) i j := by
  have hHerm :
      ((chartGramMatrix (I := I) g x x)⁻¹).IsHermitian :=
    (chartGramMatrix_isHermitian (I := I) g x x).inv
  simpa [star_trivial] using hHerm.apply i j




theorem scalar_trace_eq_volume_trace_components
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Integral.Connection.RawTwoTensorField (I := I) (M := M))
    (scalar : M → Real)
    (hScalar : DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceInFrame (I := I)
      scalar Ric
      (volumeTraceInvMetricComponents (I := I) (M := M) g)
      (volumeTraceFrame (I := I) (M := M))) (x : M) :
    scalar x =
      ∑ i : Fin (Module.finrank Real E),
        ∑ j : Fin (Module.finrank Real E),
          ((chartGramMatrix (I := I) g x x)⁻¹) i j *
            Ric x
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x) := by
  simpa [volumeTraceInvMetricComponents, volumeTraceFrame] using
    DifferentialGeometry.Integral.Connection.scalar_eq_trace (I := I) scalar Ric
      (volumeTraceInvMetricComponents (I := I) (M := M) g)
      (volumeTraceFrame (I := I) (M := M)) hScalar x






theorem traceTimeDerivMetricAt_eq_neg_two_scalar
    (td : TimeDerivativeData Real A Real)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    (hdt : ∀ (F : Real → Real) (t : Real), td.dt_apply F t = deriv F t)
    (hEq : DifferentialGeometry.Integral.Connection.MetricVariationEquation (I := I) td G Ric)
    {t : Real} {x : M}
    (hScalar :
      scalar t x =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((chartGramMatrix (I := I) (G.metric t) x x)⁻¹) i j *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x := by
  classical
  let Gmat : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    chartGramMatrix (I := I) (G.metric t) x x
  let dG : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    Matrix.of fun i j =>
      DifferentialGeometry.Integral.Connection.metricTimeDerivative td G t x
        (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x)
  have htrace :
      traceTimeDerivMetricAt (I := I) G t x =
        Matrix.trace (Gmat⁻¹ * dG) := by
    simpa [Gmat, dG] using
      traceTimeDerivMetricAt_eq_trace_metric_derivative
        (I := I) (M := M) td G (t := t) (x := x) (fun F => hdt F t)
  have hdG :
      dG =
        Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) *
            Ric t x
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simpa [dG] using (hEq t x
      (chartBasisVecFiber (I := I) x i x)
      (chartBasisVecFiber (I := I) x j x))
  have hInvSymm :
      ∀ i j : Fin (Module.finrank Real E), Gmat⁻¹ j i = Gmat⁻¹ i j := by
    intro i j
    simpa [Gmat] using
      chartGramMatrix_inv_symm (I := I) (M := M) (G.metric t) x i j
  rw [htrace, hdG]
  calc
    Matrix.trace
        (Gmat⁻¹ *
          Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x))
        =
        Matrix.trace
          ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹) := by
          rw [Matrix.trace_mul_comm]
    _ =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹ j i := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ =
        (-2 : Real) *
          (∑ i : Fin (Module.finrank Real E),
            ∑ j : Fin (Module.finrank Real E),
              Gmat⁻¹ i j *
                Ric t x
                  (chartBasisVecFiber (I := I) x i x)
                  (chartBasisVecFiber (I := I) x j x)) := by
          simp_rw [hInvSymm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (-2 : Real) * scalar t x := by
          rw [hScalar]




theorem traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace
    (td : TimeDerivativeData Real A Real)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    (hdt : ∀ (F : Real → Real) (t : Real), td.dt_apply F t = deriv F t)
    (hEq : DifferentialGeometry.Integral.Connection.MetricVariationEquation (I := I) td G Ric)
    {t : Real}
    (hScalar : DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceInFrame (I := I)
      (scalar t) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)))
    (x : M) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x :=
  traceTimeDerivMetricAt_eq_neg_two_scalar
    (I := I) (M := M) td G Ric scalar hdt hEq (t := t) (x := x)
    (scalar_trace_eq_volume_trace_components
      (I := I) (M := M) (G.metric t) (Ric t) (scalar t) hScalar x)




theorem traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {t : Real}
    (hEq : DifferentialGeometry.Integral.Connection.MetricVariationEquationDerivAt (I := I) G Ric t)
    (hScalar : DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceInFrame (I := I)
      (scalar t) (Ric t)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t))
      (volumeTraceFrame (I := I) (M := M)))
    (x : M) :
    traceTimeDerivMetricAt (I := I) G t x = (-2 : Real) * scalar t x := by
  classical
  let Gmat : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    chartGramMatrix (I := I) (G.metric t) x x
  let dG : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    Matrix.of fun i j =>
      deriv (fun s : Real =>
        (G.metric s).inner x
          (chartBasisVecFiber (I := I) x i x)
          (chartBasisVecFiber (I := I) x j x)) t
  have htrace :
      traceTimeDerivMetricAt (I := I) G t x =
        Matrix.trace (Gmat⁻¹ * dG) := by
    simp [traceTimeDerivMetric_eq, metricFamilyForMeasure,
      chartGramMatrix_apply, Gmat, dG]
  have hdG :
      dG =
        Matrix.of fun i j : Fin (Module.finrank Real E) =>
          (-2 : Real) *
            Ric t x
              (chartBasisVecFiber (I := I) x i x)
              (chartBasisVecFiber (I := I) x j x) := by
    ext i j
    simpa [dG] using
      DifferentialGeometry.Integral.Connection.metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt
        (I := I) G Ric hEq x
        (chartBasisVecFiber (I := I) x i x)
        (chartBasisVecFiber (I := I) x j x)
  have hInvSymm :
      ∀ i j : Fin (Module.finrank Real E), Gmat⁻¹ j i = Gmat⁻¹ i j := by
    intro i j
    simpa [Gmat] using
      chartGramMatrix_inv_symm (I := I) (M := M) (G.metric t) x i j
  rw [htrace, hdG]
  calc
    Matrix.trace
        (Gmat⁻¹ *
          Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x))
        =
        Matrix.trace
          ((Matrix.of fun i j : Fin (Module.finrank Real E) =>
            (-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹) := by
          rw [Matrix.trace_mul_comm]
    _ =
        ∑ i : Fin (Module.finrank Real E),
          ∑ j : Fin (Module.finrank Real E),
            ((-2 : Real) *
              Ric t x
                (chartBasisVecFiber (I := I) x i x)
                (chartBasisVecFiber (I := I) x j x)) * Gmat⁻¹ j i := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ =
        (-2 : Real) *
          (∑ i : Fin (Module.finrank Real E),
            ∑ j : Fin (Module.finrank Real E),
              Gmat⁻¹ i j *
                Ric t x
                  (chartBasisVecFiber (I := I) x i x)
                  (chartBasisVecFiber (I := I) x j x)) := by
          simp_rw [hInvSymm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (-2 : Real) * scalar t x := by
          rw [scalar_trace_eq_volume_trace_components
            (I := I) (M := M) (G.metric t) (Ric t) (scalar t) hScalar x]



theorem volume_variation_ricciFlow_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀)
    (htrace :
      ∀ x : M, traceTimeDerivMetricAt (I := I) G t₀ x =
        (-2 : Real) * scalar t₀ x) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  have hclean :=
    volume_variation_formula_clean_at (I := I) (M := M) G (f := f) (t₀ := t₀) hg hf
  refine hclean.congr_deriv ?_
  apply integral_congr_ae
  filter_upwards with x
  have hx := htrace x
  calc
    deriv (fun s : Real => f s x) t₀ +
        (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G t₀ x * f t₀ x
        =
        deriv (fun s : Real => f s x) t₀ +
          ((1 / 2 : Real) * ((-2 : Real) * scalar t₀ x)) * f t₀ x := by
          rw [hx]
    _ = deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x := by
          ring



theorem volume_variation_ricciFlow_at_of_metricVariationEquation
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (td : TimeDerivativeData Real A Real)
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hdt : ∀ (F : Real → Real) (t : Real), td.dt_apply F t = deriv F t)
    (hEq : DifferentialGeometry.Integral.Connection.MetricVariationEquation (I := I) td G Ric)
    (hScalar : DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceInFrame (I := I)
      (scalar t₀) (Ric t₀)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t₀))
      (volumeTraceFrame (I := I) (M := M)))
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  refine volume_variation_ricciFlow_at (I := I) (M := M) G scalar hg hf ?_
  intro x
  exact traceTimeDerivMetricAt_eq_neg_two_scalar_of_scalarTrace
    (I := I) (M := M) td G Ric scalar hdt hEq (t := t₀) hScalar x



theorem volume_variation_ricciFlow_at_of_metricDeriv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real)
    (scalar : Real → M → Real)
    {f : Real → M → Real} {t₀ : Real}
    (hEq : DifferentialGeometry.Integral.Connection.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hScalar : DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceInFrame (I := I)
      (scalar t₀) (Ric t₀)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric t₀))
      (volumeTraceFrame (I := I) (M := M)))
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ - scalar t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  refine volume_variation_ricciFlow_at (I := I) (M := M) G scalar hg hf ?_
  intro x
  exact traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv
    (I := I) (M := M) G Ric scalar hEq hScalar x



theorem volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real)
    {f : Real → M → Real} {t₀ : Real}
    (hEq : DifferentialGeometry.Integral.Connection.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ -
            scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ :=
  volume_variation_ricciFlow_at_of_metricDeriv
    (I := I) (M := M) G Ric
    (scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric)
    hEq
    (scalarCurvatureFromRicciInVolumeFrame_realizes (I := I) (M := M) G Ric t₀)
    hg hf



theorem total_volume_variation_ricciFlow_at_of_metricDeriv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : DifferentialGeometry.Integral.Connection.RicciTensorField (I := I) (M := M) Real)
    {t₀ : Real}
    (hEq : DifferentialGeometry.Integral.Connection.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀) :
    HasDerivAt
      (fun s : Real => ∫ _x, (1 : Real) ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, - scalarCurvatureFromRicciInVolumeFrame (I := I) (M := M) G Ric t₀ x
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  simpa [deriv_const] using
    (volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar
      (I := I) (M := M) G Ric (f := fun _ : Real => fun _ : M => (1 : Real))
      hEq hg (FunctionRegularAt_one (M := M) t₀))

end Volume
end Evolution
end DifferentialGeometry.PDE.RicciFlow
