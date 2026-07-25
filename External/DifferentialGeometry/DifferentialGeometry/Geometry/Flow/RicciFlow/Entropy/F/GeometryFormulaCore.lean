import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.Formula510Core


set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}








section GeometryFormula510

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩







omit [InnerProductSpace ℝ E] in
theorem firstVariationIntegral_eq_pre510
    [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      gradPotentialNormSqVariation : M -> Real}
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hgrad0 : gradPotentialNormSqPath s0 = gradPotentialNormSq)
    (hpotential0 : potentialPath s0 = potential)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hvariation :
      ∀ x : M,
        fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x +
            (lapPotential x - gradPotentialNormSq x) *
              expWeightedMeasureVariationFactor potentialVariation
                metricVariationTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  calc
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
        =
      ∫ x,
        expNegPotentialDensity potential x *
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) := by
      simp only [volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily, hscalar0, hgrad0, hpotential0]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (expWeightedIntegralVariation_eq_pre510 (M := M)
          (hvariation := hvariation))
    _ =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
      exact (expNegPotentialWeightedMeasure_integral_eq_base
        (mu := riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
        (potential := potential)
        (integrand :=
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace)
        hmeas).symm







omit [InnerProductSpace ℝ E] in
theorem closedIntegral_eq_pre510
    [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace closedBracketVariation : M -> Real}
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hvariation :
      ∀ x : M,
        closedBracketVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          closedBracketVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  calc
    (∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          closedBracketVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
        =
      ∫ x,
        expNegPotentialDensity potential x *
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) := by
      simp only [volumeMeasureFamily, metricFamilyForMeasure,
        riemannianMeasureFamily]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (expWeightedClosedVariation_eq_pre510 (M := M)
          (hvariation := hvariation))
    _ =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
      exact (expNegPotentialWeightedMeasure_integral_eq_base
        (mu := riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
        (potential := potential)
        (integrand :=
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace)
        hmeas).symm





omit [InnerProductSpace ℝ E] in
theorem firstVar_pre510_closed
    [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      gradPotentialNormSqVariation closedBracketVariation : M -> Real}
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hclosed_compare :
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          closedBracketVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
    (hclosed_variation :
      ∀ x : M,
        closedBracketVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  rw [hclosed_compare]
  exact closedIntegral_eq_pre510 (I := I) (M := M) G hmeas hclosed_variation



theorem bracketClosed_eventually
    {muPath : Real -> Measure M}
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {s0 : Real}
    (hmeas :
      ∀ᶠ s in nhds s0,
        AEMeasurable
          (fun x : M =>
            ENNReal.ofReal (expNegPotentialDensity (potentialPath s) x))
          (muPath s))
    (hibp :
      ∀ᶠ s in nhds s0,
        (∫ x,
          fFunctionalBracket (scalarCurvaturePath s)
            (gradPotentialNormSqPath s) x
          ∂(expNegPotentialWeightedMeasure (muPath s)
              (potentialPath s))) =
        ∫ x,
          fFunctionalClosedBracket (scalarCurvaturePath s)
            (lapPotentialPath s) x
          ∂(expNegPotentialWeightedMeasure (muPath s)
              (potentialPath s))) :
    (fun s : Real =>
      ∫ x,
        expNegPotentialDensity (potentialPath s) x *
          fFunctionalBracket (scalarCurvaturePath s)
            (gradPotentialNormSqPath s) x
        ∂(muPath s)) =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x
          ∂(muPath s) := by
  filter_upwards [hmeas, hibp] with s hmeas_s hibp_s
  calc
    (∫ x,
      expNegPotentialDensity (potentialPath s) x *
        fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x
      ∂(muPath s))
        =
      ∫ x,
        fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x
        ∂(expNegPotentialWeightedMeasure (muPath s)
            (potentialPath s)) := by
        exact (expNegPotentialWeightedMeasure_integral_eq_base
          (mu := muPath s) (potential := potentialPath s)
          (integrand :=
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s)) hmeas_s).symm
    _ =
      ∫ x,
        fFunctionalClosedBracket (scalarCurvaturePath s)
          (lapPotentialPath s) x
        ∂(expNegPotentialWeightedMeasure (muPath s)
            (potentialPath s)) := hibp_s
    _ =
      ∫ x,
        expNegPotentialDensity (potentialPath s) x *
          fFunctionalClosedBracket (scalarCurvaturePath s)
            (lapPotentialPath s) x
        ∂(muPath s) := by
        exact expNegPotentialWeightedMeasure_integral_eq_base
          (mu := muPath s) (potential := potentialPath s)
          (integrand :=
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s)) hmeas_s




omit [InnerProductSpace ℝ E] in
theorem closedCompare
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential potential
      scalarCurvatureVariation lapPotentialVariation
      gradPotentialNormSqVariation potentialVariation metricVariationTrace :
      M -> Real}
    (hbase_eq :
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s)) =ᶠ[nhds s0]
        fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalClosedBracket (scalarCurvaturePath s)
                (lapPotentialPath s) x
            ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (horig_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0)
    (hclosed_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0)
    (hpotential0 : potentialPath s0 = potential)
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hlap0 : lapPotentialPath s0 = lapPotential) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          (fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0) := by
  have horig :=
    fFunctionalBaseIntegral_hasDerivAt_at (I := I) (M := M) G
      hscalar_deriv hgrad_deriv hpotential_deriv htrace hmetric_reg horig_reg
  have hclosed :=
    closedBase_deriv (I := I) (M := M) G
      hscalar_deriv hlap_deriv hpotential_deriv htrace hmetric_reg
      hclosed_reg
  have hclosed_orig :
      HasDerivAt
        (fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalBracket (scalarCurvaturePath s)
                (gradPotentialNormSqPath s) x
            ∂(volumeMeasureFamily (I := I) (M := M) G s))
        (∫ x,
          expWeightedIntegralVariationIntegrand
            (potentialPath s0) potentialVariation metricVariationTrace
            (fFunctionalClosedBracket (scalarCurvaturePath s0)
              (lapPotentialPath s0))
            (fFunctionalClosedBracketVariation scalarCurvatureVariation
              lapPotentialVariation) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s0))
        s0 :=
    hclosed.congr_of_eventuallyEq hbase_eq
  have hderiv_eq := horig.unique hclosed_orig
  calc
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
        =
      ∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalClosedBracket (scalarCurvaturePath s0)
            (lapPotentialPath s0))
          (fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0) := hderiv_eq
    _ =
      ∫ x,
        expWeightedIntegralVariationIntegrand potential potentialVariation
          metricVariationTrace
          (fFunctionalClosedBracket scalarCurvature lapPotential)
          (fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0) := by
        simp [hpotential0, hscalar0, hlap0]



omit [InnerProductSpace ℝ E] in
theorem firstVar_pre510_weighted
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      lapPotentialVariation gradPotentialNormSqVariation : M -> Real}
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hbase_eq :
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s)) =ᶠ[nhds s0]
        fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalClosedBracket (scalarCurvaturePath s)
                (lapPotentialPath s) x
            ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (horig_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0)
    (hclosed_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0)
    (hpotential0 : potentialPath s0 = potential)
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hlap0 : lapPotentialPath s0 = lapPotential)
    (hclosed_variation :
      ∀ x : M,
        fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  apply firstVar_pre510_closed (I := I) (M := M) G hmeas
  · exact closedCompare (I := I) (M := M) G hbase_eq
      hscalar_deriv hgrad_deriv hlap_deriv hpotential_deriv htrace
      hmetric_reg horig_reg hclosed_reg hpotential0 hscalar0 hlap0
  · exact hclosed_variation




omit [InnerProductSpace ℝ E] in
theorem firstVar_pre510_ibp
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace scalarCurvatureVariation
      lapPotentialVariation gradPotentialNormSqVariation : M -> Real}
    (hmeas0 :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hmeas_near :
      ∀ᶠ s in nhds s0,
        AEMeasurable
          (fun x : M =>
            ENNReal.ofReal (expNegPotentialDensity (potentialPath s) x))
          (volumeMeasureFamily (I := I) (M := M) G s))
    (hibp_near :
      ∀ᶠ s in nhds s0,
        (∫ x,
          fFunctionalBracket (scalarCurvaturePath s)
            (gradPotentialNormSqPath s) x
          ∂(expNegPotentialWeightedMeasure
              (volumeMeasureFamily (I := I) (M := M) G s)
              (potentialPath s))) =
        ∫ x,
          fFunctionalClosedBracket (scalarCurvaturePath s)
            (lapPotentialPath s) x
          ∂(expNegPotentialWeightedMeasure
              (volumeMeasureFamily (I := I) (M := M) G s)
              (potentialPath s)))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (horig_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0)
    (hclosed_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0)
    (hpotential0 : potentialPath s0 = potential)
    (hscalar0 : scalarCurvaturePath s0 = scalarCurvature)
    (hlap0 : lapPotentialPath s0 = lapPotential)
    (hclosed_variation :
      ∀ x : M,
        fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation x =
          -metricVariationRicciHess x +
            weightedDivergenceTrace x + shiftedTrace x) :
    (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) =
      ∫ x,
        fFunctionalPre510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
            potential) := by
  apply firstVar_pre510_weighted (I := I) (M := M) G hmeas0
  · exact bracketClosed_eventually
      (M := M)
      (muPath := volumeMeasureFamily (I := I) (M := M) G)
      (scalarCurvaturePath := scalarCurvaturePath)
      (lapPotentialPath := lapPotentialPath)
      (gradPotentialNormSqPath := gradPotentialNormSqPath)
      (potentialPath := potentialPath)
      (s0 := s0)
      hmeas_near hibp_near
  · exact hscalar_deriv
  · exact hgrad_deriv
  · exact hlap_deriv
  · exact hpotential_deriv
  · exact htrace
  · exact hmetric_reg
  · exact horig_reg
  · exact hclosed_reg
  · exact hpotential0
  · exact hscalar0
  · exact hlap0
  · exact hclosed_variation




omit [InnerProductSpace ℝ E] in
theorem formula510_of_connTrace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace rawTrace actionTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess weightedDivergenceTrace shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdiv_int :
      Integrable weightedDivergenceTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential))
    (hdivTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.divergence_g
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x)
    (hlap :
      ∀ x : M,
        lapPotential x =
          DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          g.inner x
            ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  have hdiv_zero :
      ∫ x, weightedDivergenceTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 :=
    weightedDivZero_of_connTrace (I := I) g hpotential traceVec hmeas
      hdivTrace hactionTrace hweighted
  have hshift_eq :
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
                (I := I) g hpotential x -
              g.inner x
                ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
                ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) :=
    shiftIntEq (I := I) g hpotential hq hmeas hshift hqeq
  have hshift_final :
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
    calc
      ∫ x, shiftedTrace x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
                (I := I) g hpotential x -
              g.inner x
                ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
                ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                  (I := I) g hpotential :
                  Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := hshift_eq
      _ = ∫ x,
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall ?_
        intro x
        simp [hlap x, hgradSq x]
  exact formula510_of_ints
    (weightedMeasure :=
      expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)
    hfirst hfinal_int hdiv_int hshift_int hcorr_int hdiv_zero hshift_final

end GeometryFormula510

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
