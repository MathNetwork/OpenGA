import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.ConnectionTrace


set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}














section GeometryFormula510

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




omit [NeZero (Module.finrank ℝ E)] in
theorem formula510_of_connTraceField
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace rawTrace actionTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
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
            (I := I) g (connTraceField (I := I) g A) x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
            (I := I) (connTraceField (I := I) g A) potential x =
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
      potentialVariation metricVariationTrace metricVariationRicciHess :=
  formula510_of_connTrace (I := I) g hpotential hq
    (connTraceField (I := I) g A)
    hmeas hfirst hfinal_int hdiv_int hshift_int hcorr_int
    hdivTrace hactionTrace hweighted hlap hgradSq hshift hqeq





omit [NeZero (Module.finrank ℝ E)] in
theorem formula510_of_trace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      weightedDivergenceTrace shiftedTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
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
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x =
          connTraceRawDiv (I := I) g A x -
            connTraceAction (I := I) g A potential x)
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
  exact formula510_of_connTraceField (I := I) g A hpotential hq hmeas
    hfirst hfinal_int hdiv_int hshift_int hcorr_int
    (rawTrace := connTraceRawDiv (I := I) g A)
    (actionTrace := connTraceAction (I := I) g A potential)
    (fun x => rfl)
    (connTraceAction_eq (I := I) g A potential)
    hweighted hlap hgradSq hshift hqeq








omit [NeZero (Module.finrank ℝ E)] in
theorem formula510_of_components
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      shiftedTrace q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hfirst :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess
            (christoffelWeightedDivergenceTrace (I := I) g
              nablaChristoffelVariation christoffelVariation gradPotential)
            shiftedTrace x
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
      Integrable
        (christoffelWeightedDivergenceTrace (I := I) g
          nablaChristoffelVariation christoffelVariation gradPotential)
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
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p)
    (hzero : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      inverseMetricCovDerivForMetricCompInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) g x a b
            (extChartAt I x y))
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x)
        x d i j = 0)
    (hNabla : ∀ x : M, ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        extDerivFun (I := I) (compFun (I := I) A x k i j) x
            (coordinateFrameAt (I := I) x d x) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ x : M, ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k)
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
  have hraw :
      ∀ x : M,
        connTraceRawDiv (I := I) g A x =
          gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x :=
    connTraceRaw_of_components (I := I)
      (cov := DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) g rfl A
      nablaChristoffelVariation hzero hNabla hGamma
  have hweighted :
      ∀ x : M,
        christoffelWeightedDivergenceTrace (I := I) g
            nablaChristoffelVariation christoffelVariation gradPotential x =
          connTraceRawDiv (I := I) g A x -
            connTraceAction (I := I) g A potential x :=
    weightedTrace_of_raw (I := I) g A potential nablaChristoffelVariation
      christoffelVariation gradPotential hraw hA hgrad
  exact formula510_of_trace (I := I) g A
    (weightedDivergenceTrace :=
      christoffelWeightedDivergenceTrace (I := I) g
        nablaChristoffelVariation christoffelVariation gradPotential)
    hpotential hq hmeas hfirst hfinal_int hdiv_int hshift_int hcorr_int
    hweighted hlap hgradSq hshift hqeq








omit [NeZero (Module.finrank ℝ E)] in
theorem formula510_producer
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    {s0 : Real}
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    {scalarCurvaturePath lapPotentialPath gradPotentialNormSqPath
      potentialPath : Real -> M -> Real}
    {firstVariation : Real}
    {scalarCurvature lapPotential gradPotentialNormSq potential
      potentialVariation metricVariationTrace metricVariationRicciHess
      shiftedTrace q scalarCurvatureVariation lapPotentialVariation
      gradPotentialNormSqVariation : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)))
    (hfirstVariation :
      firstVariation =
        ∫ x,
          expWeightedIntegralVariationIntegrand
            (potentialPath s0) potentialVariation metricVariationTrace
            (fFunctionalBracket (scalarCurvaturePath s0)
              (gradPotentialNormSqPath s0))
            (fFunctionalBracketVariation scalarCurvatureVariation
              gradPotentialNormSqVariation) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s0))
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
            christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
              nablaChristoffelVariation christoffelVariation gradPotential x +
            shiftedTrace x)
    (hfinal_int :
      Integrable
        (fFunctionalFormula510Integrand scalarCurvature lapPotential
          gradPotentialNormSq potentialVariation metricVariationTrace
          metricVariationRicciHess)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hdiv_int :
      Integrable
        (christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
          nablaChristoffelVariation christoffelVariation gradPotential)
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hshift_int :
      Integrable shiftedTrace
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hcorr_int :
      Integrable
        (fun x : M =>
          expWeightedMeasureVariationFactor potentialVariation
            metricVariationTrace x *
            (lapPotential x - gradPotentialNormSq x))
        (expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential))
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p)
    (hzero : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      inverseMetricCovDerivForMetricCompInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) (G.metric s0) x a b
            (extChartAt I x y))
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) (G.metric s0))
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x)
        x d i j = 0)
    (hNabla : ∀ x : M, ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        extDerivFun (I := I) (compFun (I := I) A x k i j) x
            (coordinateFrameAt (I := I) x d x) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) (G.metric s0))
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) (G.metric s0))
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) (G.metric s0))
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ x : M, ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) (G.metric s0))
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) (G.metric s0))
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k)
    (hlap :
      ∀ x : M,
        lapPotential x =
          DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
            (I := I) (G.metric s0) hpotential x)
    (hgradSq :
      ∀ x : M,
        gradPotentialNormSq x =
          (G.metric s0).inner x
            ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
              (I := I) (G.metric s0) hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x)
            ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
              (I := I) (G.metric s0) hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) x))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
            (I := I) (G.metric s0) hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    FFunctionalFormula510
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0)) potential)
      firstVariation scalarCurvature lapPotential gradPotentialNormSq
      potentialVariation metricVariationTrace metricVariationRicciHess := by
  have hfirst_pre :
      firstVariation =
        ∫ x,
          fFunctionalPre510Integrand scalarCurvature lapPotential
            gradPotentialNormSq potentialVariation metricVariationTrace
            metricVariationRicciHess
            (christoffelWeightedDivergenceTrace (I := I) (G.metric s0)
              nablaChristoffelVariation christoffelVariation gradPotential)
            shiftedTrace x
          ∂(expNegPotentialWeightedMeasure
              (riemannianVolumeMeasure (I := I) (M := M) (G.metric s0))
              potential) := by
    refine hfirstVariation.trans ?_
    exact firstVar_pre510_ibp (I := I) (M := M) G hmeas hmeas_near
      hibp_near hscalar_deriv hgrad_deriv hlap_deriv hpotential_deriv
      htrace hmetric_reg horig_reg hclosed_reg hpotential0 hscalar0 hlap0
      hclosed_variation
  exact formula510_of_components (I := I) (G.metric s0) A
    nablaChristoffelVariation christoffelVariation gradPotential
    hpotential hq hmeas hfirst_pre
    hfinal_int hdiv_int hshift_int hcorr_int hA hgrad
    hzero hNabla hGamma hlap hgradSq hshift hqeq

end GeometryFormula510

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
