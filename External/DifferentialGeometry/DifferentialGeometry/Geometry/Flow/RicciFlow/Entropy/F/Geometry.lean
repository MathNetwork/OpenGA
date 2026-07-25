import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.Functional


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








section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




omit [InnerProductSpace ℝ E] in
theorem weightedIBP
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hlap :
      Integrable (fun x : M =>
        expNegPotentialDensity potential x *
          DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
            (I := I) g hpotential x)
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hgrad :
      Integrable (fun x : M =>
        expNegPotentialDensity potential x *
          g.inner x
            ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
              (I := I) g hpotential :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
      (DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
          (I := I) g hpotential x -
        g.inner x
          ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
            (I := I) g hpotential :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
            (I := I) g hpotential :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  apply expWeightedIBP_of_baseIntegral_zero
    (mu := riemannianVolumeMeasure (I := I) (M := M) g)
    (potential := potential)
    (lapPotential :=
      DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
        (I := I) g hpotential)
    (gradPotentialNormSq := fun x : M =>
      g.inner x
        ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
          (I := I) g hpotential :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
          (I := I) g hpotential :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
  · exact hmeas
  · simpa [expNegPotentialDensity] using
      DifferentialGeometry.Integral.DivergenceTheorem.expNegIBP
        (I := I) g hpotential hlap hgrad




omit [TopologicalSpace M] in
theorem bracket_eq_closed_of_ibp [MeasurableSpace M]
    (mu : Measure M)
    (scalarCurvature lapPotential gradPotentialNormSq potential : M -> Real)
    (hscalar_int :
      Integrable scalarCurvature
        (expNegPotentialWeightedMeasure mu potential))
    (hlap_int :
      Integrable lapPotential
        (expNegPotentialWeightedMeasure mu potential))
    (hgrad_int :
      Integrable gradPotentialNormSq
        (expNegPotentialWeightedMeasure mu potential))
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x)
        ∂(expNegPotentialWeightedMeasure mu potential) = 0) :
    (∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x
      ∂(expNegPotentialWeightedMeasure mu potential)) =
      ∫ x, fFunctionalClosedBracket scalarCurvature lapPotential x
        ∂(expNegPotentialWeightedMeasure mu potential) := by
  let μw := expNegPotentialWeightedMeasure mu potential
  have hdiff :
      (∫ x, lapPotential x ∂μw) =
        ∫ x, gradPotentialNormSq x ∂μw := by
    have hsub :
        (∫ x, (lapPotential x - gradPotentialNormSq x) ∂μw) =
          (∫ x, lapPotential x ∂μw) -
            ∫ x, gradPotentialNormSq x ∂μw := by
      exact integral_sub hlap_int hgrad_int
    rw [hsub] at hibp
    linarith
  calc
    (∫ x, fFunctionalBracket scalarCurvature gradPotentialNormSq x ∂μw)
        =
      ∫ x, scalarCurvature x + gradPotentialNormSq x ∂μw := by
        rfl
    _ =
      (∫ x, scalarCurvature x ∂μw) +
        ∫ x, gradPotentialNormSq x ∂μw := by
        exact integral_add hscalar_int hgrad_int
    _ =
      (∫ x, scalarCurvature x ∂μw) +
        ∫ x, lapPotential x ∂μw := by
        rw [hdiff]
    _ =
      ∫ x, scalarCurvature x + lapPotential x ∂μw := by
        exact (integral_add hscalar_int hlap_int).symm
    _ =
      ∫ x, fFunctionalClosedBracket scalarCurvature lapPotential x ∂μw := by
        rfl



omit [InnerProductSpace ℝ E] in
theorem weightedGreen
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
        DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
          (I := I) g hq x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        q x *
          (-DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
              (I := I) g hpotential x +
            g.inner x
              ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let gradSq : M -> Real := fun x =>
    g.inner x
      ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
        (I := I) g hpotential :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
        (I := I) g hpotential :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hq x)
    hmeas]
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      q x *
        (-DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
            (I := I) g hpotential x + gradSq x))
    hmeas]
  calc
    ∫ x,
        expNegPotentialDensity potential x *
          DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hq x ∂μ =
      ∫ x,
        q x *
          (expNegPotentialDensity potential x *
            (-DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
                (I := I) g hpotential x + gradSq x)) ∂μ := by
      simpa [μ, expNegPotentialDensity, gradSq] using
        DifferentialGeometry.Integral.DivergenceTheorem.expNegGreen
          (I := I) g hpotential hq
    _ =
      ∫ x,
        expNegPotentialDensity potential x *
          (q x *
            (-DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
                (I := I) g hpotential x + gradSq x)) ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      ring




omit [InnerProductSpace ℝ E] in
theorem weightedDivZero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace : M -> Real}
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdiv :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.divergence_g
            (I := I) g X x =
          expNegPotentialDensity potential x * weightedDivergenceTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  rw [expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := weightedDivergenceTrace) hmeas]
  calc
    ∫ x, expNegPotentialDensity potential x * weightedDivergenceTrace x ∂μ =
        ∫ x, DifferentialGeometry.Integral.DivergenceTheorem.divergence_g
          (I := I) g X x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (hdiv x).symm
    _ = 0 := by
      simpa [μ] using
        DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact
          (I := I) g X


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem expNegPotentialDensity_contMDiff
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) :
    ContMDiff I 𝓘(Real, Real) ∞ (expNegPotentialDensity potential) := by
  simpa [expNegPotentialDensity] using
    Real.contDiff_exp.contMDiff.comp hpotential.neg


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem tangentSectionAction_expNeg
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
        (I := I) X (expNegPotentialDensity potential) x =
      -expNegPotentialDensity potential x *
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
          (I := I) X potential x := by
  have hmf :=
    DifferentialGeometry.Integral.DivergenceTheorem.mfderiv_exp_neg_toLinearMap
      (I := I) (f := potential) (x := x)
      (hpotential.mdifferentiableAt (by simp))
  unfold DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
    expNegPotentialDensity
  change
    extDerivFun (I := I) (fun y : M => Real.exp (-(potential y))) x (X x) =
      -Real.exp (-(potential x)) *
        extDerivFun (I := I) potential x (X x)
  rw [extDerivFun, extDerivFun]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply]
  have happly := congrArg (fun L => L (X x)) hmf
  simpa [smul_eq_mul] using happly





def connTraceVec
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
  DifferentialGeometry.Integral.DivergenceTheorem.smoothSmul
    (I := I) (expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec



omit [InnerProductSpace ℝ E] in
theorem connTraceDivEq
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
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
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∀ x : M,
      DifferentialGeometry.Integral.DivergenceTheorem.divergence_g
          (I := I) g
          (connTraceVec (I := I) hpotential traceVec) x =
        expNegPotentialDensity potential x * weightedDivergenceTrace x := by
  intro x
  rw [connTraceVec]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_smoothSmul
    (I := I) g (expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec x]
  rw [hdivTrace x]
  rw [tangentSectionAction_expNeg (I := I) traceVec hpotential x]
  rw [hactionTrace x, hweighted x]
  ring



omit [InnerProductSpace ℝ E] in
theorem weightedDivZero_of_connTrace
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
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
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  exact weightedDivZero (I := I) g
    (connTraceVec (I := I) hpotential traceVec) hmeas
    (connTraceDivEq (I := I) g hpotential traceVec hdivTrace
      hactionTrace hweighted)



omit [InnerProductSpace ℝ E] in
theorem weighted_grad_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q) :
    ∫ x,
        (DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
            (I := I) g hq x -
          g.inner x
            ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
              (I := I) g hq) x)
            ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
              (I := I) g hpotential) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  have hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (ENNReal.continuous_ofReal.comp
      (expNegPotentialDensity_contMDiff (I := I) hpotential).continuous).aemeasurable
  exact weightedDivZero_of_connTrace (I := I) g hpotential
    (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hq)
    hmeas
    (fun x =>
      (DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def
        (I := I) g hq x).symm)
    (fun x =>
      DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_eq_inner_grad_g
        (I := I) g hpotential
        (DifferentialGeometry.Integral.DivergenceTheorem.grad_g (I := I) g hq) x)
    (fun _ => rfl)



omit [InnerProductSpace ℝ E] in
theorem shiftIntEq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q shiftedTrace potentialVariation metricVariationTrace :
      M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
            (I := I) g hq x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
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
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  calc
    ∫ x, shiftedTrace x
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hq x
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hshift
    _ = ∫ x,
        q x *
          (-DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
              (I := I) g hpotential x +
            g.inner x
              ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      exact weightedGreen (I := I) g hpotential hq hmeas
    _ = ∫ x,
        expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (DifferentialGeometry.Integral.DivergenceTheorem.Δ_g
              (I := I) g hpotential x -
            g.inner x
              ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Integral.DivergenceTheorem.grad_g
                (I := I) g hpotential :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      dsimp
      rw [hqeq x]
      unfold expWeightedMeasureVariationFactor
      ring


omit [InnerProductSpace ℝ E] in
theorem expWeightedMeasureIntegral_hasDerivAt_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {potentialPath phiPath : Real -> M -> Real}
    {s0 : Real}
    {potentialVariation metricVariationTrace phiVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (hphi_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => phiPath s x)
          (phiVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_reg :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x * phiPath s x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (phiPath s0) phiVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 := by
  have hvol :=
    volume_variation_formula_clean_at
      (I := I) (M := M) G
      (f := fun s : Real => fun x : M =>
        expNegPotentialDensity (potentialPath s) x * phiPath s x)
      (t₀ := s0) hmetric_reg hintegrand_reg
  refine hvol.congr_deriv ?_
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hdens :=
    expNegPotentialDensity_hasDerivAt
      (M := M) (potentialPath := potentialPath)
      (potentialVariation := potentialVariation)
      hpotential_deriv x
  have hprod :
      HasDerivAt
        (fun s : Real =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        (-(potentialVariation x) *
            expNegPotentialDensity (potentialPath s0) x * phiPath s0 x +
          expNegPotentialDensity (potentialPath s0) x * phiVariation x)
        s0 :=
    hdens.mul (hphi_deriv x)
  have hderiv := hprod.deriv
  change
    deriv
        (fun s : Real =>
          expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0 +
      1 / 2 * traceTimeDerivMetricAt (I := I) G s0 x *
        (expNegPotentialDensity (potentialPath s0) x * phiPath s0 x) =
    expWeightedIntegralVariationIntegrand
      (potentialPath s0) potentialVariation metricVariationTrace
      (phiPath s0) phiVariation x
  rw [hderiv, htrace x]
  unfold expWeightedIntegralVariationIntegrand
    expWeightedMeasureVariationFactor
  ring


def fFunctionalBracketVariation
    (scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real) :
    M -> Real :=
  fun x => scalarCurvatureVariation x + gradPotentialNormSqVariation x

omit [TopologicalSpace M] in
theorem fFunctionalBracket_hasDerivAt
    {scalarCurvaturePath gradPotentialNormSqPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x)
      (fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hgrad_deriv x)
  simpa [fFunctionalBracket, fFunctionalBracketVariation] using h


omit [TopologicalSpace M] in
theorem closedBracket_deriv
    {scalarCurvaturePath lapPotentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation lapPotentialVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        fFunctionalClosedBracket (scalarCurvaturePath s)
          (lapPotentialPath s) x)
      (fFunctionalClosedBracketVariation scalarCurvatureVariation
        lapPotentialVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hlap_deriv x)
  simpa [fFunctionalClosedBracket, fFunctionalClosedBracketVariation] using h




omit [InnerProductSpace ℝ E] in
theorem fFunctionalBaseIntegral_hasDerivAt_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
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
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
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
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 :=
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      fFunctionalBracket (scalarCurvaturePath s)
        (gradPotentialNormSqPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation)
    hpotential_deriv
    (fFunctionalBracket_hasDerivAt
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (gradPotentialNormSqPath := gradPotentialNormSqPath)
      (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (gradPotentialNormSqVariation := gradPotentialNormSqVariation)
      hscalar_deriv hgrad_deriv)
    htrace hmetric_reg hintegrand_reg




omit [InnerProductSpace ℝ E] in
theorem closedBase_deriv
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation lapPotentialVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
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
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x
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
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      fFunctionalClosedBracket (scalarCurvaturePath s)
        (lapPotentialPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      fFunctionalClosedBracketVariation scalarCurvatureVariation
        lapPotentialVariation)
    hpotential_deriv
    (closedBracket_deriv
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (lapPotentialPath := lapPotentialPath) (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (lapPotentialVariation := lapPotentialVariation)
      hscalar_deriv hlap_deriv)
    htrace hmetric_reg hintegrand_reg



omit [TopologicalSpace M] in
theorem FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    [MeasurableSpace M]
    {muPath : Real -> Measure M}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 firstVariation : Real}
    (hbase_eq :
      (fun s : Real =>
        fFunctional (muPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(muPath s))
    (hbase :
      HasDerivAt
        (fun s : Real =>
          ∫ x,
            expNegPotentialDensity (potentialPath s) x *
              fFunctionalBracket (scalarCurvaturePath s)
                (gradPotentialNormSqPath s) x
            ∂(muPath s))
        firstVariation s0) :
    FFunctionalHasFirstVariationAt muPath scalarCurvaturePath
      gradPotentialNormSqPath potentialPath s0 firstVariation := by
  unfold FFunctionalHasFirstVariationAt fFunctionalAlong
  exact hbase.congr_of_eventuallyEq hbase_eq


omit [InnerProductSpace ℝ E] in
theorem FFunctionalHasFirstVariationAt_of_volumeVariation
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hbase_eq :
      (fun s : Real =>
        fFunctional (volumeMeasureFamily (I := I) (M := M) G s)
          (scalarCurvaturePath s) (gradPotentialNormSqPath s)
          (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
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
    (hintegrand_reg :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          expNegPotentialDensity (potentialPath s) x *
            fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    FFunctionalHasFirstVariationAt
      (volumeMeasureFamily (I := I) (M := M) G)
      scalarCurvaturePath gradPotentialNormSqPath potentialPath s0
      (∫ x,
        expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) := by
  exact FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    (M := M)
    (muPath := volumeMeasureFamily (I := I) (M := M) G)
    hbase_eq
    (fFunctionalBaseIntegral_hasDerivAt_at
      (I := I) (M := M) G
      hscalar_deriv hgrad_deriv hpotential_deriv htrace hmetric_reg
      hintegrand_reg)

end Geometry

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
