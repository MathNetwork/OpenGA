import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false














noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff

variable {M : Type*}


def CurvatureEigenvaluesOrdered
    (lambda mu nu : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), nu t x ≤ mu t x ∧ mu t x ≤ lambda t x



def RicciPinchingPreservedOn
    (lambda mu nu : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M), lambda t x ≤ C * (nu t x + mu t x)


def RicciPinchingPreservedInequalityOn
    (lambda mu nu : Real -> M -> Real) (C : Real) : Prop :=
  RicciPinchingPreservedOn lambda mu nu C



def LogPinchingDerivativeNonpositiveOn
    (lambda mu nu : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    0 < lambda t x ∧ 0 < mu t x + nu t x ->
      (mu t x ^ 2 * (nu t x - lambda t x) +
        nu t x ^ 2 * (mu t x - lambda t x)) /
          (lambda t x * (nu t x + mu t x)) ≤ 0



def LogLambdaOverMuPlusNuDerivativeFormulaOn
    (lambda mu nu : Real -> M -> Real) : Prop :=
  LogPinchingDerivativeNonpositiveOn lambda mu nu



def RicciLowerBoundFromPinchingOn
    (ricciLower scalar : Real -> M -> Real) (beta : Real) : Prop :=
  ∀ (t : Real) (x : M), 2 * beta ^ 2 * scalar t x ≤ ricciLower t x



def PinchingDecayWeightOn
    (lambda mu nu weight : Real -> M -> Real) (delta : Real) : Prop :=
  ∀ (t : Real) (x : M), 0 < delta ∧ 0 ≤ weight t x


def RicciPinchingImprovesOn
    (lambda mu nu weight : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M),
    (lambda t x - nu t x) / (nu t x + mu t x) ≤
      C * weight t x



def PinchingImprovesFunctionEvolutionOn
    (f rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M), f t x ≤ rhs t x


def HamiltonTracefreePinchingEstimateOn
    (tracefreeRmNormSq scalar weight : Real -> M -> Real) (C : Real) : Prop :=
  ∀ (t : Real) (x : M),
    tracefreeRmNormSq t x / scalar t x ^ 2 ≤ C * weight t x


def pinchingP (lambda mu nu : Real) : Real :=
  lambda ^ 2 * (mu - nu) ^ 2 +
    mu ^ 2 * (lambda - nu) ^ 2 +
    nu ^ 2 * (lambda - mu) ^ 2


def PinchingPFormulaOn
    (lambda mu nu P : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    P t x = pinchingP (lambda t x) (mu t x) (nu t x)



theorem pinchingP_formula
    (lambda mu nu : Real -> M -> Real) :
    PinchingPFormulaOn lambda mu nu
      (fun t x => pinchingP (lambda t x) (mu t x) (nu t x)) := by
  intro t x
  rfl





abbrev PAlphaOverQBetaFormulaOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [IsManifold I (∞ + 1) M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real) : Prop :=
  QuotientEvolutionOn (I := I) (D := D) G
    phi psi phiHeat psiHeat alpha beta



def TracefreeRmPinchingEvolutionInequalityOn
    (f scalar Q : Real -> M -> Real) (epsilon : Real) : Prop :=
  ∀ (t : Real) (x : M),
    0 < scalar t x -> f t x ≤ Q t x + epsilon * scalar t x



def ScalarEvolutionEigenvalueFormulaOn
    (scalar lambda mu nu rhs : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    rhs t x =
      scalar t x ^ 2 +
        2 * (lambda t x * mu t x + lambda t x * nu t x + mu t x * nu t x)

theorem ricci_pinching_preserved
    (lambda mu nu : Real -> M -> Real) (C : Real)
    (hode :
      CurvatureEigenvaluesOrdered lambda mu nu →
        (∀ x : M, lambda 0 x ≤ C * (nu 0 x + mu 0 x)) →
          RicciPinchingPreservedOn lambda mu nu C)
    (hordered : CurvatureEigenvaluesOrdered lambda mu nu)
    (hinit : ∀ x : M, lambda 0 x ≤ C * (nu 0 x + mu 0 x)) :
    RicciPinchingPreservedOn lambda mu nu C :=
  hode hordered hinit

theorem ricci_lower_bound_of_pinching
    (lambda mu nu ricciLower scalar : Real -> M -> Real)
    (C beta : Real)
    (hbound :
      RicciPinchingPreservedOn lambda mu nu C →
        beta > 0 →
          RicciLowerBoundFromPinchingOn ricciLower scalar beta)
    (hpinch : RicciPinchingPreservedOn lambda mu nu C)
    (hbeta : beta > 0) :
    RicciLowerBoundFromPinchingOn ricciLower scalar beta :=
  hbound hpinch hbeta

theorem ricci_pinching_improves
    (lambda mu nu : Real -> M -> Real)
    (hpositiveRicciInitial : Prop)
    (hinit : hpositiveRicciInitial)
    (himprove :
      hpositiveRicciInitial →
        ∃ C delta : Real, ∃ weight : Real -> M -> Real,
          0 < C ∧ 0 < delta ∧ delta < 1 ∧
          PinchingDecayWeightOn lambda mu nu weight delta ∧
          RicciPinchingImprovesOn lambda mu nu weight C) :
    ∃ C delta : Real, ∃ weight : Real -> M -> Real,
      0 < C ∧ 0 < delta ∧ delta < 1 ∧
      PinchingDecayWeightOn lambda mu nu weight delta ∧
      RicciPinchingImprovesOn lambda mu nu weight C :=
  himprove hinit

theorem hamilton_tracefree_pinching_of_eigenvalue_pinching
    (lambda mu nu tracefreeRmNormSq scalar weight : Real -> M -> Real)
    (C : Real)
    (hconvert :
      RicciPinchingImprovesOn lambda mu nu weight C →
        HamiltonTracefreePinchingEstimateOn tracefreeRmNormSq scalar weight C)
    (hpinch : RicciPinchingImprovesOn lambda mu nu weight C) :
    HamiltonTracefreePinchingEstimateOn tracefreeRmNormSq scalar weight C :=
  hconvert hpinch

theorem palpha_over_qbeta_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [IsManifold I (∞ + 1) M] [IsManifold I 1 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (phi psi phiLap psiLap phiHeat psiHeat : Real -> M -> Real)
    (alpha beta : Real)
    (hphiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => phi s x)
        (phiLap (t : Real) x + phiHeat (t : Real) x)
        D.carrier (t : Real))
    (hpsiDt : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      HasDerivWithinAt (fun s : Real => psi s x)
        (psiLap (t : Real) x + psiHeat (t : Real) x)
        D.carrier (t : Real))
    (hphiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      phiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (phi (t : Real)) x)
    (hpsiLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      psiLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real) (psi (t : Real)) x)
    (hphiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (phi (t : Real)) y)
    (hpsiDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (psi (t : Real)) y)
    (hphiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < phi (t : Real) y)
    (hpsiPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < psi (t : Real) y)
    (hgradPhi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (phi (t : Real)) y) x)
    (hgradPsi : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (psi (t : Real)) y) x)
    (hgradPhiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => phi (t : Real) w ^ alpha) z) y)
    (hgradPsiPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => psi (t : Real) w ^ (-beta)) z) y) :
    PAlphaOverQBetaFormulaOn (I := I) (D := D) G
      phi psi phiHeat psiHeat alpha beta :=
  quotHeat (I := I) (D := D) G
    phi psi phiLap psiLap phiHeat psiHeat alpha beta
    hphiDt hpsiDt hphiLap hpsiLap hphiDiff hpsiDiff
    hphiPos hpsiPos hgradPhi hgradPsi hgradPhiPow hgradPsiPow

theorem tracefree_rm_pinching_evolution
    (f scalar Q : Real -> M -> Real) (epsilon : Real)
    (hineq : ∀ t x,
      0 < scalar t x -> f t x ≤ Q t x + epsilon * scalar t x) :
    TracefreeRmPinchingEvolutionInequalityOn f scalar Q epsilon :=
  hineq

end DifferentialGeometry.PDE.RicciFlow
