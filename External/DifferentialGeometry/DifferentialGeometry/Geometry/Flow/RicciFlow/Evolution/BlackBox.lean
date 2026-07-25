import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false













noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}







structure InverseMetricTimeRegularityBlackBoxInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx) where
  gInvDt : Real -> M -> Idx -> Idx -> Real
  inverseMetricDerivative :
    InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt
  uniqueTimeDerivatives :
    forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)



omit [SigmaCompactSpace M] in
theorem inverseMetricEvolution_of_timeRegularityBlackBox
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InvMetricLocal (I := I) S gInv frame Set.univ)
    (hbb : InverseMetricTimeRegularityBlackBoxInFrameOn (M := M) (Idx := Idx)
      (D := D) gInv) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ :=
  inverseMetricEvolutionEquationInFrame_of_inverse_components
    (I := I) (u := Set.univ) S hS gInv hbb.gInvDt frame
    hbb.inverseMetricDerivative hinv hbb.uniqueTimeDerivatives








structure ConnectionVariationBlackBoxInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) where
  metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real
  metricCovDerivDerivative :
    MetricCovDerivDerivativeComponentsInFrameOnLocal
      (I := I) S frame u metricCovDerivDt
  metricCovDerivRicciFlow :
    MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic



omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem variableMetricConnectionDiffDerivative_of_blackBox
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hbb : ConnectionVariationBlackBoxInFrameOn (I := I) S frame u nablaRic) :
    VariableMetricConnectionDiffDerivativeInFrameOnLocal
      (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) :=
  variableMetricConnectionDiffDerivative_of_metricCovDeriv
    (I := I) S hS frame hframe hu hbb.metricCovDerivDt nablaRic
    hbb.metricCovDerivDerivative hbb.metricCovDerivRicciFlow



omit [SigmaCompactSpace M] in
theorem christoffelEvolution_of_blackBox
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hmetricFrame :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hbb : ConnectionVariationBlackBoxInFrameOn (I := I) S frame u nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolution_of_metricFrameTimeRegularity
    (I := I) S hS gInv gInvDt frame hframe hu
    hbb.metricCovDerivDt nablaRic hmetricFrame
    hbb.metricCovDerivDerivative hbb.metricCovDerivRicciFlow







structure RicciEvolutionTimeRegularityBlackBoxInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) where
  nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real
  ricciVariation :
    RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric)
  contractedCommutators :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciEvolution_of_timeRegularityBlackBox
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hbb : RicciEvolutionTimeRegularityBlackBoxInFrameOn
      (I := I) S Rm04 gInv frame) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv hbb.nabla2Ric) :=
  ricciEvolution_of_variation_commutators
    (I := I) S Rm04 gInv frame hbb.nabla2Ric
    hbb.ricciVariation hbb.contractedCommutators






structure Section62TimeRegularityBlackBoxInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) where
  metricFrame :
    MetricFrameTimeRegularityInFrameOnLocal
      (I := I) S gInv gInvDt frame u
  connection :
    ConnectionVariationBlackBoxInFrameOn (I := I) S frame u nablaRic
  ricci :
    RicciEvolutionTimeRegularityBlackBoxInFrameOn
      (I := I) S Rm04 gInv frame

end Components

end DifferentialGeometry.PDE.RicciFlow
