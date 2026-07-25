import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Components

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
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}




def KoszulConnectionVariationInFrame
    (pairDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x i j l,
    pairDt t x i j l =
      christoffelVariationLoweredRHSInFrame nablaRic t x i j l





def ConnectionVariationPairingEquationInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j l : Idx),
    HasDerivWithinAt
      (fun s : Real =>
        (S.family.metric (t : Real)).inner x (frame l x)
          ((S.family.connection s (frame j) x) (frame i x)))
      (christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
      D.carrier
      (t : Real)


def ConnectionVariationPairingEquationInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j l : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          (S.family.metric (t : Real)).inner x (frame l x)
            ((S.family.connection s (frame j) x) (frame i x)))
        (christoffelVariationLoweredRHSInFrame nablaRic (t : Real) x i j l)
        D.carrier
        (t : Real)



omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem connectionPairDt_eq_metricVariationRHS
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j l : Idx) :
    pairDt (t : Real) x i j l =
      connectionVariationLoweredRHSFromMetricVariationInFrame
        metricCovDerivDt (t : Real) x i j l := by
  have htcarrier : (t : Real) ∈ D.carrier := D.regular_subset t.2
  have hL :
      HasDerivWithinAt
        (fun s : Real =>
          2 * connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (2 * pairDt (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    simpa using
      HasDerivWithinAt.const_mul (2 : Real) (hvarDiff t x hx i j l)
  have hL_as_R :
      HasDerivWithinAt
        (fun s : Real =>
          finiteDifferenceKoszulRHSInFrame (I := I) S frame (t : Real) s x i j l)
        (2 * pairDt (t : Real) x i j l)
        D.carrier
        (t : Real) := by
    refine hL.congr ?_ ?_
    · intro s hs
      exact (finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier hs i j l
        ).symm
    · exact (finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier htcarrier i j l).symm
  have hR :
      HasDerivWithinAt
        (fun s : Real =>
          finiteDifferenceKoszulRHSInFrame (I := I) S frame (t : Real) s x i j l)
        (metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j)
        D.carrier
        (t : Real) := by
    unfold finiteDifferenceKoszulRHSInFrame
    exact ((hmetric t x hx i j l).add (hmetric t x hx j i l)).sub
      (hmetric t x hx l i j)
  have hderiv :
      2 * pairDt (t : Real) x i j l =
        metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j := by
    exact (hL_as_R.derivWithin (hunique t)).symm.trans
      (hR.derivWithin (hunique t))
  unfold connectionVariationLoweredRHSFromMetricVariationInFrame
  linarith



omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem connectionVariationPairing_of_metricVariation
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
      forall i j l : Idx,
        HasDerivWithinAt
          (fun s : Real =>
            (S.family.metric (t : Real)).inner x (frame l x)
              ((S.family.connection s (frame j) x) (frame i x)))
          (connectionVariationLoweredRHSFromMetricVariationInFrame
            metricCovDerivDt (t : Real) x i j l)
          D.carrier
          (t : Real) := by
  intro t x hx i j l
  exact (hpair t x hx i j l).congr_deriv
    (connectionPairDt_eq_metricVariationRHS
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt
      hvarDiff hmetric hunique t x hx i j l)



omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem connectionVariationPairing_of_ricciFlow
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (pairDt metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hpair :
      ConnectionPairingDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hvarDiff :
      VariableMetricConnectionDiffDerivativeInFrameOnLocal
        (I := I) S frame u pairDt)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic)
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)) :
    ConnectionVariationPairingEquationInFrameOnLocal
      (I := I) S frame u nablaRic := by
  intro t x hx i j l
  have hmetricVar :=
    connectionVariationPairing_of_metricVariation
      (I := I) S hS frame hframe hu pairDt metricCovDerivDt
      hpair hvarDiff hmetric hunique t x hx i j l
  refine hmetricVar.congr_deriv ?_
  unfold connectionVariationLoweredRHSFromMetricVariationInFrame
    christoffelVariationLoweredRHSInFrame
  rw [hmetricRicci (t : Real) x i j l,
    hmetricRicci (t : Real) x j i l,
    hmetricRicci (t : Real) x l i j]
  ring



omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionVariationPairing_of_koszul
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (pairDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hdt : ConnectionPairingDerivativeInFrameOn (I := I) S frame pairDt)
    (hkoszul : KoszulConnectionVariationInFrame (M := M) pairDt nablaRic) :
    ConnectionVariationPairingEquationInFrameOn
      (I := I) S frame nablaRic := by
  intro t x i j l
  exact (hdt t x i j l).congr_deriv (hkoszul (t : Real) x i j l)

end Components

end DifferentialGeometry.PDE.RicciFlow
