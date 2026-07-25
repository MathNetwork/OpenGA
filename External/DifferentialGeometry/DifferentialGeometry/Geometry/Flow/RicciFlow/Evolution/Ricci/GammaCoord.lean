import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.GammaAlgebra

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
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

section CoordinateConnectionVariation

def christoffelVariationCovDerivCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (t : Real) (x₀ : M)
    (dir k i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (fun x : M => gammaDt t x i j k) x₀
      (coordinateFrameAt (I := I) x₀ dir x₀) +
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x₀ dir a k *
        gammaDt t x₀ i j a) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x₀ dir i a *
        gammaDt t x₀ a j k) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x₀ dir j a *
        gammaDt t x₀ i a k)



omit [SigmaCompactSpace M] in
private theorem christoffelCoordAt_symm_of_isSolutionOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ i j k =
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ j i k := by
  have htf : DifferentialGeometry.Integral.Connection.IsTorsionFree (I := I)
      (S.family.connection (t : Real)) := by
    simpa [DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt] using
      hS.leviCivita.2 (DifferentialGeometry.Integral.Connection.RealTimeInterval.regularToFlow t)
  have hzero :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff k x₀
          ((S.family.connection (t : Real)).torsion x₀
            (coordinateFrameAt (I := I) x₀ i x₀)
            (coordinateFrameAt (I := I) x₀ j x₀)) = 0 := by
    rw [htf x₀]
    simp
  have hskew := DifferentialGeometry.Integral.Connection.coordinate_torsion_coeff_eq_christoffel_skew
    (I := I) (S.family.connection (t : Real)) x₀ i j k
  rw [hzero] at hskew
  exact sub_eq_zero.mp hskew.symm



omit [SigmaCompactSpace M] [T2Space M] in
private theorem christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelVariation
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (dir i j k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelCoordDerivAt (I := I) (S.family.connection s)
          x₀ dir i j k)
      (extDerivFun (I := I) (fun y : M => rhs (t : Real) y i j k) x₀
        (coordinateFrameAt (I := I) x₀ dir x₀))
      D.carrier
      (t : Real) := by
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  simpa [DifferentialGeometry.Integral.Connection.christoffelCoordDerivAt, DifferentialGeometry.Integral.Connection.christoffelCoordFun] using
    fixedBaseExtDerivTimeDerivativeOnRegular_apply (I := I) (h := hmix i j k)
      (t := (t : Real)) t.2 (x := x₀) hx₀
      (coordinateFrameAt (I := I) x₀ dir x₀)



omit [SigmaCompactSpace M] [T2Space M] in
private theorem christoffelCoordAt_hasDerivWithinAt_of_christoffelVariation
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hvar : ChristoffelVariationEquationInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i j k : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection s) x₀ i j k)
      (rhs (t : Real) x₀ i j k)
      D.carrier
      (t : Real) := by
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  simpa [DifferentialGeometry.Integral.Connection.christoffelCoordAt] using hvar t x₀ hx₀ i j k






omit [SigmaCompactSpace M] in
theorem christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hvar : ChristoffelVariationEquationInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i k j m : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I) (S.family.connection s)
          x₀ i k j m)
      (christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real)) rhs (t : Real) x₀ i m k j -
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real)) rhs (t : Real) x₀ k m i j)
      D.carrier
      (t : Real) := by
  classical
  have hD_i := christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelVariation
    (I := I) S rhs x₀ hmix t i k j m
  have hD_k := christoffelCoordDerivAt_hasDerivWithinAt_of_christoffelVariation
    (I := I) S rhs x₀ hmix t k i j m
  have hΓ :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt
          (fun s : Real =>
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ a b c)
          (rhs (t : Real) x₀ a b c) D.carrier (t : Real) := by
    intro a b c
    exact christoffelCoordAt_hasDerivWithinAt_of_christoffelVariation
      (I := I) S rhs x₀ hvar t a b c
  have hprod_left :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ k j a *
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ i a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (rhs (t : Real) x₀ k j a *
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real))
              x₀ i a m +
          DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real))
              x₀ k j a *
            rhs (t : Real) x₀ i a m))
        D.carrier
        (t : Real) := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun a _ => (hΓ k j a).mul (hΓ i a m)))
  have hprod_right :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ i j a *
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection s)
              x₀ k a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (rhs (t : Real) x₀ i j a *
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real))
              x₀ k a m +
          DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real))
              x₀ i j a *
            rhs (t : Real) x₀ k a m))
        D.carrier
        (t : Real) := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun a _ => (hΓ i j a).mul (hΓ k a m)))
  have hraw :
      HasDerivWithinAt
        (fun s : Real =>
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I) (S.family.connection s)
            x₀ i k j m)
        ((extDerivFun (I := I) (fun y : M => rhs (t : Real) y k j m) x₀
            (coordinateFrameAt (I := I) x₀ i x₀) -
          extDerivFun (I := I) (fun y : M => rhs (t : Real) y i j m) x₀
            (coordinateFrameAt (I := I) x₀ k x₀)) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            (rhs (t : Real) x₀ k j a *
              DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
                (S.family.connection (t : Real)) x₀ i a m +
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
                (S.family.connection (t : Real)) x₀ k j a *
              rhs (t : Real) x₀ i a m)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            (rhs (t : Real) x₀ i j a *
              DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
                (S.family.connection (t : Real)) x₀ k a m +
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
                (S.family.connection (t : Real)) x₀ i j a *
              rhs (t : Real) x₀ k a m)))
        D.carrier
        (t : Real) := by
    simpa [DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt, sub_eq_add_neg, add_assoc,
      Finset.sum_add_distrib] using
      (((hD_i.sub hD_k).add hprod_left).sub hprod_right)
  refine hraw.congr_deriv ?_
  have hsymm :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ a b c =
          DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ b a c := by
    intro a b c
    exact christoffelCoordAt_symm_of_isSolutionOn (I := I) S hS t x₀ a b c
  let Γ : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b c =>
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (S.family.connection (t : Real)) x₀ a b c
  let A : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b c => rhs (t : Real) x₀ a b c
  let dA : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun dir a b c =>
      extDerivFun (I := I) (fun y : M => rhs (t : Real) y a b c) x₀
        (coordinateFrameAt (I := I) x₀ dir x₀)
  have hΓsymm : ∀ a b c : CoordinateIdx (𝕜 := Real) E, Γ a b c = Γ b a c := by
    intro a b c
    exact hsymm a b c
  simpa [Γ, A, dA, christoffelVariationCovDerivCoordAt,
    covDChristoffelVariation] using
    (christoffel_curv_variation_algebra Γ A dA hΓsymm i k j m)


omit [SigmaCompactSpace M] in
theorem christoffelRicciCoeffAt_hasDerivWithinAt_of_christoffelVariation
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hvar : ChristoffelVariationEquationInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (S.family.connection s)
          x₀ i j)
      (ricciVariationFromConnectionRHSInFrame (M := M)
        (fun τ x d k i j =>
          christoffelVariationCovDerivCoordAt (I := I)
            (S.family.connection τ) rhs τ x d k i j)
        (t : Real) x₀ i j)
      D.carrier
      (t : Real) := by
  classical
  have hsum :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ k : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
              (S.family.connection s) x₀ k i j k)
        (∑ k : CoordinateIdx (𝕜 := Real) E,
          (christoffelVariationCovDerivCoordAt (I := I)
              (S.family.connection (t : Real)) rhs (t : Real) x₀ k k i j -
            christoffelVariationCovDerivCoordAt (I := I)
              (S.family.connection (t : Real)) rhs (t : Real) x₀ i k k j))
        D.carrier
        (t : Real) := by
    exact HasDerivWithinAt.fun_sum fun k _ =>
      christoffelCurvCoeffAt_hasDerivWithinAt_of_christoffelVariation
        (I := I) S hS rhs x₀ hvar hmix t k i j k
  refine hsum.congr_deriv ?_
  simp [ricciVariationFromConnectionRHSInFrame, Finset.sum_sub_distrib]



omit [SigmaCompactSpace M] in
theorem ricciVariationFormulaInCoordFrameAt_of_christoffelVariation
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (rhs :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (hRicTrace : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hvar : ChristoffelVariationEquationInFrameOn (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs)
    (hmix : ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀) rhs) :
    RicciVariationFormulaInFrameOnLocal (I := I) S
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (fun τ x d k i j =>
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection τ) rhs τ x d k i j) := by
  intro t x hx i j
  have hx_eq : x = x₀ := by
    simpa using hx
  subst x
  have hderiv :=
    christoffelRicciCoeffAt_hasDerivWithinAt_of_christoffelVariation
      (I := I) S hS rhs x₀ hvar hmix t i j
  have hricci :
      ∀ s : Real, s ∈ D.carrier ->
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j =
          DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (S.family.connection s) x₀ i j := by
    intro s hs
    unfold ricciCompInFrame
    change (S.ricci s x₀)
        (DifferentialGeometry.Integral.Connection.vec2 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
        DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (S.family.connection s) x₀ i j
    rw [hRicTrace s hs x₀]
    exact DifferentialGeometry.Integral.Connection.ricciFromRm13At_coordFrame_eq_christoffelRicciCoeffAt
      (I := I) (S.family.connection s) (connSmoothOfSol (I := I) S hS s hs) (Rm13 s) x₀
      (hRm s hs) (hcurv s hs) i j
  exact hderiv.congr
    (fun s hs => hricci s hs)
    (hricci (t : Real) (D.regular_subset t.2))







omit [SigmaCompactSpace M] [T2Space M] in
theorem gammaCovNab2Core
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv :
      Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (d k i j : CoordinateIdx (𝕜 := Real) E)
    (hginv_mdiff :
      ∀ a b : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gInv (t : Real) y a b) x₀)
    (hN_mdiff :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => nablaRic (t : Real) y a b c) x₀)
    (hginv_zero :
      ∀ k l : CoordinateIdx (𝕜 := Real) E,
        inverseMetricCovDerivCompInFrame (I := I) gInv
          (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          (t : Real) x₀ d k l = 0)
    (hnabla2_at :
      ∀ a b c e : CoordinateIdx (𝕜 := Real) E,
        nabla2Ric (t : Real) x₀ a b c e =
          ricciSecondCovDerivCompInFrame
            (I := I) S (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic
            (t : Real) x₀ a b c e) :
    christoffelVariationCovDerivCoordAt (I := I)
        (S.family.connection (t : Real))
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
        (t : Real) x₀ d k i j =
      nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
        (t : Real) x₀ d k i j := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hcalc :
      christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ d k i j =
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv (t : Real) x₀ k l *
            (-ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d i j l -
              ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d j i l +
              ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d l i j) := by










    let Γ : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
      fun up low => DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
        (S.family.connection (t : Real)) x₀ d low up
    let G : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a l => gInv (t : Real) x₀ a l
    let dG : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a l => extDerivFun (I := I) (fun y : M => gInv (t : Real) y a l)
        x₀ (frame d x₀)
    let N :
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
          CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a b c => nablaRic (t : Real) x₀ a b c
    let dN :
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
          CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a b c => extDerivFun (I := I)
        (fun y : M => nablaRic (t : Real) y a b c) x₀ (frame d x₀)
    have hlower_mdiff :
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M =>
              christoffelVariationLoweredRHSInFrame nablaRic
                (t : Real) y a b c) x₀ := by
      intro a b c
      simpa [christoffelVariationLoweredRHSInFrame] using
        (((hN_mdiff a b c).neg.sub (hN_mdiff b a c)).add (hN_mdiff c a b))
    have hlower_deriv :
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I)
              (fun y : M =>
                christoffelVariationLoweredRHSInFrame nablaRic
                  (t : Real) y a b c) x₀ (frame d x₀) =
            lowerRHS dN a b c := by
      intro a b c
      unfold christoffelVariationLoweredRHSInFrame lowerRHS dN
      rw [ricci_extDerivFun_add (I := I) (v := frame d x₀)
        (f := fun y : M => -nablaRic (t : Real) y a b c -
          nablaRic (t : Real) y b a c)
        (g := fun y : M => nablaRic (t : Real) y c a b)
        ((hN_mdiff a b c).neg.sub (hN_mdiff b a c)) (hN_mdiff c a b)]
      rw [ricci_extDerivFun_sub (I := I) (v := frame d x₀)
        (f := fun y : M => -nablaRic (t : Real) y a b c)
        (g := fun y : M => nablaRic (t : Real) y b a c)
        (hN_mdiff a b c).neg (hN_mdiff b a c)]
      rw [ricci_extDerivFun_neg (I := I) (v := frame d x₀)
        (f := fun y : M => nablaRic (t : Real) y a b c) (hN_mdiff a b c)]
    have hgamma_eval :
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
              (t : Real) x₀ a b c =
            ∑ l : CoordinateIdx (𝕜 := Real) E,
              G c l * lowerRHS N a b l := by
      intro a b c
      simp [christoffelEvolutionRHSInFrame,
        christoffelVariationLoweredRHSInFrame, lowerRHS, G, N]
    have hgamma_deriv :
        extDerivFun (I := I)
            (fun y : M =>
              christoffelEvolutionRHSInFrame (M := M) gInv nablaRic
                (t : Real) y i j k) x₀ (frame d x₀) =
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            (dG k l * lowerRHS N i j l + G k l * lowerRHS dN i j l) := by
      unfold christoffelEvolutionRHSInFrame
      have hsumfun :
          (fun y : M =>
              ∑ l : CoordinateIdx (𝕜 := Real) E,
                gInv (t : Real) y k l *
                  christoffelVariationLoweredRHSInFrame nablaRic (t : Real) y i j l) =
            ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum
              (fun l y =>
                gInv (t : Real) y k l *
                  christoffelVariationLoweredRHSInFrame nablaRic (t : Real) y i j l)) := by
        ext y
        simp
      rw [hsumfun]
      rw [ricci_extDerivFun_finset_sum (I := I)
        (t := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
        (f := fun l y =>
          gInv (t : Real) y k l *
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) y i j l)
        (x := x₀) (v := frame d x₀)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ricci_extDerivFun_mul (I := I) (v := frame d x₀)
          (f := fun y : M => gInv (t : Real) y k l)
          (g := fun y : M =>
            christoffelVariationLoweredRHSInFrame nablaRic (t : Real) y i j l)
          (hginv_mdiff k l) (hlower_mdiff i j l)]
        rw [hlower_deriv i j l]
        simp [G, dG, N, lowerRHS, christoffelVariationLoweredRHSInFrame]
        ring
      · intro l _hl
        exact (hginv_mdiff k l).mul (hlower_mdiff i j l)
    have hInv :
        ∀ l : CoordinateIdx (𝕜 := Real) E, covDInv Γ G dG k l = 0 := by
      intro l
      have hz := hginv_zero k l
      simpa [covDInv, Γ, G, dG, inverseMetricCovDerivCompInFrame,
        DifferentialGeometry.Integral.Connection.christoffelCoordAt, frame, hframe] using hz
    calc
      christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ d k i j
          =
        (∑ l : CoordinateIdx (𝕜 := Real) E,
          (dG k l * lowerRHS N i j l + G k l * lowerRHS dN i j l)) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            Γ k a * (∑ l : CoordinateIdx (𝕜 := Real) E,
              G a l * lowerRHS N i j l)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            Γ a i * (∑ l : CoordinateIdx (𝕜 := Real) E,
              G k l * lowerRHS N a j l)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            Γ a j * (∑ l : CoordinateIdx (𝕜 := Real) E,
              G k l * lowerRHS N i a l)) := by
            unfold christoffelVariationCovDerivCoordAt
            rw [hgamma_deriv]
            simp [hgamma_eval, Γ, G]
      _ = ∑ l : CoordinateIdx (𝕜 := Real) E,
            G k l * covD3 Γ (lowerRHS N) (lowerRHS dN) i j l := by
            exact raised_contract_covD_of_inv_zero
              (Γ := Γ) (G := G) (dG := dG)
              (B := lowerRHS N) (dB := lowerRHS dN)
              (k := k) (i := i) (j := j) hInv
      _ = ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInv (t : Real) x₀ k l *
            (-ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d i j l -
              ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d j i l +
              ricciSecondCovDerivCompInFrame
                (I := I) S frame hframe nablaRic (t : Real) x₀ d l i j) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [covD3_lowerRHS (Γ := Γ) (N := N) (dN := dN)
              (i := i) (j := j) (l := l)]
            unfold covD3 Γ G N dN ricciSecondCovDerivCompInFrame
            simp [DifferentialGeometry.Integral.Connection.christoffelCoordAt, frame]
  rw [hcalc]
  unfold nablaGammaDtFromNabla2RicInFrame
  refine Finset.sum_congr rfl fun l _hl => ?_
  rw [hnabla2_at d i j l, hnabla2_at d j i l, hnabla2_at d l i j]




omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffelVariationCovDerivCoordAt_eq_nablaGammaDtFromNabla2RicInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv :
      Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (d k i j : CoordinateIdx (𝕜 := Real) E) :
    christoffelVariationCovDerivCoordAt (I := I)
        (S.family.connection (t : Real))
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
        (t : Real) x₀ d k i j =
      nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
        (t : Real) x₀ d k i j := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  have hu : IsOpen (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameSet_open (I := I) x₀
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection (t : Real)) (S.family.metric (t : Real)) :=
    DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.metricCompatibleAt_regular
      (I := I) S.family t
  have hginv_mdiff :
      ∀ a b : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gInv (t : Real) y a b) x₀ := by
    intro a b
    exact hmetricReg.gInv_mdiffAt
      (I := I) S gInv gInvDt frame t hu hx₀ a b
  have hmetric_mdiff :
      ∀ a b : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => metricCompInFrame (I := I) S frame (t : Real) y a b) x₀ := by
    intro a b
    exact hmetricReg.metricComp_mdiffAt
      (I := I) S gInv gInvDt frame t hu hx₀ a b
  have hginv_zero :
      ∀ k l : CoordinateIdx (𝕜 := Real) E,
        inverseMetricCovDerivCompInFrame (I := I) gInv
          (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          (t : Real) x₀ d k l = 0 := by
    intro k l
    exact invCovZeroLocal
      (I := I) S gInv (S.family.connection (t : Real)) frame hframe
      hmetricReg.nondegenerateGram (t : Real)
      hmc hu hx₀ hginv_mdiff hmetric_mdiff d k l
  have hN_mdiff :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => nablaRic (t : Real) y a b c) x₀ := by
    intro a b c
    exact hnablaReg.first.mdiffAt (t : Real) x₀ hx₀ a b c
  have hnabla2_at :
      ∀ a b c e : CoordinateIdx (𝕜 := Real) E,
        nabla2Ric (t : Real) x₀ a b c e =
          ricciSecondCovDerivCompInFrame
            (I := I) S (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic
            (t : Real) x₀ a b c e :=
    hnablaReg.second (t : Real) x₀ hx₀
  exact gammaCovNab2Core
    (I := I) S gInv nablaRic nabla2Ric x₀ t d k i j
    hginv_mdiff hN_mdiff hginv_zero hnabla2_at






omit [SigmaCompactSpace M] in
theorem ricciVarCore
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv :
      Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (hGamma :
      ChristoffelEvolutionEquationInFrameOn (I := I) S gInv
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic)
    (hginv_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => gInv (t : Real) y a b) x₀)
    (hN_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => nablaRic (t : Real) y a b c) x₀)
    (hginv_zero :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ d k l : CoordinateIdx (𝕜 := Real) E,
          inverseMetricCovDerivCompInFrame (I := I) gInv
            (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            (t : Real) x₀ d k l = 0)
    (hnabla2_at :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b c e : CoordinateIdx (𝕜 := Real) E,
          nabla2Ric (t : Real) x₀ a b c e =
            ricciSecondCovDerivCompInFrame
              (I := I) S (coordinateFrameAt (I := I) x₀)
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic
              (t : Real) x₀ a b c e)
    (hRicTrace : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)) :
    RicciVariationFormulaInFrameOnLocal (I := I) S
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric) := by
  classical
  have hvar :
      ChristoffelVariationEquationInFrameOn (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic) := by
    simpa [ChristoffelVariationEquationInFrameOn,
      ChristoffelEvolutionEquationInFrameOn] using hGamma
  have hlocal :=
    ricciVariationFormulaInCoordFrameAt_of_christoffelVariation
      (I := I) S hS (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
      Rm13 x₀ hRicTrace hRm hcurv hvar hmix
  intro t x hx i j
  have hx_eq : x = x₀ := by
    simpa using hx
  subst x
  have hbase := hlocal t x₀ (by simp) i j
  have hsum₁ :
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ a a i j) =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x₀ a a i j := by
    refine Finset.sum_congr rfl fun a _ha => ?_
    exact gammaCovNab2Core
      (I := I) S gInv nablaRic nabla2Ric x₀ t a a i j
      (hginv_mdiff t) (hN_mdiff t) (fun k l => hginv_zero t a k l)
      (hnabla2_at t)
  have hsum₂ :
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ i a a j) =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x₀ i a a j := by
    refine Finset.sum_congr rfl fun a _ha => ?_
    exact gammaCovNab2Core
      (I := I) S gInv nablaRic nabla2Ric x₀ t i a a j
      (hginv_mdiff t) (hN_mdiff t) (fun k l => hginv_zero t i k l)
      (hnabla2_at t)
  have hEq :
      ricciVariationFromConnectionRHSInFrame (M := M)
          (fun τ x d k i j =>
            christoffelVariationCovDerivCoordAt (I := I)
              (S.family.connection τ)
              (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
              τ x d k i j)
          (t : Real) x₀ i j =
        ricciVariationFromConnectionRHSInFrame (M := M)
          (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric)
          (t : Real) x₀ i j := by
    unfold ricciVariationFromConnectionRHSInFrame
    change
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection (t : Real))
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          (t : Real) x₀ a a i j) -
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          christoffelVariationCovDerivCoordAt (I := I)
            (S.family.connection (t : Real))
            (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
            (t : Real) x₀ i a a j) =
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x₀ a a i j) -
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x₀ i a a j)
    rw [hsum₁, hsum₂]
  exact hbase.congr_deriv hEq




omit [SigmaCompactSpace M] in
theorem ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution_nabla2
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv :
      Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (hRicTrace : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)) :
    RicciVariationFormulaInFrameOnLocal (I := I) S
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric) := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  have hu : IsOpen (coordinateFrameSet (I := I) x₀) :=
    coordinateFrameSet_open (I := I) x₀
  have hGamma :
      ChristoffelEvolutionEquationInFrameOn (I := I) S gInv
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic :=
    christoffelEvolution_of_spacetimeSmoothMetric
      (I := I) S hS gInv gInvDt (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (coordinateFrameSet_open (I := I) x₀) nablaRic hmetricReg
      hnablaReg.first.realizes
  have hginv_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => gInv (t : Real) y a b) x₀ := by
    intro t a b
    exact hmetricReg.gInv_mdiffAt
      (I := I) S gInv gInvDt frame t hu hx₀ a b
  have hmetric_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => metricCompInFrame (I := I) S frame (t : Real) y a b) x₀ := by
    intro t a b
    exact hmetricReg.metricComp_mdiffAt
      (I := I) S gInv gInvDt frame t hu hx₀ a b
  have hginv_zero :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ d k l : CoordinateIdx (𝕜 := Real) E,
          inverseMetricCovDerivCompInFrame (I := I) gInv
            (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            (t : Real) x₀ d k l = 0 := by
    intro t d k l
    have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
        (S.family.connection (t : Real)) (S.family.metric (t : Real)) :=
      DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.metricCompatibleAt_regular
        (I := I) S.family t
    exact invCovZeroLocal
      (I := I) S gInv (S.family.connection (t : Real)) frame hframe
      hmetricReg.nondegenerateGram (t : Real)
      hmc hu hx₀ (hginv_mdiff t) (hmetric_mdiff t) d k l
  have hN_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => nablaRic (t : Real) y a b c) x₀ := by
    intro t a b c
    exact hnablaReg.first.mdiffAt (t : Real) x₀ hx₀ a b c
  have hnabla2_at :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b c e : CoordinateIdx (𝕜 := Real) E,
          nabla2Ric (t : Real) x₀ a b c e =
            ricciSecondCovDerivCompInFrame
              (I := I) S (coordinateFrameAt (I := I) x₀)
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic
              (t : Real) x₀ a b c e := by
    intro t
    exact hnablaReg.second (t : Real) x₀ hx₀
  exact ricciVarCore
    (I := I) S hS gInv nablaRic nabla2Ric Rm13 x₀ hGamma
    hginv_mdiff hN_mdiff hginv_zero hnabla2_at
    hRicTrace hRm hcurv hmix

end CoordinateConnectionVariation

end Components

end DifferentialGeometry.PDE.RicciFlow
