import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.Definitions

set_option autoImplicit false
set_option linter.style.longLine false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff BigOperators
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]



def scalarSqLap
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real) :
    Real -> M -> Real :=
  fun t x => 2 * scalar t x * scalarLap t x + 2 * gradScalarNormSq t x


omit [Module.Finite ℝ E] in
theorem sqLap_at
    [FiniteDimensional Real E]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (t : Real) {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f y) x)
    (hfg : MDiffAt (T% (f • fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f y)) x) :
    DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t f x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t f x) := by
  have hhalf :=
    DifferentialGeometry.Integral.Connection.half_laplacian_mul_self
      (I := I) (G.connection t) (G.metric t) (f := f) (x := x)
      hf_all hf_x hgrad hfg
  unfold DifferentialGeometry.Integral.Connection.laplacianAt DifferentialGeometry.Integral.Connection.gradientAt
  have hpow :
      (fun y : M => f y ^ 2) = fun y : M => f y * f y := by
    funext y
    ring
  rw [hpow]
  have hmain :
      DifferentialGeometry.Integral.Connection.laplacian (I := I) (G.connection t) (G.metric t)
          (fun y : M => f y * f y) x =
        2 * (f x * DifferentialGeometry.Integral.Connection.laplacian (I := I) (G.connection t) (G.metric t) f x +
          (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f x)
            (DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) f x)) := by
    linarith
  rw [hmain]
  ring



omit [Module.Finite ℝ E] in
theorem sqLap_realizes
    [FiniteDimensional Real E]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarLap : ScalarLaplacianRealizesHeatOperatorOn
      (I := I) G T scalar scalarLap)
    (hgradNorm : forall t x,
      gradScalarNormSq t x =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x))
    (hdf : forall t y,
      MDifferentiableAt I 𝓘(Real, Real) (scalar t) y)
    (hgrad : forall t x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (scalar t) y) x)
    (hfg : forall t x,
      MDiffAt (T% ((scalar t) • fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (scalar t) y)) x) :
    ScalarLaplacianRealizesHeatOperatorOn
      (I := I) G T
      (fun t x => scalar t x ^ 2)
      (scalarSqLap scalar scalarLap gradScalarNormSq) := by
  intro t ht x
  have hlap :
      scalarLap t x = DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (scalar t) x := by
    simpa [DifferentialGeometry.Integral.Connection.heatOperator] using hscalarLap t ht x
  have hsq :=
    sqLap_at (I := I) G t (f := scalar t) (x := x)
      (hdf t) (hdf t x) (hgrad t x) (hfg t x)
  calc
    scalarSqLap scalar scalarLap gradScalarNormSq t x =
        2 * scalar t x * DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (scalar t) x +
          2 * (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) := by
          simp [scalarSqLap, hlap, hgradNorm t x]
    _ = DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
          (fun y : M => scalar t y ^ 2) x := by
          rw [hsq]
    _ = DifferentialGeometry.Integral.Connection.heatOperator (I := I) G t
          (fun y : M => scalar t y ^ 2) x := rfl


def tfLap
    (scalar scalarLap gradScalarNormSq ricciNormLap : Real -> M -> Real) :
    Real -> M -> Real :=
  fun t x => ricciNormLap t x -
    scalarSqLap scalar scalarLap gradScalarNormSq t x / 3


def scalarSqHeatOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarSqLap gradScalarNormSq ricciNormSq : Real -> M -> Real) :
    Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x ^ 2)
      (scalarSqLap (t : Real) x +
        (-2 * gradScalarNormSq (t : Real) x +
          4 * scalar (t : Real) x * ricciNormSq (t : Real) x))
      D.carrier
      (t : Real)



omit [TopologicalSpace M] in
theorem sqHeat_of_scalar
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarLap gradScalarNormSq ricciNormSq : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq) :
    scalarSqHeatOn
      (D := D) scalar (scalarSqLap scalar scalarLap gradScalarNormSq)
      gradScalarNormSq ricciNormSq := by
  intro t x
  have h := hscalar t x
  have hmul := h.mul h
  convert hmul using 1
  · ext s
    simp [pow_two]
  · simp [scalarSqLap]
    ring


def tfRicHeatOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (tfNormSq tfLap nablaRicNormSq gradScalarNormSq
      scalar ricciNormSq Q : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    scalar (t : Real) x ≠ 0 ->
    HasDerivWithinAt
      (fun s : Real => tfNormSq s x)
      (tfLap (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x +
          ((2 : Real) / 3) * gradScalarNormSq (t : Real) x +
          (4 * ricciNormSq (t : Real) x * tfNormSq (t : Real) x -
            2 * Q (t : Real) x) / scalar (t : Real) x))
      D.carrier
      (t : Real)



omit [TopologicalSpace M] in
theorem tfRicHeat_alg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar ricciNormSq ricciNormLap scalarSqLap tfLap
      nablaRicNormSq gradScalarNormSq Q reaction : Real -> M -> Real)
    (hRic : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hSq : scalarSqHeatOn
      (D := D) scalar scalarSqLap gradScalarNormSq ricciNormSq)
    (hLap : ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D, ∀ x,
      tfLap (t : Real) x = ricciNormLap (t : Real) x -
        scalarSqLap (t : Real) x / 3)
    (hRel : tfRicReactRel
      scalar ricciNormSq (tfRicNormSq scalar ricciNormSq) Q reaction) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      tfLap nablaRicNormSq gradScalarNormSq scalar ricciNormSq Q := by
  intro t x hR
  have hRic' := hRic t x
  have hSq' := hSq t x
  have hDeriv0 :
      HasDerivWithinAt
        (fun s : Real => ricciNormSq s x - ((1 : Real) / 3) * scalar s x ^ 2)
        ((ricciNormLap (t : Real) x +
            (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
          ((1 : Real) / 3) *
            (scalarSqLap (t : Real) x +
              (-2 * gradScalarNormSq (t : Real) x +
                4 * scalar (t : Real) x * ricciNormSq (t : Real) x)))
        D.carrier
        (t : Real) := by
    simpa [mul_assoc] using hRic'.sub (hSq'.const_mul ((1 : Real) / 3))
  have hDeriv :
      HasDerivWithinAt
        (fun s : Real => tfRicNormSq scalar ricciNormSq s x)
        ((ricciNormLap (t : Real) x +
            (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
          ((1 : Real) / 3) *
            (scalarSqLap (t : Real) x +
              (-2 * gradScalarNormSq (t : Real) x +
                4 * scalar (t : Real) x * ricciNormSq (t : Real) x)))
        D.carrier
        (t : Real) := by
    simpa [tfRicNormSq, tfRicNormSqAt, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hDeriv0
  have hValue :
      ((ricciNormLap (t : Real) x +
          (-2 * nablaRicNormSq (t : Real) x + 4 * reaction (t : Real) x)) -
        ((1 : Real) / 3) *
          (scalarSqLap (t : Real) x +
            (-2 * gradScalarNormSq (t : Real) x +
              4 * scalar (t : Real) x * ricciNormSq (t : Real) x))) =
      tfLap (t : Real) x +
        (-2 * nablaRicNormSq (t : Real) x +
          ((2 : Real) / 3) * gradScalarNormSq (t : Real) x +
          (4 * ricciNormSq (t : Real) x *
              tfRicNormSq scalar ricciNormSq (t : Real) x -
            2 * Q (t : Real) x) / scalar (t : Real) x) := by
    rw [hLap t x, ← hRel (t : Real) x hR]
    ring
  rw [hValue] at hDeriv
  exact hDeriv




omit [TopologicalSpace M] in
theorem tfHeat_base
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq Q reaction : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRic : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hRel : tfRicReactRel
      scalar ricciNormSq (tfRicNormSq scalar ricciNormSq) Q reaction) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq Q := by
  exact tfRicHeat_alg
    (D := D)
    scalar ricciNormSq ricciNormLap
    (scalarSqLap scalar scalarLap gradScalarNormSq)
    (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
    nablaRicNormSq gradScalarNormSq Q reaction
    hRic
    (sqHeat_of_scalar
      (D := D) scalar scalarLap gradScalarNormSq ricciNormSq hscalar)
    (by intro t x; rfl)
    hRel

end DifferentialGeometry.PDE.RicciFlow
