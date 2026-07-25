import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.Quotient

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




def tfHeatTerm
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q :
      Real -> M -> Real) : Real -> M -> Real :=
  fun t x =>
    -2 * nablaRicNormSq t x +
      ((2 : Real) / 3) * gradScalarNormSq t x +
      (4 * ricciNormSq t x *
          tfRicNormSq scalar ricciNormSq t x - 2 * Q t x) /
        scalar t x



def scalarHeatTerm
    (ricciNormSq : Real -> M -> Real) : Real -> M -> Real :=
  fun t x => 2 * ricciNormSq t x



abbrev PinchEvolOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q :
      Real -> M -> Real)
    (epsilon : Real) : Prop :=
  QuotientEvolutionOn (I := I) (D := D) G
    (tfRicNormSq scalar ricciNormSq) scalar
    (tfHeatTerm scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q)
    (scalarHeatTerm ricciNormSq) (1 : Real) (2 - epsilon)





omit [Module.Finite ℝ E] in
theorem pinchEvol_setup
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar scalarLap ricciNormSq tfNormLap
      nablaRicNormSq gradScalarNormSq Q : Real -> M -> Real)
    (epsilon : Real)
    (htf : tfRicHeatOn (D := D)
      (tfRicNormSq scalar ricciNormSq) tfNormLap
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq Q)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (htfLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      tfNormLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real)
          (tfRicNormSq scalar ricciNormSq (t : Real)) x)
    (hscalarLap : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      scalarLap (t : Real) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real)
          (scalar (t : Real)) x)
    (htfDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real)
        (tfRicNormSq scalar ricciNormSq (t : Real)) y)
    (hscalarDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDifferentiableAt I 𝓘(Real, Real) (scalar (t : Real)) y)
    (htfNonneg : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 <= tfRicNormSq scalar ricciNormSq (t : Real) y)
    (hscalarPos : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      0 < scalar (t : Real) y)
    (hgradTf : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (tfRicNormSq scalar ricciNormSq (t : Real)) y) x)
    (hgradScalar : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (scalar (t : Real)) y) x)
    (hgradScalarPow : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric (t : Real))
          (fun w : M => scalar (t : Real) w ^ (-(2 - epsilon))) z) y) :
    PinchEvolOn (I := I) (D := D) G
      scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q epsilon := by
  refine quotHeat1_book (I := I) (D := D) G
    (tfRicNormSq scalar ricciNormSq) scalar
    tfNormLap scalarLap
    (tfHeatTerm scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q)
    (scalarHeatTerm ricciNormSq) (2 - epsilon) ?_ ?_
    htfLap hscalarLap htfDiff hscalarDiff htfNonneg hscalarPos
    hgradTf hgradScalar hgradScalarPow
  · intro t x
    exact htf t x (ne_of_gt (hscalarPos t x))
  · intro t x
    simpa [scalarHeatTerm] using hscalar t x





def ricciGradCoupleAt {x : M}
    (scalar : Real)
    (Ric : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 2 x)
    (nablaRic : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 3 x)
    (dScalar : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 1 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 3 x :=
  scalar • nablaRic -
    (show Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 3 x from
      Bundle.continuousMultilinearMap.product_fun
        (𝕜 := Real) (F := E) (E := TangentSpace I)
        (s := 1) (q := 2) dScalar Ric)



def ricciGradCoupleSq
    (g : Real -> SmoothMetric_gen I M)
    (scalar : Real -> M -> Real)
    (Ric : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 2 x)
    (nablaRic : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 3 x) :
    Real -> M -> Real :=
  fun t x =>
    normSq0S (I := I) (g t) x 3
      (ricciGradCoupleAt (I := I)
        (scalar t x) (Ric t x) (nablaRic t x)
        (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x))



omit [Module.Finite ℝ E] in
theorem ricciGradCoupleSq_exp_inner
    [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq : Real -> M -> Real)
    (Ric : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 2 x)
    (nablaRic : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 3 x)
    (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (G.metric t) x basis gInv)
    (hnabla :
      nablaRicNormSq t x =
        normSq0S (I := I) (G.metric t) x 3 (nablaRic t x))
    (hric :
      ricciNormSq t x =
        normSq0S (I := I) (G.metric t) x 2 (Ric t x))
    (hgradScalarSq :
      gradScalarNormSq t x =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)) :
    ricciGradCoupleSq (I := I) (fun s : Real => G.metric s)
        scalar Ric nablaRic t x =
      scalar t x ^ 2 * nablaRicNormSq t x -
        2 * scalar t x *
          inner0S (I := I) (G.metric t) x 3 (nablaRic t x)
            (Bundle.continuousMultilinearMap.product_fun
              (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
              (s := 1) (q := 2)
              (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
              (Ric t x)) +
        gradScalarNormSq t x * ricciNormSq t x := by
  have hgradOne :
      inner0S (I := I) (G.metric t) x 1
          (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
          (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x) =
        gradScalarNormSq t x := by
    calc
      inner0S (I := I) (G.metric t) x 1
          (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
          (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
          = (G.metric t).inner x
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) := by
              simpa [DifferentialGeometry.Integral.Connection.gradientAt] using
                DifferentialGeometry.Integral.Connection.inner0S_differential1FormFun_pair_eq_grad_inner
                  (I := I) (G.metric t) (scalar t) (scalar t) x
      _ = gradScalarNormSq t x := hgradScalarSq.symm
  unfold ricciGradCoupleSq ricciGradCoupleAt
  rw [normSq0S_smul_sub_product_one_two (I := I)
    (G.metric t) x basis gInv hinv
    (scalar t x) (nablaRic t x)
    (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
    (Ric t x)]
  rw [← hnabla, ← hric, hgradOne]



omit [Module.Finite ℝ E] in
theorem ricciMixed_eq_gradNorm
    [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [T2Space M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar : Real -> M -> Real)
    (RicSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (nablaRicSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (duRicNorm :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 1)
    (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (G.metric t) x basis gInv)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) (G.connection t) (G.metric t))
    (hRicNabla :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (G.connection t) RicSec nablaRicSec)
    (hdu :
      DifferentialGeometry.Integral.Connection.DuFieldRealizes (I := I)
        (fun y : M => DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric t) y (RicSec y))
        duRicNorm) :
    2 * inner0S (I := I) (G.metric t) x 3 (nablaRicSec x)
          (Bundle.continuousMultilinearMap.product_fun
            (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
            (s := 1) (q := 2)
            (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
            (RicSec x)) =
      (G.metric t).inner x
        (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
          (fun y : M =>
            DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric t) y (RicSec y)) x)
        (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) := by
  let W : TangentSpace I x :=
    DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x
  let normFun : M -> Real :=
    fun y : M => DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric t) y (RicSec y)
  have hcontract :
      inner0S (I := I) (G.metric t) x 3 (nablaRicSec x)
          (Bundle.continuousMultilinearMap.product_fun
            (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
            (s := 1) (q := 2)
            (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
            (RicSec x)) =
        inner0S (I := I) (G.metric t) x 2
          ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
              (nablaRicSec x))
            (cotangentSharp_gen (I := I) (G.metric t) x
              (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)))
          (RicSec x) := by
    exact inner0S_three_product_right (I := I) (G.metric t) x
      basis gInv hinv (nablaRicSec x)
      (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x) (RicSec x)
  have hsharp :
      cotangentSharp_gen (I := I) (G.metric t) x
          (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x) = W := by
    simpa [W, DifferentialGeometry.Integral.Connection.gradientAt] using
      DifferentialGeometry.Integral.Connection.cotangentSharp_differential1FormFun_eq_gradientFun
        (I := I) (G.metric t) (scalar t) x
  have hduNorm :=
    DifferentialGeometry.Integral.Connection.du_norm02 (I := I) (G.connection t) (G.metric t) hmc
      RicSec nablaRicSec hRicNabla duRicNorm hdu (x := x) W
  have hinner_du :
      2 * inner0S (I := I) (G.metric t) x 2
          ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
              (nablaRicSec x)) W)
          (RicSec x) =
        duRicNorm x (fun _ : Fin 1 => W) := by
    rw [hduNorm]
    simp [DifferentialGeometry.Integral.Connection.inner02, DifferentialGeometry.Integral.Connection.tensor02FreezeNabla_eq_curry]
  have hdu_grad :
      duRicNorm x (fun _ : Fin 1 => W) =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t normFun x) W := by
    rw [hdu x]
    change
      DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) normFun x
          (fun _ : Fin 1 => W) =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t normFun x) W
    simpa [DifferentialGeometry.Integral.Connection.gradientAt] using
      DifferentialGeometry.Integral.Connection.differential1FormFun_apply_eq_inner_gradientFun
        (I := I) (G.metric t) normFun x W
  calc
    2 * inner0S (I := I) (G.metric t) x 3 (nablaRicSec x)
          (Bundle.continuousMultilinearMap.product_fun
            (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
            (s := 1) (q := 2)
            (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
            (RicSec x))
        = 2 * inner0S (I := I) (G.metric t) x 2
            ((tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
                (nablaRicSec x)) W)
            (RicSec x) := by
              rw [hcontract, hsharp]
    _ = duRicNorm x (fun _ : Fin 1 => W) := hinner_du
    _ = (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t normFun x) W := hdu_grad
    _ = (G.metric t).inner x
        (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
          (fun y : M =>
            DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric t) y (RicSec y)) x)
        (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) := rfl







omit [Module.Finite ℝ E] in
theorem ricciMixed_eq_tfGrad
    [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [T2Space M]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq gradScalarNormSq : Real -> M -> Real)
    (RicSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (nablaRicSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (duRicNorm :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 1)
    (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (G.metric t) x basis gInv)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) (G.connection t) (G.metric t))
    (hRicNabla :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (G.connection t) RicSec nablaRicSec)
    (hdu :
      DifferentialGeometry.Integral.Connection.DuFieldRealizes (I := I)
        (fun y : M => DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric t) y (RicSec y))
        duRicNorm)
    (hricNorm : forall y : M,
      ricciNormSq t y =
        DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric t) y (RicSec y))
    (hnormDiff : MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric t) y (RicSec y)) x)
    (hscalarDiff : MDifferentiableAt I 𝓘(Real, Real) (scalar t) x)
    (hgradScalarSq :
      gradScalarNormSq t x =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)) :
    2 * scalar t x *
        inner0S (I := I) (G.metric t) x 3 (nablaRicSec x)
          (Bundle.continuousMultilinearMap.product_fun
            (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
            (s := 1) (q := 2)
            (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
            (RicSec x)) =
      scalar t x *
        ((G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
            (tfRicNormSq scalar ricciNormSq t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) +
            ((2 : Real) / 3) * scalar t x * gradScalarNormSq t x) := by
  let R : M -> Real := scalar t
  let normFun : M -> Real :=
    fun y : M => DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric t) y (RicSec y)
  let sqFun : M -> Real := fun y : M => R y * R y
  have hraw :=
    ricciMixed_eq_gradNorm (I := I) G scalar RicSec nablaRicSec duRicNorm
      t x basis gInv hinv hmc hRicNabla hdu
  have htfFun :
      tfRicNormSq scalar ricciNormSq t =
        fun y : M => normFun y - ((1 / 3 : Real) • sqFun) y := by
    funext y
    simp [tfRicNormSq, tracefreeRicciNormSqOf, tracefreeRicciNormSqAtOf,
      normFun, sqFun, R, hricNorm y]
    ring
  have hsqDiff : MDifferentiableAt I 𝓘(Real, Real) sqFun x := by
    exact hscalarDiff.mul hscalarDiff
  have hthirdDiff : MDifferentiableAt I 𝓘(Real, Real)
      ((1 / 3 : Real) • sqFun) x := by
    exact hsqDiff.const_smul (1 / 3 : Real)
  have hgradSq :
      DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t sqFun x =
        (2 * R x) • DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t R x := by
    unfold DifferentialGeometry.Integral.Connection.gradientAt
    exact DifferentialGeometry.Integral.Connection.gradientFun_mul_self (I := I) (G.metric t) hscalarDiff
  have hgradSqFun :
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) sqFun x =
        (2 * R x) • DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) R x := by
    simpa [DifferentialGeometry.Integral.Connection.gradientAt] using hgradSq
  have hgradTf :
      DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
          (tfRicNormSq scalar ricciNormSq t) x =
        DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t normFun x -
          (((2 : Real) / 3) * R x) •
            DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t R x := by
    rw [htfFun]
    unfold DifferentialGeometry.Integral.Connection.gradientAt
    rw [DifferentialGeometry.Integral.Connection.gradientFun_sub (I := I) (G.metric t) hnormDiff hthirdDiff]
    rw [DifferentialGeometry.Integral.Connection.gradientFun_const_smul (I := I) (G.metric t)
      (1 / 3 : Real) hsqDiff]
    change
      DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) normFun x -
          (1 / 3 : Real) • DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) sqFun x =
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) normFun x -
          (((2 : Real) / 3) * R x) •
            DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) R x
    rw [hgradSqFun]
    simp [smul_smul, R]
    ring_nf
  have hgradNorm :
      DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t normFun x =
        DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
            (tfRicNormSq scalar ricciNormSq t) x +
          (((2 : Real) / 3) * R x) •
            DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t R x := by
    rw [hgradTf]
    abel
  calc
    2 * scalar t x *
        inner0S (I := I) (G.metric t) x 3 (nablaRicSec x)
          (Bundle.continuousMultilinearMap.product_fun
            (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
            (s := 1) (q := 2)
            (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
            (RicSec x))
        = scalar t x *
            (2 * inner0S (I := I) (G.metric t) x 3 (nablaRicSec x)
              (Bundle.continuousMultilinearMap.product_fun
                (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
                (s := 1) (q := 2)
                (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
                (RicSec x))) := by ring
    _ = scalar t x *
            (G.metric t).inner x
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t normFun x)
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) := by
            rw [hraw]
    _ = scalar t x *
        ((G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
            (tfRicNormSq scalar ricciNormSq t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) +
            ((2 : Real) / 3) * scalar t x * gradScalarNormSq t x) := by
          rw [hgradNorm]
          simp [R, DifferentialGeometry.Integral.Connection.gradientAt, hgradScalarSq, smul_eq_mul,
            mul_assoc, mul_comm]



omit [Module.Finite ℝ E] in
theorem ricciGradCoupleSq_exp_mixed
    [FiniteDimensional Real E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq : Real -> M -> Real)
    (Ric : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 2 x)
    (nablaRic : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 3 x)
    (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (G.metric t) x basis gInv)
    (hnabla :
      nablaRicNormSq t x =
        normSq0S (I := I) (G.metric t) x 3 (nablaRic t x))
    (hric :
      ricciNormSq t x =
        normSq0S (I := I) (G.metric t) x 2 (Ric t x))
    (hgradScalarSq :
      gradScalarNormSq t x =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x))
    (hmixed :
      2 * scalar t x *
          inner0S (I := I) (G.metric t) x 3 (nablaRic t x)
            (Bundle.continuousMultilinearMap.product_fun
              (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
              (s := 1) (q := 2)
              (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (scalar t) x)
              (Ric t x)) =
        scalar t x *
          ((G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
              (tfRicNormSq scalar ricciNormSq t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) +
              ((2 : Real) / 3) * scalar t x * gradScalarNormSq t x)) :
    ricciGradCoupleSq (I := I) (fun s : Real => G.metric s)
        scalar Ric nablaRic t x =
      scalar t x ^ 2 * nablaRicNormSq t x -
        scalar t x *
          ((G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
              (tfRicNormSq scalar ricciNormSq t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) +
              ((2 : Real) / 3) * scalar t x * gradScalarNormSq t x) +
        gradScalarNormSq t x * ricciNormSq t x := by
  rw [ricciGradCoupleSq_exp_inner (I := I) G scalar ricciNormSq
    nablaRicNormSq gradScalarNormSq Ric nablaRic t x basis gInv hinv
    hnabla hric hgradScalarSq]
  rw [hmixed]



def pinchDriftTerm
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq : Real -> M -> Real)
    (epsilon : Real) : Real -> M -> Real :=
  fun t x =>
    2 * (1 - epsilon) / scalar t x *
      (G.metric t).inner x
        (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
        (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
          (quotField (M := M) (tfRicNormSq scalar ricciNormSq)
            scalar (1 : Real) (2 - epsilon) t) x)


def pinchSquareTerm
    (scalar coupleSq : Real -> M -> Real)
    (epsilon : Real) : Real -> M -> Real :=
  fun t x => -2 / scalar t x ^ (4 - epsilon) * coupleSq t x


def pinchGradTerm
    (scalar ricciNormSq gradScalarNormSq : Real -> M -> Real)
    (epsilon : Real) : Real -> M -> Real :=
  fun t x =>
    -epsilon * (1 - epsilon) / scalar t x ^ (4 - epsilon) *
      tfRicNormSq scalar ricciNormSq t x * gradScalarNormSq t x


def pinchReactTerm
    (scalar ricciNormSq Q : Real -> M -> Real)
    (epsilon : Real) : Real -> M -> Real :=
  fun t x =>
    -2 / scalar t x ^ (3 - epsilon) *
      (Q t x -
        epsilon * ricciNormSq t x * tfRicNormSq scalar ricciNormSq t x)




def pinchBookRHS
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq gradScalarNormSq coupleSq Q : Real -> M -> Real)
    (epsilon : Real) : Real -> M -> Real :=
  fun t x =>
    pinchDriftTerm (I := I) G scalar ricciNormSq epsilon t x +
      pinchSquareTerm scalar coupleSq epsilon t x +
      pinchGradTerm scalar ricciNormSq gradScalarNormSq epsilon t x +
      pinchReactTerm scalar ricciNormSq Q epsilon t x


omit [Module.Finite ℝ E] in
theorem pinchDrift_exp
    [FiniteDimensional Real E]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq gradScalarNormSq : Real -> M -> Real)
    (epsilon t : Real) (x : M)
    (hscalar : 0 < scalar t x)
    (htfDiff : MDifferentiableAt I 𝓘(Real, Real)
      (tfRicNormSq scalar ricciNormSq t) x)
    (hscalarDiff : MDifferentiableAt I 𝓘(Real, Real) (scalar t) x)
    (hgradScalarSq :
      gradScalarNormSq t x =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)) :
    pinchDriftTerm (I := I) G scalar ricciNormSq epsilon t x =
      2 * (1 - epsilon) *
        (((G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
              (tfRicNormSq scalar ricciNormSq t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)) /
            scalar t x ^ (3 - epsilon) -
          (2 - epsilon) *
            tfRicNormSq scalar ricciNormSq t x *
            gradScalarNormSq t x / scalar t x ^ (4 - epsilon)) := by
  let phi : M -> Real := tfRicNormSq scalar ricciNormSq t
  let R : M -> Real := scalar t
  let Rpow : M -> Real := fun y => R y ^ (-(2 - epsilon))
  have hRpowDiff : MDifferentiableAt I 𝓘(Real, Real) Rpow x := by
    exact DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow
      (I := I) (-(2 - epsilon)) hscalarDiff hscalar
  have hmul :
      DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (fun y : M => phi y * Rpow y) x =
        phi x • DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t Rpow x +
          Rpow x • DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t phi x := by
    exact DifferentialGeometry.Integral.Connection.gradientAt_mul (I := I) G t
      (f := phi) (h := Rpow) (x := x) htfDiff hRpowDiff
  have hpow :
      DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t Rpow x =
        (-(2 - epsilon) * R x ^ (-(2 - epsilon) - 1)) •
          DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t R x := by
    exact DifferentialGeometry.Integral.Connection.gradientAt_rpow (I := I) G t
      (f := R) (x := x) (-(2 - epsilon)) hscalarDiff hscalar
  have hfield :
      quotField (M := M) (tfRicNormSq scalar ricciNormSq)
          scalar (1 : Real) (2 - epsilon) t =
        fun y : M => phi y * Rpow y := by
    funext y
    simp [quotField, phi, R, Rpow]
  have hpow3 :
      scalar t x ^ (3 - epsilon) =
        scalar t x * scalar t x ^ (2 - epsilon) := by
    rw [show 3 - epsilon = 1 + (2 - epsilon) by ring]
    rw [Real.rpow_add hscalar]
    simp
  have hpow4 :
      scalar t x ^ (4 - epsilon) =
        scalar t x * scalar t x ^ (3 - epsilon) := by
    rw [show 4 - epsilon = 1 + (3 - epsilon) by ring]
    rw [Real.rpow_add hscalar]
    simp
  have hnegpow :
      Rpow x = (scalar t x ^ (2 - epsilon))⁻¹ := by
    simpa [R, Rpow] using Real.rpow_neg hscalar.le (2 - epsilon)
  have hnegpow1 :
      scalar t x ^ (-(2 - epsilon) - 1) =
        (scalar t x ^ (3 - epsilon))⁻¹ := by
    rw [show -(2 - epsilon) - 1 = -(3 - epsilon) by ring]
    simpa using Real.rpow_neg hscalar.le (3 - epsilon)
  have hinnerSymm :
      (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
            (tfRicNormSq scalar ricciNormSq t) x) =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
            (tfRicNormSq scalar ricciNormSq t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) :=
    (G.metric t).symm x _ _
  unfold pinchDriftTerm
  rw [hfield]
  rw [hmul, hpow]
  rw [hgradScalarSq]
  rw [hnegpow, hnegpow1]
  rw [hpow3, hpow4]
  simp [phi, R, smul_eq_mul, div_eq_mul_inv]
  unfold DifferentialGeometry.Integral.Connection.gradientAt DifferentialGeometry.Integral.Connection.gradientFun DifferentialGeometry.Integral.Connection.metricSharp at hinnerSymm
  rw [hinnerSymm]
  field_simp [hscalar.ne']
  rw [hpow3]
  ring_nf




omit [Module.Finite ℝ E] in
omit [IsManifold I 1 M] in
theorem pinchRHS_eq_book_of_parts
    [FiniteDimensional Real E]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq
      coupleSq Q : Real -> M -> Real)
    (epsilon t : Real) (x : M)
    (hscalar : 0 < scalar t x)
    (hgradScalarSq :
      gradScalarNormSq t x =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x))
    (hdrift :
      pinchDriftTerm (I := I) G scalar ricciNormSq epsilon t x =
        2 * (1 - epsilon) *
          (((G.metric t).inner x
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
                (tfRicNormSq scalar ricciNormSq t) x)
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)) /
              scalar t x ^ (3 - epsilon) -
            (2 - epsilon) *
              tfRicNormSq scalar ricciNormSq t x *
              gradScalarNormSq t x / scalar t x ^ (4 - epsilon)))
    (hcouple :
      coupleSq t x =
        scalar t x ^ 2 * nablaRicNormSq t x -
          scalar t x *
            ((G.metric t).inner x
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
                (tfRicNormSq scalar ricciNormSq t) x)
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) +
                ((2 : Real) / 3) * scalar t x * gradScalarNormSq t x) +
          gradScalarNormSq t x * ricciNormSq t x) :
    quotHeatRHS (I := I) G
        (tfRicNormSq scalar ricciNormSq) scalar
        (tfHeatTerm scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q)
        (scalarHeatTerm ricciNormSq) (1 : Real) (2 - epsilon) t x =
      pinchBookRHS (I := I) G scalar ricciNormSq gradScalarNormSq
        coupleSq Q epsilon t x := by
  have hdiv :=
    quotHeatRHSDiv_eq (I := I) G
      (tfRicNormSq scalar ricciNormSq) scalar
      (tfHeatTerm scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q)
      (scalarHeatTerm ricciNormSq) (1 : Real) (2 - epsilon)
      (t := t) (x := x) hscalar
  rw [← hdiv]
  have hpow32 :
      scalar t x ^ (3 - epsilon) =
        scalar t x * scalar t x ^ (2 - epsilon) := by
    rw [show 3 - epsilon = 1 + (2 - epsilon) by ring]
    rw [Real.rpow_add hscalar]
    simp
  have hpow43 :
      scalar t x ^ (4 - epsilon) =
        scalar t x * scalar t x ^ (3 - epsilon) := by
    rw [show 4 - epsilon = 1 + (3 - epsilon) by ring]
    rw [Real.rpow_add hscalar]
    simp
  have hpow2_ne : scalar t x ^ (2 - epsilon) ≠ 0 :=
    (Real.rpow_pos_of_pos hscalar (2 - epsilon)).ne'
  have hpow3_ne : scalar t x ^ (3 - epsilon) ≠ 0 :=
    (Real.rpow_pos_of_pos hscalar (3 - epsilon)).ne'
  have hpow4_ne : scalar t x ^ (4 - epsilon) ≠ 0 :=
    (Real.rpow_pos_of_pos hscalar (4 - epsilon)).ne'
  have hpow32_inv :
      (scalar t x ^ (3 - epsilon))⁻¹ =
        (scalar t x)⁻¹ * (scalar t x ^ (2 - epsilon))⁻¹ := by
    rw [hpow32]
    simp [mul_inv_rev, mul_comm]
  have hpow43_inv :
      (scalar t x ^ (4 - epsilon))⁻¹ =
        (scalar t x)⁻¹ * (scalar t x ^ (3 - epsilon))⁻¹ := by
    rw [hpow43]
    simp [mul_inv_rev, mul_comm]
  unfold quotHeatRHSDiv pinchBookRHS pinchSquareTerm pinchGradTerm
    pinchReactTerm tfHeatTerm scalarHeatTerm
  rw [hdrift, hcouple]
  rw [hgradScalarSq]
  unfold tfRicNormSq tracefreeRicciNormSqOf tracefreeRicciNormSqAtOf
  ring_nf
  rw [hpow32, hpow43]
  simp [hpow32_inv]
  field_simp [hscalar.ne']
  ring_nf



omit [Module.Finite ℝ E] in
theorem pinchRHS_eq_book
    [FiniteDimensional Real E]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq
      coupleSq Q : Real -> M -> Real)
    (epsilon t : Real) (x : M)
    (hscalar : 0 < scalar t x)
    (hgradScalarSq :
      gradScalarNormSq t x =
        (G.metric t).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x))
    (htfDiff : MDifferentiableAt I 𝓘(Real, Real)
      (tfRicNormSq scalar ricciNormSq t) x)
    (hscalarDiff : MDifferentiableAt I 𝓘(Real, Real) (scalar t) x)
    (hcouple :
      coupleSq t x =
        scalar t x ^ 2 * nablaRicNormSq t x -
          scalar t x *
            ((G.metric t).inner x
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t
                (tfRicNormSq scalar ricciNormSq t) x)
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (scalar t) x) +
                ((2 : Real) / 3) * scalar t x * gradScalarNormSq t x) +
          gradScalarNormSq t x * ricciNormSq t x) :
    quotHeatRHS (I := I) G
        (tfRicNormSq scalar ricciNormSq) scalar
        (tfHeatTerm scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q)
        (scalarHeatTerm ricciNormSq) (1 : Real) (2 - epsilon) t x =
      pinchBookRHS (I := I) G scalar ricciNormSq gradScalarNormSq
        coupleSq Q epsilon t x := by
  refine pinchRHS_eq_book_of_parts (I := I) G scalar ricciNormSq
    nablaRicNormSq gradScalarNormSq coupleSq Q epsilon t x
    hscalar hgradScalarSq ?_ hcouple
  exact pinchDrift_exp (I := I) G scalar ricciNormSq gradScalarNormSq
    epsilon t x hscalar htfDiff hscalarDiff hgradScalarSq






omit [Module.Finite ℝ E] in
theorem pinchEvol_book_of_couple
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq
      coupleSq Q : Real -> M -> Real)
    (epsilon : Real)
    (hsetup : PinchEvolOn (I := I) (D := D) G
      scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q epsilon)
    (hscalar : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      0 < scalar (t : Real) x)
    (hgradScalarSq : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      gradScalarNormSq (t : Real) x =
        (G.metric (t : Real)).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
            (scalar (t : Real)) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
            (scalar (t : Real)) x))
    (htfDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (tfRicNormSq scalar ricciNormSq (t : Real)) x)
    (hscalarDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real) (scalar (t : Real)) x)
    (hcouple : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      coupleSq (t : Real) x =
        scalar (t : Real) x ^ 2 * nablaRicNormSq (t : Real) x -
          scalar (t : Real) x *
            ((G.metric (t : Real)).inner x
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
                (tfRicNormSq scalar ricciNormSq (t : Real)) x)
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
                (scalar (t : Real)) x) +
                ((2 : Real) / 3) * scalar (t : Real) x *
                  gradScalarNormSq (t : Real) x) +
          gradScalarNormSq (t : Real) x * ricciNormSq (t : Real) x) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M) (tfRicNormSq scalar ricciNormSq)
            scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) G (tfRicNormSq scalar ricciNormSq)
            scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchBookRHS (I := I) G scalar ricciNormSq gradScalarNormSq
            coupleSq Q epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  intro t x
  have h := hsetup t x
  have hrhs :=
    pinchRHS_eq_book (I := I) G scalar ricciNormSq nablaRicNormSq
      gradScalarNormSq coupleSq Q epsilon (t : Real) x
      (hscalar t x) (hgradScalarSq t x) (htfDiff t x)
      (hscalarDiff t x) (hcouple t x)
  rw [hrhs] at h
  exact h







omit [Module.Finite ℝ E] in
theorem pinchEvol_book_of_mixed
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q : Real -> M -> Real)
    (Ric : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 2 x)
    (nablaRic : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 3 x)
    (epsilon : Real)
    (hsetup : PinchEvolOn (I := I) (D := D) G
      scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q epsilon)
    (hscalar : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      0 < scalar (t : Real) x)
    (hgradScalarSq : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      gradScalarNormSq (t : Real) x =
        (G.metric (t : Real)).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
            (scalar (t : Real)) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
            (scalar (t : Real)) x))
    (htfDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (tfRicNormSq scalar ricciNormSq (t : Real)) x)
    (hscalarDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real) (scalar (t : Real)) x)
    (basis : forall (_t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      Module.Basis Idx Real (TangentSpace I x))
    (gInv : forall (_t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (_x : M),
      Idx -> Idx -> Real)
    (hinv : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      MetricInverseInBasis_gen (I := I) (G.metric (t : Real)) x
        (basis t x) (gInv t x))
    (hnabla : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      nablaRicNormSq (t : Real) x =
        normSq0S (I := I) (G.metric (t : Real)) x 3
          (nablaRic (t : Real) x))
    (hric : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      ricciNormSq (t : Real) x =
        normSq0S (I := I) (G.metric (t : Real)) x 2
          (Ric (t : Real) x))
    (hmixed : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      2 * scalar (t : Real) x *
          inner0S (I := I) (G.metric (t : Real)) x 3
            (nablaRic (t : Real) x)
            (Bundle.continuousMultilinearMap.product_fun
              (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I) (x := x)
              (s := 1) (q := 2)
              (DifferentialGeometry.Integral.Connection.differential1FormFun (I := I)
                (scalar (t : Real)) x)
              (Ric (t : Real) x)) =
        scalar (t : Real) x *
          ((G.metric (t : Real)).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
              (tfRicNormSq scalar ricciNormSq (t : Real)) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
              (scalar (t : Real)) x) +
              ((2 : Real) / 3) * scalar (t : Real) x *
                gradScalarNormSq (t : Real) x)) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M) (tfRicNormSq scalar ricciNormSq)
            scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) G (tfRicNormSq scalar ricciNormSq)
            scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchBookRHS (I := I) G scalar ricciNormSq gradScalarNormSq
            (ricciGradCoupleSq (I := I)
              (fun s : Real => G.metric s) scalar Ric nablaRic)
            Q epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  refine pinchEvol_book_of_couple (I := I) G scalar ricciNormSq
    nablaRicNormSq gradScalarNormSq
    (ricciGradCoupleSq (I := I)
      (fun s : Real => G.metric s) scalar Ric nablaRic)
    Q epsilon hsetup hscalar hgradScalarSq htfDiff hscalarDiff ?_
  intro t x
  exact ricciGradCoupleSq_exp_mixed (I := I) G scalar ricciNormSq
    nablaRicNormSq gradScalarNormSq Ric nablaRic (t : Real) x
    (basis t x) (gInv t x) (hinv t x) (hnabla t x) (hric t x)
    (hgradScalarSq t x) (hmixed t x)






omit [Module.Finite ℝ E] in
theorem pinchEvol_sec
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q : Real -> M -> Real)
    (RicSec : Real ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (nablaRicSec : Real ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (duRicNorm : Real ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 1)
    (epsilon : Real)
    (hsetup : PinchEvolOn (I := I) (D := D) G
      scalar ricciNormSq nablaRicNormSq gradScalarNormSq Q epsilon)
    (hscalar : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      0 < scalar (t : Real) x)
    (hgradScalarSq : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      gradScalarNormSq (t : Real) x =
        (G.metric (t : Real)).inner x
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
            (scalar (t : Real)) x)
          (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G (t : Real)
            (scalar (t : Real)) x))
    (htfDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (tfRicNormSq scalar ricciNormSq (t : Real)) x)
    (hscalarDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real) (scalar (t : Real)) x)
    (basis : forall (_t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      Module.Basis Idx Real (TangentSpace I x))
    (gInv : forall (_t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (_x : M),
      Idx -> Idx -> Real)
    (hinv : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      MetricInverseInBasis_gen (I := I) (G.metric (t : Real)) x
        (basis t x) (gInv t x))
    (hnabla : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      nablaRicNormSq (t : Real) x =
        normSq0S (I := I) (G.metric (t : Real)) x 3
          (nablaRicSec (t : Real) x))
    (hric : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      ricciNormSq (t : Real) x =
        normSq0S (I := I) (G.metric (t : Real)) x 2
          (RicSec (t : Real) x))
    (hmc : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D),
      DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
        (I := I) (G.connection (t : Real)) (G.metric (t : Real)))
    (hRicNabla : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D),
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (G.connection (t : Real))
        (RicSec (t : Real)) (nablaRicSec (t : Real)))
    (hdu : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D),
      DifferentialGeometry.Integral.Connection.DuFieldRealizes (I := I)
        (fun y : M =>
          DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric (t : Real)) y
            (RicSec (t : Real) y))
        (duRicNorm (t : Real)))
    (hricNorm : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      ricciNormSq (t : Real) y =
        DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric (t : Real)) y
          (RicSec (t : Real) y))
    (hnormDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          DifferentialGeometry.Integral.Connection.normSq02 (I := I) (G.metric (t : Real)) y
            (RicSec (t : Real) y)) x) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M) (tfRicNormSq scalar ricciNormSq)
            scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) G (tfRicNormSq scalar ricciNormSq)
            scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchBookRHS (I := I) G scalar ricciNormSq gradScalarNormSq
            (ricciGradCoupleSq (I := I)
              (fun s : Real => G.metric s) scalar
              (fun s y => RicSec s y) (fun s y => nablaRicSec s y))
            Q epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  refine pinchEvol_book_of_mixed (I := I) G scalar ricciNormSq
    nablaRicNormSq gradScalarNormSq Q
    (fun s y => RicSec s y) (fun s y => nablaRicSec s y)
    epsilon hsetup hscalar hgradScalarSq htfDiff hscalarDiff
    basis gInv hinv hnabla hric ?_
  intro t x
  exact ricciMixed_eq_tfGrad (I := I) G scalar ricciNormSq
    gradScalarNormSq (RicSec (t : Real)) (nablaRicSec (t : Real))
    (duRicNorm (t : Real)) (t : Real) x (basis t x) (gInv t x)
    (hinv t x) (hmc t) (hRicNabla t) (hdu t) (hricNorm t)
    (hnormDiff t x) (hscalarDiff t x) (hgradScalarSq t x)

end DifferentialGeometry.PDE.RicciFlow
