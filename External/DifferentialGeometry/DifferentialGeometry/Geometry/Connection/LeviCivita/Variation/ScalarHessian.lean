import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.RicciCoord

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}







section RicciCoordVariation

open DifferentialGeometry.Tensor.Coordinates

variable [DecidableEq (CoordinateIdx (𝕜 := Real) E)]

def scalarHessCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (f : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  scalarCoordSecondAt (I := I) f x0 i j -
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 i j p *
        scalarCoordDerivAt (I := I) f x0 p






omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem gammaTraceCovVar
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (metricTrace : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace_deriv :
      extDerivFun (I := I)
          (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
            gammaDot y p p j)
          x0 (coordinateFrameAt (I := I) x0 i x0) =
        (1 / 2 : Real) * scalarCoordSecondAt (I := I) metricTrace x0 i j)
    (htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a)
    (htrace_ext :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I) (fun y : M => gammaDot y p p j) x0
            (coordinateFrameAt (I := I) x0 i x0)) =
        extDerivFun (I := I)
          (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
            gammaDot y p p j)
          x0 (coordinateFrameAt (I := I) x0 i x0)) :
    gammaTraceCovAt (I := I) cov gammaDot x0 i j =
      (1 / 2 : Real) *
        scalarHessCoordAt (I := I) cov metricTrace x0 i j := by
  classical
  let Idx := CoordinateIdx (𝕜 := Real) E
  let Gamma : Idx -> Idx -> Idx -> Real :=
    fun a b c => DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 a b c
  let A : Idx -> Idx -> Idx -> Real := fun k a b => gammaDot x0 k a b
  let D : Real :=
    ∑ p : Idx,
      extDerivFun (I := I) (fun y : M => gammaDot y p p j) x0
        (coordinateFrameAt (I := I) x0 i x0)
  let U : Real := ∑ p : Idx, ∑ a : Idx, Gamma i a p * A a p j
  let L : Real := ∑ p : Idx, ∑ a : Idx, Gamma i p a * A p a j
  let T : Idx -> Real := fun a => ∑ p : Idx, A p p a
  have hUL : U = L := by
    calc
      U = ∑ a : Idx, ∑ p : Idx, Gamma i a p * A a p j := by
        unfold U
        rw [Finset.sum_comm]
      _ = L := by
        rfl
  have hlast :
      (∑ p : Idx, ∑ a : Idx, Gamma i j a * A p p a) =
        ∑ a : Idx, Gamma i j a * T a := by
    unfold T
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  calc
    gammaTraceCovAt (I := I) cov gammaDot x0 i j
        = D + U - L - ∑ p : Idx, ∑ a : Idx, Gamma i j a * A p p a := by
          unfold gammaTraceCovAt gammaCovCoordAt D U L A Gamma Idx
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_add_distrib]
    _ = D - ∑ a : Idx, Gamma i j a * T a := by
          rw [hUL, hlast]
          ring
    _ = (1 / 2 : Real) * scalarCoordSecondAt (I := I) metricTrace x0 i j -
          ∑ a : Idx, Gamma i j a *
            ((1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a) := by
          rw [show D = (1 / 2 : Real) *
              scalarCoordSecondAt (I := I) metricTrace x0 i j by
            unfold D
            rw [htrace_ext, htrace_deriv]]
          refine congrArg (fun z : Real =>
            (1 / 2 : Real) * scalarCoordSecondAt (I := I) metricTrace x0 i j - z) ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          unfold T A Idx
          rw [htrace_point a]
    _ = (1 / 2 : Real) *
          scalarHessCoordAt (I := I) cov metricTrace x0 i j := by
          have hsum_half :
              (∑ a : Idx, Gamma i j a *
                ((1 / 2 : Real) *
                  scalarCoordDerivAt (I := I) metricTrace x0 a)) =
                (1 / 2 : Real) *
                  ∑ a : Idx, Gamma i j a *
                    scalarCoordDerivAt (I := I) metricTrace x0 a := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
          unfold scalarHessCoordAt Gamma Idx
          rw [hsum_half]
          ring


def scalarFirstVarCoordAt
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M) : Prop :=
  ∀ p : CoordinateIdx (𝕜 := Real) E,
    HasDerivWithinAt
      (fun s : Real => scalarCoordDerivAt (I := I) (f s) x0 p)
      (scalarCoordDerivAt (I := I) h x0 p)
      timeSet
      base


def scalarSecondVarCoordAt
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M) : Prop :=
  ∀ i j : CoordinateIdx (𝕜 := Real) E,
    HasDerivWithinAt
      (fun s : Real => scalarCoordSecondAt (I := I) (f s) x0 i j)
      (scalarCoordSecondAt (I := I) h x0 i j)
      timeSet
      base



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem scalarFirst_of_fixedBase
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (hmix :
      FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x0} : Set M)
        f (fun _s : Real => h)) :
    scalarFirstVarCoordAt (I := I) f h timeSet base x0 := by
  intro p
  have hx : x0 ∈ ({x0} : Set M) := by simp
  have hderiv :=
    fixedBaseExtDerivTimeDerivativeOn_apply (I := I) (h := hmix)
      (t := base) (x := x0) hx (coordinateFrameAt (I := I) x0 p x0)
  simpa [scalarCoordDerivAt] using hderiv



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem scalarFirst_of_fixedBaseRegular
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (hmix :
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) timeSet
        ({base} : Set Real) ({x0} : Set M) f (fun _s : Real => h)) :
    scalarFirstVarCoordAt (I := I) f h timeSet base x0 := by
  intro p
  have ht : base ∈ ({base} : Set Real) := by simp
  have hx : x0 ∈ ({x0} : Set M) := by simp
  have hderiv :=
    fixedBaseExtDerivTimeDerivativeOnRegular_apply (I := I) (h := hmix)
      (t := base) ht (x := x0) hx (coordinateFrameAt (I := I) x0 p x0)
  simpa [scalarCoordDerivAt] using hderiv



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem scalarSecond_of_fixedBase
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (hmix : ∀ j : CoordinateIdx (𝕜 := Real) E,
      FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x0} : Set M)
        (fun s : Real => scalarCoordDerivFun (I := I) (f s) x0 j)
        (fun _s : Real => scalarCoordDerivFun (I := I) h x0 j)) :
    scalarSecondVarCoordAt (I := I) f h timeSet base x0 := by
  intro i j
  have hx : x0 ∈ ({x0} : Set M) := by simp
  have hderiv :=
    fixedBaseExtDerivTimeDerivativeOn_apply (I := I) (h := hmix j)
      (t := base) (x := x0) hx (coordinateFrameAt (I := I) x0 i x0)
  simpa [scalarCoordSecondAt] using hderiv



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem scalarSecond_of_fixedBaseRegular
    (f : Real -> M -> Real) (h : M -> Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (hmix : ∀ j : CoordinateIdx (𝕜 := Real) E,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) timeSet
        ({base} : Set Real) ({x0} : Set M)
        (fun s : Real => scalarCoordDerivFun (I := I) (f s) x0 j)
        (fun _s : Real => scalarCoordDerivFun (I := I) h x0 j)) :
    scalarSecondVarCoordAt (I := I) f h timeSet base x0 := by
  intro i j
  have ht : base ∈ ({base} : Set Real) := by simp
  have hx : x0 ∈ ({x0} : Set M) := by simp
  have hderiv :=
    fixedBaseExtDerivTimeDerivativeOnRegular_apply (I := I) (h := hmix j)
      (t := base) ht (x := x0) hx (coordinateFrameAt (I := I) x0 i x0)
  simpa [scalarCoordSecondAt] using hderiv



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem lcHessVarCoord
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (scalarHessCoordAt (I := I) (G.connection base) h x0 i j -
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot x0 p i j * scalarCoordDerivAt (I := I) (f base) x0 p)
      timeSet
      base := by
  classical
  have hprod :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection s) x0 i j p *
              scalarCoordDerivAt (I := I) (f s) x0 p)
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          (gammaDot x0 p i j * scalarCoordDerivAt (I := I) (f base) x0 p +
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base) x0 i j p *
              scalarCoordDerivAt (I := I) h x0 p))
        timeSet
        base := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun p _ => (hgamma i j p).mul (hfirst p)))
  have hraw :
      HasDerivWithinAt
        (fun s : Real =>
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
        (scalarCoordSecondAt (I := I) h x0 i j -
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            (gammaDot x0 p i j * scalarCoordDerivAt (I := I) (f base) x0 p +
              DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base) x0 i j p *
                scalarCoordDerivAt (I := I) h x0 p))
        timeSet
        base := by
    simpa [scalarHessCoordAt] using (hsecond i j).sub hprod
  refine hraw.congr_deriv ?_
  simp [scalarHessCoordAt, Finset.sum_add_distrib, sub_eq_add_neg, add_comm,
    add_left_comm]




def gammaWeightedDivCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (f : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  (∑ p : CoordinateIdx (𝕜 := Real) E,
    gammaCovCoordAt (I := I) cov gammaDot x0 p p i j) -
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      gammaDot x0 p i j * scalarCoordDerivAt (I := I) f x0 p



def ricciHessVarCoordRHS
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (f h : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  gammaWeightedDivCoordAt (I := I) cov gammaDot f x0 i j +
    scalarHessCoordAt (I := I) cov h x0 i j -
      gammaTraceCovAt (I := I) cov gammaDot x0 i j



omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem lcRicciHessVarCoord
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (ricciHessVarCoordRHS (I := I) (G.connection base) gammaDot
        (f base) h x0 i j)
      timeSet
      base := by
  classical
  have hric := lcRicciVarCoord (I := I) G hLC timeSet base x0 gammaDot
    hgamma hmix i j
  have hhess := lcHessVarCoord (I := I) G timeSet base x0 f h gammaDot
    hgamma hfirst hsecond i j
  have hsum := hric.add hhess
  refine hsum.congr_deriv ?_
  simp [ricciHessVarCoordRHS, ricciVarCoordRHS, gammaWeightedDivCoordAt,
    gammaTraceCovAt, scalarHessCoordAt, sub_eq_add_neg]
  ring




def shiftedScalarHessCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (h metricTrace : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  scalarHessCoordAt (I := I) cov h x0 i j -
    (1 / 2 : Real) * scalarHessCoordAt (I := I) cov metricTrace x0 i j



omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem lcRicciHessVarShifted
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace :
      gammaTraceCovAt (I := I) (G.connection base) gammaDot x0 i j =
        (1 / 2 : Real) *
          scalarHessCoordAt (I := I) (G.connection base) metricTrace x0 i j) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
          (f base) x0 i j +
        shiftedScalarHessCoordAt (I := I) (G.connection base) h metricTrace
          x0 i j)
      timeSet
      base := by
  have hpre := lcRicciHessVarCoord (I := I) G hLC timeSet base x0 f h gammaDot
    hgamma hmix hfirst hsecond i j
  refine hpre.congr_deriv ?_
  unfold ricciHessVarCoordRHS shiftedScalarHessCoordAt
  rw [htrace]
  ring_nf




omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem lcTraceVar
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvPath :
      Real -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        Real)
    (gInvDot :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (hgInv :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt (fun s : Real => gInvPath s i j)
          (gInvDot i j) timeSet base)
    (htrace :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        gammaTraceCovAt (I := I) (G.connection base) gammaDot x0 i j =
          (1 / 2 : Real) *
            scalarHessCoordAt (I := I) (G.connection base) metricTrace x0 i j) :
    HasDerivWithinAt
      (fun s : Real =>
        trace2 (gInvPath s)
          (fun i j : CoordinateIdx (𝕜 := Real) E =>
            DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
              scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j))
      ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun i =>
        (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun j =>
          gInvDot i j *
            (DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection base)
                x0 i j +
              scalarHessCoordAt (I := I) (G.connection base) (f base)
                x0 i j) +
          gInvPath base i j *
            (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
                (f base) x0 i j +
              shiftedScalarHessCoordAt (I := I) (G.connection base) h
                metricTrace x0 i j))
      timeSet base := by
  apply trace2_deriv
  · exact hgInv
  · intro i j
    exact lcRicciHessVarShifted (I := I) G hLC timeSet base x0 f h
      metricTrace gammaDot hgamma hmix hfirst hsecond i j (htrace i j)



omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem lcRicciHessShifted_of_trace
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace_eventual :
      (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
        gammaDot y p p j) =ᶠ[nhds x0]
          fun y : M =>
            (1 / 2 : Real) *
              scalarCoordDerivFun (I := I) metricTrace x0 j y)
    (htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a)
    (hgamma_mdiff :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0)
    (hscalar_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
          (f base) x0 i j +
        shiftedScalarHessCoordAt (I := I) (G.connection base) h metricTrace
          x0 i j)
      timeSet
      base := by
  have htrace_deriv := gammaTraceDeriv
    (I := I) gammaDot metricTrace x0 i j htrace_eventual hscalar_mdiff
  have htrace_ext := traceExtSum
    (I := I) gammaDot x0 i j hgamma_mdiff
  have htrace_cov := gammaTraceCovVar
    (I := I) (G.connection base) gammaDot metricTrace x0 i j
    htrace_deriv htrace_point htrace_ext
  exact lcRicciHessVarShifted (I := I) G hLC timeSet base x0 f h
    metricTrace gammaDot hgamma hmix hfirst hsecond i j htrace_cov



omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem lcTraceVar_of_trace
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvPath :
      Real -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        Real)
    (gInvDot :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (hgInv :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt (fun s : Real => gInvPath s i j)
          (gInvDot i j) timeSet base)
    (htrace_eventual :
      ∀ j : CoordinateIdx (𝕜 := Real) E,
        (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot y p p j) =ᶠ[nhds x0]
            fun y : M =>
              (1 / 2 : Real) *
                scalarCoordDerivFun (I := I) metricTrace x0 j y)
    (htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a)
    (hgamma_mdiff :
      ∀ j p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0)
    (hscalar_mdiff :
      ∀ j : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    HasDerivWithinAt
      (fun s : Real =>
        trace2 (gInvPath s)
          (fun i j : CoordinateIdx (𝕜 := Real) E =>
            DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
              scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j))
      ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun i =>
        (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun j =>
          gInvDot i j *
            (DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection base)
                x0 i j +
              scalarHessCoordAt (I := I) (G.connection base) (f base)
                x0 i j) +
          gInvPath base i j *
            (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
                (f base) x0 i j +
              shiftedScalarHessCoordAt (I := I) (G.connection base) h
                metricTrace x0 i j))
      timeSet base := by
  apply trace2_deriv
  · exact hgInv
  · intro i j
    exact lcRicciHessShifted_of_trace
      (I := I) G hLC timeSet base x0 f h metricTrace gammaDot
      hgamma hmix hfirst hsecond i j (htrace_eventual j) htrace_point
      (hgamma_mdiff j) (hscalar_mdiff j)





omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem lcTraceVar_inv
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gInvPath :
      Real -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        Real)
    (gInvDot metricVariation :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hgamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (hgInv :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt (fun s : Real => gInvPath s i j)
          (gInvDot i j) timeSet base)
    (hcontra :
      ∀ i j : CoordinateIdx (𝕜 := Real) E,
        gInvDot i j = -metricVariation i j)
    (htrace_eventual :
      ∀ j : CoordinateIdx (𝕜 := Real) E,
        (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot y p p j) =ᶠ[nhds x0]
            fun y : M =>
              (1 / 2 : Real) *
                scalarCoordDerivFun (I := I) metricTrace x0 j y)
    (htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a)
    (hgamma_mdiff :
      ∀ j p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0)
    (hscalar_mdiff :
      ∀ j : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    HasDerivWithinAt
      (fun s : Real =>
        trace2 (gInvPath s)
          (fun i j : CoordinateIdx (𝕜 := Real) E =>
            DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
              scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j))
      (-trace2 metricVariation
          (fun i j : CoordinateIdx (𝕜 := Real) E =>
            DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection base)
                x0 i j +
              scalarHessCoordAt (I := I) (G.connection base) (f base)
                x0 i j) +
        ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun i =>
          (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum fun j =>
            gInvPath base i j *
              (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
                  (f base) x0 i j +
                shiftedScalarHessCoordAt (I := I) (G.connection base) h
                  metricTrace x0 i j)))
      timeSet base := by
  have htrace :=
    lcTraceVar_of_trace (I := I) G hLC timeSet base x0 f h metricTrace
      gammaDot gInvPath gInvDot hgamma hmix hfirst hsecond hgInv
      htrace_eventual htrace_point hgamma_mdiff hscalar_mdiff
  refine htrace.congr_deriv ?_
  exact trace2_neg gInvDot metricVariation
    (fun i j : CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection base)
          x0 i j +
        scalarHessCoordAt (I := I) (G.connection base) (f base)
          x0 i j)
    (fun i j : CoordinateIdx (𝕜 := Real) E =>
      gInvPath base i j *
        (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
            (f base) x0 i j +
          shiftedScalarHessCoordAt (I := I) (G.connection base) h
            metricTrace x0 i j))
    hcontra




omit [SigmaCompactSpace M] [T2Space M] in
theorem lcTraceShifted
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (f : Real -> M -> Real) (h metricTrace : M -> Real)
    (metricDot : M -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real)
    (metricCovDerivDt gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv (coordinateFrameAt (I := I) x0))
    (hmetricVar :
      metricVarOn (I := I) G (coordinateFrameAt (I := I) x0) base
        (coordinateFrameSet (I := I) x0) metricDot)
    (hmetric :
      metricCovVarOn (I := I) G (coordinateFrameAt (I := I) x0) base
        (coordinateFrameSet (I := I) x0) metricCovDerivDt)
    (hExt :
      metricExtDtOn (I := I) G (coordinateFrameAt (I := I) x0) base
        (coordinateFrameSet (I := I) x0) metricDot)
    (hgammaLocal :
      gammaDerivOn (I := I) G (coordinateFrameAt (I := I) x0)
        (coordinateFrameAt_isLocalFrame_one (I := I) x0) base
        (coordinateFrameSet (I := I) x0) gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (hfirst : scalarFirstVarCoordAt (I := I) f h timeSet base x0)
    (hsecond : scalarSecondVarCoordAt (I := I) f h timeSet base x0)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace_on :
      ∀ y : M, y ∈ coordinateFrameSet (I := I) x0 ->
        metricTrace y =
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            ∑ l : CoordinateIdx (𝕜 := Real) E,
              gInv y p l * metricDot y p l)
    (hgInv_mdiff :
      ∀ y : M, y ∈ coordinateFrameSet (I := I) x0 ->
        ∀ p l : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real) (fun z : M => gInv z p l) y)
    (hmetricDot_mdiff :
      ∀ y : M, y ∈ coordinateFrameSet (I := I) x0 ->
        ∀ p l : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun z : M => metricDot z p l) y)
    (hgamma_mdiff :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0)
    (hscalar_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection s) x0 i j +
          scalarHessCoordAt (I := I) (G.connection s) (f s) x0 i j)
      (gammaWeightedDivCoordAt (I := I) (G.connection base) gammaDot
          (f base) x0 i j +
        shiftedScalarHessCoordAt (I := I) (G.connection base) h metricTrace
          x0 i j)
      timeSet
      base := by
  classical
  let frame := coordinateFrameAt (I := I) x0
  let u0 := coordinateFrameSet (I := I) x0
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hu : IsOpen u0 := coordinateFrameSet_open (I := I) x0
  have hx0 : x0 ∈ u0 := coordinateFrameAt_mem (I := I) x0
  have hcoordGamma : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot := by
    intro a b c
    have h := hgammaLocal x0 hx0 a b c
    simpa [gammaCoordDerivAt, DifferentialGeometry.Integral.Connection.christoffelCoordAt, frame, hframe] using
      h.hasDerivWithinAt
  have hcov :
      ∀ y : M, y ∈ u0 -> ∀ d a b : CoordinateIdx (𝕜 := Real) E,
        metricCovDerivDt y d a b =
          dotCovAt (I := I) (G.connection base) frame hframe metricDot
            y d a b :=
    covDtEqDotCov (I := I) G frame hframe base metricDot metricCovDerivDt
      hmetricVar hmetric hExt
  have hinvCoord :
      DifferentialGeometry.Tensor.Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) (G.metric base) gInv frame := by
    intro y a b
    constructor
    · simpa [DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame, frame] using
        (hinv y a b).1
    · simpa [DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame, frame] using
        (hinv y a b).2
  have hmetric_mdiff :
      ∀ y : M, y ∈ u0 -> ∀ a b : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun z : M =>
            DifferentialGeometry.Tensor.Coordinates.metricCompForMetricInFrame
              (I := I) (G.metric base) frame z a b) y := by
    intro y hy a b
    exact DifferentialGeometry.Tensor.Coordinates.metricComp_mdiffAt
      (I := I) (G.metric base) frame hframe hu hy a b
  have hzero :
      ∀ y : M, y ∈ u0 -> ∀ d p l : CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Tensor.Coordinates.inverseMetricCovDerivForMetricCompInFrame
          (I := I) gInv (G.connection base) frame hframe y d p l = 0 := by
    intro y hy d p l
    exact DifferentialGeometry.Tensor.Coordinates.inverseMetricCovDerivForMetricCompInFrame_eq_zero
      (I := I) (g := G.metric base) (gInv := gInv)
      (cov := G.connection base) (frame := frame) (hframe := hframe)
      hinvCoord (hLC base).1 hu hy (hgInv_mdiff y hy)
      (hmetric_mdiff y hy) d p l
  have htrace_nhds :
      ∀ y : M, y ∈ u0 ->
        metricTrace =ᶠ[nhds y]
          fun z : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
            ∑ l : CoordinateIdx (𝕜 := Real) E,
              gInv z p l * metricDot z p l := by
    intro y hy
    filter_upwards [hu.mem_nhds hy] with z hz using htrace_on z hz
  have htraceCov :
      ∀ y : M, y ∈ u0 -> ∀ d : CoordinateIdx (𝕜 := Real) E,
        metricTraceCovAt gInv metricCovDerivDt y d =
          extDerivFun (I := I) metricTrace y (frame d y) := by
    intro y hy d
    exact traceCovEqDeriv (I := I) gInv metricDot metricCovDerivDt
      metricTrace (G.connection base) frame hframe d (hcov y hy d)
      (htrace_nhds y hy) (hgInv_mdiff y hy) (hmetricDot_mdiff y hy)
      (hzero y hy d)
  have htrace_point :
      ∀ a : CoordinateIdx (𝕜 := Real) E,
        (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
          (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a := by
    intro a
    have hgammaTrace :=
      gammaTraceVar_of_lcGammaVar (I := I) G hLC gInv frame hframe hu base
        metricDot metricCovDerivDt gammaDot hinv hmetricVar hmetric
        hgammaLocal x0 hx0 a
    have hmetricTrace :
        metricTraceCovAt gInv metricCovDerivDt x0 a =
          scalarCoordDerivAt (I := I) metricTrace x0 a := by
      simpa [scalarCoordDerivAt, frame] using htraceCov x0 hx0 a
    exact gammaTracePoint (I := I) gInv metricCovDerivDt gammaDot
      metricTrace x0 a hgammaTrace hmetricTrace
  have htrace_eventual :
      (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
        gammaDot y p p j) =ᶠ[nhds x0]
          fun y : M =>
            (1 / 2 : Real) *
              scalarCoordDerivFun (I := I) metricTrace x0 j y := by
    filter_upwards [hu.mem_nhds hx0] with y hy
    have hgammaTrace :=
      gammaTraceVar_of_lcGammaVar (I := I) G hLC gInv frame hframe hu base
        metricDot metricCovDerivDt gammaDot hinv hmetricVar hmetric
        hgammaLocal y hy j
    have hmetricTrace :
        metricTraceCovAt gInv metricCovDerivDt y j =
          scalarCoordDerivFun (I := I) metricTrace x0 j y := by
      simpa [scalarCoordDerivFun, frame] using htraceCov y hy j
    rw [hgammaTrace, hmetricTrace]
  exact lcRicciHessShifted_of_trace
    (I := I) G hLC timeSet base x0 f h metricTrace gammaDot
    hcoordGamma hmix hfirst hsecond i j htrace_eventual htrace_point
    hgamma_mdiff hscalar_mdiff

end RicciCoordVariation

end DifferentialGeometry.Integral.Connection
