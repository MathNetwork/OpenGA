import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.Connection

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




def trace2
    {ι : Type*} [Fintype ι]
    (gInv T : ι -> ι -> Real) : Real :=
  ∑ i : ι, ∑ j : ι, gInv i j * T i j


theorem trace2_deriv
    {ι : Type*} [Fintype ι]
    {timeSet : Set Real} {base : Real}
    {gInvPath TPath : Real -> ι -> ι -> Real}
    {gInvDot TDot : ι -> ι -> Real}
    (hgInv :
      ∀ i j : ι,
        HasDerivWithinAt (fun s : Real => gInvPath s i j)
          (gInvDot i j) timeSet base)
    (hT :
      ∀ i j : ι,
        HasDerivWithinAt (fun s : Real => TPath s i j)
          (TDot i j) timeSet base) :
    HasDerivWithinAt
      (fun s : Real => trace2 (gInvPath s) (TPath s))
      ((Finset.univ : Finset ι).sum fun i =>
        (Finset.univ : Finset ι).sum fun j =>
          gInvDot i j * TPath base i j + gInvPath base i j * TDot i j)
      timeSet base := by
  unfold trace2
  refine HasDerivWithinAt.fun_sum ?_
  intro i _
  refine HasDerivWithinAt.fun_sum ?_
  intro j _
  simpa [mul_add] using (hgInv i j).mul (hT i j)





theorem trace2_neg
    {ι : Type*} [Fintype ι]
    (gInvDot metricVariation T U : ι -> ι -> Real)
    (h : ∀ i j : ι, gInvDot i j = -metricVariation i j) :
    ((Finset.univ : Finset ι).sum fun i =>
      (Finset.univ : Finset ι).sum fun j =>
        gInvDot i j * T i j + U i j) =
      -trace2 metricVariation T +
        ((Finset.univ : Finset ι).sum fun i =>
          (Finset.univ : Finset ι).sum fun j => U i j) := by
  classical
  unfold trace2
  calc
    ((Finset.univ : Finset ι).sum fun i =>
      (Finset.univ : Finset ι).sum fun j =>
        gInvDot i j * T i j + U i j)
        =
      ((Finset.univ : Finset ι).sum fun i =>
        (Finset.univ : Finset ι).sum fun j =>
          gInvDot i j * T i j) +
        ((Finset.univ : Finset ι).sum fun i =>
          (Finset.univ : Finset ι).sum fun j => U i j) := by
        simp [Finset.sum_add_distrib]
    _ =
      ((Finset.univ : Finset ι).sum fun i =>
        (Finset.univ : Finset ι).sum fun j =>
          -metricVariation i j * T i j) +
        ((Finset.univ : Finset ι).sum fun i =>
          (Finset.univ : Finset ι).sum fun j => U i j) := by
        refine congrArg (fun z =>
          z + ((Finset.univ : Finset ι).sum fun i =>
            (Finset.univ : Finset ι).sum fun j => U i j)) ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h i j]
    _ =
      -((Finset.univ : Finset ι).sum fun i =>
        (Finset.univ : Finset ι).sum fun j =>
          metricVariation i j * T i j) +
        ((Finset.univ : Finset ι).sum fun i =>
          (Finset.univ : Finset ι).sum fun j => U i j) := by
        simp [Finset.sum_neg_distrib]

private def covDGamma
    {ι : Type*} [Fintype ι]
    (Gamma A : ι -> ι -> ι -> Real)
    (dA : ι -> ι -> ι -> ι -> Real)
    (dir k i j : ι) : Real :=
  dA dir i j k +
    (∑ a : ι, Gamma dir a k * A i j a) -
    (∑ a : ι, Gamma dir i a * A a j k) -
    (∑ a : ι, Gamma dir j a * A i a k)

private theorem curvVarAlg
    {ι : Type*} [Fintype ι]
    (Gamma A : ι -> ι -> ι -> Real)
    (dA : ι -> ι -> ι -> ι -> Real)
    (hGammaSymm : ∀ a b c : ι, Gamma a b c = Gamma b a c)
    (i k j m : ι) :
    dA i k j m - dA k i j m +
        (∑ a : ι, (A k j a * Gamma i a m + Gamma k j a * A i a m)) -
        (∑ a : ι, (A i j a * Gamma k a m + Gamma i j a * A k a m)) =
      covDGamma Gamma A dA i m k j -
        covDGamma Gamma A dA k m i j := by
  classical
  unfold covDGamma
  have hmid :
      (∑ a : ι, Gamma i k a * A a j m) =
        ∑ a : ι, Gamma k i a * A a j m := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hGammaSymm i k a]
  have hleft :
      (∑ a : ι, A k j a * Gamma i a m) =
        ∑ a : ι, Gamma i a m * A k j a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hright :
      (∑ a : ι, A i j a * Gamma k a m) =
        ∑ a : ι, Gamma k a m * A i j a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleft, hright, hmid]
  ring



def gammaCoordDerivAt
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real) : Prop :=
  ∀ i j k : CoordinateIdx (𝕜 := Real) E,
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection s) x0 i j k)
      (gammaDot x0 k i j)
      timeSet
      base



def gammaMixedCoordAt
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (timeSet : Set Real) (base : Real) (x0 : M)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real) : Prop :=
  ∀ dir i j k : CoordinateIdx (𝕜 := Real) E,
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelCoordDerivAt (I := I) (G.connection s)
          x0 dir i j k)
      (extDerivFun (I := I) (fun y : M => gammaDot y k i j) x0
        (coordinateFrameAt (I := I) x0 dir x0))
      timeSet
      base



def gammaCovCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x0 : M)
    (dir k i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (fun y : M => gammaDot y k i j) x0
      (coordinateFrameAt (I := I) x0 dir x0) +
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 dir a k *
        gammaDot x0 a i j) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 dir i a *
        gammaDot x0 k a j) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 dir j a *
        gammaDot x0 k i a)


def gammaTraceCovAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x0 : M) (dir j : CoordinateIdx (𝕜 := Real) E) : Real :=
  ∑ p : CoordinateIdx (𝕜 := Real) E,
    gammaCovCoordAt (I := I) cov gammaDot x0 dir p p j


def ricciVarCoordRHS
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  (∑ p : CoordinateIdx (𝕜 := Real) E,
    gammaCovCoordAt (I := I) cov gammaDot x0 p p i j) -
    gammaTraceCovAt (I := I) cov gammaDot x0 i j

omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
private theorem christoffelCoordAt_symm_of_lc
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hLC : IsLeviCivita (I := I) cov g)
    (x0 : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 i j k =
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 j i k := by
  have htf : DifferentialGeometry.Integral.Connection.IsTorsionFree (I := I) cov := hLC.2
  have hzero :
      (coordinateFrameAt_isLocalFrame_one (I := I) x0).coeff k x0
          (cov.torsion x0
            (coordinateFrameAt (I := I) x0 i x0)
            (coordinateFrameAt (I := I) x0 j x0)) = 0 := by
    rw [htf x0]
    simp
  have hskew := DifferentialGeometry.Integral.Connection.coordinate_torsion_coeff_eq_christoffel_skew
    (I := I) cov x0 i j k
  rw [hzero] at hskew
  simpa [DifferentialGeometry.Integral.Connection.christoffelCoordAt] using sub_eq_zero.mp hskew.symm

omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
private theorem curvVarCoord
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hvar : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (i k j m : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I) (G.connection s)
          x0 i k j m)
      (gammaCovCoordAt (I := I) (G.connection base) gammaDot x0 i m k j -
        gammaCovCoordAt (I := I) (G.connection base) gammaDot x0 k m i j)
      timeSet
      base := by
  classical
  have hD_i := hmix i k j m
  have hD_k := hmix k i j m
  have hGamma :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        HasDerivWithinAt
          (fun s : Real =>
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection s)
              x0 a b c)
          (gammaDot x0 c a b) timeSet base := by
    intro a b c
    exact hvar a b c
  have hprod_left :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection s)
              x0 k j a *
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection s)
              x0 i a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (gammaDot x0 a k j *
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base)
              x0 i a m +
          DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base)
              x0 k j a *
            gammaDot x0 m i a))
        timeSet
        base := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun a _ => (hGamma k j a).mul (hGamma i a m)))
  have hprod_right :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ a : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection s)
              x0 i j a *
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection s)
              x0 k a m)
        (∑ a : CoordinateIdx (𝕜 := Real) E,
          (gammaDot x0 a i j *
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base)
              x0 k a m +
          DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base)
              x0 i j a *
            gammaDot x0 m k a))
        timeSet
        base := by
    simpa [Finset.sum_add_distrib] using
      (HasDerivWithinAt.fun_sum
        (fun a _ => (hGamma i j a).mul (hGamma k a m)))
  have hraw :
      HasDerivWithinAt
        (fun s : Real =>
          DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I) (G.connection s)
            x0 i k j m)
        ((extDerivFun (I := I) (fun y : M => gammaDot y m k j) x0
            (coordinateFrameAt (I := I) x0 i x0) -
          extDerivFun (I := I) (fun y : M => gammaDot y m i j) x0
            (coordinateFrameAt (I := I) x0 k x0)) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            (gammaDot x0 a k j *
              DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
                (G.connection base) x0 i a m +
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
                (G.connection base) x0 k j a *
              gammaDot x0 m i a)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            (gammaDot x0 a i j *
              DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
                (G.connection base) x0 k a m +
            DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I)
                (G.connection base) x0 i j a *
              gammaDot x0 m k a)))
        timeSet
        base := by
    simpa [DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt, sub_eq_add_neg, add_assoc,
      Finset.sum_add_distrib] using
      (((hD_i.sub hD_k).add hprod_left).sub hprod_right)
  refine hraw.congr_deriv ?_
  have hsymm :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base) x0 a b c =
          DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base) x0 b a c := by
    intro a b c
    exact christoffelCoordAt_symm_of_lc (I := I) (G.connection base)
      (G.metric base) (hLC base) x0 a b c
  let Gamma : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b c =>
      DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) (G.connection base) x0 a b c
  let A : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b c => gammaDot x0 c a b
  let dA : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun dir a b c =>
      extDerivFun (I := I) (fun y : M => gammaDot y c a b) x0
        (coordinateFrameAt (I := I) x0 dir x0)
  have hGammaSymm :
      ∀ a b c : CoordinateIdx (𝕜 := Real) E, Gamma a b c = Gamma b a c := by
    intro a b c
    exact hsymm a b c
  simpa [Gamma, A, dA, gammaCovCoordAt, covDGamma] using
    (curvVarAlg Gamma A dA hGammaSymm i k j m)



omit [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem lcRicciVarCoord
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (timeSet : Set Real) (base : Real) (x0 : M)
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (hvar : gammaCoordDerivAt (I := I) G timeSet base x0 gammaDot)
    (hmix : gammaMixedCoordAt (I := I) G timeSet base x0 gammaDot)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        DifferentialGeometry.Integral.Connection.christoffelRicciCoeffAt (I := I) (G.connection s)
          x0 i j)
      (ricciVarCoordRHS (I := I) (G.connection base) gammaDot x0 i j)
      timeSet
      base := by
  classical
  have hsum :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ k : CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Integral.Connection.christoffelCurvCoeffAt (I := I)
              (G.connection s) x0 k i j k)
        (∑ k : CoordinateIdx (𝕜 := Real) E,
          (gammaCovCoordAt (I := I) (G.connection base) gammaDot x0 k k i j -
            gammaCovCoordAt (I := I) (G.connection base) gammaDot x0 i k k j))
        timeSet
        base := by
    exact HasDerivWithinAt.fun_sum fun k _ =>
      curvVarCoord (I := I) G hLC timeSet base x0 gammaDot hvar hmix k i j k
  refine hsum.congr_deriv ?_
  simp [ricciVarCoordRHS, gammaTraceCovAt, Finset.sum_sub_distrib]


def scalarCoordDerivAt
    (f : M -> Real) (x0 : M) (i : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) f x0 (coordinateFrameAt (I := I) x0 i x0)



def scalarCoordDerivFun
    (f : M -> Real) (x0 : M) (j : CoordinateIdx (𝕜 := Real) E)
    (x : M) : Real :=
  extDerivFun (I := I) f x (coordinateFrameAt (I := I) x0 j x)


def scalarCoordSecondAt
    (f : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (scalarCoordDerivFun (I := I) f x0 j) x0
    (coordinateFrameAt (I := I) x0 i x0)



omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
private theorem extDerivFun_congr_eventually_real
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[nhds x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem traceExtSum
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x0 : M) (i j : CoordinateIdx (𝕜 := Real) E)
    (hmdiff :
      ∀ p : CoordinateIdx (𝕜 := Real) E,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gammaDot y p p j) x0) :
    (∑ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) (fun y : M => gammaDot y p p j) x0
          (coordinateFrameAt (I := I) x0 i x0)) =
      extDerivFun (I := I)
        (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot y p p j)
        x0 (coordinateFrameAt (I := I) x0 i x0) := by
  classical
  let t : Finset (CoordinateIdx (𝕜 := Real) E) := Finset.univ
  let F : CoordinateIdx (𝕜 := Real) E -> M -> Real :=
    fun p y => gammaDot y p p j
  have hsum := DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real
    (I := I) (t := t) (f := F)
    (x := x0) (v := coordinateFrameAt (I := I) x0 i x0)
    (by
      intro p _hp
      exact hmdiff p)
  have hfun :
      t.sum F =
        fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot y p p j := by
    funext y
    simp [t, F]
  rw [← hfun]
  simpa [t, F] using hsum.symm



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem gammaTracePoint
    (gInv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (metricCovDerivDt gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (metricTrace : M -> Real) (x0 : M)
    (a : CoordinateIdx (𝕜 := Real) E)
    (hgammaTrace :
      (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
        (1 / 2 : Real) * metricTraceCovAt gInv metricCovDerivDt x0 a)
    (hmetricTrace :
      metricTraceCovAt gInv metricCovDerivDt x0 a =
        scalarCoordDerivAt (I := I) metricTrace x0 a) :
    (∑ p : CoordinateIdx (𝕜 := Real) E, gammaDot x0 p p a) =
      (1 / 2 : Real) * scalarCoordDerivAt (I := I) metricTrace x0 a := by
  rw [hgammaTrace, hmetricTrace]




omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem metricTraceCov_eq_deriv
    (gInv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (metricDot : M -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real)
    (metricCovDerivDt :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (metricTrace : M -> Real) (x0 : M)
    (j : CoordinateIdx (𝕜 := Real) E)
    (metricDotDeriv gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (htrace_deriv :
      scalarCoordDerivAt (I := I) metricTrace x0 j =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            (gInv x0 p l * metricDotDeriv p l +
              gInvDeriv p l * metricDot x0 p l))
    (hmetricCov :
      ∀ p l : CoordinateIdx (𝕜 := Real) E,
        metricCovDerivDt x0 j p l =
          metricDotDeriv p l -
            (∑ a : CoordinateIdx (𝕜 := Real) E,
              DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 j p a *
                metricDot x0 a l) -
            (∑ a : CoordinateIdx (𝕜 := Real) E,
              DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 j l a *
                metricDot x0 p a))
    (hinv_contract :
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInvDeriv p l * metricDot x0 p l) =
        -∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l *
              ((∑ a : CoordinateIdx (𝕜 := Real) E,
                DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 j p a *
                  metricDot x0 a l) +
               (∑ a : CoordinateIdx (𝕜 := Real) E,
                DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 j l a *
                  metricDot x0 p a))) :
    metricTraceCovAt gInv metricCovDerivDt x0 j =
      scalarCoordDerivAt (I := I) metricTrace x0 j := by
  classical
  let corr :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun p l =>
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 j p a *
          metricDot x0 a l) +
      (∑ a : CoordinateIdx (𝕜 := Real) E,
        DifferentialGeometry.Integral.Connection.christoffelCoordAt (I := I) cov x0 j l a *
          metricDot x0 p a)
  calc
    metricTraceCovAt gInv metricCovDerivDt x0 j =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l * (metricDotDeriv p l - corr p l) := by
          unfold metricTraceCovAt corr
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hmetricCov p l]
          ring
    _ =
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l * metricDotDeriv p l) -
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l * corr p l) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ =
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInv x0 p l * metricDotDeriv p l) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          ∑ l : CoordinateIdx (𝕜 := Real) E,
            gInvDeriv p l * metricDot x0 p l) := by
          rw [hinv_contract]
          unfold corr
          ring
    _ = scalarCoordDerivAt (I := I) metricTrace x0 j := by
          rw [htrace_deriv]
          simp [Finset.sum_add_distrib]



omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem traceDerivAt
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricTrace : M -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {x : M} (d : Idx)
    (htrace :
      metricTrace =ᶠ[nhds x]
        fun y : M => ∑ p : Idx, ∑ l : Idx,
          gInv y p l * metricDot y p l)
    (hgInv_mdiff : ∀ p l : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y p l) x)
    (hmetricDot_mdiff : ∀ p l : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => metricDot y p l) x) :
    extDerivFun (I := I) metricTrace x (frame d x) =
      ∑ p : Idx, ∑ l : Idx,
        (gInv x p l *
          extDerivFun (I := I) (fun y : M => metricDot y p l)
            x (frame d x) +
        extDerivFun (I := I) (fun y : M => gInv y p l)
            x (frame d x) *
          metricDot x p l) := by
  classical
  have hcongr := extDerivFun_congr_eventually_real
    (I := I) (x := x) (frame d x) htrace
  rw [hcongr]
  have hmdiffInner : ∀ p : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ∑ l : Idx, gInv y p l * metricDot y p l) x := by
    intro p
    have hmd :=
      DifferentialGeometry.Tensor.Coordinates.mdiffAt_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv y p l * metricDot y p l)
        (by
          intro l _hl
          exact (hgInv_mdiff p l).mul (hmetricDot_mdiff p l))
    have hfun :
        ((Finset.univ : Finset Idx).sum
          (fun l : Idx => fun y : M =>
            gInv y p l * metricDot y p l)) =
          (fun y : M =>
            ∑ l : Idx, gInv y p l * metricDot y p l) := by
      funext y
      simp
    rw [← hfun]
    exact hmd
  have houter :
      extDerivFun (I := I)
          (fun y : M => ∑ p : Idx, ∑ l : Idx,
            gInv y p l * metricDot y p l)
          x (frame d x) =
        ∑ p : Idx,
          extDerivFun (I := I)
            (fun y : M => ∑ l : Idx, gInv y p l * metricDot y p l)
            x (frame d x) := by
    have hsum := DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (f := fun p y => ∑ l : Idx, gInv y p l * metricDot y p l)
      (x := x) (v := frame d x)
      (by
        intro p _hp
        exact hmdiffInner p)
    have hfun :
        ((Finset.univ : Finset Idx).sum
          (fun p : Idx => fun y : M =>
            ∑ l : Idx, gInv y p l * metricDot y p l)) =
          (fun y : M => ∑ p : Idx, ∑ l : Idx,
            gInv y p l * metricDot y p l) := by
      funext y
      simp
    rw [← hfun]
    exact hsum
  rw [houter]
  refine Finset.sum_congr rfl fun p _hp => ?_
  have hinner :
      extDerivFun (I := I)
          (fun y : M => ∑ l : Idx, gInv y p l * metricDot y p l)
          x (frame d x) =
        ∑ l : Idx,
          extDerivFun (I := I)
            (fun y : M => gInv y p l * metricDot y p l)
            x (frame d x) := by
    have hsum := DifferentialGeometry.Tensor.Coordinates.extDerivFun_finset_sum_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (f := fun l y => gInv y p l * metricDot y p l)
      (x := x) (v := frame d x)
      (by
        intro l _hl
        exact (hgInv_mdiff p l).mul (hmetricDot_mdiff p l))
    have hfun :
        ((Finset.univ : Finset Idx).sum
          (fun l : Idx => fun y : M =>
            gInv y p l * metricDot y p l)) =
          (fun y : M =>
            ∑ l : Idx, gInv y p l * metricDot y p l) := by
      funext y
      simp
    rw [← hfun]
    exact hsum
  rw [hinner]
  refine Finset.sum_congr rfl fun l _hl => ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    DifferentialGeometry.Tensor.Coordinates.extDerivFun_mul_real
      (I := I) (x := x) (frame d x)
      (hgInv_mdiff p l) (hmetricDot_mdiff p l)

private theorem traceCancelAlg
    {ι : Type*} [Fintype ι]
    (G V DU : ι -> ι -> Real)
    (Γ : ι -> ι -> Real)
    (hDU : ∀ p l : ι,
      DU p l =
        -((∑ a : ι, Γ a p * G a l) +
          (∑ a : ι, Γ a l * G p a))) :
    (∑ p : ι, ∑ l : ι, DU p l * V p l) =
      -∑ p : ι, ∑ l : ι,
        G p l *
          ((∑ a : ι, Γ p a * V a l) +
           (∑ a : ι, Γ l a * V p a)) := by
  classical
  have hfirst :
      (∑ p : ι, ∑ l : ι,
        (∑ a : ι, Γ a p * G a l) * V p l) =
        ∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ p a * V a l) := by
    calc
      (∑ p : ι, ∑ l : ι,
        (∑ a : ι, Γ a p * G a l) * V p l)
          =
        ∑ p : ι, ∑ l : ι, ∑ a : ι,
          Γ a p * G a l * V p l := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ a : ι, ∑ l : ι, ∑ p : ι,
          Γ a p * G a l * V p l := by
            calc
              (∑ p : ι, ∑ l : ι, ∑ a : ι,
                Γ a p * G a l * V p l)
                  =
                ∑ p : ι, ∑ a : ι, ∑ l : ι,
                  Γ a p * G a l * V p l := by
                    refine Finset.sum_congr rfl fun p _ => ?_
                    rw [Finset.sum_comm]
              _ = ∑ a : ι, ∑ p : ι, ∑ l : ι,
                  Γ a p * G a l * V p l := by
                    rw [Finset.sum_comm]
              _ = ∑ a : ι, ∑ l : ι, ∑ p : ι,
                  Γ a p * G a l * V p l := by
                    refine Finset.sum_congr rfl fun a _ => ?_
                    rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ l : ι, ∑ a : ι,
          Γ p a * G p l * V a l := by
            simp
      _ = ∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ p a * V a l) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring_nf
  have hsecond :
      (∑ p : ι, ∑ l : ι,
        (∑ a : ι, Γ a l * G p a) * V p l) =
        ∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ l a * V p a) := by
    calc
      (∑ p : ι, ∑ l : ι,
        (∑ a : ι, Γ a l * G p a) * V p l)
          =
        ∑ p : ι, ∑ l : ι, ∑ a : ι,
          Γ a l * G p a * V p l := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ p : ι, ∑ a : ι, ∑ l : ι,
          Γ a l * G p a * V p l := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ p : ι, ∑ l : ι, ∑ a : ι,
          Γ l a * G p l * V p a := by
            simp
      _ = ∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ l a * V p a) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring_nf
  calc
    (∑ p : ι, ∑ l : ι, DU p l * V p l)
        =
      ∑ p : ι, ∑ l : ι,
        -((∑ a : ι, Γ a p * G a l) +
          (∑ a : ι, Γ a l * G p a)) * V p l := by
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hDU p l]
    _ =
      -((∑ p : ι, ∑ l : ι,
          (∑ a : ι, Γ a p * G a l) * V p l) +
        (∑ p : ι, ∑ l : ι,
          (∑ a : ι, Γ a l * G p a) * V p l)) := by
        simp [add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ =
      -((∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ p a * V a l)) +
        (∑ p : ι, ∑ l : ι,
          G p l * (∑ a : ι, Γ l a * V p a))) := by
        rw [hfirst, hsecond]
    _ =
      -∑ p : ι, ∑ l : ι,
        G p l *
          ((∑ a : ι, Γ p a * V a l) +
           (∑ a : ι, Γ l a * V p a)) := by
        simp [Finset.sum_add_distrib, mul_add]



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem gInvTraceCancel
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (metricDot : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d : Idx)
    (hzero : ∀ p l : Idx,
      DifferentialGeometry.Tensor.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I) gInv cov frame hframe x d p l = 0) :
    (∑ p : Idx, ∑ l : Idx,
      extDerivFun (I := I) (fun y : M => gInv y p l) x (frame d x) *
        metricDot x p l) =
      -∑ p : Idx, ∑ l : Idx,
        gInv x p l *
          ((∑ a : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe x d p a *
              metricDot x a l) +
           (∑ a : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe x d l a *
              metricDot x p a)) := by
  classical
  let DU : Idx -> Idx -> Real := fun p l =>
    extDerivFun (I := I) (fun y : M => gInv y p l) x (frame d x)
  let G : Idx -> Idx -> Real := fun p l => gInv x p l
  let V : Idx -> Idx -> Real := fun p l => metricDot x p l
  let Γ : Idx -> Idx -> Real := fun a c =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe x d a c
  have hDU : ∀ p l : Idx,
      DU p l =
        -((∑ a : Idx, Γ a p * G a l) +
          (∑ a : Idx, Γ a l * G p a)) := by
    intro p l
    have hz := hzero p l
    unfold DifferentialGeometry.Tensor.Coordinates.inverseMetricCovDerivForMetricCompInFrame at hz
    change DU p l +
        (∑ a : Idx, Γ a p * G a l) +
        (∑ a : Idx, Γ a l * G p a) = 0 at hz
    linarith
  simpa [DU, G, V, Γ] using traceCancelAlg G V DU Γ hDU



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem traceCovEqDeriv
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (metricTrace : M -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (d : Idx)
    (hmetricCov : ∀ p l : Idx,
      metricCovDerivDt x d p l =
        dotCovAt (I := I) cov frame hframe metricDot x d p l)
    (htrace :
      metricTrace =ᶠ[nhds x]
        fun y : M => ∑ p : Idx, ∑ l : Idx,
          gInv y p l * metricDot y p l)
    (hgInv_mdiff : ∀ p l : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y p l) x)
    (hmetricDot_mdiff : ∀ p l : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => metricDot y p l) x)
    (hzero : ∀ p l : Idx,
      DifferentialGeometry.Tensor.Coordinates.inverseMetricCovDerivForMetricCompInFrame
        (I := I) gInv cov frame hframe x d p l = 0) :
    metricTraceCovAt gInv metricCovDerivDt x d =
      extDerivFun (I := I) metricTrace x (frame d x) := by
  classical
  have htraceDeriv := traceDerivAt
    (I := I) gInv metricDot metricTrace frame d htrace
    hgInv_mdiff hmetricDot_mdiff
  have hcancel := gInvTraceCancel
    (I := I) gInv metricDot cov frame hframe x d hzero
  calc
    metricTraceCovAt gInv metricCovDerivDt x d =
        ∑ p : Idx, ∑ l : Idx,
          gInv x p l *
            dotCovAt (I := I) cov frame hframe metricDot x d p l := by
          unfold metricTraceCovAt
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hmetricCov p l]
    _ =
        (∑ p : Idx, ∑ l : Idx,
          gInv x p l *
            extDerivFun (I := I) (fun y : M => metricDot y p l)
              x (frame d x)) +
        (∑ p : Idx, ∑ l : Idx,
          extDerivFun (I := I) (fun y : M => gInv y p l)
              x (frame d x) *
            metricDot x p l) := by
          rw [hcancel]
          unfold dotCovAt
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, mul_add, mul_sub]
          ring
    _ =
        ∑ p : Idx, ∑ l : Idx,
          (gInv x p l *
            extDerivFun (I := I) (fun y : M => metricDot y p l)
              x (frame d x) +
          extDerivFun (I := I) (fun y : M => gInv y p l)
              x (frame d x) *
            metricDot x p l) := by
          simp [Finset.sum_add_distrib]
    _ = extDerivFun (I := I) metricTrace x (frame d x) := htraceDeriv.symm



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq (CoordinateIdx (𝕜 := Real) E)] in
theorem gammaTraceDeriv
    (gammaDot :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (metricTrace : M -> Real) (x0 : M)
    (i j : CoordinateIdx (𝕜 := Real) E)
    (htrace_eventual :
      (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
        gammaDot y p p j) =ᶠ[nhds x0]
          fun y : M =>
            (1 / 2 : Real) *
              scalarCoordDerivFun (I := I) metricTrace x0 j y)
    (hscalar_mdiff :
      MDifferentiableAt I 𝓘(Real, Real)
        (scalarCoordDerivFun (I := I) metricTrace x0 j) x0) :
    extDerivFun (I := I)
        (fun y : M => ∑ p : CoordinateIdx (𝕜 := Real) E,
          gammaDot y p p j)
        x0 (coordinateFrameAt (I := I) x0 i x0) =
      (1 / 2 : Real) *
        scalarCoordSecondAt (I := I) metricTrace x0 i j := by
  have hcongr := extDerivFun_congr_eventually_real
    (I := I) (x := x0)
    (coordinateFrameAt (I := I) x0 i x0) htrace_eventual
  rw [hcongr]
  have hconst := extDerivFun_const_mul
    (I := I) (c := (1 / 2 : Real))
    (f := scalarCoordDerivFun (I := I) metricTrace x0 j)
    (x := x0) hscalar_mdiff
  change extDerivFun (I := I)
      (fun y : M =>
        (1 / 2 : Real) *
          scalarCoordDerivFun (I := I) metricTrace x0 j y)
      x0 (coordinateFrameAt (I := I) x0 i x0) = _
  rw [hconst]
  rfl

end RicciCoordVariation

end DifferentialGeometry.Integral.Connection
