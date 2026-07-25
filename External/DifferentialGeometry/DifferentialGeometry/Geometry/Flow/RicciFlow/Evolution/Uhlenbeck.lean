import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.Basic
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false












noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]


abbrev MatrixComp (M : Type*) (Idx : Type*) := Real -> M -> Idx -> Idx -> Real


abbrev FourComp (M : Type*) (Idx : Type*) :=
  Real -> M -> Idx -> Idx -> Idx -> Idx -> Real



def MetricCompRicciFlowInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (metricComp Ric : MatrixComp M Idx) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => metricComp s x i j)
      (-2 * Ric (t : Real) x i j)
      D.carrier
      (t : Real)




def FrameRicciODEInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (frameComp ricciOneUp : MatrixComp M Idx) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (a k : Idx),
    HasDerivWithinAt
      (fun s : Real => frameComp s x a k)
      (∑ l : Idx, ricciOneUp (t : Real) x l k * frameComp (t : Real) x a l)
      D.carrier
      (t : Real)




def RicciEndomorphismCompatibleInFrame
    (metricComp Ric ricciOneUp : MatrixComp M Idx) : Prop :=
  forall (t : Real) (x : M) (v w : Idx -> Real),
    (∑ l : Idx, ∑ k : Idx, ∑ j : Idx,
        v l * ricciOneUp t x l k * w j * metricComp t x k j) =
      (∑ i : Idx, ∑ j : Idx, v i * w j * Ric t x i j) /\
    (∑ i : Idx, ∑ l : Idx, ∑ k : Idx,
        v i * w l * ricciOneUp t x l k * metricComp t x i k) =
      (∑ i : Idx, ∑ j : Idx, v i * w j * Ric t x i j)


def movingFrameGramInFrame
    (metricComp frameComp : MatrixComp M Idx)
    (t : Real) (x : M) (a b : Idx) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    frameComp t x a i * frameComp t x b j * metricComp t x i j






def MovingFrameGramDerivativeZeroOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (metricComp frameComp : MatrixComp M Idx) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (a b : Idx),
    HasDerivWithinAt
      (fun s : Real => movingFrameGramInFrame metricComp frameComp s x a b)
      0
      D.carrier
      (t : Real)






abbrev MovingFrameGramConstantOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (metricComp frameComp : MatrixComp M Idx) : Prop :=
  MovingFrameGramDerivativeZeroOn (D := D) metricComp frameComp



def MovingFrameGramValueConstantOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (metricComp frameComp : MatrixComp M Idx) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (a b : Idx),
    movingFrameGramInFrame metricComp frameComp (t : Real) x a b =
      movingFrameGramInFrame metricComp frameComp D.initial x a b

omit [DecidableEq Idx] in
private theorem gramLeft_eq_ric
    (metricComp Ric ricciOneUp frameComp : MatrixComp M Idx)
    (hcompat : RicciEndomorphismCompatibleInFrame
      metricComp Ric ricciOneUp)
    (t : Real) (x : M) (a b : Idx) :
    (∑ i : Idx, ∑ j : Idx,
      (∑ l : Idx, ricciOneUp t x l i * frameComp t x a l) *
        frameComp t x b j * metricComp t x i j) =
      ∑ i : Idx, ∑ j : Idx,
        frameComp t x a i * frameComp t x b j * Ric t x i j := by
  classical
  let v : Idx -> Real := fun l => frameComp t x a l
  let w : Idx -> Real := fun j => frameComp t x b j
  have h := (hcompat t x v w).1
  calc
    (∑ i : Idx, ∑ j : Idx,
      (∑ l : Idx, ricciOneUp t x l i * frameComp t x a l) *
        frameComp t x b j * metricComp t x i j)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ l : Idx,
        ricciOneUp t x l i * frameComp t x a l *
          frameComp t x b j * metricComp t x i j := by
          simp [Finset.sum_mul]
    _ =
      ∑ i : Idx, ∑ l : Idx, ∑ j : Idx,
        frameComp t x a l * ricciOneUp t x l i *
          frameComp t x b j * metricComp t x i j := by
          refine Finset.sum_congr rfl fun i _hi => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _hl => ?_
          refine Finset.sum_congr rfl fun j _hj => ?_
          ring_nf
    _ =
      ∑ l : Idx, ∑ i : Idx, ∑ j : Idx,
        frameComp t x a l * ricciOneUp t x l i *
          frameComp t x b j * metricComp t x i j := by
          rw [Finset.sum_comm]
    _ = ∑ i : Idx, ∑ j : Idx,
        frameComp t x a i * frameComp t x b j * Ric t x i j := by
          simpa [v, w, mul_assoc, mul_left_comm, mul_comm] using h

omit [DecidableEq Idx] in
private theorem gramRight_eq_ric
    (metricComp Ric ricciOneUp frameComp : MatrixComp M Idx)
    (hcompat : RicciEndomorphismCompatibleInFrame
      metricComp Ric ricciOneUp)
    (t : Real) (x : M) (a b : Idx) :
    (∑ i : Idx, ∑ j : Idx,
      frameComp t x a i *
        (∑ l : Idx, ricciOneUp t x l j * frameComp t x b l) *
        metricComp t x i j) =
      ∑ i : Idx, ∑ j : Idx,
        frameComp t x a i * frameComp t x b j * Ric t x i j := by
  classical
  let v : Idx -> Real := fun i => frameComp t x a i
  let w : Idx -> Real := fun l => frameComp t x b l
  have h := (hcompat t x v w).2
  calc
    (∑ i : Idx, ∑ j : Idx,
      frameComp t x a i *
        (∑ l : Idx, ricciOneUp t x l j * frameComp t x b l) *
        metricComp t x i j)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ l : Idx,
        frameComp t x a i * frameComp t x b l *
          ricciOneUp t x l j * metricComp t x i j := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ =
      ∑ i : Idx, ∑ l : Idx, ∑ j : Idx,
        frameComp t x a i * frameComp t x b l *
          ricciOneUp t x l j * metricComp t x i j := by
          refine Finset.sum_congr rfl fun i _hi => ?_
          rw [Finset.sum_comm]
    _ = ∑ i : Idx, ∑ j : Idx,
        frameComp t x a i * frameComp t x b j * Ric t x i j := by
          simpa [v, w, mul_assoc, mul_left_comm, mul_comm] using h

omit [DecidableEq Idx] in
private theorem gramMetric_eq_neg_two_ric
    (Ric frameComp : MatrixComp M Idx)
    (t : Real) (x : M) (a b : Idx) :
    (∑ i : Idx, ∑ j : Idx,
      (frameComp t x a i * frameComp t x b j) *
        (-2 * Ric t x i j)) =
      -2 * (∑ i : Idx, ∑ j : Idx,
        frameComp t x a i * frameComp t x b j * Ric t x i j) := by
  classical
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]


omit [DecidableEq Idx] in
theorem evolvingFrameGram_constant_of_ricciFlow
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (metricComp Ric frameComp ricciOneUp :
      MatrixComp M Idx)
    (hmetric : MetricCompRicciFlowInFrameOn (D := D) metricComp Ric)
    (hframe : FrameRicciODEInFrameOn (D := D) frameComp ricciOneUp)
    (hcompat : RicciEndomorphismCompatibleInFrame
      metricComp Ric ricciOneUp) :
    MovingFrameGramConstantOn (D := D) metricComp frameComp := by
  classical
  intro t x a b
  let τ : Real := (t : Real)
  let dA : Idx -> Real := fun i =>
    ∑ l : Idx, ricciOneUp τ x l i * frameComp τ x a l
  let dB : Idx -> Real := fun j =>
    ∑ l : Idx, ricciOneUp τ x l j * frameComp τ x b l
  let ricSum : Real :=
    ∑ i : Idx, ∑ j : Idx,
      frameComp τ x a i * frameComp τ x b j * Ric τ x i j
  let termDeriv : Idx -> Idx -> Real := fun i j =>
    (dA i * frameComp τ x b j + frameComp τ x a i * dB j) *
      metricComp τ x i j +
      (frameComp τ x a i * frameComp τ x b j) *
        (-2 * Ric τ x i j)
  have hsum :
      HasDerivWithinAt
        (fun s : Real => ∑ i : Idx, ∑ j : Idx,
          frameComp s x a i * frameComp s x b j *
            metricComp s x i j)
        (∑ i : Idx, ∑ j : Idx, termDeriv i j)
        D.carrier τ := by
    refine HasDerivWithinAt.fun_sum ?_
    intro i _hi
    refine HasDerivWithinAt.fun_sum ?_
    intro j _hj
    have hA := hframe t x a i
    have hB := hframe t x b j
    have hG := hmetric t x i j
    have hAB := hA.mul hB
    have hABG := hAB.mul hG
    simpa [τ, dA, dB, termDeriv, mul_assoc] using hABG
  have hleft :
      (∑ i : Idx, ∑ j : Idx,
        dA i * frameComp τ x b j * metricComp τ x i j) = ricSum := by
    simpa [τ, dA, ricSum] using
      gramLeft_eq_ric metricComp Ric ricciOneUp frameComp hcompat τ x a b
  have hright :
      (∑ i : Idx, ∑ j : Idx,
        frameComp τ x a i * dB j * metricComp τ x i j) = ricSum := by
    simpa [τ, dB, ricSum] using
      gramRight_eq_ric metricComp Ric ricciOneUp frameComp hcompat τ x a b
  have hmetricTerm :
      (∑ i : Idx, ∑ j : Idx,
        (frameComp τ x a i * frameComp τ x b j) *
          (-2 * Ric τ x i j)) = -2 * ricSum := by
    simpa [τ, ricSum] using
      gramMetric_eq_neg_two_ric Ric frameComp τ x a b
  have hzero : (∑ i : Idx, ∑ j : Idx, termDeriv i j) = 0 := by
    calc
      (∑ i : Idx, ∑ j : Idx, termDeriv i j)
          =
        (∑ i : Idx, ∑ j : Idx,
          dA i * frameComp τ x b j * metricComp τ x i j) +
        (∑ i : Idx, ∑ j : Idx,
          frameComp τ x a i * dB j * metricComp τ x i j) +
        (∑ i : Idx, ∑ j : Idx,
          (frameComp τ x a i * frameComp τ x b j) *
            (-2 * Ric τ x i j)) := by
            simp [termDeriv, Finset.sum_add_distrib,
              mul_add, mul_assoc, mul_left_comm, mul_comm]
      _ = ricSum + ricSum + (-2 * ricSum) := by
            rw [hleft, hright, hmetricTerm]
      _ = 0 := by ring
  simpa [movingFrameGramInFrame, τ, hzero] using hsum


def MovingFrameOrthonormalInFrame
    (metricComp frameComp : MatrixComp M Idx)
    (t : Real) (x : M) : Prop :=
  forall a b : Idx,
    movingFrameGramInFrame metricComp frameComp t x a b =
      if a = b then 1 else 0



theorem evolvingFrame_orthonormal_of_initial
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (metricComp frameComp : MatrixComp M Idx)
    (hconst : MovingFrameGramValueConstantOn (D := D) metricComp frameComp)
    (_hinit : forall x : M,
      MovingFrameOrthonormalInFrame metricComp frameComp D.initial x) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      MovingFrameOrthonormalInFrame metricComp frameComp (t : Real) x := by
  intro t x a b
  rw [hconst t x a b]
  exact _hinit x a b



def BundleIsomorphismODEInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (iota ricciOneUp : Real -> M -> Idx -> Idx -> Real) : Prop :=
  FrameRicciODEInFrameOn (D := D) iota ricciOneUp


def uhlenbeckPullbackMetricCompInFrame
    (metricComp iota : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b : Idx) : Real :=
  movingFrameGramInFrame metricComp iota t x a b


def UhlenbeckPullbackMetricComponents
    (metricComp iota hComp : MatrixComp M Idx) : Prop :=
  forall (t : Real) (x : M) (a b : Idx),
    hComp t x a b =
      uhlenbeckPullbackMetricCompInFrame metricComp iota t x a b



omit [DecidableEq Idx] in
theorem uhlenbeck_pullbackMetric_constant_of_ricciFlow
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (metricComp Ric iota ricciOneUp :
      MatrixComp M Idx)
    (hmetric : MetricCompRicciFlowInFrameOn (D := D) metricComp Ric)
    (hiota : BundleIsomorphismODEInFrameOn (D := D) iota ricciOneUp)
    (hcompat : RicciEndomorphismCompatibleInFrame
      metricComp Ric ricciOneUp) :
    MovingFrameGramConstantOn (D := D) metricComp iota :=
  evolvingFrameGram_constant_of_ricciFlow
    (D := D) metricComp Ric iota ricciOneUp hmetric hiota hcompat



def uhlenbeckPullbackRmInFrame
    (iota : MatrixComp M Idx)
    (Rm04 : FourComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    iota t x a i * iota t x b j * iota t x c k * iota t x d l *
      Rm04 t x i j k l


def UhlenbeckPullbackRmComponents
    (iota : MatrixComp M Idx)
    (Rm04 pulledRm : FourComp M Idx) : Prop :=
  forall (t : Real) (x : M) (a b c d : Idx),
    pulledRm t x a b c d =
      uhlenbeckPullbackRmInFrame iota Rm04 t x a b c d


def uhlenbeckBTensorInFrame
    (hInv : MatrixComp M Idx)
    (pulledRm : FourComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ e : Idx, ∑ g : Idx, ∑ f : Idx, ∑ r : Idx,
    hInv t x e g * hInv t x f r *
      pulledRm t x a e b f * pulledRm t x c g d r


def UhlenbeckBTensorComponents
    (hInv : MatrixComp M Idx)
    (pulledRm B : FourComp M Idx) : Prop :=
  forall (t : Real) (x : M) (a b c d : Idx),
    B t x a b c d = uhlenbeckBTensorInFrame hInv pulledRm t x a b c d





def UhlenbeckPullbackBComponents
    (iota : MatrixComp M Idx)
    (Borig Bpull : FourComp M Idx) : Prop :=
  forall (t : Real) (x : M) (a b c d : Idx),
    Bpull t x a b c d =
      uhlenbeckPullbackRmInFrame iota Borig t x a b c d



def UhlenbeckLaplacianPullbackComponents
    (iota : MatrixComp M Idx)
    (roughLapRm04 roughLapD : FourComp M Idx) : Prop :=
  forall (t : Real) (x : M) (a b c d : Idx),
    roughLapD t x a b c d =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        iota t x a i * iota t x b j * iota t x c k * iota t x d l *
          roughLapRm04 t x i j k l


def riemann04RicciDriftInFrame
    (ricciOneUp : MatrixComp M Idx)
    (Rm04 : FourComp M Idx)
    (t : Real) (x : M) (i j k l : Idx) : Real :=
  (∑ p : Idx, ricciOneUp t x i p * Rm04 t x p j k l) +
    (∑ p : Idx, ricciOneUp t x j p * Rm04 t x i p k l) +
    (∑ p : Idx, ricciOneUp t x k p * Rm04 t x i j p l) +
    (∑ p : Idx, ricciOneUp t x l p * Rm04 t x i j k p)


private def iotaDotInFrame
    (iota ricciOneUp : MatrixComp M Idx)
    (t : Real) (x : M) (a i : Idx) : Real :=
  ∑ p : Idx, ricciOneUp t x p i * iota t x a p



private def derivProduct5RHS
    (u v w y z du dv dw dy dz : Real) : Real :=
  ((((du * v + u * dv) * w + (u * v) * dw) * y +
      ((u * v) * w) * dy) * z +
    (((u * v) * w) * y) * dz)

private theorem derivProduct5RHS_eq
    (u v w y z du dv dw dy dz : Real) :
    derivProduct5RHS u v w y z du dv dw dy dz =
      du * v * w * y * z + u * dv * w * y * z +
        u * v * dw * y * z + u * v * w * dy * z +
          u * v * w * y * dz := by
  unfold derivProduct5RHS
  ring

omit [DecidableEq Idx] in
private theorem sum4_derivProduct5RHS_eq
    (A B C D DA DB DC DD : Idx -> Real)
    (Z DZ : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      derivProduct5RHS (A i) (B j) (C k) (D l) (Z i j k l)
        (DA i) (DB j) (DC k) (DD l) (DZ i j k l)) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        DA i * B j * C k * D l * Z i j k l) +
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        A i * DB j * C k * D l * Z i j k l) +
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        A i * B j * DC k * D l * Z i j k l) +
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        A i * B j * C k * DD l * Z i j k l) +
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        A i * B j * C k * D l * DZ i j k l) := by
  classical
  simp [derivProduct5RHS_eq, Finset.sum_add_distrib, add_assoc]


private def uhlenbeckPullbackRmDerivRHSInFrame
    (iota : MatrixComp M Idx)
    (Rm04 roughLapRm04 B : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    derivProduct5RHS
      (iota t x a i) (iota t x b j) (iota t x c k)
      (iota t x d l) (Rm04 t x i j k l)
      (iotaDotInFrame iota Rup t x a i)
      (iotaDotInFrame iota Rup t x b j)
      (iotaDotInFrame iota Rup t x c k)
      (iotaDotInFrame iota Rup t x d l)
      (roughLapRm04 t x i j k l -
        2 * (B t x i j k l - B t x i j l k +
          B t x i k j l - B t x i l j k) -
        riemann04RicciDriftInFrame Rup Rm04 t x i j k l)



private def uhlenbeckIotaDriftInFrame
    (iota : MatrixComp M Idx)
    (Rm04 : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    (iotaDotInFrame iota Rup t x a i * iota t x b j *
        iota t x c k * iota t x d l * Rm04 t x i j k l +
      iota t x a i * iotaDotInFrame iota Rup t x b j *
        iota t x c k * iota t x d l * Rm04 t x i j k l +
      iota t x a i * iota t x b j *
        iotaDotInFrame iota Rup t x c k * iota t x d l *
          Rm04 t x i j k l +
      iota t x a i * iota t x b j * iota t x c k *
        iotaDotInFrame iota Rup t x d l * Rm04 t x i j k l)



private def uhlenbeckPullbackDriftInFrame
    (iota : MatrixComp M Idx)
    (Rm04 : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    iota t x a i * iota t x b j * iota t x c k * iota t x d l *
      riemann04RicciDriftInFrame Rup Rm04 t x i j k l

omit [DecidableEq Idx] in
private theorem sum4_swap34
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j l k) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  refine Finset.sum_congr rfl ?_
  intro j _hj
  simpa using (Finset.sum_comm :
    (∑ k : Idx, ∑ l : Idx, F i j k l) =
      ∑ l : Idx, ∑ k : Idx, F i j k l)

omit [DecidableEq Idx] in
private theorem sum4_swap23
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i k j l) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simpa using (Finset.sum_comm :
    (∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
      ∑ k : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l)

omit [DecidableEq Idx] in
private theorem sum4_cycle234
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i l j k) := by
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i k j l :=
        sum4_swap23 (Idx := Idx) F
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i l j k :=
        sum4_swap34 (Idx := Idx) (fun i j k l => F i k j l)

omit [DecidableEq Idx] in
private theorem sum4_mul_right
    (F : Idx -> Idx -> Idx -> Idx -> Real) (r : Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l * r) =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) * r := by
  classical
  simp [Finset.sum_mul]

omit [DecidableEq Idx] in
private theorem iotaDrift_first
    (iota : MatrixComp M Idx) (Rm04 : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iotaDotInFrame iota Rup t x a i * iota t x b j *
        iota t x c k * iota t x d l * Rm04 t x i j k l) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        (∑ p : Idx, Rup t x i p * Rm04 t x p j k l)) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iotaDotInFrame iota Rup t x a i * iota t x b j *
        iota t x c k * iota t x d l * Rm04 t x i j k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
        Rup t x p i * iota t x a p * iota t x b j *
          iota t x c k * iota t x d l * Rm04 t x i j k l := by
          simp [iotaDotInFrame, Finset.mul_sum, mul_left_comm,
            mul_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
        Rup t x i p * iota t x a i * iota t x b j *
          iota t x c k * iota t x d l * Rm04 t x p j k l := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (Tensor0SBundle.sum5_swap_first_last (Idx := Idx)
              (fun i j k l p =>
                Rup t x p i * iota t x a p * iota t x b j *
                  iota t x c k * iota t x d l * Rm04 t x i j k l))
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        iota t x a i * iota t x b j * iota t x c k * iota t x d l *
          (∑ p : Idx, Rup t x i p * Rm04 t x p j k l)) := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]

omit [DecidableEq Idx] in
private theorem iotaDrift_second
    (iota : MatrixComp M Idx) (Rm04 : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iotaDotInFrame iota Rup t x b j *
        iota t x c k * iota t x d l * Rm04 t x i j k l) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        (∑ p : Idx, Rup t x j p * Rm04 t x i p k l)) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iotaDotInFrame iota Rup t x b j *
        iota t x c k * iota t x d l * Rm04 t x i j k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
        iota t x a i * Rup t x p j * iota t x b p *
          iota t x c k * iota t x d l * Rm04 t x i j k l := by
          simp [iotaDotInFrame, Finset.mul_sum,
            mul_left_comm, mul_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
        iota t x a i * Rup t x j p * iota t x b j *
          iota t x c k * iota t x d l * Rm04 t x i p k l := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (Tensor0SBundle.sum5_swap_second_last (Idx := Idx)
              (fun i j k l p =>
                iota t x a i * Rup t x p j * iota t x b p *
                  iota t x c k * iota t x d l * Rm04 t x i j k l))
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        iota t x a i * iota t x b j * iota t x c k * iota t x d l *
          (∑ p : Idx, Rup t x j p * Rm04 t x i p k l)) := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]

omit [DecidableEq Idx] in
private theorem iotaDrift_third
    (iota : MatrixComp M Idx) (Rm04 : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j *
        iotaDotInFrame iota Rup t x c k * iota t x d l *
          Rm04 t x i j k l) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        (∑ p : Idx, Rup t x k p * Rm04 t x i j p l)) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j *
        iotaDotInFrame iota Rup t x c k * iota t x d l *
          Rm04 t x i j k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
        iota t x a i * iota t x b j * Rup t x p k *
          iota t x c p * iota t x d l * Rm04 t x i j k l := by
          simp [iotaDotInFrame, Finset.mul_sum,
            mul_left_comm, mul_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
        iota t x a i * iota t x b j * Rup t x k p *
          iota t x c k * iota t x d l * Rm04 t x i j p l := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (Tensor0SBundle.sum5_swap_third_last (Idx := Idx)
              (fun i j k l p =>
                iota t x a i * iota t x b j * Rup t x p k *
                  iota t x c p * iota t x d l * Rm04 t x i j k l))
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        iota t x a i * iota t x b j * iota t x c k * iota t x d l *
          (∑ p : Idx, Rup t x k p * Rm04 t x i j p l)) := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]

omit [DecidableEq Idx] in
private theorem iotaDrift_fourth
    (iota : MatrixComp M Idx) (Rm04 : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k *
        iotaDotInFrame iota Rup t x d l * Rm04 t x i j k l) =
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        (∑ p : Idx, Rup t x l p * Rm04 t x i j k p)) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k *
        iotaDotInFrame iota Rup t x d l * Rm04 t x i j k l)
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
        iota t x a i * iota t x b j * iota t x c k *
          Rup t x p l * iota t x d p * Rm04 t x i j k l := by
          simp [iotaDotInFrame, Finset.mul_sum,
            mul_left_comm, mul_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ p : Idx,
        iota t x a i * iota t x b j * iota t x c k *
          Rup t x l p * iota t x d l * Rm04 t x i j k p := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (Tensor0SBundle.sum5_swap_fourth_last (Idx := Idx)
              (fun i j k l p =>
                iota t x a i * iota t x b j * iota t x c k *
                  Rup t x p l * iota t x d p * Rm04 t x i j k l))
    _ =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        iota t x a i * iota t x b j * iota t x c k * iota t x d l *
          (∑ p : Idx, Rup t x l p * Rm04 t x i j k p)) := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]

omit [DecidableEq Idx] in
private theorem iotaDrift_eq_pullbackDrift
    (iota : MatrixComp M Idx) (Rm04 : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) :
    uhlenbeckIotaDriftInFrame iota Rm04 Rup t x a b c d =
      uhlenbeckPullbackDriftInFrame iota Rm04 Rup t x a b c d := by
  classical
  calc
    uhlenbeckIotaDriftInFrame iota Rm04 Rup t x a b c d =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          iotaDotInFrame iota Rup t x a i * iota t x b j *
            iota t x c k * iota t x d l * Rm04 t x i j k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          iota t x a i * iotaDotInFrame iota Rup t x b j *
            iota t x c k * iota t x d l * Rm04 t x i j k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          iota t x a i * iota t x b j *
            iotaDotInFrame iota Rup t x c k * iota t x d l *
              Rm04 t x i j k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          iota t x a i * iota t x b j * iota t x c k *
            iotaDotInFrame iota Rup t x d l * Rm04 t x i j k l) := by
          simp [uhlenbeckIotaDriftInFrame, Finset.sum_add_distrib, add_assoc]
    _ =
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          iota t x a i * iota t x b j * iota t x c k * iota t x d l *
            (∑ p : Idx, Rup t x i p * Rm04 t x p j k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          iota t x a i * iota t x b j * iota t x c k * iota t x d l *
            (∑ p : Idx, Rup t x j p * Rm04 t x i p k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          iota t x a i * iota t x b j * iota t x c k * iota t x d l *
            (∑ p : Idx, Rup t x k p * Rm04 t x i j p l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          iota t x a i * iota t x b j * iota t x c k * iota t x d l *
            (∑ p : Idx, Rup t x l p * Rm04 t x i j k p)) := by
          rw [iotaDrift_first iota Rm04 Rup t x a b c d]
          rw [iotaDrift_second iota Rm04 Rup t x a b c d]
          rw [iotaDrift_third iota Rm04 Rup t x a b c d]
          rw [iotaDrift_fourth iota Rm04 Rup t x a b c d]
    _ = uhlenbeckPullbackDriftInFrame iota Rm04 Rup t x a b c d := by
          simp [uhlenbeckPullbackDriftInFrame, riemann04RicciDriftInFrame,
            Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_assoc,
            mul_left_comm, mul_comm]


def Riemann04BTensorWithRicciDriftEvolutionInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (Rm04 roughLapRm04 B : FourComp M Idx)
    (ricciOneUp : MatrixComp M Idx) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (i j k l : Idx),
    HasDerivWithinAt
      (fun s : Real => Rm04 s x i j k l)
      (roughLapRm04 (t : Real) x i j k l -
        2 * (B (t : Real) x i j k l - B (t : Real) x i j l k +
          B (t : Real) x i k j l - B (t : Real) x i l j k) -
        riemann04RicciDriftInFrame ricciOneUp Rm04 (t : Real) x i j k l)
      D.carrier
      (t : Real)


def uhlenbeckCurvatureEvolutionRHSInFrame
    (roughLapD B : FourComp M Idx)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  roughLapD t x a b c d -
    2 * (B t x a b c d - B t x a b d c +
      B t x a c b d - B t x a d b c)



def UhlenbeckCurvatureEvolutionInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (pulledRm roughLapD B : FourComp M Idx) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (a b c d : Idx),
    HasDerivWithinAt
      (fun s : Real => pulledRm s x a b c d)
      (uhlenbeckCurvatureEvolutionRHSInFrame roughLapD B
        (t : Real) x a b c d)
      D.carrier
      (t : Real)

omit [DecidableEq Idx] in
private theorem uhlenbeckPullbackRm_deriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (iota : MatrixComp M Idx)
    (Rm04 roughLapRm04 B : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (hiota : BundleIsomorphismODEInFrameOn (D := D) iota Rup)
    (hrm : Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := D) Rm04 roughLapRm04 B Rup)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (a b c d : Idx) :
    HasDerivWithinAt
      (fun s : Real => uhlenbeckPullbackRmInFrame iota Rm04 s x a b c d)
      (uhlenbeckPullbackRmDerivRHSInFrame iota Rm04 roughLapRm04 B Rup
        (t : Real) x a b c d)
      D.carrier
      (t : Real) := by
  classical
  refine HasDerivWithinAt.fun_sum ?_
  intro i _hi
  refine HasDerivWithinAt.fun_sum ?_
  intro j _hj
  refine HasDerivWithinAt.fun_sum ?_
  intro k _hk
  refine HasDerivWithinAt.fun_sum ?_
  intro l _hl
  have hA := hiota t x a i
  have hB := hiota t x b j
  have hC := hiota t x c k
  have hD := hiota t x d l
  have hR := hrm t x i j k l
  have hAB := hA.mul hB
  have hABC := hAB.mul hC
  have hABCD := hABC.mul hD
  have hAll := hABCD.mul hR
  simpa [uhlenbeckPullbackRmInFrame, uhlenbeckPullbackRmDerivRHSInFrame,
    derivProduct5RHS, iotaDotInFrame, mul_assoc] using hAll

omit [DecidableEq Idx] in
private theorem pullbackDerivRHS_eq_evolutionRHS
    (iota : MatrixComp M Idx)
    (Rm04 roughLapRm04 roughLapD Borig Bpull : FourComp M Idx)
    (Rup : MatrixComp M Idx)
    (hlap : UhlenbeckLaplacianPullbackComponents iota roughLapRm04 roughLapD)
    (hB : UhlenbeckPullbackBComponents iota Borig Bpull)
    (t : Real) (x : M) (a b c d : Idx) :
    uhlenbeckPullbackRmDerivRHSInFrame iota Rm04 roughLapRm04 Borig Rup
        t x a b c d =
      uhlenbeckCurvatureEvolutionRHSInFrame roughLapD Bpull t x a b c d := by
  classical
  let I1 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iotaDotInFrame iota Rup t x a i * iota t x b j *
        iota t x c k * iota t x d l * Rm04 t x i j k l
  let I2 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iotaDotInFrame iota Rup t x b j *
        iota t x c k * iota t x d l * Rm04 t x i j k l
  let I3 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j *
        iotaDotInFrame iota Rup t x c k * iota t x d l *
          Rm04 t x i j k l
  let I4 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k *
        iotaDotInFrame iota Rup t x d l * Rm04 t x i j k l
  let L : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        roughLapRm04 t x i j k l
  let Q1 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        Borig t x i j k l
  let Q2 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        Borig t x i j l k
  let Q3 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        Borig t x i k j l
  let Q4 : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        Borig t x i l j k
  let Q : Real := Q1 - Q2 + Q3 - Q4
  let Drift : Real :=
    uhlenbeckPullbackDriftInFrame iota Rm04 Rup t x a b c d
  let E : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      iota t x a i * iota t x b j * iota t x c k * iota t x d l *
        (roughLapRm04 t x i j k l -
          2 * (Borig t x i j k l - Borig t x i j l k +
            Borig t x i k j l - Borig t x i l j k) -
          riemann04RicciDriftInFrame Rup Rm04 t x i j k l)
  have hraw :
      uhlenbeckPullbackRmDerivRHSInFrame iota Rm04 roughLapRm04 Borig Rup
          t x a b c d =
        (I1 + I2 + I3 + I4) + (L - 2 * Q - Drift) := by
    have hprod :
        uhlenbeckPullbackRmDerivRHSInFrame iota Rm04 roughLapRm04 Borig Rup
            t x a b c d =
          I1 + I2 + I3 + I4 + E := by
      simpa [uhlenbeckPullbackRmDerivRHSInFrame, I1, I2, I3, I4, E] using
        (sum4_derivProduct5RHS_eq (Idx := Idx)
          (fun i => iota t x a i)
          (fun j => iota t x b j)
          (fun k => iota t x c k)
          (fun l => iota t x d l)
          (fun i => iotaDotInFrame iota Rup t x a i)
          (fun j => iotaDotInFrame iota Rup t x b j)
          (fun k => iotaDotInFrame iota Rup t x c k)
          (fun l => iotaDotInFrame iota Rup t x d l)
          (fun i j k l => Rm04 t x i j k l)
          (fun i j k l =>
            roughLapRm04 t x i j k l -
              2 * (Borig t x i j k l - Borig t x i j l k +
                Borig t x i k j l - Borig t x i l j k) -
              riemann04RicciDriftInFrame Rup Rm04 t x i j k l))
    have hE : E = L - 2 * Q - Drift := by
      dsimp [E, L, Q, Q1, Q2, Q3, Q4, Drift,
        uhlenbeckPullbackDriftInFrame]
      simp [sub_eq_add_neg, mul_add, mul_neg, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
      ring_nf
      repeat rw [sum4_mul_right]
    rw [hprod, hE]
  have hiotaDrift :
      I1 + I2 + I3 + I4 = Drift := by
    have h := iotaDrift_eq_pullbackDrift iota Rm04 Rup t x a b c d
    have hI :
        uhlenbeckIotaDriftInFrame iota Rm04 Rup t x a b c d =
          I1 + I2 + I3 + I4 := by
      simp [uhlenbeckIotaDriftInFrame, I1, I2, I3, I4,
        Finset.sum_add_distrib, add_assoc]
    exact hI.symm.trans h
  have hL : L = roughLapD t x a b c d := by
    simpa [L] using (hlap t x a b c d).symm
  have hQ :
      Q =
        Bpull t x a b c d - Bpull t x a b d c +
          Bpull t x a c b d - Bpull t x a d b c := by
    have hQ1 : Q1 = Bpull t x a b c d := by
      simpa [Q1, uhlenbeckPullbackRmInFrame] using (hB t x a b c d).symm
    have hQ2 : Q2 = Bpull t x a b d c := by
      have hswap :
          Q2 =
            (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
              iota t x a i * iota t x b j * iota t x d k *
                iota t x c l * Borig t x i j k l) := by
        change
          (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            iota t x a i * iota t x b j * iota t x c k *
              iota t x d l * Borig t x i j l k) =
            (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
              iota t x a i * iota t x b j * iota t x d k *
                iota t x c l * Borig t x i j k l)
        convert (sum4_swap34 (Idx := Idx)
          (fun i j k l =>
            iota t x a i * iota t x b j * iota t x d k *
              iota t x c l * Borig t x i j k l)).symm using 5
        ring
      exact hswap.trans <| by
        simpa [uhlenbeckPullbackRmInFrame, mul_assoc, mul_left_comm,
          mul_comm] using (hB t x a b d c).symm
    have hQ3 : Q3 = Bpull t x a c b d := by
      have hswap :
          Q3 =
            (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
              iota t x a i * iota t x c j * iota t x b k *
                iota t x d l * Borig t x i j k l) := by
        change
          (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            iota t x a i * iota t x b j * iota t x c k *
              iota t x d l * Borig t x i k j l) =
            (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
              iota t x a i * iota t x c j * iota t x b k *
                iota t x d l * Borig t x i j k l)
        convert (sum4_swap23 (Idx := Idx)
          (fun i j k l =>
            iota t x a i * iota t x c j * iota t x b k *
              iota t x d l * Borig t x i j k l)).symm using 5
        ring
      exact hswap.trans <| by
        simpa [uhlenbeckPullbackRmInFrame, mul_assoc, mul_left_comm,
          mul_comm] using (hB t x a c b d).symm
    have hQ4 : Q4 = Bpull t x a d b c := by
      have hswap :
          Q4 =
            (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
              iota t x a i * iota t x d j * iota t x b k *
                iota t x c l * Borig t x i j k l) := by
        change
          (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            iota t x a i * iota t x b j * iota t x c k *
              iota t x d l * Borig t x i l j k) =
            (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
              iota t x a i * iota t x d j * iota t x b k *
                iota t x c l * Borig t x i j k l)
        convert (sum4_cycle234 (Idx := Idx)
          (fun i j k l =>
            iota t x a i * iota t x d j * iota t x b k *
              iota t x c l * Borig t x i j k l)).symm using 5
        ring
      exact hswap.trans <| by
        simpa [uhlenbeckPullbackRmInFrame, mul_assoc, mul_left_comm,
          mul_comm] using (hB t x a d b c).symm
    change Q1 - Q2 + Q3 - Q4 =
      Bpull t x a b c d - Bpull t x a b d c +
        Bpull t x a c b d - Bpull t x a d b c
    rw [hQ1, hQ2, hQ3, hQ4]
  calc
    uhlenbeckPullbackRmDerivRHSInFrame iota Rm04 roughLapRm04 Borig Rup
        t x a b c d =
      (I1 + I2 + I3 + I4) + (L - 2 * Q - Drift) := hraw
    _ = L - 2 * Q := by
          rw [hiotaDrift]
          ring
    _ = uhlenbeckCurvatureEvolutionRHSInFrame roughLapD Bpull t x a b c d := by
          rw [hL, hQ]
          simp [uhlenbeckCurvatureEvolutionRHSInFrame]


omit [DecidableEq Idx] in
theorem uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (iota : MatrixComp M Idx)
    (Rm04 pulledRm roughLapRm04 roughLapD Borig Bpull : FourComp M Idx)
    (ricciOneUp : MatrixComp M Idx)
    (hiota : BundleIsomorphismODEInFrameOn (D := D) iota ricciOneUp)
    (hpull : UhlenbeckPullbackRmComponents iota Rm04 pulledRm)
    (hlap : UhlenbeckLaplacianPullbackComponents iota roughLapRm04 roughLapD)
    (hB : UhlenbeckPullbackBComponents iota Borig Bpull)
    (hrm : Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := D) Rm04 roughLapRm04 Borig ricciOneUp) :
    UhlenbeckCurvatureEvolutionInFrameOn
      (D := D) pulledRm roughLapD Bpull := by
  intro t x a b c d
  have hderiv :=
    uhlenbeckPullbackRm_deriv
      (D := D) iota Rm04 roughLapRm04 Borig ricciOneUp
      hiota hrm t x a b c d
  have hcongr :
      HasDerivWithinAt
        (fun s : Real => pulledRm s x a b c d)
        (uhlenbeckPullbackRmDerivRHSInFrame iota Rm04 roughLapRm04 Borig
          ricciOneUp (t : Real) x a b c d)
        D.carrier
        (t : Real) := by
    exact hderiv.congr
      (fun s _hs => hpull s x a b c d)
      (hpull (t : Real) x a b c d)
  have hrhs :=
    pullbackDerivRHS_eq_evolutionRHS
      iota Rm04 roughLapRm04 roughLapD Borig Bpull ricciOneUp
      hlap hB (t : Real) x a b c d
  exact hcongr.congr_deriv hrhs

section SolutionFrame

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]


abbrev solutionMetricCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    MatrixComp M Idx :=
  metricCompInFrame (I := I) S frame


abbrev solutionRicciCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    MatrixComp M Idx :=
  ricciCompInFrame (I := I) S frame



abbrev solutionRicciOneUpInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    MatrixComp M Idx :=
  ricciOneUpCompInFrame (I := I) S gInv frame


def solutionRm04CompInFrame
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    FourComp M Idx :=
  fun t x i j k l => DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i j k l





omit [DecidableEq Idx] in
omit [Fintype Idx] in
omit [SigmaCompactSpace M] in
theorem metricCompRicciFlowInFrameOn_of_solution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    MetricCompRicciFlowInFrameOn (D := D)
      (solutionMetricCompInFrame (I := I) S frame)
      (solutionRicciCompInFrame (I := I) S frame) := by
  intro t x i j
  exact metricCompInFrame_hasDerivWithinAt (I := I) S hS frame t x i j


abbrev BundleIsomorphismODEInSolutionFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (iota : MatrixComp M Idx) : Prop :=
  BundleIsomorphismODEInFrameOn (D := D) iota
    (solutionRicciOneUpInFrame (I := I) S gInv frame)



abbrev UhlenbeckPullbackRmComponentsOfSolution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (_S : SolutionOn (I := I) (M := M) D)
    (iota : MatrixComp M Idx)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (pulledRm : FourComp M Idx) : Prop :=
  UhlenbeckPullbackRmComponents iota
    (solutionRm04CompInFrame (I := I) Rm04 frame) pulledRm



abbrev Riemann04BTensorWithRicciDriftEvolutionInSolutionFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (roughLapRm04 B : FourComp M Idx) : Prop :=
  Riemann04BTensorWithRicciDriftEvolutionInFrameOn (D := D)
    (solutionRm04CompInFrame (I := I) Rm04 frame) roughLapRm04 B
    (solutionRicciOneUpInFrame (I := I) S gInv frame)





omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem uhlenbeckCurvatureEvolution_of_solution_components
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (iota : MatrixComp M Idx)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (pulledRm roughLapRm04 roughLapD Borig Bpull : FourComp M Idx)
    (hiota : BundleIsomorphismODEInSolutionFrameOn (I := I) S gInv frame iota)
    (hpull : UhlenbeckPullbackRmComponentsOfSolution
      (I := I) S iota Rm04 frame pulledRm)
    (hlap : UhlenbeckLaplacianPullbackComponents iota roughLapRm04 roughLapD)
    (hB : UhlenbeckPullbackBComponents iota Borig Bpull)
    (hrm : Riemann04BTensorWithRicciDriftEvolutionInSolutionFrameOn
      (I := I) S gInv frame Rm04 roughLapRm04 Borig) :
    UhlenbeckCurvatureEvolutionInFrameOn (D := D) pulledRm roughLapD Bpull :=
  uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow
    (D := D) iota (solutionRm04CompInFrame (I := I) Rm04 frame) pulledRm
    roughLapRm04 roughLapD Borig Bpull
    (solutionRicciOneUpInFrame (I := I) S gInv frame)
    hiota hpull hlap hB hrm

end SolutionFrame

end DifferentialGeometry.PDE.RicciFlow
