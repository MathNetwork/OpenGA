import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric
import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity
import DifferentialGeometry.Geometry.Connection.MetricCompatibility
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

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



def christoffelVariationLoweredRHSInFrame
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j l : Idx) : Real :=
  -nablaRic t x i j l - nablaRic t x j i l + nablaRic t x l i j


def nablaRicLastRaisedInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv t x k l * nablaRic t x i j l


def nablaRicDirectionRaisedInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv t x k l * nablaRic t x l i j



def christoffelEvolutionRHSInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx,
    gInv t x k l * christoffelVariationLoweredRHSInFrame nablaRic t x i j l




omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem christoffelRHS_id
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    {t : Real} {x : M}
    (hinv_id : ∀ e l : Idx, gInv t x e l = if e = l then 1 else 0)
    (i j k : Idx) :
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic t x i j k =
      -nablaRic t x i j k - nablaRic t x j i k + nablaRic t x k i j := by
  calc
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic t x i j k =
        ∑ l : Idx,
          (if k = l then (1 : Real) else 0) *
            christoffelVariationLoweredRHSInFrame nablaRic t x i j l := by
          refine Finset.sum_congr rfl fun l _hl => ?_
          rw [hinv_id k l]
    _ = christoffelVariationLoweredRHSInFrame nablaRic t x i j k := by
          simp
    _ = -nablaRic t x i j k - nablaRic t x j i k +
          nablaRic t x k i j := by
          rfl



def christoffelVariationRHSFromLoweredInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (loweredRHS : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv t x k l * loweredRHS t x i j l

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem christoffelEvolutionRHSInFrame_eq_coordinates_rhs
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) :
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic t x i j k =
      DifferentialGeometry.Tensor.Coordinates.ricciFlowChristoffelEvolutionRHSInFrame
        (nablaRicLastRaisedInFrame (M := M) gInv nablaRic)
        (nablaRicDirectionRaisedInFrame (M := M) gInv nablaRic)
        t x i j k := by
  let A : Idx -> Real := fun l => gInv t x k l * nablaRic t x i j l
  let B : Idx -> Real := fun l => gInv t x k l * nablaRic t x j i l
  let C : Idx -> Real := fun l => gInv t x k l * nablaRic t x l i j
  change (∑ l : Idx,
      gInv t x k l * christoffelVariationLoweredRHSInFrame nablaRic t x i j l) =
    - (∑ l : Idx, A l) - (∑ l : Idx, B l) + ∑ l : Idx, C l
  calc
    (∑ l : Idx,
        gInv t x k l * christoffelVariationLoweredRHSInFrame nablaRic t x i j l)
        = ∑ l : Idx, (-A l - B l + C l) := by
            refine Finset.sum_congr rfl fun l _hl => ?_
            simp [A, B, C, christoffelVariationLoweredRHSInFrame]
            ring
    _ = - (∑ l : Idx, A l) - (∑ l : Idx, B l) + ∑ l : Idx, C l := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]





def NablaRicciTensorComponentsInFrameOn
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRicTensor : Real ->
      Tensor0SBundle.Tensor0SField
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ⊤ 3)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x i j l,
    nablaRic t x i j l =
      nablaRicTensor t x
        (DifferentialGeometry.Integral.Connection.vec3 (frame i x) (frame j x) (frame l x))



def connectionDiffVectorInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (i j : Idx) : TangentSpace I x :=
  (S.family.connection var (frame j) x) (frame i x) -
    (S.family.connection base (frame j) x) (frame i x)




def connectionDiffLoweredInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base var : Real) (x : M) (i j l : Idx) : Real :=
  (S.family.metric metricTime).inner x
    (connectionDiffVectorInFrame (I := I) S frame base var x i j)
    (frame l x)

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem connectionDiffVectorInFrame_self
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (x : M) (i j : Idx) :
    connectionDiffVectorInFrame (I := I) S frame base base x i j = 0 := by
  simp [connectionDiffVectorInFrame]

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem connectionDiffLoweredInFrame_self
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base : Real) (x : M) (i j l : Idx) :
    connectionDiffLoweredInFrame (I := I) S frame metricTime base base x i j l = 0 := by
  simp [connectionDiffLoweredInFrame]




def metricCovDerivCompInFrameAtBase
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => (S.family.metric var).inner y (frame a y) (frame b y))
      x (frame d x) -
    (S.family.metric var).inner x
      ((S.family.connection base (frame a) x) (frame d x)) (frame b x) -
    (S.family.metric var).inner x (frame a x)
      ((S.family.connection base (frame b) x) (frame d x))




def finiteDifferenceKoszulRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (i j l : Idx) : Real :=
  metricCovDerivCompInFrameAtBase (I := I) S frame base var x i j l +
    metricCovDerivCompInFrameAtBase (I := I) S frame base var x j i l -
      metricCovDerivCompInFrameAtBase (I := I) S frame base var x l i j

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] [DecidableEq Idx] in
private theorem localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
private theorem connectionDiffVectorInFrame_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {base var : Real} (hbase : base ∈ D.carrier) (hvar : var ∈ D.carrier)
    (i j : Idx) :
    connectionDiffVectorInFrame (I := I) S frame base var x i j =
      connectionDiffVectorInFrame (I := I) S frame base var x j i := by
  have hfi : MDiffAt (T% (frame i)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx i
  have hfj : MDiffAt (T% (frame j)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx j
  have hvar_torsion :=
    DifferentialGeometry.Integral.Connection.torsion_free_apply
      (I := I) (hS.leviCivita.2 ⟨var, hvar⟩) (hX := hfi) (hY := hfj)
  have hbase_torsion :=
    DifferentialGeometry.Integral.Connection.torsion_free_apply
      (I := I) (hS.leviCivita.2 ⟨base, hbase⟩) (hX := hfi) (hY := hfj)
  have hdiff :
      (S.family.connection var (frame j) x) (frame i x) -
          (S.family.connection var (frame i) x) (frame j x) =
        (S.family.connection base (frame j) x) (frame i x) -
          (S.family.connection base (frame i) x) (frame j x) := by
    exact hvar_torsion.trans hbase_torsion.symm
  unfold connectionDiffVectorInFrame
  apply sub_eq_zero.mp
  calc
    ((S.family.connection var (frame j) x) (frame i x) -
          (S.family.connection base (frame j) x) (frame i x)) -
        ((S.family.connection var (frame i) x) (frame j x) -
          (S.family.connection base (frame i) x) (frame j x))
        =
      ((S.family.connection var (frame j) x) (frame i x) -
          (S.family.connection var (frame i) x) (frame j x)) -
        ((S.family.connection base (frame j) x) (frame i x) -
          (S.family.connection base (frame i) x) (frame j x)) := by
        abel
    _ = 0 := by
        rw [hdiff, sub_self]

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
private theorem connectionDiffLoweredInFrame_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {metricTime base var : Real} (hbase : base ∈ D.carrier) (hvar : var ∈ D.carrier)
    (i j l : Idx) :
    connectionDiffLoweredInFrame (I := I) S frame metricTime base var x i j l =
      connectionDiffLoweredInFrame (I := I) S frame metricTime base var x j i l := by
  unfold connectionDiffLoweredInFrame
  rw [connectionDiffVectorInFrame_symm
    (I := I) S hS frame hframe hu hx hbase hvar i j]




omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivCompInFrameAtBase_eq_connectionDiff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {base var : Real} (hvar : var ∈ D.carrier)
    (d a b : Idx) :
    metricCovDerivCompInFrameAtBase (I := I) S frame base var x d a b =
      connectionDiffLoweredInFrame (I := I) S frame var base var x d a b +
        (S.family.metric var).inner x (frame a x)
          (connectionDiffVectorInFrame (I := I) S frame base var x d b) := by
  have hfd : MDiffAt (T% (frame d)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx d
  have hfa : MDiffAt (T% (frame a)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hfb : MDiffAt (T% (frame b)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmc :=
    DifferentialGeometry.Integral.Connection.metric_compatible_apply
      (I := I) (hS.leviCivita.1 ⟨var, hvar⟩)
      (frame d) (frame a) (frame b) hfd hfa hfb
  unfold metricCovDerivCompInFrameAtBase connectionDiffLoweredInFrame
    connectionDiffVectorInFrame
  have hmc' :
      extDerivFun (I := I)
          (fun y : M => (S.family.metric var).inner y (frame a y) (frame b y))
          x (frame d x) =
        (S.family.metric var).inner x
            ((S.family.connection var (frame a) x) (frame d x)) (frame b x) +
          (S.family.metric var).inner x (frame a x)
            ((S.family.connection var (frame b) x) (frame d x)) := by
    simpa [extDerivFun] using hmc
  rw [hmc']
  simp
  ring



omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem finiteDifferenceKoszulInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {base var : Real} (hbase : base ∈ D.carrier) (hvar : var ∈ D.carrier)
    (i j l : Idx) :
    2 * connectionDiffLoweredInFrame (I := I) S frame var base var x i j l =
      finiteDifferenceKoszulRHSInFrame (I := I) S frame base var x i j l := by
  rw [finiteDifferenceKoszulRHSInFrame]
  rw [metricCovDerivCompInFrameAtBase_eq_connectionDiff
    (I := I) S hS frame hframe hu hx hvar i j l]
  rw [metricCovDerivCompInFrameAtBase_eq_connectionDiff
    (I := I) S hS frame hframe hu hx hvar j i l]
  rw [metricCovDerivCompInFrameAtBase_eq_connectionDiff
    (I := I) S hS frame hframe hu hx hvar l i j]
  have hji := connectionDiffLoweredInFrame_symm
    (I := I) S hS frame hframe hu hx (metricTime := var) hbase hvar j i l
  have hli := connectionDiffLoweredInFrame_symm
    (I := I) S hS frame hframe hu hx (metricTime := var) hbase hvar l i j
  have hlj := connectionDiffVectorInFrame_symm
    (I := I) S hS frame hframe hu hx hbase hvar l j
  have hsym1 :
      (S.family.metric var).inner x (frame j x)
          (connectionDiffVectorInFrame (I := I) S frame base var x i l) =
        connectionDiffLoweredInFrame (I := I) S frame var base var x i l j := by
    unfold connectionDiffLoweredInFrame
    exact (S.family.metric var).symm x (frame j x)
      (connectionDiffVectorInFrame (I := I) S frame base var x i l)
  rw [hji, hli, hlj, hsym1]
  ring






def ConnectionPairingDerivativeInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (pairDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j l : Idx),
    HasDerivWithinAt
      (fun s : Real =>
        (S.family.metric (t : Real)).inner x (frame l x)
          ((S.family.connection s (frame j) x) (frame i x)))
      (pairDt (t : Real) x i j l)
      D.carrier
      (t : Real)



def ConnectionPairingDerivativeInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (pairDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j l : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          (S.family.metric (t : Real)).inner x (frame l x)
            ((S.family.connection s (frame j) x) (frame i x)))
        (pairDt (t : Real) x i j l)
        D.carrier
        (t : Real)





def VariableMetricConnectionDiffDerivativeInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (pairDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j l : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (pairDt (t : Real) x i j l)
        D.carrier
        (t : Real)



def MetricCovDerivDerivativeComponentsInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall d a b : Idx,
      HasDerivWithinAt
        (fun s : Real =>
          metricCovDerivCompInFrameAtBase (I := I) S frame (t : Real) s x d a b)
        (metricCovDerivDt (t : Real) x d a b)
        D.carrier
        (t : Real)



def connectionVariationLoweredRHSFromMetricVariationInFrame
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j l : Idx) : Real :=
  (1 / 2 : Real) *
    (metricCovDerivDt t x i j l + metricCovDerivDt t x j i l -
      metricCovDerivDt t x l i j)



def christoffelVariationRHSFromMetricVariationInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j k : Idx) : Real :=
  christoffelVariationRHSFromLoweredInFrame (M := M) gInv
    (connectionVariationLoweredRHSFromMetricVariationInFrame metricCovDerivDt)
    t x i j k



def MetricCovDerivDerivativeIsRicciFlowInFrame
    (metricCovDerivDt nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) :
    Prop :=
  forall t x i j l,
    metricCovDerivDt t x i j l = (-2 : Real) * nablaRic t x i j l




def ricciCovDerivCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => ricciCompInFrame (I := I) S frame t y a b)
      x (frame d x) -
    S.ricciAt t x
      (DifferentialGeometry.Integral.Connection.vec2
        ((S.family.connection t (frame a) x) (frame d x))
        (frame b x)) -
    S.ricciAt t x
      (DifferentialGeometry.Integral.Connection.vec2
        (frame a x)
        ((S.family.connection t (frame b) x) (frame d x)))



def NablaRicciComponentsByConnectionInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M), x ∈ u ->
    forall d a b : Idx,
      nablaRic t x d a b =
        ricciCovDerivCompInFrame (I := I) S frame t x d a b






structure NablaRicciComponentsRegularInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) : Prop where
  realizes :
    NablaRicciComponentsByConnectionInFrameOn
      (I := I) S frame u nablaRic
  mdiffAt :
    forall (t : Real) (x : M), x ∈ u ->
      forall d i j : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => nablaRic t y d i j) x





def ricciSecondCovDerivCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d a i j : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => nablaRic t y a i j) x
      (frame d x) -
    (∑ p : Idx,
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection t) frame hframe x d a p *
        nablaRic t x p i j) -
    (∑ p : Idx,
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection t) frame hframe x d i p *
        nablaRic t x a p j) -
    (∑ p : Idx,
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (S.family.connection t) frame hframe x d j p *
        nablaRic t x a i p)



def Nabla2RicciComponentsByConnectionInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Real) (x : M), x ∈ u ->
    forall d a i j : Idx,
      nabla2Ric t x d a i j =
        ricciSecondCovDerivCompInFrame
          (I := I) S frame hframe nablaRic t x d a i j





structure Nabla2RicciComponentsRegularInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop where
  first :
    NablaRicciComponentsRegularInFrameOnLocal
      (I := I) S frame u nablaRic
  second :
    Nabla2RicciComponentsByConnectionInFrameOn
      (I := I) S frame u hframe nablaRic nabla2Ric

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] [DecidableEq Idx] in
theorem metricCovDerivDerivativeIsRicciFlowInFrame_neg_two
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) :
    MetricCovDerivDerivativeIsRicciFlowInFrame
      (fun t x d a b => (-2 : Real) * nablaRic t x d a b)
      nablaRic := by
  intro t x i j l
  rfl



omit [DecidableEq Idx] in
omit [Fintype Idx] in
omit [SigmaCompactSpace M] in
theorem metricCovDerivOfMix
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hricci :
      forall t x, x ∈ u -> forall a b : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => ricciCompInFrame (I := I) S frame t y a b) x)
    (hmix :
      forall a b : Idx,
        FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
          D.carrier D.regular u
          (fun s x => metricCompInFrame (I := I) S frame s x a b)
          (fun t x => (-2 : Real) *
            ricciCompInFrame (I := I) S frame t x a b))
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S frame u nablaRic) :
    MetricCovDerivDerivativeComponentsInFrameOnLocal
      (I := I) S frame u
      (fun t x d a b => (-2 : Real) * nablaRic t x d a b) := by
  intro t x hx d a b
  let Ca : TangentSpace I x :=
    (S.family.connection (t : Real) (frame a) x) (frame d x)
  let Cb : TangentSpace I x :=
    (S.family.connection (t : Real) (frame b) x) (frame d x)
  have hExtRaw :
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun y : M => metricCompInFrame (I := I) S frame s y a b)
            x (frame d x))
        (extDerivFun (I := I)
          (fun y : M => (-2 : Real) *
            ricciCompInFrame (I := I) S frame (t : Real) y a b)
          x (frame d x))
        D.carrier
        (t : Real) :=
    fixedBaseExtDerivTimeDerivativeOnRegular_apply (I := I)
      (h := hmix a b) (t := (t : Real)) t.2 (x := x) hx (frame d x)
  have hscale :
      extDerivFun (I := I)
          (fun y : M => (-2 : Real) *
            ricciCompInFrame (I := I) S frame (t : Real) y a b)
          x (frame d x) =
        (-2 : Real) *
          extDerivFun (I := I)
            (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
            x (frame d x) := by
    have h :=
      extDerivFun_const_mul (I := I) (-2 : Real)
        (hricci (t : Real) x hx a b)
    simpa [smul_eq_mul] using congrArg (fun L => L (frame d x)) h
  have hExt :
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun y : M => metricCompInFrame (I := I) S frame s y a b)
            x (frame d x))
        ((-2 : Real) *
          extDerivFun (I := I)
            (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
            x (frame d x))
        D.carrier
        (t : Real) :=
    hExtRaw.congr_deriv hscale
  have hCa :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x Ca (frame b x))
        ((-2 : Real) *
          S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 Ca (frame b x)))
        D.carrier
        (t : Real) := by
    simpa [Ca, ricciCompInFrame] using
      metric_derivWithin_eq_neg_two_ricci
        (I := I) S hS t x Ca (frame b x)
  have hCb :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x (frame a x) Cb)
        ((-2 : Real) *
          S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (frame a x) Cb))
        D.carrier
        (t : Real) := by
    simpa [Cb, ricciCompInFrame] using
      metric_derivWithin_eq_neg_two_ricci
        (I := I) S hS t x (frame a x) Cb
  have hDeriv :
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
              (fun y : M => metricCompInFrame (I := I) S frame s y a b)
              x (frame d x) -
            (S.family.metric s).inner x Ca (frame b x) -
            (S.family.metric s).inner x (frame a x) Cb)
        (((-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x)) -
          ((-2 : Real) *
            S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 Ca (frame b x))) -
          ((-2 : Real) *
            S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (frame a x) Cb)))
        D.carrier
        (t : Real) :=
    (hExt.sub hCa).sub hCb
  refine hDeriv.congr ?_ ?_ |>.congr_deriv ?_
  · intro s _hs
    simp [metricCovDerivCompInFrameAtBase, metricCompInFrame, Ca, Cb]
  · simp [metricCovDerivCompInFrameAtBase, metricCompInFrame, Ca, Cb]
  · have hn := hnabla (t : Real) x hx d a b
    unfold ricciCovDerivCompInFrame at hn
    change
      (-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x) -
          (-2 : Real) *
            S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 Ca (frame b x)) -
          (-2 : Real) *
            S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (frame a x) Cb) =
        (-2 : Real) * nablaRic (t : Real) x d a b
    rw [hn]
    simp [Ca, Cb]
    ring







omit [SigmaCompactSpace M] in
theorem metricCovDerivDerivativeComponents_of_ricciFlow
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S frame u nablaRic) :
    MetricCovDerivDerivativeComponentsInFrameOnLocal
      (I := I) S frame u
      (fun t x d a b => (-2 : Real) * nablaRic t x d a b) := by
  intro t x hx d a b
  let Ca : TangentSpace I x :=
    (S.family.connection (t : Real) (frame a) x) (frame d x)
  let Cb : TangentSpace I x :=
    (S.family.connection (t : Real) (frame b) x) (frame d x)
  have hExt :
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun y : M => metricCompInFrame (I := I) S frame s y a b)
            x (frame d x))
        ((-2 : Real) *
          extDerivFun (I := I)
            (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
            x (frame d x))
        D.carrier
        (t : Real) :=
    hreg.frameMetricExtDerivTimeDerivative t x hx d a b
  have hCa :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x Ca (frame b x))
        ((-2 : Real) *
          S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 Ca (frame b x)))
        D.carrier
        (t : Real) := by
    simpa [Ca, ricciCompInFrame] using
      metric_derivWithin_eq_neg_two_ricci
        (I := I) S hS t x Ca (frame b x)
  have hCb :
      HasDerivWithinAt
        (fun s : Real => (S.family.metric s).inner x (frame a x) Cb)
        ((-2 : Real) *
          S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (frame a x) Cb))
        D.carrier
        (t : Real) := by
    simpa [Cb, ricciCompInFrame] using
      metric_derivWithin_eq_neg_two_ricci
        (I := I) S hS t x (frame a x) Cb
  have hDeriv :
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
              (fun y : M => metricCompInFrame (I := I) S frame s y a b)
              x (frame d x) -
            (S.family.metric s).inner x Ca (frame b x) -
            (S.family.metric s).inner x (frame a x) Cb)
        (((-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x)) -
          ((-2 : Real) *
            S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 Ca (frame b x))) -
          ((-2 : Real) *
            S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (frame a x) Cb)))
        D.carrier
        (t : Real) :=
    (hExt.sub hCa).sub hCb
  refine hDeriv.congr ?_ ?_ |>.congr_deriv ?_
  · intro s _hs
    simp [metricCovDerivCompInFrameAtBase, metricCompInFrame, Ca, Cb]
  · simp [metricCovDerivCompInFrameAtBase, metricCompInFrame, Ca, Cb]
  · have hn := hnabla (t : Real) x hx d a b
    unfold ricciCovDerivCompInFrame at hn
    change
      (-2 : Real) *
            extDerivFun (I := I)
              (fun y : M => ricciCompInFrame (I := I) S frame (t : Real) y a b)
              x (frame d x) -
          (-2 : Real) *
            S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 Ca (frame b x)) -
          (-2 : Real) *
            S.ricciAt (t : Real) x (DifferentialGeometry.Integral.Connection.vec2 (frame a x) Cb) =
        (-2 : Real) * nablaRic (t : Real) x d a b
    rw [hn]
    simp [Ca, Cb]
    ring





omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem variableMetricConnectionDiffDerivative_of_metricCovDeriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (metricCovDerivDt nablaRic :
      Real -> M -> Idx -> Idx -> Idx -> Real)
    (hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame u metricCovDerivDt)
    (hmetricRicci :
      MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic) :
    VariableMetricConnectionDiffDerivativeInFrameOnLocal
      (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) := by
  intro t x hx i j l
  have htcarrier : (t : Real) ∈ D.carrier := D.regular_subset t.2
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
  have hTwoDiff :
      HasDerivWithinAt
        (fun s : Real =>
          2 * connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        (metricCovDerivDt (t : Real) x i j l +
          metricCovDerivDt (t : Real) x j i l -
            metricCovDerivDt (t : Real) x l i j)
        D.carrier
        (t : Real) := by
    refine hR.congr ?_ ?_
    · intro s hs
      exact finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier hs i j l
    · exact finiteDifferenceKoszulInFrame
        (I := I) S hS frame hframe hu hx htcarrier htcarrier i j l
  have hHalf :
      HasDerivWithinAt
        (fun s : Real =>
          (1 / 2 : Real) *
            (2 * connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l))
        ((1 / 2 : Real) *
          (metricCovDerivDt (t : Real) x i j l +
            metricCovDerivDt (t : Real) x j i l -
              metricCovDerivDt (t : Real) x l i j))
        D.carrier
        (t : Real) :=
    HasDerivWithinAt.const_mul (1 / 2 : Real) hTwoDiff
  have hDiff :
      HasDerivWithinAt
        (fun s : Real =>
          connectionDiffLoweredInFrame (I := I) S frame s (t : Real) s x i j l)
        ((1 / 2 : Real) *
          (metricCovDerivDt (t : Real) x i j l +
            metricCovDerivDt (t : Real) x j i l -
              metricCovDerivDt (t : Real) x l i j))
        D.carrier
        (t : Real) := by
    refine hHalf.congr ?_ ?_
    · intro s _hs
      ring
    · ring
  refine hDiff.congr_deriv ?_
  unfold christoffelVariationLoweredRHSInFrame
  rw [hmetricRicci (t : Real) x i j l,
    hmetricRicci (t : Real) x j i l,
    hmetricRicci (t : Real) x l i j]
  ring


end Components

end DifferentialGeometry.PDE.RicciFlow
