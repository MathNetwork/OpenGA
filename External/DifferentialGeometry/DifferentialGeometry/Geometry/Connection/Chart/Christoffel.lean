import DifferentialGeometry.Analysis.Time
import DifferentialGeometry.Geometry.Connection.Chart.Basic


namespace DifferentialGeometry
namespace Coordinates

noncomputable section

open Bundle Module
open scoped BigOperators Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Idx : Type*}
  {u : Set M}

def christoffelSymbolInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) : Real :=
  hframe.coeff k x ((cov (frame j) x) (frame i x))

def christoffelAlongInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (j k : Idx) : Real :=
  hframe.coeff k x ((cov (frame j) x) X)

@[simp] theorem christoffelSymbolInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) :
    christoffelSymbolInFrame cov frame hframe x i j k =
      hframe.coeff k x ((cov (frame j) x) (frame i x)) := by
  rfl

@[simp] theorem christoffelAlongInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (j k : Idx) :
    christoffelAlongInFrame cov frame hframe x X j k =
      hframe.coeff k x ((cov (frame j) x) X) := by
  rfl

theorem christoffelAlongInFrame_frame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) :
    christoffelAlongInFrame cov frame hframe x (frame i x) j k =
      christoffelSymbolInFrame cov frame hframe x i j k := by
  rfl

theorem covariantDerivative_eq_sum_christoffel
    [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    (cov (frame j) x) (frame i x) =
      ∑ k, christoffelSymbolInFrame cov frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq (fun y => (cov (frame j) y) (frame i y)) hx

def IsNormalFrameForConnectionAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) : Prop :=
  forall i j k : Idx, christoffelSymbolInFrame cov frame hframe x i j k = 0

section Difference

variable [FiniteDimensional Real E]
  [VectorBundle Real E (TangentSpace I : M -> Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

def christoffelSymbolDifferenceInFrame
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) : Real :=
  hframe.coeff k x (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))

theorem christoffelSymbolDifference_expansion
    [Fintype Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x) =
      ∑ k, christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq
    (fun y => ((CovariantDerivative.difference cov cov' y) (frame j y)) (frame i y)) hx

theorem christoffelSymbolDifferenceInFrame_eq_sub
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (i j k : Idx)
    (hframe_j : MDiffAt (T% (frame j)) x) :
    christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k =
      christoffelSymbolInFrame cov frame hframe x i j k -
        christoffelSymbolInFrame cov' frame hframe x i j k := by
  unfold christoffelSymbolDifferenceInFrame christoffelSymbolInFrame
  change hframe.coeff k x
      (((cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv x)
        (frame j x)) (frame i x)) =
    hframe.coeff k x ((cov (frame j) x) (frame i x)) -
      hframe.coeff k x ((cov' (frame j) x) (frame i x))
  rw [IsCovariantDerivativeOn.difference_apply
    (hcov := cov.isCovariantDerivativeOnUniv)
    (hcov' := cov'.isCovariantDerivativeOnUniv)
    (σ := frame j) (x := x) (hx := by trivial) hframe_j]
  simp

end Difference

section TimeDerivative

variable {A Time : Type*} [CommRing A] [Algebra Real A]

def christoffelSymbolTimeDerivativeInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : Idx) : Real :=
  td.dt_apply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t

@[simp] theorem christoffelSymbolTimeDerivativeInFrame_eval
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      td.dt_apply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t := by
  rfl

def ChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x i j k,
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k

theorem christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> Idx -> Idx -> Idx -> Real)
    (h_evol : ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe rhs)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k :=
  h_evol t x i j k

def ricciFlowChristoffelEvolutionRHSInFrame
    (nablaRicLastRaised nablaRicDirectionRaised : Time -> M -> Idx -> Idx -> Idx -> Real)
    (t : Time) (x : M) (i j k : Idx) : Real :=
  - nablaRicLastRaised t x i j k -
    nablaRicLastRaised t x j i k +
    nablaRicDirectionRaised t x i j k

def RicciFlowChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised :
      Time -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe
    (ricciFlowChristoffelEvolutionRHSInFrame nablaRicLastRaised nablaRicDirectionRaised)

theorem ricciFlow_christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData Real A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised :
      Time -> M -> Idx -> Idx -> Idx -> Real)
    (h_evol : RicciFlowChristoffelSymbolEvolutionEquationInFrame
      td covFam frame hframe nablaRicLastRaised nablaRicDirectionRaised)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      - nablaRicLastRaised t x i j k -
        nablaRicLastRaised t x j i k +
        nablaRicDirectionRaised t x i j k := by
  simpa [RicciFlowChristoffelSymbolEvolutionEquationInFrame,
    ChristoffelSymbolEvolutionEquationInFrame, ricciFlowChristoffelEvolutionRHSInFrame]
    using h_evol t x i j k

end TimeDerivative

end

end Coordinates
end DifferentialGeometry
