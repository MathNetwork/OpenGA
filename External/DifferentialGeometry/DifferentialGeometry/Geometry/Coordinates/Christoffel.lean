import DifferentialGeometry.Analysis.Time
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

set_option autoImplicit false
set_option linter.style.longLine false










namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle Module
open scoped BigOperators Manifold ContDiff

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Idx : Type*}
  {u : Set M}



def christoffelSymbolInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) : 𝕜 :=
  hframe.coeff k x ((cov (frame j) x) (frame i x))


def christoffelAlongInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (j k : Idx) : 𝕜 :=
  hframe.coeff k x ((cov (frame j) x) X)

omit [CompleteSpace 𝕜] in
@[simp] theorem christoffelSymbolInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) :
    christoffelSymbolInFrame cov frame hframe x i j k =
      hframe.coeff k x ((cov (frame j) x) (frame i x)) := by
  rfl

omit [CompleteSpace 𝕜] in
@[simp] theorem christoffelAlongInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (j k : Idx) :
    christoffelAlongInFrame cov frame hframe x X j k =
      hframe.coeff k x ((cov (frame j) x) X) := by
  rfl



omit [CompleteSpace 𝕜] in
theorem christoffelAlongInFrame_frame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) :
    christoffelAlongInFrame cov frame hframe x (frame i x) j k =
      christoffelSymbolInFrame cov frame hframe x i j k := by
  rfl


omit [CompleteSpace 𝕜] in
theorem christoffelAlongInFrame_eq_sum_coeff
    [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (X : TangentSpace I x) (j k : Idx) :
    christoffelAlongInFrame cov frame hframe x X j k =
      ∑ i : Idx,
        hframe.coeff i x X *
          christoffelSymbolInFrame cov frame hframe x i j k := by
  classical
  have hX : X = ∑ i : Idx, hframe.coeff i x X • frame i x := by
    simpa [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe] using
      ((hframe.toBasisAt hx).sum_repr X).symm
  calc
    christoffelAlongInFrame cov frame hframe x X j k
        = hframe.coeff k x ((cov (frame j) x) X) := rfl
    _ = hframe.coeff k x
          ((cov (frame j) x)
            (∑ i : Idx, hframe.coeff i x X • frame i x)) := by
          rw [← hX]
    _ = ∑ i : Idx,
          hframe.coeff i x X *
            christoffelSymbolInFrame cov frame hframe x i j k := by
          simp [map_sum, map_smul, christoffelSymbolInFrame]


omit [CompleteSpace 𝕜] in
theorem covariantDerivative_eq_sum_christoffel
    [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    (cov (frame j) x) (frame i x) =
      ∑ k, christoffelSymbolInFrame cov frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq (fun y => (cov (frame j) y) (frame i y)) hx



theorem torsion_coeff_eq_christoffel_skew
    [FiniteDimensional 𝕜 E] [CompleteSpace E]
    [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (i j k : Idx)
    (hi : MDiffAt (T% (frame i)) x) (hj : MDiffAt (T% (frame j)) x) :
    hframe.coeff k x (cov.torsion x (frame i x) (frame j x)) =
      christoffelSymbolInFrame cov frame hframe x i j k -
        christoffelSymbolInFrame cov frame hframe x j i k -
          hframe.coeff k x (VectorField.mlieBracket I (frame i) (frame j) x) := by
  rw [cov.torsion_apply hi hj]
  simp [christoffelSymbolInFrame, map_sub]





def IsNormalFrameForConnectionAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) : Prop :=
  forall i j k : Idx, christoffelSymbolInFrame cov frame hframe x i j k = 0

section Difference

variable [FiniteDimensional 𝕜 E]
  [VectorBundle 𝕜 E (TangentSpace I : M -> Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]


def christoffelSymbolDifferenceInFrame
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) : 𝕜 :=
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

variable {A Time : Type*} [CommRing A] [Algebra 𝕜 A]


def christoffelSymbolTimeDerivativeInFrame
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : Idx) : 𝕜 :=
  td.dt_apply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t

omit [CompleteSpace 𝕜] in
@[simp] theorem christoffelSymbolTimeDerivativeInFrame_eval
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      td.dt_apply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t := by
  rfl


def ChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> Idx -> Idx -> Idx -> 𝕜) : Prop :=
  forall t x i j k,
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k

omit [CompleteSpace 𝕜] in
theorem christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> Idx -> Idx -> Idx -> 𝕜)
    (h_evol : ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe rhs)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k :=
  h_evol t x i j k





def ricciFlowChristoffelEvolutionRHSInFrame
    (nablaRicLastRaised nablaRicDirectionRaised : Time -> M -> Idx -> Idx -> Idx -> 𝕜)
    (t : Time) (x : M) (i j k : Idx) : 𝕜 :=
  - nablaRicLastRaised t x i j k -
    nablaRicLastRaised t x j i k +
    nablaRicDirectionRaised t x i j k



def RicciFlowChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised :
      Time -> M -> Idx -> Idx -> Idx -> 𝕜) : Prop :=
  ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe
    (ricciFlowChristoffelEvolutionRHSInFrame nablaRicLastRaised nablaRicDirectionRaised)

omit [CompleteSpace 𝕜] in
theorem ricciFlow_christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised :
      Time -> M -> Idx -> Idx -> Idx -> 𝕜)
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

end DifferentialGeometry.Tensor.Coordinates
