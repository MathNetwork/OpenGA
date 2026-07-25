import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Geometry.Coordinates.Tensor
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import DifferentialGeometry.Tensor.RSTensor.TensorRSRiemannian

set_option autoImplicit false
set_option linter.style.longLine false









namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle Module Tensor0SBundle
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}




theorem tensor12Comp_connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j k : Idx) :
    tensor12CompInFrame (I := I)
        (fun y : M => connectionDifferenceTensorAt (I := I) cov cov' y)
        frame hframe x hx k i j =
      christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k := by
  unfold tensor12CompInFrame tensorRSComponentInFrame
    christoffelSymbolDifferenceInFrame
  change
    componentRS_gen (I := I) (hframe.toBasisAt hx)
        (connectionDifferenceTensorAt (I := I) cov cov' x)
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j) =
      (hframe.coeff k x)
        (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))
  rw [componentRS_connectionDifferenceTensorAt]
  simp [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]




theorem normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum
    [IsManifold I ∞ M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g : SmoothMetric_gen I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u)
    (hinv :
      MetricInverseInBasis_gen (I := I) g x (hframe.toBasisAt hx)
        (identityInvMetric (Idx := Idx))) :
    normSqRS (I := I) (g := g) (x := x) 1 2
        (connectionDifferenceTensorAt (I := I) cov cov' x) =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
        (christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k) ^ 2 := by
  rw [normSqRS_one_two_identity_eq_sum (I := I) g x
    (hframe.toBasisAt hx) hinv
    (connectionDifferenceTensorAt (I := I) cov cov' x)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold christoffelSymbolDifferenceInFrame
  rw [componentRS_connectionDifferenceTensorAt]
  simp [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

end

end DifferentialGeometry.Tensor.Coordinates
