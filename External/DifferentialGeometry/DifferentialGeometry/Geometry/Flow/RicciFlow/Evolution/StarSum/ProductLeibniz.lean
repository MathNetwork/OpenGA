import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridgeAllK
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false
set_option linter.style.longLine false






















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]







omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm_product_eval
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (i j : ℕ)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin ((4 + i) + (4 + j)) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ((4 + i) + (4 + j))
        (S.family.connection t) X
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 4 + i) (q := 4 + j)
          (nablaKRm04Field (I := I) S t i) (nablaKRm04Field (I := I) S t j)) x)
        (fun a : Fin ((4 + i) + (4 + j)) => V a x) =
      nablaKRm04Field (I := I) S t (i + 1) x
          (Fin.cons (X x) (fun a : Fin (4 + i) => V (Fin.castAdd (4 + j) a) x)) *
          nablaKRm04Field (I := I) S t j x
            (fun a : Fin (4 + j) => V (Fin.natAdd (4 + i) a) x) +
        nablaKRm04Field (I := I) S t i x
            (fun a : Fin (4 + i) => V (Fin.castAdd (4 + j) a) x) *
          nablaKRm04Field (I := I) S t (j + 1) x
            (Fin.cons (X x) (fun a : Fin (4 + j) => V (Fin.natAdd (4 + i) a) x)) :=
  nabla0SFun_product_eval (I := I) (S.family.connection t)
    (nablaKRm04Field (I := I) S t i) (nablaKRm04Field (I := I) S t j)
    (nablaKRm04Field (I := I) S t (i + 1)) (nablaKRm04Field (I := I) S t (j + 1))
    (nablaKRm04Field_realizes (I := I) S t i) (nablaKRm04Field_realizes (I := I) S t j)
    X V x

end DifferentialGeometry.PDE.RicciFlow
