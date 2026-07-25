import DifferentialGeometry.Geometry.Coordinates.Tensor
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Formula








set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]





theorem nablaRS_coordFrame_1_2_of_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M)
    (k i j : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 2 cov X A x₀)
      (upperIdx1 k)
      (lowerIdx2 i j)
    =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => A x)
        (upperIdx1 k)
        (lowerIdx2 i j)
      +
      ∑ m : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov
          (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) m k
        *
        coordComponentRSAt (I := I)
          (A x₀)
          (upperIdx1 m)
          (lowerIdx2 i j)
      -
      ∑ m : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov
          (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) i m
        *
        coordComponentRSAt (I := I)
          (A x₀)
          (upperIdx1 k)
          (lowerIdx2 m j)
      -
      ∑ m : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov
          (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) j m
        *
        coordComponentRSAt (I := I)
          (A x₀)
          (upperIdx1 k)
          (lowerIdx2 i m) := by
  classical
  have h := nablaRS_coordFrame_slots_of_smooth
    (I := I) cov X A x₀ (upperIdx1 k) (lowerIdx2 i j)
  rw [h]
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, upperIdx1_apply,
    lowerIdx2_zero, lowerIdx2_one, Function_update_upperIdx1,
    Function_update_lowerIdx2_zero, Function_update_lowerIdx2_one]
  abel

end DifferentialGeometry.Tensor.Coordinates
