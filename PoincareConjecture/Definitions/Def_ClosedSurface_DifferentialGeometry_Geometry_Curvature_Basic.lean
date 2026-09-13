import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

variable {H : Type*} [TopologicalSpace H]

variable {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev RawTangentField :=
  (x : M) -> TangentSpace I x

def connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) :
    RawTangentField (I := I) (M := M) :=
  fun x =>
    (cov (fun y => (cov Z y) (Y y)) x) (X x) -
      (cov (fun y => (cov Z y) (X y)) x) (Y x) -
        (cov Z x) (VectorField.mlieBracket I X Y x)

theorem connectionRiemannCurvatureField_swap
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) (x : M) :
    connectionRiemannCurvatureField (I := I) cov Y X Z x =
      -connectionRiemannCurvatureField (I := I) cov X Y Z x := by
  unfold connectionRiemannCurvatureField
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Y) (W := X) (x := x)]
  simp [map_neg, sub_eq_add_neg]
  abel

end DifferentialGeometry.Geometry.Curvature

end
