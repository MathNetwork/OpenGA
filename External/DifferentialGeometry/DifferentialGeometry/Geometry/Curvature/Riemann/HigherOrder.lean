import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Pointwise
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion









suppress_compilation

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false

open Bundle DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]




def nabla2VectorField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) :
    RawTangentField (I := I) (M := M) :=
  fun x =>
    (cov (fun p : M => (cov Z p) (Y p)) x) (X x) -
      (cov Z x) ((cov Y x) (X x))

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp]
theorem nabla2VectorField_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) (x : M) :
    nabla2VectorField (I := I) cov X Y Z x =
      (cov (fun p : M => (cov Z p) (Y p)) x) (X x) -
        (cov Z x) ((cov Y x) (X x)) :=
  rfl



theorem nabla2VectorField_skew_eq_curvature_sub_torsion
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y Z : RawTangentField (I := I) (M := M)} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    nabla2VectorField (I := I) cov X Y Z x -
        nabla2VectorField (I := I) cov Y X Z x =
      connectionRiemannCurvatureField (I := I) cov X Y Z x -
        (cov Z x) (cov.torsion x (X x) (Y x)) := by
  rw [cov.torsion_apply hX hY]
  unfold nabla2VectorField connectionRiemannCurvatureField
  simp [sub_eq_add_neg, map_add, add_assoc, add_left_comm, add_comm]
  abel



theorem connectionRiemannCurvatureField_eq_nabla2VectorField_skew_of_torsion_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y Z : RawTangentField (I := I) (M := M)} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (htor : cov.torsion x (X x) (Y x) = 0) :
    connectionRiemannCurvatureField (I := I) cov X Y Z x =
      nabla2VectorField (I := I) cov X Y Z x -
        nabla2VectorField (I := I) cov Y X Z x := by
  have h :=
    nabla2VectorField_skew_eq_curvature_sub_torsion
      (I := I) cov (X := X) (Y := Y) (Z := Z) (x := x) hX hY
  rw [htor, map_zero, sub_zero] at h
  exact h.symm



theorem riemannCurvatureAux_eq_nabla2VectorField_skew_of_torsion_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y Z : RawTangentField (I := I) (M := M)} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (htor : cov.torsion x (X x) (Y x) = 0) :
    CovariantDerivative.riemannCurvatureAux (I := I) cov X Y Z x =
      nabla2VectorField (I := I) cov X Y Z x -
        nabla2VectorField (I := I) cov Y X Z x := by
  rw [CovariantDerivative.riemannCurvatureAux_eq_connectionRiemannCurvatureField]
  exact connectionRiemannCurvatureField_eq_nabla2VectorField_skew_of_torsion_zero
    (I := I) cov hX hY htor




theorem leviCivita_connectionRiemannCurvatureField_eq_nabla2VectorField_skew
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {X Y Z : RawTangentField (I := I) (M := M)} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    connectionRiemannCurvatureField (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) X Y Z x =
      nabla2VectorField (I := I)
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) X Y Z x -
        nabla2VectorField (I := I)
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Y X Z x := by
  refine connectionRiemannCurvatureField_eq_nabla2VectorField_skew_of_torsion_zero
    (I := I) (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) hX hY ?_
  have htf :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isTorsionFree (I := I) g
  change (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g).torsion x
    (X x) (Y x) = 0
  rw [htf x]
  simp

end DifferentialGeometry.Integral.Connection
