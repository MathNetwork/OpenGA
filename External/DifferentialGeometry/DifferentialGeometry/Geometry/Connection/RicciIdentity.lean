import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity

set_option autoImplicit false
set_option linter.style.longLine false









noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]







def nablaDualEval {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (act : V -> R -> R) (conn : V -> V -> V)
    (X : V) (alpha : V -> R) (Y : V) : R :=
  act X (alpha Y) - alpha (conn X Y)


def connectionRmRaw {V : Type*} [Sub V]
    (bracket : V -> V -> V) (conn : V -> V -> V)
    (X Y Z : V) : V :=
  conn X (conn Y Z) - conn Y (conn X Z) - conn (bracket X Y) Z






theorem oneFormRicciIdentity_algebra
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (act : V -> R -> R) (bracket : V -> V -> V) (conn : V -> V -> V)
    (hact_sub : ∀ X f g, act X (f - g) = act X f - act X g)
    (hact_bracket : ∀ X Y f,
      act (bracket X Y) f = act X (act Y f) - act Y (act X f))
    (X Y Z : V) (alpha : V →ₗ[R] R) :
    nablaDualEval act conn X
        (fun W => nablaDualEval act conn Y (fun U => alpha U) W) Z -
      nablaDualEval act conn Y
        (fun W => nablaDualEval act conn X (fun U => alpha U) W) Z -
      nablaDualEval act conn (bracket X Y) (fun U => alpha U) Z =
        -alpha (connectionRmRaw bracket conn X Y Z) := by
  unfold nablaDualEval connectionRmRaw
  rw [hact_sub X (act Y (alpha Z)) (alpha (conn Y Z))]
  rw [hact_sub Y (act X (alpha Z)) (alpha (conn X Z))]
  rw [hact_bracket]
  simp only [map_sub]
  abel









omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
theorem oneFormRicciIdentity_of_connection
    [FiniteDimensional Real E]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  one_form_third_comm_coord_of_christoffelCurv (I := I) inferInstance cov hcov Rm13 x alpha
    nabla2Alpha hRm hcurv hcoord






omit [FiniteDimensional ℝ E] in
omit [IsManifold I 2 M] in
theorem oneFormRicciIdentity_of_smooth_connection
    [FiniteDimensional Real E]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov_one : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  oneFormRicciIdentity_of_connection (I := I) cov Rm13 x alpha nabla2Alpha
    hRm hcov_one (connection_curvature_coord_of_christoffel (I := I) cov hcov x) hcoord


omit [FiniteDimensional ℝ E] in
omit [IsManifold I 2 M] in
theorem oneFormRicciIdentity_of_connection_apply
    [FiniteDimensional Real E]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  one_form_third_covDeriv_comm (I := I) Rm13 alpha nabla2Alpha
    (oneFormRicciIdentity_of_connection (I := I) cov Rm13 x alpha nabla2Alpha
      hRm hcov hcurv hcoord) X Y Z


omit [FiniteDimensional ℝ E] in
omit [IsManifold I 2 M] in
theorem oneFormRicciIdentity_of_smooth_connection_apply
    [FiniteDimensional Real E]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov_one : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  one_form_third_covDeriv_comm (I := I) Rm13 alpha nabla2Alpha
    (oneFormRicciIdentity_of_smooth_connection (I := I) cov Rm13 x alpha
      nabla2Alpha hRm hcov hcov_one hcoord) X Y Z

end DifferentialGeometry.Integral.Connection
