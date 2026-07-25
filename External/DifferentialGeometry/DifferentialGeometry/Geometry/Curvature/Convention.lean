import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RiemannFromRicci

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false























noncomputable section

namespace DifferentialGeometry.Integral.Connection


open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]


@[simp]
theorem ricciFromRm13At_eq_contract_trace
    (Rm13 : Tensor13At (I := I) (M := M) x) :
    ricciFromRm13At (I := I) (M := M) Rm13 =
      (contract_trace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        (scalarOne0S (I := I) x) := by
  rfl


theorem rm04LowersRm13At_convention
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (h : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (X Y Z W : TangentSpace I x) :
  Rm04 (vec4 X Y Z W) =
      Rm13 (dualToCotangent_gen (I := I) ((tangentFlatLinear_gen (I := I) g x) W))
        (vec3 X Y Z) :=
  h X Y Z W


omit [FiniteDimensional ℝ E] in
theorem tensor04StdAt_convention
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) Rm04 X Y Z W =
      Rm04 (vec4 X Y Z W) := by
  rfl



theorem ricciFromRm13At_rm04_first_trace_convention
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (_hInvSym : forall a b : Idx, gInv a b = gInv b a)
    (i j : Idx) :
    DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis
        (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv k l * DifferentialGeometry.Integral.Connection.rm04CompAt (I := I) basis Rm04 k i j l := by
  have h := DifferentialGeometry.Integral.Connection.ricciFromRm13_comp_eq_rm04_trace
    (I := I) g basis gInv hinv Rm13 Rm04 hLower i j
  simpa using h


namespace Realized

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem rm04RealizesConnection_convention
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (h : Rm04RealizesConnection (I := I) g cov Rm04)
    (X Y Z W : SmoothTangentSection (I := I) (M := M)) (x : M) :
    Rm04 x (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x) ((connectionRiemannCurvatureField (I := I) cov X Y Z) x) :=
  h X Y Z W x



theorem rm04StdRealizesConnection_convention
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (h : Rm04RealizesConnection (I := I) g cov Rm04)
    (X Y Z W : SmoothTangentSection (I := I) (M := M)) (x : M) :
    DifferentialGeometry.Integral.Connection.tensor04StdAt (I := I) (M := M) (Rm04 x)
        (X x) (Y x) (Z x) (W x) =
      g.inner x (W x) ((connectionRiemannCurvatureField (I := I) cov X Y Z) x) :=
  h X Y Z W x

end Realized

namespace DimensionThree

open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}



omit [FiniteDimensional ℝ E] in
@[simp]
theorem standardRmCompAt_slot_convention
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (i j k l : Fin 3) :
    standardRmCompAt (I := I) basis Rm04 i j k l =
      rm04CompAt (I := I) basis Rm04 i j k l := by
  rfl

end DimensionThree

end DifferentialGeometry.Integral.Connection
