import DifferentialGeometry.Geometry.Curvature.Basic
import DifferentialGeometry.Tensor.RSTensor.Field

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false








noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


section MetricTrace

variable {Idx : Type*} [Fintype Idx]


def RicciRealizesRm04TraceInFrame
    (Ric : RawTwoTensorField (I := I) (M := M))
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x X Y, Ric x X Y =
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame x X Y

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem ricci_comp_eq_trace
    (Ric : RawTwoTensorField (I := I) (M := M))
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciRealizesRm04TraceInFrame (I := I) Ric Riemann04 gInv frame)
    (x : M) (i j : Idx) :
    Ric x (frame i x) (frame j x) =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Riemann04 x (frame k x) (frame i x) (frame j x)
          (frame l x) := by
  simpa [ricciFromRiemann04TraceInFrame] using hRic x (frame i x) (frame j x)











abbrev scalarCurvatureFromRicciTraceInFrame
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : M -> Real :=
  scalarFromRicciTraceInFrame (I := I) Ric gInv frame

omit [FiniteDimensional ℝ E] in
omit [IsManifold I ∞ M] in
@[simp]
theorem scalarCurvatureFromRicciTraceInFrame_apply
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) (x : M) :
    scalarCurvatureFromRicciTraceInFrame (I := I) Ric gInv frame x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) := by
  exact scalarFromRicciTraceInFrame_apply (I := I) Ric gInv frame x


def ScalarRealizesRicciTraceInFrame
    (scalar : M -> Real)
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x, scalar x = scalarFromRicciTraceInFrame (I := I) Ric gInv frame x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem scalar_eq_trace
    (scalar : M -> Real)
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : ScalarRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    (x : M) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) := by
  simpa [scalarFromRicciTraceInFrame] using hScalar x


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem scalarCurvatureFromRicciTraceInFrame_realizes
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    ScalarRealizesRicciTraceInFrame (I := I)
      (scalarCurvatureFromRicciTraceInFrame (I := I) Ric gInv frame)
      Ric gInv frame := by
  intro x
  rfl

end MetricTrace

end DifferentialGeometry.Integral.Connection
