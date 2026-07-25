import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace

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
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}







section LocalFrame

variable {u : Set M}

omit [Fintype Idx] [DecidableEq Idx] in
theorem ricciCompAt_eq_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ricciComp (I := I) Ric frame x i j := by
  unfold ricciCompAt ricciComp component0S slots2 vec2
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

omit [Fintype Idx] [DecidableEq Idx] in
theorem rm04CompAt_eq_frame
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j k l : Idx) :
    rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) i j k l =
      rm04Comp (I := I) Rm04 frame x i j k l := by
  unfold rm04CompAt rm04Comp component0S slots4 vec4
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

omit [DecidableEq Idx] in
theorem ricciTraceAt_of_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) :
    RicciRealizesRm04TraceAt (I := I) (Ric x) (Rm04 x) (gInv x)
      (hframe.toBasisAt hx) := by
  intro X Y
  simpa [RicciTensorRealizesRm04TraceInFrame, tensor02ToField, tensor04ToField,
    IsLocalFrameOn.toBasisAt_coe] using hRic x X Y



def RicciTensorRealizesRm04FirstTraceInFrame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    Ric x (vec2 (frame i x) (frame j x)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Rm04 x (vec4 (frame k x) (frame i x) (frame j x) (frame l x))



omit [DecidableEq Idx] in
theorem ricciFirstTraceAt_of_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04FirstTraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) :
    RicciRealizesRm04FirstTraceAt (I := I) (Ric x) (Rm04 x) (gInv x)
      (hframe.toBasisAt hx) := by
  intro i j
  simpa [RicciTensorRealizesRm04FirstTraceInFrame, IsLocalFrameOn.toBasisAt_coe]
    using hRic x i j


omit [DecidableEq Idx] in
theorem ricciComp_eq_firstTrace_rm04_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04FirstTraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l := by
  have hAt := ricciFirstTraceAt_of_frame
    (I := I) Ric Rm04 gInv frame hframe hRic hx
  rw [ricciCompAt_apply]
  simp_rw [rm04CompAt_apply]
  exact hAt i j

omit [DecidableEq Idx] in
theorem scalarTraceAt_of_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    ScalarRealizesRicciTraceAt (I := I) (scalar x) (Ric x) (gInv x)
      (hframe.toBasisAt hx) := by
  simpa [ScalarRealizesRicciTraceAt, ScalarSectionRealizesRicciTraceInFrame,
    tensor02ToField, IsLocalFrameOn.toBasisAt_coe] using hScalar x

omit [DecidableEq Idx] in
theorem ricciComp_eq_trace_rm04_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l := by
  exact ricciComp_eq_trace_rm04 (I := I) (hframe.toBasisAt hx) (Ric x) (Rm04 x)
    (gInv x) (ricciTraceAt_of_frame (I := I) Ric Rm04 gInv frame hframe hRic hx) i j

omit [DecidableEq Idx] in
theorem scalar_eq_trace_ricci_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j := by
  exact scalar_eq_trace_ricci (I := I) (hframe.toBasisAt hx) (scalar x) (Ric x)
    (gInv x) (scalarTraceAt_of_frame (I := I) scalar Ric gInv frame hframe hScalar hx)

end LocalFrame
end DifferentialGeometry.Integral.Connection
