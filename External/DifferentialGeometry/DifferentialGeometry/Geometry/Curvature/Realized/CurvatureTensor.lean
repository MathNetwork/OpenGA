import DifferentialGeometry.Geometry.Curvature.Tensor
import DifferentialGeometry.Geometry.Curvature.Realized.Curvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false









noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev SmoothTangentSection :=
  ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)








def Rm13RealizesConnection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall (X Y Z : SmoothTangentSection (I := I) (M := M)) (x : M)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x),
      Rm13 x alpha (vec3 (X x) (Y x) (Z x)) =
        cotangentToDual_gen (I := I) alpha
          ((connectionRiemannCurvatureField (I := I) cov
            (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p)) x)



def Rm04RealizesConnection
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M)) : Prop :=
  forall (X Y Z W : SmoothTangentSection (I := I) (M := M)) (x : M),
    Rm04 x (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x) ((connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p)) x)


theorem rm04_eq_of_realizes [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {A B : Tensor04Section (I := I) (M := M)}
    (hA : Rm04RealizesConnection (I := I) g cov A)
    (hB : Rm04RealizesConnection (I := I) g cov B)
    (x : M) :
    A x = B x := by
  classical
  apply tensor0SSpace_ext 4 x
  intro v
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 0)
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 1)
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 2)
  obtain ⟨W, hW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 3)
  have hv : v = vec4 (I := I) (X x) (Y x) (Z x) (W x) := by
    funext i
    fin_cases i <;> simp_all [vec4]
  rw [hv, hA X Y Z W x, hB X Y Z W x]


def RicciTensorRealizesRm13Trace
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall x : M, Ric x = ricciFromRm13At (I := I) (M := M) (Rm13 x)


def RicciTensorRealizesRm04TraceInFrame
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  DifferentialGeometry.Integral.Connection.RicciRealizesRm04TraceInFrame (I := I)
    (tensor02ToField (I := I) Ric) (tensor04ToField (I := I) Rm04) gInv frame


def ScalarSectionRealizesRicciTraceInFrame
    {Idx : Type*} [Fintype Idx]
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceInFrame (I := I)
    scalar (tensor02ToField (I := I) Ric) gInv frame


theorem rm04_comp_eq_connection
    {Idx : Type*}
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : Rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) Rm04 (fun i y => frame i y) x a b c d =
      g.inner x (frame d x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)) x) := by
  simpa [rm04Comp] using
    hRm (frame a) (frame b) (frame c) (frame d) x

theorem ricciComp_eq_trace
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) Ric frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * rm04Comp (I := I) Rm04 frame x k i j l := by
  simpa [RicciTensorRealizesRm04TraceInFrame, tensor02ToField, tensor04ToField,
    ricciComp, rm04Comp] using
    DifferentialGeometry.Integral.Connection.ricci_comp_eq_trace (I := I)
      (tensor02ToField (I := I) Ric) (tensor04ToField (I := I) Rm04) gInv frame hRic x i j

theorem scalarSection_eq_trace
    {Idx : Type*} [Fintype Idx]
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    (x : M) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciComp (I := I) Ric frame x i j := by
  simpa [ScalarSectionRealizesRicciTraceInFrame, tensor02ToField, ricciComp] using
    DifferentialGeometry.Integral.Connection.scalar_eq_trace (I := I)
      scalar (tensor02ToField (I := I) Ric) gInv frame hScalar x

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hframe : IsLocalFrameOn I E ∞ (fun i y => frame i y) u)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) Rm13 (fun i y => frame i y) hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) := by
  simpa [rm13Comp] using
    hRm (frame b) (frame c) (frame d) x (dualToCotangent_gen (hframe.coeff a x))

namespace CurvatureTensorData

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (K : CurvatureTensorData (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hframe : IsLocalFrameOn I E ∞ (fun i y => frame i y) u)
    (hRm : Rm13RealizesConnection (I := I) cov K.rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) K.rm13 (fun i y => frame i y) hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) :=
  DifferentialGeometry.Integral.Connection.rm13_comp_eq_connection (I := I) cov K.rm13 frame hframe hRm x a b c d

theorem rm04_comp_eq_connection
    {Idx : Type*}
    (K : CurvatureTensorData (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : Rm04RealizesConnection (I := I) g cov K.rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) K.rm04 (fun i y => frame i y) x a b c d =
      g.inner x (frame d x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)) x) :=
  DifferentialGeometry.Integral.Connection.rm04_comp_eq_connection (I := I) g cov K.rm04 frame hRm x a b c d

theorem ricci_comp_eq_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureTensorData (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * rm04Comp (I := I) K.rm04 frame x k i j l :=
  DifferentialGeometry.Integral.Connection.ricciComp_eq_trace (I := I) K.ricci K.rm04 gInv frame hRic x i j

theorem ricci_comp_eq_connection_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureTensorData (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : Rm04RealizesConnection (I := I) g cov K.rm04)
    (hRic : RicciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv
      (fun i y => frame i y))
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci (fun i y => frame i y) x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          g.inner x (frame l x) ((connectionRiemannCurvatureField (I := I) cov
            (fun y => frame k y) (fun y => frame i y) (fun y => frame j y)) x) := by
  rw [CurvatureTensorData.ricci_comp_eq_trace (I := I) K gInv
    (fun i y => frame i y) hRic x i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [DifferentialGeometry.Integral.Connection.rm04_comp_eq_connection (I := I) g cov K.rm04 frame hRm x k i j l]

theorem scalar_eq_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureTensorData (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : ScalarSectionRealizesRicciTraceInFrame (I := I) K.scalar K.ricci gInv frame)
    (x : M) :
    K.scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciComp (I := I) K.ricci frame x i j :=
  DifferentialGeometry.Integral.Connection.scalarSection_eq_trace (I := I) K.scalar K.ricci gInv frame hScalar x

end CurvatureTensorData

end DifferentialGeometry.Integral.Connection
