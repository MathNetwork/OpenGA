import DifferentialGeometry.Geometry.Connection.Chart.Basic
import DifferentialGeometry.Tensor.RSTensor.Defs



namespace DifferentialGeometry
namespace Coordinates

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Idx : Type*}
  {u : Set M}

abbrev FrameTensor0SField (s : Nat) :=
  (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := Real) s I x

abbrev FrameTensorRSField (r s : Nat) :=
  (x : M) -> Tensor0SBundle.TensorRSSpace (𝕜 := Real) r s I x

def coframeInFrame
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i : Idx) : TangentSpace I x →ₗ[Real] Real :=
  hframe.coeff i x

omit [FiniteDimensional ℝ E] in
@[simp] theorem coframeInFrame_apply
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i : Idx) (v : TangentSpace I x) :
    coframeInFrame frame hframe x i v = hframe.coeff i x v := by
  rfl

def tensor0SComponentInFrame {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hframe : IsLocalFrameOn I E 1 frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) : Real :=
  T x (fun a => frame (vectorSlots a) x)

omit [FiniteDimensional ℝ E] in
@[simp] theorem tensor0SComponentInFrame_eval {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) :
    tensor0SComponentInFrame T frame hframe x vectorSlots =
      T x (fun a => frame (vectorSlots a) x) := by
  rfl

def tensorRSComponentFromCovariantInputInFrame {r s : Nat}
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (input : (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := Real) r I x)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hframe : IsLocalFrameOn I E 1 frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) : Real :=
  (T x (input x)) (fun a => frame (vectorSlots a) x)

omit [FiniteDimensional ℝ E] in
@[simp] theorem tensorRSComponentFromCovariantInputInFrame_eval {r s : Nat}
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (input : (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := Real) r I x)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M)
    (vectorSlots : Fin s -> Idx) :
    tensorRSComponentFromCovariantInputInFrame T input frame hframe x vectorSlots =
      (T x (input x)) (fun a => frame (vectorSlots a) x) := by
  rfl

end

end Coordinates
end DifferentialGeometry
