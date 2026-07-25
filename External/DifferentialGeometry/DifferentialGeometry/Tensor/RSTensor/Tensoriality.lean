import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality















noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold Topology ContDiff

namespace Tensor0SBundle

variable {K : Type*} [NontriviallyNormedField K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  [FiniteDimensional K E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners K E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

section LinearMap

variable {F A : Type*} [NormedAddCommGroup F] [NormedSpace K F]
variable {V : M -> Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
variable [AddCommGroup A] [Module K A]




omit [FiniteDimensional K E] [IsManifold I 1 M] in
theorem tensorialAt_apply_linearMap {x : M} (L : V x →ₗ[K] A) :
    TensorialAt I F (fun σ : (p : M) -> V p => L (σ x)) x := by
  refine ⟨?_, ?_⟩
  · intro f σ _ _
    change L ((f • σ) x) = f x • L (σ x)
    simpa only [Pi.smul_apply] using L.map_smul (f x) (σ x)
  · intro σ τ _ _
    change L ((σ + τ) x) = L (σ x) + L (τ x)
    simpa only [Pi.add_apply] using L.map_add (σ x) (τ x)

end LinearMap

namespace Tensor0SSpace






omit [FiniteDimensional K E] in
theorem tensorialAt_evalSlot {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (i : Fin s)
    (slots : Fin s -> (p : M) -> TangentSpace I p) :
    TensorialAt I E
      (fun X : (p : M) -> TangentSpace I p =>
        A (Function.update (fun j => slots j x) i (X x))) x := by
  classical
  refine ⟨?_, ?_⟩
  · intro f X _ _
    change
      A (Function.update (fun j => slots j x) i ((f • X) x)) =
        f x • A (Function.update (fun j => slots j x) i (X x))
    simpa only [Pi.smul_apply] using
      A.map_update_smul (fun j => slots j x) i (f x) (X x)
  · intro X Y _ _
    change
      A (Function.update (fun j => slots j x) i ((X + Y) x)) =
        A (Function.update (fun j => slots j x) i (X x)) +
          A (Function.update (fun j => slots j x) i (Y x))
    simpa only [Pi.add_apply] using
      A.map_update_add (fun j => slots j x) i (X x) (Y x)

end Tensor0SSpace

namespace TensorRSSpace





theorem tensorialAt_applyInput {r s : ℕ} {x : M}
    (T : TensorRSSpace r s I x) :
    TensorialAt I (Tensor0SModel r K E)
      (fun A : (p : M) -> Tensor0SSpace r I p => T (A x)) x := by
  exact tensorialAt_apply_linearMap (I := I) (F := Tensor0SModel r K E)
    (V := fun p : M => Tensor0SSpace r I p) (x := x)
    (A := Tensor0SSpace s I x)
    (T : Tensor0SSpace r I x →ₗ[K] Tensor0SSpace s I x)



omit [FiniteDimensional K E] in
theorem tensorialAt_evalOutputSlot {r s : ℕ} {x : M}
    (T : TensorRSSpace r s I x) (input : Tensor0SSpace r I x) (i : Fin s)
    (slots : Fin s -> (p : M) -> TangentSpace I p) :
    TensorialAt I E
      (fun X : (p : M) -> TangentSpace I p =>
        (T input) (Function.update (fun j => slots j x) i (X x))) x :=
  Tensor0SSpace.tensorialAt_evalSlot (I := I) (A := T input) i slots



theorem tensorialAt_applyInput_evalOutput {r s : ℕ} {x : M}
    (T : TensorRSSpace r s I x)
    (slots : Fin s -> (p : M) -> TangentSpace I p) :
    TensorialAt I (Tensor0SModel r K E)
      (fun A : (p : M) -> Tensor0SSpace r I p =>
        (T (A x)) (fun j => slots j x)) x := by
  let L : Tensor0SSpace r I x →ₗ[K] K :=
    { toFun := fun A => (T A) (fun j => slots j x)
      map_add' := by
        intro A B
        change (T (A + B)) (fun j => slots j x) =
          (T A) (fun j => slots j x) + (T B) (fun j => slots j x)
        rw [map_add]
        rfl
      map_smul' := by
        intro c A
        change (T (c • A)) (fun j => slots j x) =
          c • (T A) (fun j => slots j x)
        rw [map_smul]
        rfl }
  exact tensorialAt_apply_linearMap (I := I) (F := Tensor0SModel r K E)
    (V := fun p : M => Tensor0SSpace r I p) (x := x) L

end TensorRSSpace

end Tensor0SBundle
