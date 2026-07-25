import DifferentialGeometry.Tensor.RSTensor.CoordinateBasis
import DifferentialGeometry.Tensor.Multilinear.Tensor
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
import DifferentialGeometry.Tensor.Multilinear.Field
import DifferentialGeometry.Tensor.Product.Basis
import DifferentialGeometry.Tensor.Product.Bundle
import DifferentialGeometry.Tensor.Product.Pretrivialization
import DifferentialGeometry.Tensor.Product.Defs
import DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LinearMap
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.Alternating.Curry
import DifferentialGeometry.Tensor.Alternating.Flip
import DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import DifferentialGeometry.Tensor.Alternating.Congr
import Mathlib.LinearAlgebra.Alternating.Basic
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Decomposition
import DifferentialGeometry.Tensor.Auxiliary.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import Mathlib.Topology.FiberBundle.Basic
import DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import DifferentialGeometry.Bundle.SectionRealized

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false








noncomputable section

namespace Tensor0SBundle

open Bundle Module
open scoped Manifold BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

section Covariant

variable {s q : Nat}
variable (basis : Module.Basis Idx 𝕜 (TangentSpace I x))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component0S_add_gen
    (A B : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (A + B) slots =
      component0S (I := I) basis A slots + component0S (I := I) basis B slots := by
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component0S_neg_gen
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (-A) slots =
      -component0S (I := I) basis A slots := by
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component0S_sub_gen
    (A B : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (A - B) slots =
      component0S (I := I) basis A slots - component0S (I := I) basis B slots := by
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component0S_smul_gen
    (c : 𝕜) (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (c • A) slots =
      c * component0S (I := I) basis A slots := by
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component0S_nsmul
    (n : ℕ) (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (n • A) slots =
      n • component0S (I := I) basis A slots := by
  rfl


omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_product_gen
    (A : Tensor0SSpace s I x) (B : Tensor0SSpace q I x)
    (slots : Fin (s + q) -> Idx) :
    component0S (I := I) basis
        (Bundle.continuousMultilinearMap.product_fun
          (𝕜 := 𝕜) (F := E) (E := TangentSpace I) A B) slots =
      component0S (I := I) basis A (slots ∘ Fin.castAdd q) *
        component0S (I := I) basis B (slots ∘ Fin.natAdd s) := by
  have hP := Bundle.continuousMultilinearMap.product_fun_apply
    (𝕜 := 𝕜) (F := E) (E := TangentSpace I) A B
    (fun a => basis (slots a))
  simp only [component0S_apply]
  exact hP

end Covariant

section Mixed

variable {r s : Nat}
variable (basis : Module.Basis Idx 𝕜 (TangentSpace I x))





def componentRS_gen
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) : 𝕜 :=
  component0S (I := I) basis (T (basisTensor0S (I := I) basis upper)) lower

@[simp]
theorem componentRS_apply_gen
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRS_gen (I := I) basis T upper lower =
      (T (basisTensor0S (I := I) basis upper))
        (fun a => basis (lower a)) :=
  rfl



theorem componentRS_gen_congr_slots
    (T : TensorRSSpace r s I x)
    {upper upper' : Fin r -> Idx} {lower lower' : Fin s -> Idx}
    (hu : upper = upper') (hl : lower = lower') :
    componentRS_gen (I := I) basis T upper lower =
      componentRS_gen (I := I) basis T upper' lower' := by
  rw [hu, hl]



theorem componentRS_apply_input_eq_sum
    (T : TensorRSSpace r s I x) (input : Tensor0SSpace r I x)
    (lower : Fin s -> Idx) :
    component0S (I := I) basis (T input) lower =
      ∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper *
          componentRS_gen (I := I) basis T upper lower := by
  have hinput :
      (∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper • basisTensor0S (I := I) basis upper) =
        input := by
    simpa [basisTensor0S] using (tensor0SBasis (I := I) basis r).sum_repr input
  calc
    component0S (I := I) basis (T input) lower =
        component0S (I := I) basis
          (T (∑ upper : Fin r -> Idx,
            component0S (I := I) basis input upper •
              basisTensor0S (I := I) basis upper)) lower := by
          rw [hinput]
    _ = ∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper *
          componentRS_gen (I := I) basis T upper lower := by
          let inputSum : Tensor0SSpace r I x :=
            ∑ upper : Fin r -> Idx,
              component0S (I := I) basis input upper •
                basisTensor0S (I := I) basis upper
          change component0S (I := I) basis (T inputSum) lower =
            ∑ upper : Fin r -> Idx,
              component0S (I := I) basis input upper *
                componentRS_gen (I := I) basis T upper lower
          rw [← congrFun (coordMap0S_apply (I := I) basis (T inputSum)) lower]
          dsimp [inputSum]
          rw [map_sum]
          simp [map_smul]


theorem extRS_basis_gen
    {A B : TensorRSSpace r s I x}
    (h : ∀ upper : Fin r -> Idx, ∀ lower : Fin s -> Idx,
      componentRS_gen (I := I) basis A upper lower =
        componentRS_gen (I := I) basis B upper lower) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro input
  apply ext0S_basis (I := I) basis
  intro lower
  calc
    component0S (I := I) basis (A input) lower =
        ∑ upper : Fin r -> Idx,
          component0S (I := I) basis input upper *
            componentRS_gen (I := I) basis A upper lower :=
      componentRS_apply_input_eq_sum (I := I) basis A input lower
    _ = ∑ upper : Fin r -> Idx,
          component0S (I := I) basis input upper *
            componentRS_gen (I := I) basis B upper lower := by
      refine Finset.sum_congr rfl fun upper _ => ?_
      rw [h upper lower]
    _ = component0S (I := I) basis (B input) lower :=
      (componentRS_apply_input_eq_sum (I := I) basis B input lower).symm

end Mixed

end Tensor0SBundle
