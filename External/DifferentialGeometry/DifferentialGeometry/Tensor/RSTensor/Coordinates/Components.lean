import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis
import DifferentialGeometry.Tensor.Multilinear.Tensor

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


noncomputable section

namespace Tensor0SBundle

open Bundle Module
open scoped Manifold BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

section Covariant

variable {s q : Nat}
variable (basis : Module.Basis Idx Real (TangentSpace I x))

omit [FiniteDimensional ℝ E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component0S_add
    (A B : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (A + B) slots =
      component0S (I := I) basis A slots + component0S (I := I) basis B slots := by
  rfl

omit [FiniteDimensional ℝ E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component0S_smul
    (c : Real) (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (c • A) slots =
      c * component0S (I := I) basis A slots := by
  rfl

omit [FiniteDimensional ℝ E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_product
    (A : Tensor0SSpace s I x) (B : Tensor0SSpace q I x)
    (slots : Fin (s + q) -> Idx) :
    component0S (I := I) basis
        (Bundle.continuousMultilinearMap.product_fun
          (𝕜 := Real) (F := E) (E := TangentSpace I) A B) slots =
      component0S (I := I) basis A (slots ∘ Fin.castAdd q) *
        component0S (I := I) basis B (slots ∘ Fin.natAdd s) := by
  have hP := Bundle.continuousMultilinearMap.product_fun_apply
    (𝕜 := Real) (F := E) (E := TangentSpace I) A B
    (fun a => basis (slots a))
  simp only [component0S_apply]
  exact hP

end Covariant

section Mixed

variable {r s : Nat}
variable (basis : Module.Basis Idx Real (TangentSpace I x))

def componentRS
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) : Real :=
  component0S (I := I) basis (T (basisTensor0S (I := I) basis upper)) lower

@[simp]
theorem componentRS_apply
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRS (I := I) basis T upper lower =
      (T (basisTensor0S (I := I) basis upper))
        (fun a => basis (lower a)) :=
  rfl



theorem componentRS_congr_slots
    (T : TensorRSSpace r s I x)
    {upper upper' : Fin r -> Idx} {lower lower' : Fin s -> Idx}
    (hu : upper = upper') (hl : lower = lower') :
    componentRS (I := I) basis T upper lower =
      componentRS (I := I) basis T upper' lower' := by
  rw [hu, hl]

private theorem componentRS_expand_input
    (T : TensorRSSpace r s I x) (input : Tensor0SSpace r I x)
    (lower : Fin s -> Idx) :
    component0S (I := I) basis (T input) lower =
      ∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper *
          componentRS (I := I) basis T upper lower := by
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
          componentRS (I := I) basis T upper lower := by
          let inputSum : Tensor0SSpace r I x :=
            ∑ upper : Fin r -> Idx,
              component0S (I := I) basis input upper •
                basisTensor0S (I := I) basis upper
          change component0S (I := I) basis (T inputSum) lower =
            ∑ upper : Fin r -> Idx,
              component0S (I := I) basis input upper *
                componentRS (I := I) basis T upper lower
          rw [← congrFun (coordMap0S_apply (I := I) basis (T inputSum)) lower]
          dsimp [inputSum]
          rw [map_sum]
          simp [map_smul]

theorem extRS_basis
    {A B : TensorRSSpace r s I x}
    (h : ∀ upper : Fin r -> Idx, ∀ lower : Fin s -> Idx,
      componentRS (I := I) basis A upper lower =
        componentRS (I := I) basis B upper lower) :
    A = B := by

  have key : ∀ input : Tensor0SSpace r I x, A input = B input := by
    intro input
    apply ext0S_basis (I := I) basis
    intro lower
    rw [componentRS_expand_input (I := I) basis A input lower,
      componentRS_expand_input (I := I) basis B input lower]
    refine Finset.sum_congr rfl fun upper _ => ?_
    rw [h upper lower]
  exact ContinuousLinearMap.ext (f := A) (g := B) key

end Mixed

end Tensor0SBundle
