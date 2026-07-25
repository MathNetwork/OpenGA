import DifferentialGeometry.Tensor.RSTensor.Components
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
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
import DifferentialGeometry.Tensor.Multilinear.Tensor
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
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.Auxiliary.PredualBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

























noncomputable section

namespace Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

open Bundle Module
open scoped Manifold ContDiff Topology BigOperators

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
variable [FiniteDimensional K E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners K E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {omega : WithTop ℕ∞} [IsManifold I omega M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

section Components

variable (basis : Module.Basis Idx K (TangentSpace I x))



@[simp]
theorem componentRS_basisTensor_apply {r s : Nat}
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRS_gen (I := I) basis T upper lower =
      (T (basisTensor0S (I := I) basis upper))
        (fun a => basis (lower a)) := by
  rfl


@[simp]
theorem component11_apply
    (T : TensorRSSpace 1 1 I x) (i j : Idx) :
    componentRS_gen (I := I) basis T (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) =
      (T (basisTensor0S (I := I) basis (fun _ : Fin 1 => i)))
        (fun _ : Fin 1 => basis j) := by
  rfl


@[simp]
theorem component13_apply
    (T : TensorRSSpace 1 3 I x) (a i j k : Idx) :
    componentRS_gen (I := I) basis T
        (fun _ : Fin 1 => a)
        (fun q : Fin 3 => if q = 0 then i else if q = 1 then j else k) =
      (T (basisTensor0S (I := I) basis (fun _ : Fin 1 => a)))
        (fun q : Fin 3 => if q = 0 then basis i else if q = 1 then basis j else basis k) := by
  rw [componentRS_apply_gen]
  congr 1
  funext q
  by_cases h0 : q = 0
  · simp [h0]
  · by_cases h1 : q = 1
    · simp [h1]
    · simp [h0, h1]


omit [CompleteSpace K] [FiniteDimensional K E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component02_apply
    (A : Tensor0SSpace 2 I x) (i j : Idx) :
    component0S (I := I) basis A
        (fun q : Fin 2 => if q = 0 then i else j) =
      A (fun q : Fin 2 => if q = 0 then basis i else basis j) := by
  rw [component0S_apply]
  congr 1
  funext q
  by_cases h0 : q = 0 <;> simp [h0]


omit [CompleteSpace K] [FiniteDimensional K E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem component04_apply
    (A : Tensor0SSpace 4 I x) (i j k l : Idx) :
    component0S (I := I) basis A
        (fun q : Fin 4 => if q = 0 then i else if q = 1 then j else if q = 2 then k else l) =
      A (fun q : Fin 4 =>
        if q = 0 then basis i else if q = 1 then basis j else if q = 2 then basis k else basis l) := by
  rw [component0S_apply]
  congr 1
  funext q
  by_cases h0 : q = 0
  · simp [h0]
  · by_cases h1 : q = 1
    · simp [h1]
    · by_cases h2 : q = 2
      · simp [h2]
      · simp [h0, h1, h2]

end Components

section Contractions



@[simp]
theorem model_contract_trace_first_upper_first_lower_apply
    (r s : Nat) (T : TensorRSModel (1 + r) (s + 1) K E) :
    model_contract_trace (𝕜 := K) (E := E) r s T =
      ∑ i : Fin (Module.finrank K E),
        (model_contract_covariant_bilinear
          (𝕜 := K) (E := E) r s
          ((Module.finBasis K E) i))
          ((model_contract_contravariant_first_bilinear
            (𝕜 := K) (E := E) r (s + 1)
            (model_covectorOfCLM (𝕜 := K) (E := E)
              ((Module.finBasis K E).cDualBasis i))) T) := by
  exact model_contract_trace_apply (𝕜 := K) (E := E) r s T



@[simp]
theorem contract_contravariant_first_model_apply
    {r : Nat} (alpha : Tensor0SModel 1 K E) (beta : Tensor0SModel r K E)
    (v : Fin (1 + r) -> E) :
    model_tensorWithCovector_first (𝕜 := K) (E := E) r alpha beta v =
      alpha (v ∘ Fin.castAdd r) * beta (v ∘ Fin.natAdd 1) := by
  change Bundle.continuousMultilinearMap.modelProduct 1 r alpha beta v =
    alpha (v ∘ Fin.castAdd r) * beta (v ∘ Fin.natAdd 1)
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]

end Contractions

end Tensor0SBundle
